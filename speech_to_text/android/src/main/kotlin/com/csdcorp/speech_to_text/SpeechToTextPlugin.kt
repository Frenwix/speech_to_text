package com.csdcorp.speech_to_text

import android.Manifest
import android.R.attr.data
import android.annotation.TargetApi
import android.app.Activity
import android.bluetooth.BluetoothAdapter
import android.bluetooth.BluetoothHeadset
import android.bluetooth.BluetoothProfile
import android.content.BroadcastReceiver
import android.content.ComponentName
import android.content.Context
import android.content.Intent
import android.content.pm.PackageManager
import android.content.pm.ResolveInfo
import android.media.AudioFormat
import android.media.AudioRecord
import android.media.MediaRecorder
import android.net.Uri
import android.os.Build
import android.os.Bundle
import android.os.Handler
import android.os.Looper
import android.os.ParcelFileDescriptor
import android.speech.*
import android.speech.SpeechRecognizer.createOnDeviceSpeechRecognizer
import android.speech.SpeechRecognizer.createSpeechRecognizer
import android.util.Log
import androidx.annotation.NonNull
import androidx.core.app.ActivityCompat
import androidx.core.content.ContextCompat
import io.flutter.embedding.engine.plugins.FlutterPlugin
import io.flutter.embedding.engine.plugins.activity.ActivityAware
import io.flutter.embedding.engine.plugins.activity.ActivityPluginBinding
import io.flutter.plugin.common.BinaryMessenger
import io.flutter.plugin.common.MethodCall
import io.flutter.plugin.common.MethodChannel
import io.flutter.plugin.common.MethodChannel.MethodCallHandler
import io.flutter.plugin.common.MethodChannel.Result
import io.flutter.plugin.common.PluginRegistry
import org.json.JSONArray
import org.json.JSONObject
import java.util.*
import java.util.concurrent.Executors


enum class SpeechToTextErrors {
    multipleRequests,
    unimplemented,
    noLanguageIntent,
    recognizerNotAvailable,
    missingOrInvalidArg,
    missingContext,
    unknown
}

enum class SpeechToTextCallbackMethods {
    textRecognition,
    notifyStatus,
    notifyError,
    soundLevelChange,
}

enum class SpeechToTextStatus {
    listening,
    notListening,
    unavailable,
    available,
    done,
    doneNoResult,
}

enum class ListenMode {
    deviceDefault,
    dictation,
    search,
    confirmation,
}

enum class ResultType {
    partial,
    intermediate,
    finalResult,
}

fun ResultType.intValue(): Int {
    return when (this) {
        ResultType.partial -> 0
        ResultType.intermediate -> 1
        ResultType.finalResult -> 2
    }
}

const val pluginChannelName = "plugin.csdcorp.com/speech_to_text"

@TargetApi(8)
/** SpeechToTextPlugin */
public class SpeechToTextPlugin :
        MethodCallHandler, RecognitionListener,
        PluginRegistry.RequestPermissionsResultListener, FlutterPlugin,
        ActivityAware {
    private var pluginContext: Context? = null
    private var channel: MethodChannel? = null
    private val minSdkForSpeechSupport = 21
    private val brokenStopSdk = 29
    private val minSdkForOnDeviceSpeechSupport = 31
    private val speechToTextPermissionCode = 28521
    private val missingConfidence: Double = -1.0
    private var speechThresholdRms = 9
    private val logTag = "SpeechToTextPlugin"
    private var recognizerStops = true
    private var currentActivity: Activity? = null
    private var activeResult: Result? = null
    private var initializedSuccessfully: Boolean = false
    private var permissionToRecordAudio: Boolean = false
    private var listening = false
    private var debugLogging: Boolean = false
    private var alwaysUseStop: Boolean = false
    private var intentLookup: Boolean = false
    private var noBluetoothOpt: Boolean = false // user-defined option
    private var bluetoothDisabled = true // final bluetooth state (combines user-defined option and permissions)
    private var resultSent: Boolean = false
    private var lastOnDevice: Boolean = false
    // Feed the recogniser OUR capture instead of letting it open its own
    // (#559). While this app owns a Telecom call, Android hands a
    // different-process recogniser a successfully-opened input that reads
    // zeros — no error, no denial, just silence — so on-device recognition
    // can never hear the user. This app's own capture IS allowed (it owns
    // the call), so capture here and pipe PCM in via EXTRA_AUDIO_SOURCE.
    private var appAudioSource: Boolean = false
    private var audioPumpThread: Thread? = null
    private var pendingReadSide: ParcelFileDescriptor? = null
    @Volatile private var audioPumpRunning: Boolean = false
    private val appAudioSampleRate = 16000
    private var speechRecognizer: SpeechRecognizer? = null
    private var recognizerIntent: Intent? = null
    private var bluetoothAdapter: android.bluetooth.BluetoothAdapter? = null
    private var pairedDevices: Set<android.bluetooth.BluetoothDevice>? = null
    private var activeBluetooth: android.bluetooth.BluetoothDevice? = null
    private var bluetoothHeadset: BluetoothHeadset? = null
    private var previousRecognizerLang: String? = null
    private var previousPartialResults: Boolean = true
    private var previousListenMode: ListenMode = ListenMode.deviceDefault
    private var previousPauseFor: Int? = null
    private var lastFinalTime: Long = 0
    private var speechStartTime: Long = 0
    private var minRms: Float = 1000.0F
    private var maxRms: Float = -100.0F
    private val handler: Handler = Handler(Looper.getMainLooper())
    private val defaultLanguageTag: String = Locale.getDefault().toLanguageTag()
    private var timer: Timer? = null
    private lateinit var timerTask: TimerTask
    private var downloadRecognizer: SpeechRecognizer? = null
    private val availabilityTimeoutMs: Long = 4000

    override fun onAttachedToEngine(@NonNull flutterPluginBinding: FlutterPlugin.FlutterPluginBinding) {

        onAttachedToEngine(flutterPluginBinding.getApplicationContext(), flutterPluginBinding.getBinaryMessenger());
    }

    private fun onAttachedToEngine(applicationContext: Context, messenger: BinaryMessenger) {
        this.pluginContext = applicationContext;
        channel = MethodChannel(messenger, pluginChannelName)
        channel?.setMethodCallHandler(this)
    }

    override fun onDetachedFromEngine(@NonNull binding: FlutterPlugin.FlutterPluginBinding) {
        this.pluginContext = null;
        channel?.setMethodCallHandler(null)
        channel = null
    }

    override fun onDetachedFromActivity() {
        currentActivity = null
    }

    override fun onReattachedToActivityForConfigChanges(binding: ActivityPluginBinding) {
        currentActivity = binding.activity
        binding.addRequestPermissionsResultListener(this)
    }

    override fun onAttachedToActivity(binding: ActivityPluginBinding) {
        currentActivity = binding.activity
        binding.addRequestPermissionsResultListener(this)
    }

    override fun onDetachedFromActivityForConfigChanges() {
        currentActivity = null
    }

    override fun onMethodCall(@NonNull call: MethodCall, @NonNull rawrResult: Result) {
        val result = ChannelResultWrapper(rawrResult)
        try {
            when (call.method) {
                "has_permission" -> hasPermission(result)
                "initialize" -> {
                    var dlog = call.argument<Boolean>("debugLogging")
                    if (null != dlog) {
                        debugLogging = dlog
                    }
                    var ausOpt = call.argument<Boolean>("alwaysUseStop")
                    if (null != ausOpt) {
                        alwaysUseStop = ausOpt == true
                    }
                    var iOpt = call.argument<Boolean>("intentLookup")
                    if (null != iOpt) {
                        intentLookup = iOpt == true
                    }
                    var noBtOpt = call.argument<Boolean>("noBluetooth")
                    if (null != noBtOpt) {
                        noBluetoothOpt = noBtOpt == true
                    }
                    initialize(result)
                }
                "listen" -> {
                    var localeId = call.argument<String>("localeId")
                    if (null == localeId) {
                        localeId = defaultLanguageTag
                    }
                    localeId = localeId.replace( '_', '-')
                    var partialResults = call.argument<Boolean>("partialResults")
                    if (null == partialResults) {
                        partialResults = true
                    }
                    var onDevice = call.argument<Boolean>("onDevice")
                    if ( null == onDevice ) {
                        onDevice = false
                    }
                    val listenModeIndex = call.argument<Int>("listenMode")
                    if ( null == listenModeIndex ) {
                        result.error(SpeechToTextErrors.missingOrInvalidArg.name,
                                "listenMode is required", null)
                        return
                    }
                    val pauseFor =
                        call.argument<Int?>("pauseFor")
                    startListening(result, localeId, partialResults, listenModeIndex, onDevice, pauseFor )
                }
                "setAppAudioSource" -> {
                    // Opt-in, set by the host app rather than inferred: only the
                    // app knows it is inside a call, and this trades the
                    // recogniser's own (better-tuned) capture for one that is
                    // merely audible, so it must not be the default.
                    appAudioSource = call.argument<Boolean>("enabled") == true
                    result.success(appAudioSource)
                }
                "stop" -> stopListening(result)
                "cancel" -> cancelListening(result)
                "locales" -> locales(result)
                "recognitionAvailability" -> {
                    val localeId = call.argument<String>("localeId")
                    if (null == localeId) {
                        result.error(SpeechToTextErrors.missingOrInvalidArg.name,
                                "localeId is required", null)
                        return
                    }
                    recognitionAvailability(result, localeId.replace('_', '-'))
                }
                "triggerModelDownload" -> {
                    val localeId = call.argument<String>("localeId")
                    if (null == localeId) {
                        result.error(SpeechToTextErrors.missingOrInvalidArg.name,
                                "localeId is required", null)
                        return
                    }
                    triggerModelDownload(result, localeId.replace('_', '-'))
                }
                else -> result.notImplemented()
            }
        } catch (exc: Exception) {
            Log.e(logTag, "Unexpected exception", exc)
            result.error(SpeechToTextErrors.unknown.name,
                    "Unexpected exception", exc.localizedMessage)
        }
    }

    private fun hasPermission(result: Result) {
        if (sdkVersionTooLow()) {
            result.success(false)
            return
        }
        debugLog("Start has_permission")
        val localContext = pluginContext
        if (localContext != null) {
            val hasPerm = ContextCompat.checkSelfPermission(localContext,
                    Manifest.permission.RECORD_AUDIO) == PackageManager.PERMISSION_GRANTED
            result.success(hasPerm)
        }
    }

    private fun initialize(result: Result) {
        if (sdkVersionTooLow()) {
            result.success(false)
            return
        }
        recognizerStops = Build.VERSION.SDK_INT != brokenStopSdk || alwaysUseStop
        debugLog("Start initialize")
        if (null != activeResult) {
            result.error(SpeechToTextErrors.multipleRequests.name,
                    "Only one initialize at a time", null)
            return
        }
        activeResult = result
        initializeIfPermitted(pluginContext)
    }

    private fun sdkVersionTooLow(): Boolean {
        if (Build.VERSION.SDK_INT < minSdkForSpeechSupport) {
            return true;
        }
        return false;
    }

    private fun isNotInitialized(): Boolean {
        return !initializedSuccessfully
    }

    private fun isListening(): Boolean {
        return listening
    }

    private fun isNotListening(): Boolean {
        return !listening
    }

    private fun startListening(result: Result, languageTag: String, partialResults: Boolean,
                               listenModeIndex: Int, onDevice: Boolean, pauseFor: Int?) {
        if (sdkVersionTooLow() || isNotInitialized() || isListening()) {
            result.success(false)
            return
        }
        var listenMode = enumValues<ListenMode>()[listenModeIndex]

        resultSent = false
        createRecognizer(onDevice, listenMode, pauseFor)
        minRms = 1000.0F
        maxRms = -100.0F
        debugLog("Start listening")

        optionallyStartBluetooth()
        setupRecognizerIntent(languageTag, partialResults, listenMode, onDevice, pauseFor )
        handler.post {
            run {
                // Per listen, never baked into the cached intent:
                // setupRecognizerIntent reuses one Intent across listens, and a
                // pipe fd left on it would be closed and useless by the second.
                attachAppAudioSource()
                speechRecognizer?.startListening(recognizerIntent)
                // Deliberately NOT closed here. SpeechRecognizerImpl.startListening
                // is asynchronous — it posts to its own handler and parcels the
                // intent LATER, so closing on return raced the parcel write and
                // died with "Bad file descriptor" / ERROR_CLIENT on every listen
                // (#559, observed 2026-08-20). The read end lives until
                // stopAppAudioPump; keeping it open cannot delay EOF, which is
                // signalled by the WRITE end closing.
            }
        }
        speechStartTime = System.currentTimeMillis()
        notifyListening(isRecording = true)
        result.success(true)
        debugLog("Start listening done")
    }

    private fun optionallyStartBluetooth() {
        if ( bluetoothDisabled ) return
        val context = pluginContext
        val lbt = bluetoothAdapter
        val lpaired = pairedDevices
        val lhead = bluetoothHeadset
        if (null != lbt && null!= lhead && null != lpaired && lbt.isEnabled) {
            for (tryDevice in lpaired) {
                //This loop tries to start VoiceRecognition mode on every paired device until it finds one that works(which will be the currently in use bluetooth headset)
                if (lhead.startVoiceRecognition(tryDevice)) {
                    debugLog("Starting bluetooth voice recognition")
                    activeBluetooth = tryDevice;
                    break
                }
            }
        }
    }

    private fun stopListening(result: Result) {
        if (sdkVersionTooLow() || isNotInitialized() || isNotListening()) {
            result.success(false)
            return
        }
        debugLog("Stop listening")
        stopAppAudioPump()
        handler.post {
            run {
                speechRecognizer?.stopListening()
            }
        }
        if ( !recognizerStops ) {
            destroyRecognizer()
        }
        notifyListening(isRecording = false)
        result.success(true)
        debugLog("Stop listening done")
    }

    private fun cancelListening(result: Result) {
        if (sdkVersionTooLow() || isNotInitialized() || isNotListening()) {
            result.success(false)
            return
        }
        debugLog("Cancel listening")
        stopAppAudioPump()
        handler.post {
            run {
                speechRecognizer?.cancel()
            }
        }
        if ( !recognizerStops ) {
            destroyRecognizer()
        }
        notifyListening(isRecording = false)
        result.success(true)
        debugLog("Cancel listening done")
    }

    private fun locales(result: Result) {
        if (sdkVersionTooLow()) {
            result.success(false)
            return
        }
        var hasPermission = ContextCompat.checkSelfPermission(pluginContext!!,
            Manifest.permission.RECORD_AUDIO) == PackageManager.PERMISSION_GRANTED
        if (Build.VERSION.SDK_INT >= 33 && hasPermission) {
            if ( SpeechRecognizer.isOnDeviceRecognitionAvailable(pluginContext!!)) {
                // after much experimentation this was the only working iteration of the
                // checkRecognitionSupport that works.
            var recognizer = createOnDeviceSpeechRecognizer(pluginContext!!)
            var recognizerIntent = Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH)
//            var recognizer = createSpeechRecognizer(pluginContext!!)
//            var recognizerIntent = Intent(RecognizerIntent.ACTION_GET_LANGUAGE_DETAILS)
            recognizer?.checkRecognitionSupport(recognizerIntent, Executors.newSingleThreadExecutor(),
                object : RecognitionSupportCallback {
                    override fun onSupportResult(recognitionSupport: RecognitionSupport) {
                        var details = LanguageDetailsChecker( result, debugLogging )
                        details.createResponse(recognitionSupport.supportedOnDeviceLanguages )
                        recognizer?.destroy()
                    }
                    override fun onError(error: Int) {
                        debugLog("error from checkRecognitionSupport: " + error)
                        recognizer?.destroy()
                    }
                })
            }
        } else {
            var detailsIntent = RecognizerIntent.getVoiceDetailsIntent(pluginContext)
            if (null == detailsIntent) {
                detailsIntent = Intent(RecognizerIntent.ACTION_GET_LANGUAGE_DETAILS)
                detailsIntent.setPackage("com.google.android.googlequicksearchbox")
            }
            pluginContext?.sendOrderedBroadcast(
                    detailsIntent, null, LanguageDetailsChecker(result, debugLogging),
                    null, Activity.RESULT_OK, null, null)
        }
    }

    /**
     * Reports whether a given language can be recognised *right now*, which is a
     * different question from the one [locales] answers.
     *
     * [locales] returns `supportedOnDeviceLanguages` — languages that could work
     * once a model is downloaded. Selecting one of those and calling listen fails
     * with ERROR_LANGUAGE_UNAVAILABLE. RecognitionSupport keeps four separate
     * lists and this method keeps them separate too:
     *
     *   installed    -> usable now (model downloaded, or the language works online)
     *   downloadable -> supported on device but not yet downloaded
     *   pending      -> a download is already running
     *   unsupported  -> no path to recognising this language on this device
     *   unknown      -> the query itself could not be answered. Never conflated
     *                   with unsupported: callers must not nag a user because a
     *                   permission was missing or a callback never fired.
     */
    private fun recognitionAvailability(result: Result, localeId: String) {
        val context = pluginContext
        if (sdkVersionTooLow() || null == context) {
            respondAvailability(result, "unknown", localeId)
            return
        }
        val hasPermission = ContextCompat.checkSelfPermission(context,
                Manifest.permission.RECORD_AUDIO) == PackageManager.PERMISSION_GRANTED
        // checkRecognitionSupport reports nothing useful without the mic permission.
        if (Build.VERSION.SDK_INT < 33 || !hasPermission) {
            respondAvailability(result, "unknown", localeId)
            return
        }
        if (!SpeechRecognizer.isRecognitionAvailable(context) &&
                !SpeechRecognizer.isOnDeviceRecognitionAvailable(context)) {
            respondAvailability(result, "unsupported", localeId)
            return
        }

        val responded = java.util.concurrent.atomic.AtomicBoolean(false)
        val outstanding = java.util.concurrent.atomic.AtomicInteger(0)
        val installed = Collections.synchronizedSet(HashSet<String>())
        val onDeviceInstalled = Collections.synchronizedSet(HashSet<String>())
        val online = Collections.synchronizedSet(HashSet<String>())
        val downloadable = Collections.synchronizedSet(HashSet<String>())
        val pending = Collections.synchronizedSet(HashSet<String>())
        val answered = java.util.concurrent.atomic.AtomicBoolean(false)

        fun finish() {
            if (!responded.compareAndSet(false, true)) return
            val onDevice = matchesTag(onDeviceInstalled, localeId)
            val status = when {
                !answered.get() -> "unknown"
                matchesTag(installed, localeId) -> "installed"
                matchesTag(pending, localeId) -> "pending"
                matchesTag(downloadable, localeId) -> "downloadable"
                // An empty answer is not evidence of absence.
                installed.isEmpty() && downloadable.isEmpty() && pending.isEmpty() -> "unknown"
                else -> "unsupported"
            }
            respondAvailability(result, status, localeId, onDevice,
                    matchesTag(online, localeId))
        }

        fun collect(support: RecognitionSupport) {
            answered.set(true)
            onDeviceInstalled.addAll(support.installedOnDeviceLanguages)
            installed.addAll(support.installedOnDeviceLanguages)
            downloadable.addAll(support.supportedOnDeviceLanguages)
            pending.addAll(support.pendingOnDeviceLanguages)
            // Reported separately, never folded into `status`: a caller that
            // requires on-device recognition (for privacy, or to work offline)
            // would be told a network-only language is ready and then fail at
            // listen() with the very error this method exists to predict.
            online.addAll(support.onlineLanguages)
        }

        val executor = Executors.newSingleThreadExecutor()
        val recognizers = ArrayList<SpeechRecognizer>()
        // The default recogniser knows about online languages; the on-device one is
        // the only reliable source for the on-device lists. Ask both — either alone
        // gives a partial and, in the unsupported direction, a wrong answer.
        if (SpeechRecognizer.isRecognitionAvailable(context)) {
            createSpeechRecognizer(context)?.let { recognizers.add(it) }
        }
        if (SpeechRecognizer.isOnDeviceRecognitionAvailable(context)) {
            createOnDeviceSpeechRecognizer(context)?.let { recognizers.add(it) }
        }
        if (recognizers.isEmpty()) {
            respondAvailability(result, "unknown", localeId)
            return
        }
        outstanding.set(recognizers.size)

        for (recognizer in recognizers) {
            val intent = Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH)
            intent.putExtra(RecognizerIntent.EXTRA_LANGUAGE, localeId)
            try {
                recognizer.checkRecognitionSupport(intent, executor,
                        object : RecognitionSupportCallback {
                            override fun onSupportResult(recognitionSupport: RecognitionSupport) {
                                collect(recognitionSupport)
                                recognizer.destroy()
                                if (outstanding.decrementAndGet() <= 0) finish()
                            }

                            override fun onError(error: Int) {
                                debugLog("checkRecognitionSupport error: $error")
                                recognizer.destroy()
                                if (outstanding.decrementAndGet() <= 0) finish()
                            }
                        })
            } catch (exc: Exception) {
                debugLog("checkRecognitionSupport threw: ${exc.localizedMessage}")
                recognizer.destroy()
                if (outstanding.decrementAndGet() <= 0) finish()
            }
        }

        // Some recognition services never call back at all; without this the Dart
        // side would await forever rather than fall back to tap-only rating.
        Handler(Looper.getMainLooper()).postDelayed({ finish() }, availabilityTimeoutMs)
    }

    /** Exact tag first, then language subtag: "pl" answers for a "pl-PL" request. */
    private fun matchesTag(tags: Set<String>, localeId: String): Boolean {
        val wanted = localeId.replace('_', '-').lowercase()
        val wantedLanguage = wanted.substringBefore('-')
        return tags.any { tag ->
            val candidate = tag.replace('_', '-').lowercase()
            candidate == wanted || candidate.substringBefore('-') == wantedLanguage
        }
    }

    private fun respondAvailability(result: Result, status: String, localeId: String,
                                    onDevice: Boolean = false, online: Boolean = false) {
        val payload = HashMap<String, Any>()
        payload["status"] = status
        payload["localeId"] = localeId
        payload["onDevice"] = onDevice
        payload["online"] = online
        payload["canTriggerDownload"] = Build.VERSION.SDK_INT >= 33 && status == "downloadable"
        result.success(payload)
    }

    /**
     * Asks the on-device recognition service to fetch the model for [localeId].
     * API 33's overload has no completion callback, so this reports only that the
     * request was accepted — the caller must re-query availability to see the
     * outcome rather than assuming success.
     */
    private fun triggerModelDownload(result: Result, localeId: String) {
        val context = pluginContext
        if (sdkVersionTooLow() || null == context || Build.VERSION.SDK_INT < 33 ||
                !SpeechRecognizer.isOnDeviceRecognitionAvailable(context)) {
            result.success(false)
            return
        }
        try {
            downloadRecognizer?.destroy()
            val recognizer = createOnDeviceSpeechRecognizer(context)
            downloadRecognizer = recognizer
            val intent = Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH)
            intent.putExtra(RecognizerIntent.EXTRA_LANGUAGE, localeId)
            recognizer?.triggerModelDownload(intent)
            // Destroying the recogniser immediately can cancel the download it just
            // started, so it is held and released on the next request instead.
            result.success(true)
        } catch (exc: Exception) {
            debugLog("triggerModelDownload failed: ${exc.localizedMessage}")
            result.success(false)
        }
    }

    private fun notifyListening(isRecording: Boolean ) {
        if ( listening == isRecording ) return;
        listening = isRecording
        val status = when (isRecording) {
            true -> SpeechToTextStatus.listening.name
            false -> SpeechToTextStatus.notListening.name
        }
        debugLog("Notify status:" + status)
        channel?.invokeMethod(SpeechToTextCallbackMethods.notifyStatus.name, status)
        if ( !isRecording ) {
            if (timer != null) {
                timer?.cancel()
                timer = null
            }
            val doneStatus = when( resultSent) {
                false -> SpeechToTextStatus.doneNoResult.name
                else -> SpeechToTextStatus.done.name
            }
            debugLog("Notify status:" + doneStatus )
            optionallyStopBluetooth();
            channel?.invokeMethod(SpeechToTextCallbackMethods.notifyStatus.name,
                doneStatus )
        }
    }

    private fun optionallyStopBluetooth() {
        if ( bluetoothDisabled ) return
        val lactive = activeBluetooth
        val lbt = bluetoothHeadset
        if (null != lactive && null != lbt ) {
            debugLog("Stopping bluetooth voice recognition")
            lbt.stopVoiceRecognition(lactive)
            activeBluetooth = null
        }
    }
    
    private fun updateResults(speechBundle: Bundle?, isFinal: Boolean) {
        if (isDuplicateFinal( isFinal )) {
            debugLog("Discarding duplicate final")
            return
        }
        val userSaid = speechBundle?.getStringArrayList(SpeechRecognizer.RESULTS_RECOGNITION)
        if (null != userSaid && userSaid.isNotEmpty()) {
            val speechResult = JSONObject()
            val finalResult = speechBundle.getBoolean("final_result", false)
            val resultType = if (isFinal) {
                ResultType.finalResult
            } else if (finalResult) {
                ResultType.intermediate
            } else {
                ResultType.partial
            }
            speechResult.put("resultType", resultType.intValue())
            val confidence = speechBundle.getFloatArray(SpeechRecognizer.CONFIDENCE_SCORES)
            val alternates = JSONArray()
            for (resultIndex in 0..userSaid.size - 1) {
                val speechWords = JSONObject()
                speechWords.put("recognizedWords", userSaid[resultIndex])
                if (null != confidence && confidence.size >= userSaid.size) {
                    speechWords.put("confidence", confidence[resultIndex])
                } else {
                    speechWords.put("confidence", missingConfidence)
                }
                alternates.put(speechWords)
            }
            speechResult.put("alternates", alternates)
            val jsonResult = speechResult.toString()
            debugLog("Calling results callback")
            resultSent = true
            channel?.invokeMethod(SpeechToTextCallbackMethods.textRecognition.name,
                    jsonResult)
        } else {
            debugLog("Results null or empty")
        }
    }

    private fun isDuplicateFinal( isFinal: Boolean ) : Boolean {
        if ( !isFinal ) {
            return false
        }
        val delta = System.currentTimeMillis() - lastFinalTime
        lastFinalTime = System.currentTimeMillis()
        return delta >= 0 && delta < 100
    }

    private fun initializeIfPermitted(context: Context?) {
        val localContext = context
        if (null == localContext) {
            completeInitialize()
            return
        }
        permissionToRecordAudio = ContextCompat.checkSelfPermission(localContext,
                Manifest.permission.RECORD_AUDIO) == PackageManager.PERMISSION_GRANTED
        val permissionToEnableBluetooth = ContextCompat.checkSelfPermission(localContext,
                Manifest.permission.BLUETOOTH_CONNECT) == PackageManager.PERMISSION_GRANTED
        bluetoothDisabled = !permissionToEnableBluetooth || noBluetoothOpt
        debugLog("Checked permission")
        if (!permissionToRecordAudio) {
            val localActivity = currentActivity
            if (null != localActivity) {
                debugLog("Requesting permission")
                var requiredPermissions = arrayOf(Manifest.permission.RECORD_AUDIO)
                if ( !noBluetoothOpt ) {
                    requiredPermissions = requiredPermissions.plus(Manifest.permission.BLUETOOTH_CONNECT)
                }
                ActivityCompat.requestPermissions(localActivity, requiredPermissions, speechToTextPermissionCode)
            } else {
                debugLog("no permission, no activity, completing")
                completeInitialize()
            }
        } else {
            debugLog("has permission, completing")
            completeInitialize()
        }
        debugLog("leaving initializeIfPermitted")
    }

    private fun completeInitialize() {

        debugLog("completeInitialize")
        if (permissionToRecordAudio) {
            debugLog("Testing recognition availability")
            val localContext = pluginContext
            if (localContext != null) {
                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S) {
                    if (!SpeechRecognizer.isRecognitionAvailable(localContext) && !SpeechRecognizer.isOnDeviceRecognitionAvailable(
                            localContext
                        )
                    ) {
                        Log.e(logTag, "Speech recognition not available on this device")
                        activeResult?.error(
                            SpeechToTextErrors.recognizerNotAvailable.name,
                            "Speech recognition not available on this device", ""
                        )
                        activeResult = null
                        return
                    }
                } else {
                    if (!SpeechRecognizer.isRecognitionAvailable(localContext)) {
                        Log.e(logTag, "Speech recognition not available on this device")
                        activeResult?.error(
                            SpeechToTextErrors.recognizerNotAvailable.name,
                            "Speech recognition not available on this device", ""
                        )
                        activeResult = null
                        return
                    }
                }
                setupBluetooth()
            } else {
                debugLog("null context during initialization")
                activeResult?.success(false)
                activeResult?.error(
                        SpeechToTextErrors.missingContext.name,
                        "context unexpectedly null, initialization failed", "")
                activeResult = null
                return
            }
        }

        initializedSuccessfully = permissionToRecordAudio
        debugLog("sending result")
        activeResult?.success(permissionToRecordAudio)
        debugLog("leaving complete")
        activeResult = null
    }

    private fun setupBluetooth() {
        if ( bluetoothDisabled ) return
        bluetoothAdapter = BluetoothAdapter.getDefaultAdapter()
        pairedDevices = bluetoothAdapter?.getBondedDevices()

        val mProfileListener: BluetoothProfile.ServiceListener = object : BluetoothProfile.ServiceListener {
            override fun onServiceConnected(profile: Int, proxy: BluetoothProfile) {
                if (profile == BluetoothProfile.HEADSET) {
                    bluetoothHeadset = proxy as BluetoothHeadset
                    debugLog("Found a headset: " + bluetoothHeadset.toString())
                }
            }

            override fun onServiceDisconnected(profile: Int) {
                if (profile == BluetoothProfile.HEADSET) {
                    debugLog("Clearing headset: ")
                    bluetoothHeadset = null
                }
            }
        }
        bluetoothAdapter?.getProfileProxy(pluginContext, mProfileListener, BluetoothProfile.HEADSET)
    }

    private fun Context.findComponentName(): ComponentName? {
        val list: List<ResolveInfo> = packageManager.queryIntentServices(Intent(RecognitionService.SERVICE_INTERFACE), 0)
        debugLog("RecognitionService, found: ${list.size}")
        list.forEach() { it.serviceInfo?.let { it1 -> debugLog("RecognitionService: packageName: ${it1.packageName}, name: ${it1.name}") } }
        return list.firstOrNull()?.serviceInfo?.let { ComponentName(it.packageName, it.name) }
    }

    private fun createRecognizer(onDevice: Boolean, listenMode: ListenMode, pauseFor: Int?) {
        if ( null != speechRecognizer && onDevice == lastOnDevice ) {
            return
        }
        lastOnDevice = onDevice
        speechRecognizer?.destroy()
        speechRecognizer = null
        handler.post {
            run {
                debugLog("Creating recognizer")
                if (intentLookup) {
                    speechRecognizer = createSpeechRecognizer(
                        pluginContext,
                        pluginContext?.findComponentName()
                    ).apply {
                        debugLog("Setting listener after intent lookup")
                        setRecognitionListener(this@SpeechToTextPlugin)
                    }
                } else {
                        var supportsLocal = false
                    if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.S && onDevice) {
                        supportsLocal = SpeechRecognizer.isOnDeviceRecognitionAvailable(pluginContext!!)
                        if (supportsLocal ) {
                            speechRecognizer = createOnDeviceSpeechRecognizer(pluginContext!!).apply {
                                debugLog("Setting on device listener")
                                setRecognitionListener(this@SpeechToTextPlugin)
                            }
                        }
                    }
                    if ( null == speechRecognizer) {
                            speechRecognizer = createSpeechRecognizer(pluginContext).apply {
                                debugLog("Setting default listener")
                                setRecognitionListener(this@SpeechToTextPlugin)
                        }
                    }
                }
                if (null == speechRecognizer) {
                    Log.e(logTag, "Speech recognizer null")
                    activeResult?.error(
                        SpeechToTextErrors.recognizerNotAvailable.name,
                        "Speech recognizer null", ""
                    )
                    activeResult = null
                }
            }
        }
        debugLog("before setup intent")
        setupRecognizerIntent(defaultLanguageTag, true, listenMode, false, pauseFor )
        debugLog("after setup intent")
    }

    private fun setupRecognizerIntent(languageTag: String, partialResults: Boolean, listenMode: ListenMode, onDevice: Boolean, pauseFor: Int? ) {
        debugLog("setupRecognizerIntent")
        if (previousRecognizerLang == null ||
                previousRecognizerLang != languageTag ||
                partialResults != previousPartialResults || previousListenMode != listenMode ||
                previousPauseFor != pauseFor ) {
            previousRecognizerLang = languageTag;
            previousPartialResults = partialResults
            previousListenMode = listenMode
            previousPauseFor = pauseFor
            handler.post {
                run {
                    recognizerIntent = Intent(RecognizerIntent.ACTION_RECOGNIZE_SPEECH).apply {
                        debugLog("In RecognizerIntent apply")
                        if (listenMode == ListenMode.search) {
                            putExtra(RecognizerIntent.EXTRA_LANGUAGE_MODEL, RecognizerIntent.LANGUAGE_MODEL_WEB_SEARCH)
                        }
                        else {
                            putExtra(RecognizerIntent.EXTRA_LANGUAGE_MODEL, RecognizerIntent.LANGUAGE_MODEL_FREE_FORM)
                        }
                        debugLog("put model")
                        val localContext = pluginContext
                        if (null != localContext) {
                            putExtra(RecognizerIntent.EXTRA_CALLING_PACKAGE,
                                    localContext.applicationInfo.packageName)
                        }
                        debugLog("put package")
                        putExtra(RecognizerIntent.EXTRA_PARTIAL_RESULTS, partialResults)
                        debugLog("put partial")
                        if (languageTag != Locale.getDefault().toLanguageTag()) {
                            putExtra(RecognizerIntent.EXTRA_LANGUAGE, languageTag);
                            debugLog("put languageTag")
                        }
                        if ( onDevice ) {
                            putExtra(RecognizerIntent.EXTRA_PREFER_OFFLINE, onDevice );
                        }
                        putExtra(RecognizerIntent.EXTRA_MAX_RESULTS,10)

                        pauseFor?.also {
                            putExtra(RecognizerIntent.EXTRA_SPEECH_INPUT_COMPLETE_SILENCE_LENGTH_MILLIS, it)
                        }
                    }
                }
            }
        }
    }

    // Returns the read end so the caller can close it AFTER startListening, or
    // null when app-supplied audio is off/unavailable — in which case the
    // recogniser opens its own capture exactly as before. Every failure here
    // degrades to that old behaviour rather than breaking the listen: a call
    // that rates by tapping is worse than one that rates by voice, but a call
    // that crashes is worse than both.
    private fun attachAppAudioSource() {
        val intent = recognizerIntent ?: return
        // A stale fd from a previous listen must never survive on the cached
        // intent: it is already closed, and leaving it would starve the
        // recogniser instead of letting it fall back to its own microphone.
        intent.removeExtra(RecognizerIntent.EXTRA_AUDIO_SOURCE)
        if (!appAudioSource) return
        if (Build.VERSION.SDK_INT < Build.VERSION_CODES.TIRAMISU) return
        val context = pluginContext ?: return
        if (ContextCompat.checkSelfPermission(context, Manifest.permission.RECORD_AUDIO)
                != PackageManager.PERMISSION_GRANTED) return

        stopAppAudioPump()

        val minBuf = AudioRecord.getMinBufferSize(
                appAudioSampleRate, AudioFormat.CHANNEL_IN_MONO, AudioFormat.ENCODING_PCM_16BIT)
        if (minBuf <= 0) return
        val bufSize = minBuf * 2

        // VOICE_COMMUNICATION, not MIC: the answer clip is playing out of the
        // same device during barge-in, and this source carries the platform's
        // echo cancellation. Without it the recogniser transcribes our own
        // playback.
        val record = try {
            AudioRecord(MediaRecorder.AudioSource.VOICE_COMMUNICATION, appAudioSampleRate,
                    AudioFormat.CHANNEL_IN_MONO, AudioFormat.ENCODING_PCM_16BIT, bufSize)
        } catch (e: Exception) {
            debugLog("app audio source: AudioRecord ctor failed: $e")
            null
        } ?: return
        if (record.state != AudioRecord.STATE_INITIALIZED) {
            record.release()
            return
        }

        val pipe = try {
            ParcelFileDescriptor.createPipe()
        } catch (e: Exception) {
            record.release()
            return
        }
        val readSide = pipe[0]
        val writeSide = pipe[1]

        audioPumpRunning = true
        try {
            record.startRecording()
        } catch (e: Exception) {
            record.release()
            try { readSide.close() } catch (e2: Exception) { }
            try { writeSide.close() } catch (e2: Exception) { }
            audioPumpRunning = false
            return
        }

        // Only once the capture is genuinely running: extras attached before a
        // failed startRecording would leave THIS listen parceling a closed fd.
        intent.putExtra(RecognizerIntent.EXTRA_AUDIO_SOURCE, readSide)
        intent.putExtra(RecognizerIntent.EXTRA_AUDIO_SOURCE_ENCODING, AudioFormat.ENCODING_PCM_16BIT)
        intent.putExtra(RecognizerIntent.EXTRA_AUDIO_SOURCE_SAMPLING_RATE, appAudioSampleRate)
        intent.putExtra(RecognizerIntent.EXTRA_AUDIO_SOURCE_CHANNEL_COUNT, 1)

        val pump = Thread {
            val out = ParcelFileDescriptor.AutoCloseOutputStream(writeSide)
            val buf = ByteArray(bufSize)
            try {
                while (audioPumpRunning) {
                    val n = record.read(buf, 0, buf.size)
                    if (n > 0) {
                        out.write(buf, 0, n)
                    } else if (n < 0) {
                        break
                    }
                }
            } catch (e: Exception) {
                // The recogniser closed its end (normal end of listen), or the
                // capture died. Either way this listen is over.
                debugLog("app audio pump ended: $e")
            } finally {
                try { out.close() } catch (e: Exception) { }
                try { record.stop() } catch (e: Exception) { }
                record.release()
            }
        }
        pump.isDaemon = true
        pump.name = "stt-app-audio-pump"
        audioPumpThread = pump
        pendingReadSide = readSide
        pump.start()
    }

    // Closing the write end is what tells the recogniser the audio ended, so
    // this must run on every path that finishes a listen — otherwise the
    // recogniser waits out its own silence timeout on a stream nobody is
    // feeding.
    private fun stopAppAudioPump() {
        audioPumpRunning = false
        try { pendingReadSide?.close() } catch (e: Exception) { }
        pendingReadSide = null
        val pump = audioPumpThread ?: return
        audioPumpThread = null
        try {
            pump.join(500)
        } catch (e: InterruptedException) {
            Thread.currentThread().interrupt()
        }
    }

    private fun destroyRecognizer() {
        stopAppAudioPump()

        handler.postDelayed( {
                run {
                    debugLog("Recognizer destroy")
                    speechRecognizer?.destroy();
                    speechRecognizer = null;
                }
        }, 50 )
    }
    override fun onRequestPermissionsResult(requestCode: Int, permissions: Array<out String>, grantResults: IntArray): Boolean {
        when (requestCode) {
            speechToTextPermissionCode -> {
                permissionToRecordAudio = grantResults.isNotEmpty() &&
                        grantResults[0] == PackageManager.PERMISSION_GRANTED
                bluetoothDisabled = (grantResults.isEmpty() || grantResults.size == 1 ||
                        grantResults[1] != PackageManager.PERMISSION_GRANTED) ||
                        noBluetoothOpt
                completeInitialize()
                return true
            }
        }
        return false
    }


    override fun onPartialResults(results: Bundle?) = updateResults(results, false)
    override fun onResults(results: Bundle?) = updateResults(results, true)
    override fun onBeginningOfSpeech() {
        if (timer != null) {
            timer?.cancel()
            timer = null
        }
    }

    override fun onEndOfSpeech() {
        (previousPauseFor ?: 1000).also {
            timerTask = object : TimerTask() {
                override fun run() {
                    timer = null
                    handler.post {
                        run {
                            notifyListening(isRecording = false)
                        }
                    }
                }
            }
            timer = Timer().apply {
                schedule(timerTask, it.toLong())
            }
        }
    }

    override fun onError(errorCode: Int) {
        val delta = System.currentTimeMillis() - speechStartTime
        var errorReturn = errorCode
        if ( SpeechRecognizer.ERROR_NO_MATCH == errorCode && maxRms < speechThresholdRms ) {
            errorReturn = SpeechRecognizer.ERROR_SPEECH_TIMEOUT
        }
        debugLog( "Error $errorCode after start at $delta $minRms / $maxRms")
        val errorMsg = when (errorReturn) {
            SpeechRecognizer.ERROR_AUDIO -> "error_audio_error"
            SpeechRecognizer.ERROR_CLIENT -> "error_client"
            SpeechRecognizer.ERROR_INSUFFICIENT_PERMISSIONS -> "error_permission"
            SpeechRecognizer.ERROR_NETWORK -> "error_network"
            SpeechRecognizer.ERROR_NETWORK_TIMEOUT -> "error_network_timeout"
            SpeechRecognizer.ERROR_NO_MATCH -> "error_no_match"
            SpeechRecognizer.ERROR_RECOGNIZER_BUSY -> "error_busy"
            SpeechRecognizer.ERROR_SERVER -> "error_server"
            SpeechRecognizer.ERROR_SPEECH_TIMEOUT -> "error_speech_timeout"
            SpeechRecognizer.ERROR_LANGUAGE_NOT_SUPPORTED -> "error_language_not_supported"
            SpeechRecognizer.ERROR_LANGUAGE_UNAVAILABLE -> "error_language_unavailable"
            SpeechRecognizer.ERROR_SERVER_DISCONNECTED -> "error_server_disconnected"
            SpeechRecognizer.ERROR_TOO_MANY_REQUESTS -> "error_too_many_requests"
            else -> "error_unknown ($errorCode)"
        }

        sendError(errorMsg)
        if ( isListening()) {
            notifyListening(false)
        }
    }

    private fun debugLog( msg: String ) {
        if ( debugLogging ) {
            Log.d( logTag, msg )
        }
    }

    private fun sendError(errorMsg: String) {
        val speechError = JSONObject()
        speechError.put("errorMsg", errorMsg)
        speechError.put("permanent", true)
        handler.post {
            run {
                channel?.invokeMethod(SpeechToTextCallbackMethods.notifyError.name, speechError.toString())
            }
        }
    }

    override fun onRmsChanged(rmsdB: Float) {
        if ( rmsdB < minRms ) {
            minRms = rmsdB
        }
        if ( rmsdB > maxRms ) {
            maxRms = rmsdB
        }
        debugLog("rmsDB $minRms / $maxRms")
        handler.post {
            run {
                channel?.invokeMethod(SpeechToTextCallbackMethods.soundLevelChange.name, rmsdB)
            }
        }
    }

    override fun onReadyForSpeech(p0: Bundle?) {}
    override fun onBufferReceived(p0: ByteArray?) {}
    override fun onEvent(p0: Int, p1: Bundle?) {}

}

// See https://stackoverflow.com/questions/10538791/how-to-set-the-language-in-speech-recognition-on-android/10548680#10548680
class LanguageDetailsChecker(flutterResult: Result, logging: Boolean ) : BroadcastReceiver() {
    private val logTag = "SpeechToTextPlugin"
    private val result: Result = flutterResult
    private val debugLogging: Boolean = logging
    private var supportedLanguages: List<String>? = null

    private var languagePreference: String? = null

    override fun onReceive(context: Context, intent: Intent) {
        debugLog( "Received extra language broadcast" )
        val results = getResultExtras(true)
        if (results.containsKey(RecognizerIntent.EXTRA_LANGUAGE_PREFERENCE)) {
            languagePreference = results.getString(RecognizerIntent.EXTRA_LANGUAGE_PREFERENCE)
        }
        if (results.containsKey(RecognizerIntent.EXTRA_SUPPORTED_LANGUAGES)) {
            debugLog( "Extra supported languages" )
            supportedLanguages = results.getStringArrayList(
                    RecognizerIntent.EXTRA_SUPPORTED_LANGUAGES)
            createResponse(supportedLanguages)
        }
        else {
            debugLog(  "No extra supported languages" )
            createResponse( ArrayList<String>())
        }
    }

    public fun createResponse(supportedLanguages: List<String>?) {
        val currentLocale = Locale.getDefault()
        val localeNames = ArrayList<String>()
        localeNames.add(buildIdNameForLocale(currentLocale))
        if (null != supportedLanguages) {
            for (lang in supportedLanguages) {
                if (currentLocale.toLanguageTag() == lang) {
                    continue
                }
                val locale = Locale.forLanguageTag(lang)
                localeNames.add(buildIdNameForLocale(locale))
            }
        }
        result.success(localeNames)

    }

    private fun buildIdNameForLocale(locale: Locale): String {
        val name = locale.displayName.replace(':', ' ')
        return "${locale.language}_${locale.country}:$name"
    }

    private fun debugLog( msg: String ) {
        if ( debugLogging ) {
            Log.d( logTag, msg )
        }
    }
}

private class ChannelResultWrapper(result: Result) : Result {
    // Caller handler
    val handler: Handler = Handler(Looper.getMainLooper())
    val result: Result = result

    // make sure to respond in the caller thread
    override fun success(results: Any?) {

        handler.post {
            run {
                result.success(results);
            }
        }
    }

    override fun error(errorCode: String, errorMessage: String?, data: Any?) {
        handler.post {
            run {
                result.error(errorCode, errorMessage, data);
            }
        }
    }

    override fun notImplemented() {
        handler.post {
            run {
                result.notImplemented();
            }
        }
    }
}