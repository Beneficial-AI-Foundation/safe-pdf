// main.swift — entry point of the native macOS shell (task 11.3b).
// Plan.md §6 Phase 11; docs/macos-design.md §3 decision 6 (Swift over the C API).
//
//   SafePdf [FILE.pdf]                              the app (normally launched from the bundle)
//   SAFEPDF_MACOS_SELFTEST=DIR safepdf-mac FILE.pdf the headless self-test (macos/selftest.sh):
//       activation policy Prohibited before anything else, no window, never `run` or activate;
//       renders through the full v2 path and exits with 0 when `failures: 0`.

import AppKit

let processStartMs = Core.nowMs()
let selfTestDir = ProcessInfo.processInfo.environment["SAFEPDF_MACOS_SELFTEST"].flatMap { $0.isEmpty ? nil : $0 }
let app = NSApplication.shared
// Never become a UI app in the self-test: no Dock icon, no activation, no window.
app.setActivationPolicy(selfTestDir != nil ? .prohibited : .regular)

if let problem = Core.initialise() {
    FileHandle.standardError.write(Data("SafePDF: \(problem)\n".utf8))
    exit(1)
}

// File arguments (AppKit's own `-Name value` defaults arguments are skipped).
var fileArgs: [String] = []
var argIndex = 1
let argv = CommandLine.arguments
while argIndex < argv.count {
    if argv[argIndex].hasPrefix("-") {
        argIndex += 2
    } else {
        fileArgs.append(argv[argIndex])
        argIndex += 1
    }
}

if let dir = selfTestDir {
    guard let path = fileArgs.first else {
        FileHandle.standardError.write(Data("self-test needs a PDF path\n".utf8))
        exit(2)
    }
    exit(SelfTest.run(dir: dir, path: path, processStartMs: processStartMs))
}

let delegate = AppDelegate(initialPath: fileArgs.first)
app.delegate = delegate
app.run()
