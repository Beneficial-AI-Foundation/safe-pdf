// CoreBridge.swift — start-up of the C API and small conversions (task 11.3b).
// Plan.md §6 Phase 11; docs/macos-design.md §3 (decisions 1, 2, 4). Unverified shell code
// (Plan.md §8): it only moves data between AppKit and the core's C API.

import Foundation
import SafePdfC

/// Helpers around the C API that every other file uses.
enum Core {
    /// Converts a malloc'd UTF-8 string from the C API and frees it.
    static func take(_ p: UnsafeMutablePointer<CChar>?) -> String? {
        guard let p else { return nil }
        defer { free(p) }
        return String(cString: p)
    }

    /// Converts a borrowed C string ("" for NULL).
    static func string(_ p: UnsafePointer<CChar>?) -> String {
        guard let p else { return "" }
        return String(cString: p)
    }

    /// Converts a borrowed mutable C string ("" for NULL).
    static func string(_ p: UnsafeMutablePointer<CChar>?) -> String {
        guard let p else { return "" }
        return String(cString: p)
    }

    /// Initialises the Lean runtime and the four modules, on the main thread, once.
    /// Returns an error message, or nil on success.
    @MainActor static func initialise() -> String? {
        if safepdf_init() != 0 { return "the core could not be initialised (safepdf_init)" }
        if safepdf_view_init() != 0 { return "the view module could not be initialised" }
        if safepdf_marks_init() != 0 { return "the marks module could not be initialised" }
        if safepdf_select_init() != 0 { return "the selection module could not be initialised" }
        return nil
    }

    /// The confined `worker` executable: `Contents/Helpers/worker` inside the app bundle, else
    /// `worker` next to the executable (macos/build/ for the unbundled binary). Absolute,
    /// because the session spawns it with cwd `/` and an empty environment (task 12.2b).
    static func workerPath() -> String? {
        let exe = (Bundle.main.executableURL ?? URL(fileURLWithPath: CommandLine.arguments[0]))
            .resolvingSymlinksInPath()
        let dir = exe.deletingLastPathComponent()
        let candidates = [
            dir.deletingLastPathComponent().appendingPathComponent("Helpers/worker"),
            dir.appendingPathComponent("worker"),
        ]
        for url in candidates where FileManager.default.isExecutableFile(atPath: url.path) {
            return url.standardizedFileURL.path
        }
        return nil
    }

    /// Hands the worker path to the C API (`safepdf_set_worker_path`). Returns an error message
    /// when there is no worker or the call fails.
    static func configureWorker() -> String? {
        guard let path = workerPath() else {
            return "the document worker is missing (expected Contents/Helpers/worker or worker next to the executable)"
        }
        if safepdf_set_worker_path(path) != 0 { return "safepdf_set_worker_path failed for \(path)" }
        return nil
    }

    /// An exact rational for a display length in points, in 1/64 steps (the view module's
    /// quantum). Used for page sizes, which the C API reports as doubles (see Document).
    static func rat(_ x: Double) -> safepdf_rat {
        safepdf_rat(num: Int64((x * 64).rounded()), den: 64)
    }

    /// Milliseconds since an arbitrary origin (monotonic).
    static func nowMs() -> Double {
        Double(DispatchTime.now().uptimeNanoseconds) / 1e6
    }
}
