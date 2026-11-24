// Commands.swift — which exported commands this shell implements yet (tasks 11.3b, 11.3c1,
// 11.3c2, 11.3d1).
// Plan.md §6 Phase 11; docs/macos-design.md §4 (the 11.3c/d/e split). Every Menu.Cmd is in the
// menubar; a command not implemented yet stays disabled, and `pendingTask` names the task that
// implements it.

import Foundation
import SafePdfC

enum Commands {
    static func id(_ c: safepdf_cmd) -> Int { Int(c.rawValue) }

    /// Commands this shell performs: the scaffold's (11.3b), the zoom and rotation commands
    /// (11.3c1), the view modes, Go to page and Back / Forward (11.3c2), Copy, Select All and
    /// Find (11.3d1; Find next / previous are the key actions, always available with a
    /// document).
    static let implemented: Set<Int> = [
        id(SAFEPDF_CMD_OPEN_FILE), id(SAFEPDF_CMD_CLOSE), id(SAFEPDF_CMD_QUIT),
        id(SAFEPDF_CMD_ABOUT), id(SAFEPDF_CMD_OUTLINE), id(SAFEPDF_CMD_PREV_PAGE),
        id(SAFEPDF_CMD_NEXT_PAGE), id(SAFEPDF_CMD_FIRST_PAGE), id(SAFEPDF_CMD_LAST_PAGE),
        id(SAFEPDF_CMD_ZOOM_IN), id(SAFEPDF_CMD_ZOOM_OUT), id(SAFEPDF_CMD_ACTUAL_SIZE),
        id(SAFEPDF_CMD_FIT_PAGE), id(SAFEPDF_CMD_FIT_WIDTH), id(SAFEPDF_CMD_ROTATE_CW),
        id(SAFEPDF_CMD_ROTATE_CCW), id(SAFEPDF_CMD_SCROLL_PAGE), id(SAFEPDF_CMD_SCROLL_VERTICAL),
        id(SAFEPDF_CMD_SPREAD_NONE), id(SAFEPDF_CMD_SPREAD_ODD), id(SAFEPDF_CMD_SPREAD_EVEN),
        id(SAFEPDF_CMD_GOTO_PAGE), id(SAFEPDF_CMD_BACK), id(SAFEPDF_CMD_FORWARD),
        id(SAFEPDF_CMD_COPY), id(SAFEPDF_CMD_SELECT_ALL), id(SAFEPDF_CMD_FIND),
    ]

    /// The task that implements a command not implemented yet (nil when implemented).
    static func pendingTask(_ cmd: Int) -> String? {
        if implemented.contains(cmd) { return nil }
        let marks: Set<Int> = [
            id(SAFEPDF_CMD_SAVE), id(SAFEPDF_CMD_SAVE_AS), id(SAFEPDF_CMD_IMPORT_XFDF),
            id(SAFEPDF_CMD_EXPORT_XFDF), id(SAFEPDF_CMD_UNDO), id(SAFEPDF_CMD_REDO),
            id(SAFEPDF_CMD_HIGHLIGHT), id(SAFEPDF_CMD_ADD_NOTE), id(SAFEPDF_CMD_DELETE_MARK),
            id(SAFEPDF_CMD_HL_TOOL), id(SAFEPDF_CMD_SHOW_ALL),
        ]
        if marks.contains(cmd) { return "11.3e" }
        return "11.3d" // the rest (none today: every viewing and text command is implemented)
    }
}
