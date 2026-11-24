/*
 * all_headers.c — the four C API v2 headers in one translation unit (task 11.3a5).
 * Compiled by run_all.sh with -Wall -Wextra -Werror: a clash between the headers (a type,
 * enum constant or function declared twice with different meaning) fails the build. It
 * touches one name from each header so that every one is actually parsed and used.
 */
#include "safepdf_core.h"
#include "safepdf_view.h"
#include "safepdf_marks.h"
#include "safepdf_select.h"

int main(void) {
    safepdf_box core_box = {0, 0, 1, 1};                 /* core: doubles */
    safepdf_rat_box view_box = {{0, 1}, {0, 1}, {1, 1}, {1, 1}}; /* view: rationals */
    safepdf_marks_bytes mbytes = {0, 0};                 /* marks: data only */
    safepdf_bytes cbytes = {0, 0};                       /* core: struct + data */
    safepdf_select_range range = {0, 0};
    safepdf_view_action action = SAFEPDF_ACTION_FIND_NEXT;
    safepdf_action_kind kind = SAFEPDF_ACTION_GOTO;
    (void)view_box; (void)mbytes; (void)cbytes; (void)range;
    return (int)core_box.llx + (int)action + (int)kind + SAFEPDF_MARK_INK + SAFEPDF_STATUS_OK;
}
