// Lean compiler output
// Module: ReentryExport
// Imports: public import Init public import Init.Paraconsistent
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT uint8_t l_exportedRuntime;
static uint8_t _init_l_exportedRuntime() {
_start:
{
uint8_t x_1;
x_1 = 1;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init_Paraconsistent(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ReentryExport(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Paraconsistent(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_exportedRuntime = _init_l_exportedRuntime();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
