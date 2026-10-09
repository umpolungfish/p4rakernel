// Lean compiler output
// Module: Imscribing.PublishedNS.BorelExtension
// Imports: public import Init public import Imscribing.PublishedNS.SmoothCutoffs public import Imscribing.PublishedNS.DiagonalScale public import Mathlib.Analysis.Calculus.SmoothSeries public import Mathlib.Analysis.Calculus.Deriv.Pow
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_imscribing_x2dlean_Imscribing_PublishedNS_SmoothCutoffs(uint8_t builtin);
lean_object* initialize_imscribing_x2dlean_Imscribing_PublishedNS_DiagonalScale(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_SmoothSeries(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Pow(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_imscribing_x2dlean_Imscribing_PublishedNS_BorelExtension(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_imscribing_x2dlean_Imscribing_PublishedNS_SmoothCutoffs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_imscribing_x2dlean_Imscribing_PublishedNS_DiagonalScale(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_SmoothSeries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
