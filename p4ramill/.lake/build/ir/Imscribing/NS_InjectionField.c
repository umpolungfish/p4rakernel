// Lean compiler output
// Module: Imscribing.NS_InjectionField
// Imports: public import Init public import Imscribing.NS_Reentry public import Mathlib.Analysis.Calculus.FDeriv.Mul public import Mathlib.Analysis.Calculus.ContDiff.Comp public import Mathlib.Analysis.InnerProductSpace.PiL2
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
lean_object* lp_mathlib_WithLp_equiv(lean_object*, lean_object*);
lean_object* lp_mathlib_Nat_cast___at___00TopCat_diskBoundaryInclusion_spec__0(lean_object*);
static lean_object* lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__1;
LEAN_EXPORT lean_object* lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__2;
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_Equiv_symm___redArg(lean_object*);
static lean_object* lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__0;
LEAN_EXPORT lean_object* lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_2(x_1, x_2, x_4);
x_6 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_4214226450____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lp_mathlib_Nat_cast___at___00TopCat_diskBoundaryInclusion_spec__0(x_1);
return x_2;
}
}
static lean_object* _init_lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__0;
x_2 = lp_mathlib_WithLp_equiv(x_1, lean_box(0));
return x_2;
}
}
static lean_object* _init_lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__1;
x_2 = lp_mathlib_Equiv_symm___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__1;
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__2;
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___lam__0), 4, 3);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_3);
x_9 = lean_apply_1(x_7, x_8);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_imscribing_x2dlean_Imscribing_NS__Reentry(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_FDeriv_Mul(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_ContDiff_Comp(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_PiL2(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_imscribing_x2dlean_Imscribing_NS__InjectionField(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_imscribing_x2dlean_Imscribing_NS__Reentry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_FDeriv_Mul(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_ContDiff_Comp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_PiL2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__0 = _init_lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__0();
lean_mark_persistent(lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__0);
lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__1 = _init_lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__1();
lean_mark_persistent(lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__1);
lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__2 = _init_lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__2();
lean_mark_persistent(lp_imscribing_x2dlean_Imscribing_NSInjectionField_timeLinearVelocity___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
