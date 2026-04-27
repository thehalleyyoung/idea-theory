// Lean compiler output
// Module: IdeaTheory.Theorems3
// Imports: Init IdeaTheory.Foundations Mathlib.Tactic
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
LEAN_EXPORT lean_object* l_IdeaTheory_aufheb___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_iterateNegated___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_iteratePreserved___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_mediated(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_aufheb(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_iterateNegated(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_mediated___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_iteratePreserved(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_triadOf(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_triadOf___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_iterateNegated___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_iteratePreserved___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_aufheb___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_5, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_aufheb(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_aufheb___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_mediated___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_apply_1(x_6, x_2);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_8, x_3);
x_10 = lean_apply_2(x_5, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_mediated(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_mediated___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_triadOf___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_1(x_3, x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = lean_apply_1(x_5, x_2);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_triadOf(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_triadOf___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_iteratePreserved___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_IdeaTheory_iteratePreserved___rarg(x_1, x_7, x_3);
lean_dec(x_7);
x_10 = lean_apply_1(x_8, x_9);
return x_10;
}
else
{
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_iteratePreserved(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_iteratePreserved___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_iteratePreserved___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IdeaTheory_iteratePreserved___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_iterateNegated___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = l_IdeaTheory_iterateNegated___rarg(x_1, x_7, x_3);
lean_dec(x_7);
x_10 = lean_apply_1(x_8, x_9);
return x_10;
}
else
{
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_iterateNegated(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_iterateNegated___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_iterateNegated___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IdeaTheory_iterateNegated___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_IdeaTheory_Foundations(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_IdeaTheory_Theorems3(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_IdeaTheory_Foundations(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
