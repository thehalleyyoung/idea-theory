// Lean compiler output
// Module: IdeaTheory.Theorems11
// Imports: Init IdeaTheory.Foundations IdeaTheory.Theorems10
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
LEAN_EXPORT lean_object* l_IdeaTheory_idTrans(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_idTrans___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_rightMul(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_tradition___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_transmitVertical___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IdeaTheory_Coalition_trivial___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_leftMul___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_IdeaTheory_aggregate___rarg(lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_tradition(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_composeTrans___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Lineage_singleton___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_idTrans___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Lineage_singleton(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Lineage_trivial___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_rightMul___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Lineage_trivial(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_leftMul(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_transmitHorizontal___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_transmitVertical(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_transmitVertical___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_composeTrans(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_transmitHorizontal(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Lineage_then___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Lineage_then(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_idTrans___rarg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_idTrans(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_idTrans___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_idTrans___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IdeaTheory_idTrans___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_composeTrans___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_composeTrans(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_composeTrans___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_leftMul___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_leftMul(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_leftMul___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_rightMul___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, x_3, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_rightMul(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_rightMul___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_transmitVertical___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_dec(x_1);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_IdeaTheory_transmitVertical___rarg(x_1, x_5, x_3);
x_8 = lean_apply_2(x_6, x_4, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_transmitVertical(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_transmitVertical___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_transmitVertical___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IdeaTheory_transmitVertical___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_transmitHorizontal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_apply_2(x_6, x_2, x_4);
x_2 = x_7;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_transmitHorizontal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_transmitHorizontal___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_tradition___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IdeaTheory_aggregate___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_tradition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_tradition___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Lineage_trivial___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IdeaTheory_Coalition_trivial___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Lineage_trivial(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_Lineage_trivial___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Lineage_singleton___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Lineage_singleton(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_Lineage_singleton___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Lineage_then___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_appendTR___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Lineage_then(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_Lineage_then___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_IdeaTheory_Foundations(uint8_t builtin, lean_object*);
lean_object* initialize_IdeaTheory_Theorems10(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_IdeaTheory_Theorems11(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_IdeaTheory_Foundations(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_IdeaTheory_Theorems10(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
