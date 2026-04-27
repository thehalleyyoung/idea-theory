// Lean compiler output
// Module: IdeaTheory.Theorems10
// Imports: Init IdeaTheory.Foundations IdeaTheory.Theorems9
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
LEAN_EXPORT lean_object* l___private_IdeaTheory_Theorems10_0__IdeaTheory_aggregate_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_singleton(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_insertAt(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_insertAt___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_trivial___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Committee_collective___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_aggregate___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Committee_collective(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_IdeaTheory_Assembly_collective___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_IdeaTheory_Theorems10_0__IdeaTheory_aggregate_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_replicateTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Assembly_collective___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Assembly_collective(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_triple(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_IdeaTheory_Assembly_collective___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_delegate(lean_object*);
LEAN_EXPORT lean_object* l___private_IdeaTheory_Theorems10_0__IdeaTheory_aggregate_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_aggregate(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_triple___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_pair___rarg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_insertAt___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_pair(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_singleton___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_trivial(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_delegate___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_aggregate___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
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
x_7 = l_IdeaTheory_aggregate___rarg(x_1, x_5);
x_8 = lean_apply_2(x_6, x_4, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_aggregate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_aggregate___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Committee_collective___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_IdeaTheory_aggregate___rarg(x_1, x_5);
x_7 = lean_apply_2(x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Committee_collective(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_Committee_collective___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_IdeaTheory_Assembly_collective___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_IdeaTheory_Committee_collective___rarg(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_IdeaTheory_Committee_collective___rarg(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_IdeaTheory_Assembly_collective___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_mapTR_loop___at_IdeaTheory_Assembly_collective___spec__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Assembly_collective___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
lean_inc(x_1);
x_4 = l_List_mapTR_loop___at_IdeaTheory_Assembly_collective___spec__1___rarg(x_1, x_2, x_3);
x_5 = l_IdeaTheory_aggregate___rarg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Assembly_collective(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_Assembly_collective___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_trivial___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_List_replicateTR___rarg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_trivial(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_Coalition_trivial___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_singleton___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_singleton(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_Coalition_singleton___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_pair___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_pair(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_Coalition_pair___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_triple___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_triple(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_Coalition_triple___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_insertAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
x_12 = l_IdeaTheory_Coalition_insertAt___rarg(x_1, x_11, x_9);
lean_dec(x_11);
lean_ctor_set(x_3, 1, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
x_17 = l_IdeaTheory_Coalition_insertAt___rarg(x_1, x_16, x_14);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_insertAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_Coalition_insertAt___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_insertAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IdeaTheory_Coalition_insertAt___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_delegate___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_appendTR___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_Coalition_delegate(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_Coalition_delegate___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_IdeaTheory_Theorems10_0__IdeaTheory_aggregate_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_IdeaTheory_Theorems10_0__IdeaTheory_aggregate_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_IdeaTheory_Theorems10_0__IdeaTheory_aggregate_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_IdeaTheory_Theorems10_0__IdeaTheory_aggregate_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_IdeaTheory_Theorems10_0__IdeaTheory_aggregate_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_IdeaTheory_Foundations(uint8_t builtin, lean_object*);
lean_object* initialize_IdeaTheory_Theorems9(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_IdeaTheory_Theorems10(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_IdeaTheory_Foundations(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_IdeaTheory_Theorems9(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
