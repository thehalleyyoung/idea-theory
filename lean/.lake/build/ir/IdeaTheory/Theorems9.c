// Lean compiler output
// Module: IdeaTheory.Theorems9
// Imports: Init IdeaTheory.Foundations
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
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_trivial(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padM(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_compose(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_BalancedIdea4_composeL___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_BalancedIdea4_composeB(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_BalancedIdea4_composeR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_composeR(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_swap(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_trivial___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_trivial(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_swap___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padL___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_trivial___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padR(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_composeL(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_trivial___rarg(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_BalancedIdea4_composeR(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padL(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_composeR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padM___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_composeL___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padM___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_swap___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_BalancedIdea4_composeB___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padL___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_compose___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padR___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_BalancedIdea4_composeL(lean_object*);
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_compose___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_compose(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_IdeaPair_compose___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_composeL___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_3);
x_6 = lean_apply_2(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_composeL(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_IdeaTriple_composeL___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_composeR___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_3);
x_7 = lean_apply_2(x_3, x_5, x_6);
x_8 = lean_apply_2(x_3, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_composeR(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_IdeaTriple_composeR___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_BalancedIdea4_composeB___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_3);
x_6 = lean_apply_2(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_3);
x_9 = lean_apply_2(x_3, x_7, x_8);
x_10 = lean_apply_2(x_3, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_BalancedIdea4_composeB(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_BalancedIdea4_composeB___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_BalancedIdea4_composeL___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_3);
x_6 = lean_apply_2(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_inc(x_3);
x_8 = lean_apply_2(x_3, x_6, x_7);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_2(x_3, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_BalancedIdea4_composeL(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_BalancedIdea4_composeL___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_BalancedIdea4_composeR___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
lean_inc(x_3);
x_8 = lean_apply_2(x_3, x_6, x_7);
lean_inc(x_3);
x_9 = lean_apply_2(x_3, x_5, x_8);
x_10 = lean_apply_2(x_3, x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_BalancedIdea4_composeR(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_BalancedIdea4_composeR___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_trivial___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 0);
lean_dec(x_4);
lean_inc(x_3);
lean_ctor_set(x_1, 0, x_3);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_trivial(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_IdeaPair_trivial___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_trivial___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_n(x_2, 3);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_trivial(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_IdeaTriple_trivial___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaTriple_trivial___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IdeaTheory_IdeaTriple_trivial___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_swap___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_swap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_IdeaPair_swap___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_swap___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_IdeaTheory_IdeaPair_swap___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padR___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padR(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_IdeaPair_padR___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padR___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IdeaTheory_IdeaPair_padR___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padL___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padL(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_IdeaPair_padL___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padL___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IdeaTheory_IdeaPair_padL___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padM___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_5);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_IdeaTheory_IdeaPair_padM___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_IdeaTheory_IdeaPair_padM___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IdeaTheory_IdeaPair_padM___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_IdeaTheory_Foundations(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_IdeaTheory_Theorems9(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_IdeaTheory_Foundations(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
