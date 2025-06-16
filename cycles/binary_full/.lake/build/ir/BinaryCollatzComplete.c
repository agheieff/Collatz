// Lean compiler output
// Module: BinaryCollatzComplete
// Imports: Init Mathlib.Data.Nat.Basic Mathlib.Data.Fintype.Card Mathlib.Algebra.Ring.Parity Mathlib.Tactic.Ring Mathlib.Tactic.Linarith
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
LEAN_EXPORT lean_object* l_BinaryCollatz_binaryCollatz(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BinaryCollatzComplete_0__BinaryCollatz_jValue_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_BinaryCollatz_jValue(lean_object*);
LEAN_EXPORT lean_object* l___private_BinaryCollatzComplete_0__BinaryCollatz_sumJ_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BinaryCollatzComplete_0__BinaryCollatz_jValue_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BinaryCollatz_sumJ___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BinaryCollatz_sumJ___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BinaryCollatz_binaryCollatz___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BinaryCollatz_jValue___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_BinaryCollatzComplete_0__BinaryCollatz_sumJ_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BinaryCollatz_sumJ___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BinaryCollatzComplete_0__BinaryCollatz_jValue_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_BinaryCollatz_sumJ(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_BinaryCollatzComplete_0__BinaryCollatz_sumJ_match__1_splitter(lean_object*);
LEAN_EXPORT lean_object* l_BinaryCollatz_jValue(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(1u);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_BinaryCollatz_jValue___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_BinaryCollatz_jValue(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_BinaryCollatz_binaryCollatz(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_unsigned_to_nat(3u);
x_4 = lean_nat_mul(x_3, x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
x_7 = l_BinaryCollatz_jValue(x_2);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_pow(x_8, x_7);
lean_dec(x_7);
x_10 = lean_nat_div(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_BinaryCollatz_binaryCollatz___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BinaryCollatz_binaryCollatz(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BinaryCollatz_sumJ___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_BinaryCollatz_sumJ(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = lean_nat_add(x_6, x_5);
x_8 = lean_nat_mod(x_3, x_7);
lean_dec(x_7);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_8);
x_10 = l_BinaryCollatz_jValue(x_9);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l_BinaryCollatz_sumJ___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_2);
x_12 = l_BinaryCollatz_sumJ(x_6, x_11);
lean_dec(x_6);
x_13 = lean_nat_add(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_unsigned_to_nat(0u);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_BinaryCollatz_sumJ___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BinaryCollatz_sumJ___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_BinaryCollatz_sumJ___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BinaryCollatz_sumJ(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_BinaryCollatzComplete_0__BinaryCollatz_jValue_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_inc(x_3);
return x_3;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_BinaryCollatzComplete_0__BinaryCollatz_jValue_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_BinaryCollatzComplete_0__BinaryCollatz_jValue_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_BinaryCollatzComplete_0__BinaryCollatz_jValue_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_BinaryCollatzComplete_0__BinaryCollatz_jValue_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_BinaryCollatzComplete_0__BinaryCollatz_sumJ_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_1, x_7);
x_9 = lean_apply_2(x_4, x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_4);
x_10 = lean_apply_1(x_3, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_BinaryCollatzComplete_0__BinaryCollatz_sumJ_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_BinaryCollatzComplete_0__BinaryCollatz_sumJ_match__1_splitter___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_BinaryCollatzComplete_0__BinaryCollatz_sumJ_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_BinaryCollatzComplete_0__BinaryCollatz_sumJ_match__1_splitter___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Data_Fintype_Card(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Algebra_Ring_Parity(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_Ring(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic_Linarith(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_BinaryCollatzComplete(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Data_Fintype_Card(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Algebra_Ring_Parity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_Ring(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic_Linarith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
