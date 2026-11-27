// Lean compiler output
// Module: BMLProb.Weight
// Imports: public import Init public meta import Init public import Mathlib.Algebra.BigOperators.Ring.Finset public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset public import Mathlib.Algebra.BigOperators.Pi public import Mathlib.Algebra.Order.BigOperators.Ring.Finset public import Mathlib.Algebra.Order.Field.Basic public import Mathlib.Data.Fintype.Pi public import Mathlib.Data.Fintype.Prod public import Mathlib.Data.Rat.Defs public import Mathlib.Tactic public import BML.Torus
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
lean_object* l_Nat_cast___at___00Std_Http_Internal_Test_defaultConfig_spec__0(lean_object*);
lean_object* l_Rat_sub(lean_object*, lean_object*);
lean_object* l_Rat_div(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Rat_commMonoid;
lean_object* lp_mathlib_Finset_prod___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lp_bml_BML_instDecidableEqCell___boxed(lean_object*, lean_object*);
lean_object* lp_mathlib_Multiset_ndinsert___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__0 = (const lean_object*)&lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__0_value;
static lean_once_cell_t lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__1;
static lean_once_cell_t lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__2;
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_instFintypeCell__bMLProb;
static lean_once_cell_t lp_bml__prob_BML_Prob_cellWeight___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_bml__prob_BML_Prob_cellWeight___closed__0;
static lean_once_cell_t lp_bml__prob_BML_Prob_cellWeight___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_bml__prob_BML_Prob_cellWeight___closed__1;
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_cellWeight(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_cellWeight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_bml__prob___private_BMLProb_Weight_0__BML_Prob_cellWeight_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_bml__prob___private_BMLProb_Weight_0__BML_Prob_cellWeight_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_bml__prob___private_BMLProb_Weight_0__BML_Prob_cellWeight_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_bml__prob___private_BMLProb_Weight_0__BML_Prob_cellWeight_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_weight___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_weight___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_weight(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__1(void){
_start:
{
lean_object* v___x_5_; uint8_t v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_5_ = ((lean_object*)(lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__0));
v___x_6_ = 1;
v___x_7_ = lean_alloc_closure((void*)(lp_bml_BML_instDecidableEqCell___boxed), 2, 0);
v___x_8_ = lean_box(v___x_6_);
v___x_9_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_7_, v___x_8_, v___x_5_);
return v___x_9_;
}
}
static lean_object* _init_lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__2(void){
_start:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_10_ = lean_obj_once(&lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__1, &lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__1_once, _init_lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__1);
v___x_11_ = 0;
v___x_12_ = lean_alloc_closure((void*)(lp_bml_BML_instDecidableEqCell___boxed), 2, 0);
v___x_13_ = lean_box(v___x_11_);
v___x_14_ = lp_mathlib_Multiset_ndinsert___redArg(v___x_12_, v___x_13_, v___x_10_);
return v___x_14_;
}
}
static lean_object* _init_lp_bml__prob_BML_Prob_instFintypeCell__bMLProb(void){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__2, &lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__2_once, _init_lp_bml__prob_BML_Prob_instFintypeCell__bMLProb___closed__2);
return v___x_15_;
}
}
static lean_object* _init_lp_bml__prob_BML_Prob_cellWeight___closed__0(void){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_unsigned_to_nat(1u);
v___x_17_ = l_Nat_cast___at___00Std_Http_Internal_Test_defaultConfig_spec__0(v___x_16_);
return v___x_17_;
}
}
static lean_object* _init_lp_bml__prob_BML_Prob_cellWeight___closed__1(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(2u);
v___x_19_ = l_Nat_cast___at___00Std_Http_Internal_Test_defaultConfig_spec__0(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_cellWeight(lean_object* v_p_20_, uint8_t v_x_21_){
_start:
{
if (v_x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_obj_once(&lp_bml__prob_BML_Prob_cellWeight___closed__0, &lp_bml__prob_BML_Prob_cellWeight___closed__0_once, _init_lp_bml__prob_BML_Prob_cellWeight___closed__0);
v___x_23_ = l_Rat_sub(v___x_22_, v_p_20_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_obj_once(&lp_bml__prob_BML_Prob_cellWeight___closed__1, &lp_bml__prob_BML_Prob_cellWeight___closed__1_once, _init_lp_bml__prob_BML_Prob_cellWeight___closed__1);
v___x_25_ = l_Rat_div(v_p_20_, v___x_24_);
lean_dec_ref(v_p_20_);
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_cellWeight___boxed(lean_object* v_p_26_, lean_object* v_x_27_){
_start:
{
uint8_t v_x_70__boxed_28_; lean_object* v_res_29_; 
v_x_70__boxed_28_ = lean_unbox(v_x_27_);
v_res_29_ = lp_bml__prob_BML_Prob_cellWeight(v_p_26_, v_x_70__boxed_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* lp_bml__prob___private_BMLProb_Weight_0__BML_Prob_cellWeight_match__1_splitter___redArg(uint8_t v_x_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_, lean_object* v_h__3_33_){
_start:
{
switch(v_x_30_)
{
case 0:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
lean_dec(v_h__3_33_);
lean_dec(v_h__2_32_);
v___x_34_ = lean_box(0);
v___x_35_ = lean_apply_1(v_h__1_31_, v___x_34_);
return v___x_35_;
}
case 1:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v_h__3_33_);
lean_dec(v_h__1_31_);
v___x_36_ = lean_box(0);
v___x_37_ = lean_apply_1(v_h__2_32_, v___x_36_);
return v___x_37_;
}
default: 
{
lean_object* v___x_38_; lean_object* v___x_39_; 
lean_dec(v_h__2_32_);
lean_dec(v_h__1_31_);
v___x_38_ = lean_box(0);
v___x_39_ = lean_apply_1(v_h__3_33_, v___x_38_);
return v___x_39_;
}
}
}
}
LEAN_EXPORT lean_object* lp_bml__prob___private_BMLProb_Weight_0__BML_Prob_cellWeight_match__1_splitter___redArg___boxed(lean_object* v_x_40_, lean_object* v_h__1_41_, lean_object* v_h__2_42_, lean_object* v_h__3_43_){
_start:
{
uint8_t v_x_33__boxed_44_; lean_object* v_res_45_; 
v_x_33__boxed_44_ = lean_unbox(v_x_40_);
v_res_45_ = lp_bml__prob___private_BMLProb_Weight_0__BML_Prob_cellWeight_match__1_splitter___redArg(v_x_33__boxed_44_, v_h__1_41_, v_h__2_42_, v_h__3_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* lp_bml__prob___private_BMLProb_Weight_0__BML_Prob_cellWeight_match__1_splitter(lean_object* v_motive_46_, uint8_t v_x_47_, lean_object* v_h__1_48_, lean_object* v_h__2_49_, lean_object* v_h__3_50_){
_start:
{
switch(v_x_47_)
{
case 0:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
lean_dec(v_h__3_50_);
lean_dec(v_h__2_49_);
v___x_51_ = lean_box(0);
v___x_52_ = lean_apply_1(v_h__1_48_, v___x_51_);
return v___x_52_;
}
case 1:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
lean_dec(v_h__3_50_);
lean_dec(v_h__1_48_);
v___x_53_ = lean_box(0);
v___x_54_ = lean_apply_1(v_h__2_49_, v___x_53_);
return v___x_54_;
}
default: 
{
lean_object* v___x_55_; lean_object* v___x_56_; 
lean_dec(v_h__2_49_);
lean_dec(v_h__1_48_);
v___x_55_ = lean_box(0);
v___x_56_ = lean_apply_1(v_h__3_50_, v___x_55_);
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* lp_bml__prob___private_BMLProb_Weight_0__BML_Prob_cellWeight_match__1_splitter___boxed(lean_object* v_motive_57_, lean_object* v_x_58_, lean_object* v_h__1_59_, lean_object* v_h__2_60_, lean_object* v_h__3_61_){
_start:
{
uint8_t v_x_48__boxed_62_; lean_object* v_res_63_; 
v_x_48__boxed_62_ = lean_unbox(v_x_58_);
v_res_63_ = lp_bml__prob___private_BMLProb_Weight_0__BML_Prob_cellWeight_match__1_splitter(v_motive_57_, v_x_48__boxed_62_, v_h__1_59_, v_h__2_60_, v_h__3_61_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_weight___redArg___lam__0(lean_object* v_s_64_, lean_object* v_p_65_, lean_object* v_i_66_){
_start:
{
lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; 
v___x_67_ = lean_apply_1(v_s_64_, v_i_66_);
v___x_68_ = lean_unbox(v___x_67_);
v___x_69_ = lp_bml__prob_BML_Prob_cellWeight(v_p_65_, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_weight___redArg(lean_object* v_inst_70_, lean_object* v_p_71_, lean_object* v_s_72_){
_start:
{
lean_object* v___f_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v___f_73_ = lean_alloc_closure((void*)(lp_bml__prob_BML_Prob_weight___redArg___lam__0), 3, 2);
lean_closure_set(v___f_73_, 0, v_s_72_);
lean_closure_set(v___f_73_, 1, v_p_71_);
v___x_74_ = lp_mathlib_Rat_commMonoid;
v___x_75_ = lp_mathlib_Finset_prod___redArg(v___x_74_, v_inst_70_, v___f_73_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_weight(lean_object* v_00_u03b9_76_, lean_object* v_inst_77_, lean_object* v_p_78_, lean_object* v_s_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = lp_bml__prob_BML_Prob_weight___redArg(v_inst_77_, v_p_78_, v_s_79_);
return v___x_80_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Ring_Finset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_GroupWithZero_Finset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_BigOperators_Pi(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Order_BigOperators_Ring_Finset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Order_Field_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Pi(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Prod(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Rat_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
lean_object* initialize_bml_BML_Torus(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_bml__prob_BMLProb_Weight(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
lean_initialize();
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Ring_Finset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_GroupWithZero_Finset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_BigOperators_Pi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Order_BigOperators_Ring_Finset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Order_Field_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Pi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Rat_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_bml_BML_Torus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_bml__prob_BML_Prob_instFintypeCell__bMLProb = _init_lp_bml__prob_BML_Prob_instFintypeCell__bMLProb();
lean_mark_persistent(lp_bml__prob_BML_Prob_instFintypeCell__bMLProb);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
