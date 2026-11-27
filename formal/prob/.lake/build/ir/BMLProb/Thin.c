// Lean compiler output
// Module: BMLProb.Thin
// Imports: public import Init public meta import Init public import BMLProb.Weight public import BML.ThinRigidity
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
LEAN_EXPORT uint8_t lp_bml__prob_BML_Prob_column___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_column___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_bml__prob_BML_Prob_column(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_column___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_bml__prob_BML_Prob_column___redArg(lean_object* v_s_1_, lean_object* v_x_2_, lean_object* v_y_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; uint8_t v___x_6_; 
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v_x_2_);
lean_ctor_set(v___x_4_, 1, v_y_3_);
v___x_5_ = lean_apply_1(v_s_1_, v___x_4_);
v___x_6_ = lean_unbox(v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_column___redArg___boxed(lean_object* v_s_7_, lean_object* v_x_8_, lean_object* v_y_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = lp_bml__prob_BML_Prob_column___redArg(v_s_7_, v_x_8_, v_y_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t lp_bml__prob_BML_Prob_column(lean_object* v_w_12_, lean_object* v_h_13_, lean_object* v_s_14_, lean_object* v_x_15_, lean_object* v_y_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = lp_bml__prob_BML_Prob_column___redArg(v_s_14_, v_x_15_, v_y_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_bml__prob_BML_Prob_column___boxed(lean_object* v_w_18_, lean_object* v_h_19_, lean_object* v_s_20_, lean_object* v_x_21_, lean_object* v_y_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = lp_bml__prob_BML_Prob_column(v_w_18_, v_h_19_, v_s_20_, v_x_21_, v_y_22_);
lean_dec(v_h_19_);
lean_dec(v_w_18_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_bml__prob_BMLProb_Weight(uint8_t builtin);
lean_object* initialize_bml_BML_ThinRigidity(uint8_t builtin);
void lean_initialize();
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_bml__prob_BMLProb_Thin(uint8_t builtin) {
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
res = initialize_bml__prob_BMLProb_Weight(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_bml_BML_ThinRigidity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
