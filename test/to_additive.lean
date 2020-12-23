import tactic
import algebra.group.units

attribute [to_additive] units.eq_iff
  #print add_units.eq_iff
  open tactic
example : (add_units.mk_of_add_eq_zero 0 0 (by simp) : ℕ) = (add_units.mk_of_add_eq_zero 0 0 (by simp) : ℕ) :=
begin
  norm_cast,
end
run_cmd (do trace $ user_attribute.get_param norm_cast.norm_cast_attr `units.eq_iff )
run_cmd (do trace $ user_attribute.get_param norm_cast.norm_cast_attr `add_units.eq_iff )
run_cmd (do trace $ has_attribute `norm_cast `units.eq_iff )
run_cmd (do trace $ has_attribute `norm_cast `add_units.eq_iff )
run_cmd (set_attribute `norm_cast `add_units.eq_iff)
open norm_cast.label
meta def aa : tactic unit := do
  user_attr_nm ← get_user_attribute_name `norm_cast,
  trace user_attr_nm,
  user_attr_const ← mk_const user_attr_nm,
  tac ← eval_pexpr (tactic unit) ``(user_attribute.get_param %%user_attr_const %%`units.eq_iff >>= λ x, user_attribute.set %%user_attr_const %%`add_units.eq_iff x %%ff),
  tac,
  return ()
run_cmd aa
  -- tac ← eval_pexpr (tactic unit) ``(user_attribute.set %%user_attr_const %%c_name () %%persistent) <|>
  --   fail!"Cannot set attribute @[{attr_name}]. The corresponding user attribute {user_attr_nm} has a parameter.",
  -- user_attribute.set_untyped `norm_cast `add_units.eq_iff)
run_cmd (do trace $ has_attribute `norm_cast `add_units.eq_iff )
run_cmd (do trace $ user_attribute.get_param norm_cast.norm_cast_attr `units.eq_iff )
run_cmd (do trace $ user_attribute.get_param norm_cast.norm_cast_attr `add_units.eq_iff )
