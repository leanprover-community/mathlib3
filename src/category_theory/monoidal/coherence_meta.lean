import category_theory.monoidal.coherence

open category_theory
open category_theory.monoidal_category

namespace tactic

meta def construct_monoidal_obj : expr → pexpr
| `(tensor_obj %%n %%m) :=
  let k := construct_monoidal_obj n, l := construct_monoidal_obj m in
    ``(monoidal_obj.tensor %%k %%l)
| `(@tensor_unit %%C %%d %%e) := ``(@monoidal_obj.unit %%C %%d %%e)
| e := ``(monoidal_obj.of %%e)

#check new_goals

meta def handle_comp_expression : expr → tactic unit
| `(@category_struct.comp %%C %%c %%X %%Y %%Z %%f %%g) := do
  handle_comp_expression f,
  handle_comp_expression g,
  let u := construct_monoidal_obj Y,
  let v := ``(comp_eq_coherent_comp %%u),
  w ← i_to_expr v,
  try (rewrite_target w)
  --try (tactic.interactive.simp_core {} skip tt [simp_arg_type.expr v] [] (interactive.loc.ns [none]))
| _ := skip

meta def monoidal : tactic unit :=
do
  (n, L, R) ← target_lhs_rhs,
  handle_comp_expression L,
  handle_comp_expression R

namespace interactive

meta def monoidal : tactic unit :=
tactic.monoidal

end interactive

end tactic

universes v u
variables {C : Type u} [category.{v} C] [monoidal_category C]

example {X Y Z : C} (f : (X ⊗ Y) ⊗ Z ⟶ (X ⊗ Y) ⊗ Z) : f ≫ f = f ≫ f ≫ f :=
begin
  monoidal,
  sorry,
end
