import tactic.lint
import algebra.group.basic

/-! ## Commutativity lemmas should be rejected  -/

attribute [simp] add_comm add_left_comm

open tactic
run_cmd do
decl ← get_decl ``add_comm,
res ← linter.simp_comm.test decl,
-- linter complains
guard res.is_some

open tactic
run_cmd do
decl ← get_decl ``add_left_comm,
res ← linter.simp_comm.test decl,
-- linter complains
guard res.is_some

/-! ## Floris' trick should be accepted -/

@[simp] lemma list.filter_congr_decidable {α} (s : list α) (p : α → Prop) (h : decidable_pred p)
  [decidable_pred p] : @list.filter α p h s = s.filter p :=
by congr

-- lemma is unproblematic
example : @list.filter _ (λ x, x > 0) (λ _, classical.prop_decidable _) [1,2,3] = [1,2,3] :=
begin
  -- can rewrite once
  simp only [list.filter_congr_decidable],
  -- but not twice
  success_if_fail { simp only [list.filter_congr_decidable] },
  refl
end

open tactic
set_option pp.all true
run_cmd do
decl ← get_decl ``list.filter_congr_decidable,
res ← linter.simp_comm.test decl,
-- linter does not complain
guard res.is_none
