/-
Copyright (c) 2020 Mario Carneiro All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.nat.digits

theorem nat.digits_def' : ∀ {b : ℕ} (h : 2 ≤ b) {n : ℕ} (w : 0 < n),
  nat.digits b n = n % b :: nat.digits b (n/b)
| 0 h := absurd h dec_trivial
| 1 h := absurd h dec_trivial
| (b+2) h := nat.digits_aux_def _ _

theorem digits_succ
  (b n m r l)
  (e : r + b * m = n)
  (hr : r < b)
  (h : nat.digits b m = l ∧ 2 ≤ b ∧ 0 < m) :
  nat.digits b n = r :: l ∧ 2 ≤ b ∧ 0 < n :=
begin
  rcases h with ⟨h, b2, m0⟩,
  have b0 : 0 < b := by linarith,
  have n0 : 0 < n := by linarith [mul_pos b0 m0],
  refine ⟨_, b2, n0⟩,
  obtain ⟨rfl, rfl⟩ := (nat.div_mod_unique b0).2 ⟨e, hr⟩,
  subst h, exact nat.digits_def' b2 n0,
end

theorem digits_one
  (b n) (n0 : 0 < n) (nb : n < b) :
  nat.digits b n = [n] ∧ 2 ≤ b ∧ 0 < n :=
begin
  have b2 : 2 ≤ b := by linarith,
  refine ⟨_, b2, n0⟩,
  rw [nat.digits_def' b2 n0, nat.mod_eq_of_lt nb,
    (nat.div_eq_zero_iff (by linarith : 0 < b)).2 nb, nat.digits_zero],
end

namespace tactic

/--
Helper function for the `norm_digits` tactic.
-/
meta def eval_digits_aux (eb : expr) (b : ℕ) : expr → ℕ → tactic (expr × expr)
| en n := do
  let m := n / b,
  let r := n % b,
  ic ← mk_instance_cache `(ℕ),
  er ← expr.of_nat `(ℕ) r,
  (_, pr) ← norm_num.prove_lt_nat ic er eb,
  if m = 0 then do
    (_, pn0) ← norm_num.prove_pos ic en,
    return (`([%%en] : list nat), `(digits_one %%eb %%en %%pn0 %%pr))
  else do
    em ← expr.of_nat `(ℕ) m,
    (_, pe) ← norm_num.derive `(%%er + %%eb * %%em : ℕ),
    (el, p) ← eval_digits_aux em m,
    return (`(@list.cons ℕ %%er %%el),
      `(digits_succ %%eb %%en %%em %%er %%el %%pe %%pr %%p))

/--
Helper function for the `norm_digits` tactic.
-/
meta def eval_digits (eb : expr) (b : ℕ) : expr → ℕ → tactic (expr × expr)
| en 0 := return (`([] : list nat), `(nat.digits_zero %%eb))
| en n := do
  (l, p) ← eval_digits_aux eb b en n,
  p ← mk_app ``and.left [p],
  return (l, p)

/--
`norm_digits` solves goals of the form `nat.digits 10 123 = [3,2,1]`.
-/
meta def norm_digits : tactic unit :=
do `(nat.digits %%eb %%en = %%el') ← target,
  b ← expr.to_nat eb,
  n ← expr.to_nat en,
  (el, p) ← eval_digits eb b en n,
  unify el el',
  exact p

example : nat.digits 10 123 = [3,2,1] := by norm_digits

run_cmd add_interactive [``norm_digits]

end tactic

add_tactic_doc
{ name        := "norm_digits",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.norm_digits],
  tags        := ["arithmetic", "decision procedure"] }
