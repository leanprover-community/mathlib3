/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum.algebra

/-! # Tuples `fin na → α` form a graded ring under concatenation -/

namespace fin

variables {α : Sort*} {α' : Type*} {na nb nc : ℕ}

/-- Concatenate two tuples. -/
def concat (a : fin na → α) (b : fin nb → α) : fin (na + nb) → α :=
sum.elim a b ∘ fin_sum_fin_equiv.symm

@[simp] lemma concat_apply_left {α} {na nb} (a : fin na → α) (b : fin nb → α) (i : fin na) :
  concat a b (fin_sum_fin_equiv (sum.inl i)) = a i :=
by rw [concat, function.comp_apply, equiv.symm_apply_apply, sum.elim_inl]

@[simp] def concat_apply_right {α} {na nb} (a : fin na → α) (b : fin nb → α) (j : fin nb) :
  concat a b (fin_sum_fin_equiv (sum.inr j)) = b j :=
by rw [concat, function.comp_apply, equiv.symm_apply_apply, sum.elim_inr]

lemma concat_cases {na nb} {P : fin (na + nb) → Prop}
  (hl : ∀ l : fin na, P (fin_sum_fin_equiv (sum.inl l)))
  (hr : ∀ r : fin nb, P (fin_sum_fin_equiv (sum.inr r))) : ∀ i, P i :=
begin
  intro i,
  cases h : fin_sum_fin_equiv.symm i with l r,
  { rw (equiv.apply_eq_iff_eq_symm_apply _).1 h,
    exact hl l, },
  { rw (equiv.apply_eq_iff_eq_symm_apply _).1 h,
    exact hr r, },
end

lemma concat_elim0 (a : fin na → α) : concat a fin.elim0 = a ∘ fin.cast (add_zero _) :=
begin
  ext i,
  apply concat_cases (λ l, _) fin.elim0 i,
  rw [concat_apply_left, fin_sum_fin_equiv_apply_left],
  refine congr_arg a (fin.ext _),
  simp,
end

lemma elim0_concat (b : fin nb → α) : concat (fin.elim0 : _ → α) b = b ∘ fin.cast (zero_add _) :=
begin
  ext i,
  apply concat_cases fin.elim0 (λ r, _) i,
  rw [concat_apply_right, fin_sum_fin_equiv_apply_right],
  refine congr_arg b (fin.ext _),
  simp,
end

lemma concat_assoc (a : fin na → α) (b : fin nb → α) (c : fin nc → α) :
  concat (concat a b) c = concat a (concat b c) ∘ fin.cast (add_assoc _ _ _) :=
begin
  ext i,
  rw function.comp_apply,
  apply concat_cases (λ l, _) (λ r, _) i,
  { rw concat_apply_left,
    apply concat_cases (λ ll, _) (λ lr, _) l,
    { rw concat_apply_left,
      sorry, },
    { rw concat_apply_right,
      sorry, }, },
  { rw [concat_apply_right],
    sorry },
end

lemma sigma_eq_of_eq_comp_cast :
  ∀ {a b : Σ ii, fin ii → α'} (h : a.fst = b.fst), a.snd = b.snd ∘ fin.cast h → a = b
| ⟨ai, a⟩ ⟨bi, b⟩ hi h :=
begin
  simp only at hi,
  subst hi,
  simpa using h,
end

instance pi_graded_monoid {α : Type*} : graded_monoid.gmonoid (λ n, fin n → α) :=
{ mul := λ i j, fin.concat,
  one := fin.elim0,
  one_mul := λ b, sigma_eq_of_eq_comp_cast (zero_add _) (elim0_concat _),
  mul_one := λ a, sigma_eq_of_eq_comp_cast (add_zero _) (concat_elim0 _),
  mul_assoc := λ a b c, sigma_eq_of_eq_comp_cast (add_assoc _ _ _) (concat_assoc _ _ _),
  gnpow := _,
  gnpow_zero' := _,
  gnpow_succ' := _ }

end fin
