/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum.algebra
import data.fin.vec_notation

/-! # Tuples `fin na → α` form a graded ring under append -/

namespace fin

variables {α : Sort*} {α' : Type*} {na nb nc : ℕ}

/-- Append `b` to `a`. -/
def append' (a : fin na → α) (b : fin nb → α) : fin (na + nb) → α :=
sum.elim a b ∘ fin_sum_fin_equiv.symm

/-- Repeat `a` `n` times. -/
def repeat (a : fin na → α) (n : ℕ) : fin (n * na) → α :=
a ∘ prod.snd ∘ fin_prod_fin_equiv.symm

@[simp] lemma append'_apply_left {α} {na nb} (a : fin na → α) (b : fin nb → α) (i : fin na) :
  append' a b (fin_sum_fin_equiv (sum.inl i)) = a i :=
by rw [append', function.comp_apply, equiv.symm_apply_apply, sum.elim_inl]

@[simp] def append'_apply_right {α} {na nb} (a : fin na → α) (b : fin nb → α) (j : fin nb) :
  append' a b (fin_sum_fin_equiv (sum.inr j)) = b j :=
by rw [append', function.comp_apply, equiv.symm_apply_apply, sum.elim_inr]

lemma append'_cases {na nb} {P : fin (na + nb) → Prop}
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

lemma append'_elim0 (a : fin na → α) : append' a fin.elim0 = a ∘ fin.cast (add_zero _) :=
begin
  ext i,
  apply append'_cases (λ l, _) fin.elim0 i,
  rw [append'_apply_left, fin_sum_fin_equiv_apply_left],
  refine congr_arg a (fin.ext _),
  simp,
end

lemma elim0_append' (b : fin nb → α) : append' (fin.elim0 : _ → α) b = b ∘ fin.cast (zero_add _) :=
begin
  ext i,
  apply append'_cases fin.elim0 (λ r, _) i,
  rw [append'_apply_right, fin_sum_fin_equiv_apply_right],
  refine congr_arg b (fin.ext _),
  simp,
end

lemma append'_assoc (a : fin na → α) (b : fin nb → α) (c : fin nc → α) :
  append' (append' a b) c = append' a (append' b c) ∘ fin.cast (add_assoc _ _ _) :=
begin
  ext i,
  rw function.comp_apply,
  apply append'_cases (λ l, _) (λ r, _) i,
  { rw append'_apply_left,
    apply append'_cases (λ ll, _) (λ lr, _) l,
    { rw append'_apply_left,
      sorry, },
    { rw append'_apply_right,
      sorry, }, },
  { rw [append'_apply_right],
    sorry },
end

@[simp] lemma repeat_zero (a : fin na → α) : repeat a 0 = fin.elim0 ∘ cast (zero_mul _) :=
begin
  ext,
  rw zero_mul at x,
  exact x.elim0,
end

@[simp] lemma repeat_succ (a : fin na → α) (n : ℕ) :
  repeat a n.succ = append' a (repeat a n) ∘ cast ((nat.succ_mul _ _).trans (add_comm _ _)) :=
begin
  ext,
  cases h : fin_prod_fin_equiv.symm x;
    rw equiv.apply_eq_iff_eq_symm_apply at h; rw [h, equiv.symm_symm],
  sorry,
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
{ mul := λ i j, fin.append',
  one := fin.elim0,
  one_mul := λ b, sigma_eq_of_eq_comp_cast _ (elim0_append' _),
  mul_one := λ a, sigma_eq_of_eq_comp_cast _ (append'_elim0 _),
  mul_assoc := λ a b c, sigma_eq_of_eq_comp_cast _ (append'_assoc _ _ _),
  gnpow := λ n i a, repeat a n,
  gnpow_zero' := λ a, sigma_eq_of_eq_comp_cast _ (repeat_zero _),
  gnpow_succ' := λ a n, sigma_eq_of_eq_comp_cast _ (repeat_succ _ _) }

end fin
