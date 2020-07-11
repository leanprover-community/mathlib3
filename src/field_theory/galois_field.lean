/-
Copyleft. No rights reserved.
Authors: Johan Commelin
-/

import field_theory.finite
import field_theory.separable
import linear_algebra.finite_dimensional

/-!
# Galois fields

If `p` is a prime number, and `n` a natural number,
then `galois_field p n` is defined as the splitting field of `X^(p^n) - X` over `zmod p`.
It is a finite field with `p ^ n` elements.

## Main definition

* `galois_field p n` is a field with `p ^ n` elements

-/

noncomputable theory

-- move this
section
open function
variables {K L : Type*} [field K] [field L]

lemma ring_hom.char_p_iff (f : K →+* L) (p : ℕ) :
  char_p K p ↔ char_p L p :=
begin
  split; introI; constructor; intro n,
  { rw [← f.map_nat_cast, f.map_eq_zero],
    apply char_p.cast_eq_zero_iff },
  { rw [← f.injective.eq_iff, f.map_nat_cast, f.map_zero],
    apply char_p.cast_eq_zero_iff }
end

variables (K L) [algebra K L]

lemma algebra.char_p_iff (p : ℕ) :
  char_p K p ↔ char_p L p :=
(algebra_map K L).char_p_iff p

end

open polynomial

lemma galois_poly_separable {K : Type*} [field K] (p q : ℕ) [char_p K p] (h : p ∣ q) :
  separable (X ^ q - X : polynomial K) :=
begin
  use [1, (X ^ q - X - 1)],
  rw [← char_p.cast_eq_zero_iff (polynomial K) p] at h,
  rw [derivative_sub, derivative_pow, derivative_X, h],
  ring,
end

section polynomial_facts

open_locale big_operators
open finset

variables {R : Type*} [integral_domain R]

@[simp] lemma roots_one : roots (1 : polynomial R) = ∅ :=
begin
  ext r,
  simp only [mem_roots, ne.def, one_ne_zero, is_root.def, eval_one, not_mem_empty, not_false_iff],
end

variables  [decidable_eq R]

-- move this
lemma roots_prod_X_sub_C (s : finset R) : (∏ i in s, (X - C i)).roots = s :=
begin
  apply s.induction_on,
  { simp only [prod_empty, roots_one], },
  intros a s' has' ih,
  rw [finset.prod_insert has', roots_mul, ih, roots_X_sub_C],
  { ext, simp only [mem_union, mem_insert, mem_singleton], },
  { intro con, cases eq_zero_or_eq_zero_of_mul_eq_zero con with h h,
    work_on_goal 1
    { rw finset.prod_eq_zero_iff at h, rcases h with ⟨x, hx, h⟩, },
    all_goals
    { exact polynomial.ne_zero_of_monic (monic_X_sub_C _) h, } }
end

end polynomial_facts

section splitting_field_facts

variables {K : Type*} {L : Type*} [field K] [field L] {f : polynomial K}
/-- The canonical isomorphism between a field and the splitting field of a polynomial that splits-/
def ring_equiv_splitting_field_of_splits (h : polynomial.splits (ring_hom.id K) f) :
  (K ≃+* f.splitting_field) :=
-- move this
section splitting_field_facts

variables {K : Type*} [field K] {f : polynomial K}

/-- The canonical isomorphism between
the splitting field of a polynomial that splits and the base field. -/
def equiv_of_splits (h : polynomial.splits (ring_hom.id K) f) :
  f.splitting_field ≃ₐ[K] K :=
begin
  -- apply ring_equiv.of _,
  -- { refine equiv.mk (algebra_map K f.splitting_field) (polynomial.splitting_field.lift f h) _ _,
  --   swap, apply function.right_inverse_of_injective_of_left_inverse, apply ring_hom.injective,
  --   iterate 2 {intro, simp}, },
  -- apply_instance,
end

-- Needs one more step, showing basically that separable implies squarefree
lemma exists_finset_of_splits [decidable_eq L] (i : K →+* L) (sep : separable f) : splits i f →
  ∃ (s : finset L), f.map i = C (i f.leading_coeff) *
  (s.prod (λ a : L, (X : polynomial L) - C a)) :=
begin
  intro sp, cases exists_multiset_of_splits i sp with s h, existsi s.to_finset, rw h,
  rw finset.prod_eq_multiset_prod, rw ← multiset.to_finset_eq,
  rw multiset.nodup_iff_le, intro a, intro con, rw le_iff_exists_add at con,
  cases con with c hc, rw multiset.cons_add at hc, rw multiset.cons_add at hc,
  rw hc at h, simp at h, sorry,
end

open_locale big_operators
variables {α : Type*} [decidable_eq α] (s : finset α) (g : α → polynomial K)

-- I have a proof in another project, hope to PR soon - Aaron Anderson
lemma nat_degree_prod_eq' (h : ∏ i in s, (g i).leading_coeff ≠ 0) :
  (s.prod g).nat_degree = ∑ i in s, (g i).nat_degree :=
begin
  sorry
end

-- move this, generalise to integral domain
lemma roots_C_mul (x : K) (hx : x ≠ 0) (f : polynomial K) :
  roots (C x * f) = roots f :=
begin
  classical, by_cases hf : f = 0,
  { simp only [hf, mul_zero] },
  { have aux : C x * f ≠ 0,
    { apply mul_ne_zero _ hf, rwa [← C_0, ne.def, C_inj] },
    ext y,
    rw [mem_roots aux, mem_roots hf],
    simp only [hx, eval_C, false_or, is_root.def, eval_mul, mul_eq_zero], }
end

-- move this
lemma not_separable_zero : ¬ separable (0 : polynomial K) :=
begin
  rintro ⟨x, y, h⟩,
  simpa only [add_zero, derivative_zero, zero_ne_one, mul_zero, zero_ne_one] using h,
end

-- move this, generalise
lemma nat_degree_C_mul (x : K) (hx : x ≠ 0) (f : polynomial K) :
  nat_degree (C x * f) = nat_degree f :=
begin
  classical, by_cases hf : f = 0,
  { simp only [hf, mul_zero] },
  { rw [nat_degree_mul_eq _ hf, nat_degree_C, zero_add],
    rwa [← C_0, ne.def, C_inj] }
end

-- monic should be removed eventually
lemma card_roots_eq_of_separable_of_splits
  (sep : separable f) (sp : polynomial.splits (ring_hom.id K) f) :
  f.roots.card = f.nat_degree :=
begin
  classical,
  have hf : f ≠ 0, { rintro rfl, exact not_separable_zero sep },
  have hflc : f.leading_coeff ≠ 0, { rwa [ne.def, leading_coeff_eq_zero] },
  cases (exists_finset_of_splits (ring_hom.id K) sep sp) with s hs,
  simp only [ring_hom.id_apply, map_id] at hs, rw hs,
  -- rw [m.leading_coeff, C_1, one_mul] at *,
  rw [roots_C_mul _ hflc, roots_prod_X_sub_C, nat_degree_C_mul _ hflc],
  rw nat_degree_prod_eq',
  { simp only [mul_one, nat_degree_X_sub_C, nat.cast_id, finset.sum_const, nsmul_eq_mul], },
  { simp only [(monic_X_sub_C _).leading_coeff, finset.prod_const_one,
                ne.def, not_false_iff, one_ne_zero] }
end

instance is_splitting_field.finite_dimensional  [algebra K L] [is_splitting_field K L f] :
  finite_dimensional K L :=
sorry

end splitting_field_facts

/-- A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field. -/
@[derive field]
def galois_field (p : ℕ) [fact p.prime] (n : ℕ) :=
splitting_field (X^(p^n) - X : polynomial (zmod p))

namespace galois_field
variables (p : ℕ) [fact p.prime] (n : ℕ)

instance : algebra (zmod p) (galois_field p n) :=
splitting_field.algebra _

instance : is_splitting_field (zmod p) (galois_field p n) (X^(p^n) - X) :=
polynomial.is_splitting_field_splitting_field _

instance : char_p (galois_field p n) p :=
(algebra.char_p_iff (zmod p) (galois_field p n) p).mp (by apply_instance)

-- should be able to apply_instance from finite_dimensional.fintype on finite.lean
instance : fintype (galois_field p n) :=
begin
  have b := classical.some_spec
    (finite_dimensional.exists_is_basis_finset (zmod p) (galois_field p n)),
  apply module.fintype_of_fintype b,
end

lemma findim : finite_dimensional.findim (zmod p) (galois_field p n) = n :=
begin
  sorry,
end

lemma card : fintype.card (galois_field p n) = p ^ n :=
begin
  have b := classical.some_spec
    (finite_dimensional.exists_is_basis_finset (zmod p) (galois_field p n)),
  rw [module.card_fintype b, ← finite_dimensional.findim_eq_card_basis b, zmod.card, findim],
end

theorem splits_zmod_X_pow_sub_X : splits (ring_hom.id (zmod p)) (X ^ p - X) :=
begin
  refine @splits_of_exists_multiset _ _ _ _ _ _ finset.univ.1 _,
  simp only [ring_hom.id_apply, map_id, map_sub],
  conv_rhs { rw [sub_eq_add_neg, add_comm] },
  rw [leading_coeff_add_of_degree_lt, leading_coeff_X_pow, C_1, one_mul],
  swap,
  { rw [degree_X_pow, degree_neg, degree_X], norm_cast, exact nat.prime.one_lt' _, },
  { sorry },
end

def equiv_zmod_p : galois_field p 1 ≃ₐ[zmod p] (zmod p) :=
equiv_of_splits (by { rw nat.pow_one, apply zmod_p_splits_X_pow_p_sub_X p, })

end galois_field
