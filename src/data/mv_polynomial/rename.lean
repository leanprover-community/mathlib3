/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/

import data.mv_polynomial.basic

/-!
# Renaming variables of polynomials

This file establishes the `rename` operation on multivariate polynomials,
which modifies the set of variables.

## Main declarations

* `mv_polynomial.rename`

## Notation

As in other polynomial files we typically use the notation:

+ `σ : Type*` (indexing the variables)

+ `α : Type*` `[comm_semiring α]` (the coefficients)

+ `s : σ →₀ ℕ`, a function from `σ` to `ℕ` which is zero away from a finite set.
This will give rise to a monomial in `mv_polynomial σ R` which mathematicians might call `X^s`

+ `a : α`

+ `i : σ`, with corresponding monomial `X i`, often denoted `X_i` by mathematicians

+ `p : mv_polynomial σ α`

-/

noncomputable theory

open_locale classical big_operators

open set function finsupp add_monoid_algebra
open_locale big_operators

universes u v w x
variables {R : Type u} {S : Type*} {β : Type v} {γ : Type w} {δ : Type x}

namespace mv_polynomial
variables {σ τ : Type*} {a a' a₁ a₂ : R} {e : ℕ} {n m : σ} {s : σ →₀ ℕ}


section rename
variables {R} [comm_semiring R]

/-- Rename all the variables in a multivariable polynomial. -/
def rename (f : β → γ) : mv_polynomial β R →ₐ[R] mv_polynomial γ R :=
aeval (X ∘ f)

@[simp] lemma rename_C (f : β → γ) (a : R) : rename f (C a) = C a :=
eval₂_C _ _ _

@[simp] lemma rename_X (f : β → γ) (b : β) : rename f (X b : mv_polynomial β R) = X (f b) :=
eval₂_X _ _ _

lemma map_rename [comm_semiring S] (f : R →+* S)
  (g : γ → δ) (p : mv_polynomial γ R) :
  map f (rename g p) = rename g (map f p) :=
mv_polynomial.induction_on p
  (λ a, by simp)
  (λ p q hp hq, by simp [hp, hq])
  (λ p n hp, by simp [hp])

@[simp] lemma rename_rename (f : β → γ) (g : γ → δ) (p : mv_polynomial β R) :
  rename g (rename f p) = rename (g ∘ f) p :=
show rename g (eval₂ C (X ∘ f) p) = _,
begin
  simp only [rename, aeval_eq_eval₂_hom],
  simp [eval₂_comp_left _ C (X ∘ f) p, (∘), eval₂_C, eval_X],
  apply eval₂_hom_congr _ rfl rfl,
  ext1, simp only [comp_app, ring_hom.coe_comp, eval₂_hom_C],
end

@[simp] lemma rename_id (p : mv_polynomial β R) : rename id p = p :=
eval₂_eta p

lemma rename_monomial (f : β → γ) (p : β →₀ ℕ) (a : R) :
  rename f (monomial p a) = monomial (p.map_domain f) a :=
begin
  rw [rename, aeval_monomial, monomial_eq, finsupp.prod_map_domain_index],
  { refl },
  { exact assume n, pow_zero _ },
  { exact assume n i₁ i₂, pow_add _ _ _ }
end

lemma rename_eq (f : β → γ) (p : mv_polynomial β R) :
  rename f p = finsupp.map_domain (finsupp.map_domain f) p :=
begin
  simp only [rename, aeval_def, eval₂, finsupp.map_domain, ring_hom.coe_of],
  congr' with s a : 2,
  rw [← monomial, monomial_eq, finsupp.prod_sum_index],
  congr' with n i : 2,
  rw [finsupp.prod_single_index],
  exact pow_zero _,
  exact assume a, pow_zero _,
  exact assume a b c, pow_add _ _ _
end

lemma rename_injective (f : β → γ) (hf : function.injective f) :
  function.injective (rename f : mv_polynomial β R → mv_polynomial γ R) :=
have (rename f : mv_polynomial β R → mv_polynomial γ R) =
  finsupp.map_domain (finsupp.map_domain f) := funext (rename_eq f),
begin
  rw this,
  exact finsupp.map_domain_injective (finsupp.map_domain_injective hf)
end

section
variables [comm_semiring S] (f : R →+* S)
variables (k : γ → δ) (g : δ → S) (p : mv_polynomial γ R)

lemma eval₂_rename : (rename k p).eval₂ f g = p.eval₂ f (g ∘ k) :=
by apply mv_polynomial.induction_on p; { intros, simp [*] }

lemma eval₂_hom_rename : eval₂_hom f g (rename k p) = eval₂_hom f (g ∘ k) p :=
eval₂_rename _ _ _ _

lemma rename_eval₂ (g : δ → mv_polynomial γ R) :
  rename k (p.eval₂ C (g ∘ k)) = (rename k p).eval₂ C (rename k ∘ g) :=
by apply mv_polynomial.induction_on p; { intros, simp [*] }

lemma rename_prodmk_eval₂ (d : δ) (g : γ → mv_polynomial γ R) :
  rename (prod.mk d) (p.eval₂ C g) = p.eval₂ C (λ x, rename (prod.mk d) (g x)) :=
by apply mv_polynomial.induction_on p; { intros, simp [*] }

lemma eval₂_rename_prodmk (g : δ × γ → S) (d : δ) :
  (rename (prod.mk d) p).eval₂ f g = eval₂ f (λ i, g (d, i)) p :=
by apply mv_polynomial.induction_on p; { intros, simp [*] }

lemma eval_rename_prodmk (g : δ × γ → R) (d : δ) :
  eval g (rename (prod.mk d) p) = eval (λ i, g (d, i)) p :=
eval₂_rename_prodmk (ring_hom.id _) _ _ _

end

/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_finset_rename (p : mv_polynomial γ R) :
  ∃ (s : finset γ) (q : mv_polynomial {x // x ∈ s} R), p = rename coe q :=
begin
  apply induction_on p,
  { intro r, exact ⟨∅, C r, by rw rename_C⟩ },
  { rintro p q ⟨s, p, rfl⟩ ⟨t, q, rfl⟩,
    refine ⟨s ∪ t, ⟨_, _⟩⟩,
    { refine rename (subtype.map id _) p + rename (subtype.map id _) q;
      simp only [id.def, true_or, or_true, finset.mem_union, forall_true_iff] {contextual := tt}, },
    { simp only [rename_rename, alg_hom.map_add], refl, }, },
  { rintro p n ⟨s, p, rfl⟩,
    refine ⟨insert n s, ⟨_, _⟩⟩,
  { refine rename (subtype.map id _) p * X ⟨n, s.mem_insert_self n⟩,
    simp only [id.def, or_true, finset.mem_insert, forall_true_iff] {contextual := tt}, },
    { simp only [rename_rename, rename_X, subtype.coe_mk, alg_hom.map_mul], refl, }, },
end

/-- Every polynomial is a polynomial in finitely many variables. -/
theorem exists_fin_rename (p : mv_polynomial γ R) :
  ∃ (n : ℕ) (f : fin n → γ) (hf : injective f) (q : mv_polynomial (fin n) R), p = rename f q :=
begin
  obtain ⟨s, q, rfl⟩ := exists_finset_rename p,
  obtain ⟨n, ⟨e⟩⟩ := fintype.exists_equiv_fin {x // x ∈ s},
  refine ⟨n, coe ∘ e.symm, subtype.val_injective.comp e.symm.injective, rename e q, _⟩,
  rw [← rename_rename, rename_rename e],
  simp only [function.comp, equiv.symm_apply_apply, rename_rename]
end

end rename

lemma eval₂_cast_comp {β : Type u} {γ : Type v} (f : γ → β)
  {R : Type w} [comm_ring R] (c : ℤ →+* R) (g : β → R) (x : mv_polynomial γ ℤ) :
  eval₂ c (g ∘ f) x = eval₂ c g (rename f x) :=
mv_polynomial.induction_on x
(λ n, by simp only [eval₂_C, rename_C])
(λ p q hp hq, by simp only [hp, hq, rename, eval₂_add, alg_hom.map_add])
(λ p n hp, by simp only [hp, rename, aeval_def, eval₂_X, eval₂_mul])

section coeff
variables [comm_semiring R]

@[simp]
lemma coeff_rename_map_domain (f : σ → τ) (hf : injective f) (φ : mv_polynomial σ R) (d : σ →₀ ℕ) :
  (rename f φ).coeff (d.map_domain f) = φ.coeff d :=
begin
  apply induction_on' φ,
  { intros u r,
    rw [rename_monomial, coeff_monomial, coeff_monomial],
    simp only [(finsupp.map_domain_injective hf).eq_iff],
    split_ifs; refl, },
  { intros, simp only [*, alg_hom.map_add, coeff_add], }
end

lemma coeff_rename_eq_zero (f : σ → τ) (φ : mv_polynomial σ R) (d : τ →₀ ℕ)
  (h : ∀ u : σ →₀ ℕ, u.map_domain f = d → φ.coeff u = 0) :
  (rename f φ).coeff d = 0 :=
begin
  rw [rename_eq, coeff, ← not_mem_support_iff],
  intro H,
  replace H := map_domain_support H,
  rw [finset.mem_image] at H,
  obtain ⟨u, hu, rfl⟩ := H,
  specialize h u rfl,
  simp [mem_support_iff, coeff] at h hu,
  contradiction
end

lemma coeff_rename_ne_zero (f : σ → τ) (φ : mv_polynomial σ R) (d : τ →₀ ℕ)
  (h : (rename f φ).coeff d ≠ 0) :
  ∃ u : σ →₀ ℕ, u.map_domain f = d ∧ φ.coeff u ≠ 0 :=
by { contrapose! h, apply coeff_rename_eq_zero _ _ _ h }

end coeff

end mv_polynomial
