/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import data.mv_polynomial
import data.fintype.card

open equiv (perm)
open_locale big_operators

-- move this
def equiv.finset {α : Type*} {β : Type*} (e : α ≃ β) :
  finset α ≃ finset β :=
{ to_fun := finset.map e.to_embedding,
  inv_fun := finset.map e.symm.to_embedding,
  left_inv := λ s, by simp [finset.map_map, finset.map_refl],
  right_inv := λ s, by simp [finset.map_map, finset.map_refl] }

-- move this
noncomputable def equiv.finsupp {α : Type*} {β : Type*} {A : Type*} [add_comm_monoid A] (e : α ≃ β) :
  (α →₀ A) ≃ (β →₀ A) :=
{ to_fun := finsupp.emb_domain e.to_embedding,
  inv_fun := finsupp.emb_domain e.symm.to_embedding,
  left_inv := λ f, by { ext a,
    erw [← e.symm_apply_apply a, finsupp.emb_domain_apply,
        finsupp.emb_domain_apply, e.symm_apply_apply], },
  right_inv := λ f, by { ext b,
    erw [← e.apply_symm_apply b, finsupp.emb_domain_apply,
        finsupp.emb_domain_apply, e.apply_symm_apply] } }

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {R : Type*} {S : Type*}

/-- A symmetric polynomial is a polynomial that is invariant under
arbitrary permutations of the polynomial variables. -/
def is_symmetric [comm_semiring R] (φ : mv_polynomial σ R) : Prop :=
∀ ⦃e : perm σ⦄, φ.rename e = φ

namespace is_symmetric
variables [comm_semiring R] [comm_semiring S] {φ ψ : mv_polynomial σ R}

@[simp]
lemma C (r : R) : is_symmetric (C r : mv_polynomial σ R) :=
λ e, rename_C e r

@[simp]
lemma zero : is_symmetric (0 : mv_polynomial σ R) :=
by { rw [← C_0], exact is_symmetric.C 0 }

@[simp]
lemma one : is_symmetric (1 : mv_polynomial σ R) :=
by { rw [← C_1], exact is_symmetric.C 1 }

@[simp]
lemma add (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ + ψ) :=
λ e, by rw [rename_add, hφ, hψ]

@[simp]
lemma mul (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ * ψ) :=
λ e, by rw [rename_mul, hφ, hψ]

@[simp]
lemma map (hφ : is_symmetric φ) (f : R →+* S) : is_symmetric (map f φ) :=
λ e, by rw [← map_rename, hφ]

end is_symmetric

namespace is_symmetric
variables [comm_ring R] (φ ψ : mv_polynomial σ R)

@[simp]
lemma neg (hφ : is_symmetric φ) : is_symmetric (-φ) :=
λ e, by rw [rename_neg, hφ]

@[simp]
lemma sub (hφ : is_symmetric φ) (hψ : is_symmetric ψ) : is_symmetric (φ - ψ) :=
λ e, by rw [rename_sub, hφ, hψ]

end is_symmetric

section
/-!
## Elementary symmetric polynomials
-/
variables (σ R) [fintype σ] [fintype τ] [comm_semiring R] [comm_semiring S]

/-- `elementary_symmetric σ R n` is the `n`th elementary symmetric polynomial
with variables indexed by `σ` and coefficients in `R`.
It is defined as the sum of all products of `n` distinct variables. -/
noncomputable def elementary_symmetric (n : ℕ) : mv_polynomial σ R :=
∑ t : {s : finset σ // s.card = n},
  ∏ i in (t : finset σ), X i

@[simp] lemma elementary_symmetric_zero :
  elementary_symmetric σ R 0 = 1 :=
begin
  letI : unique ({s : finset σ // s.card = 0}) :=
  { default := ⟨∅, finset.card_empty⟩,
    uniq := by { rintro ⟨s, hs⟩, rw subtype.ext, rwa finset.card_eq_zero at hs, } },
  simp only [elementary_symmetric, univ_unique, finset.sum_singleton],
  exact finset.prod_empty,
end

variables {σ R}

lemma map_elementary_symmetric (n : ℕ) (f : R →+* S) :
  map f (elementary_symmetric σ R n) = elementary_symmetric σ S n :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial σ S := ring_hom.of (map f),
  show F (elementary_symmetric σ R n) = elementary_symmetric σ S n,
  rw [elementary_symmetric, F.map_sum],
  apply fintype.sum_congr,
  intros t,
  calc _ = _ : F.map_prod _ _
     ... = _ : _,
  apply finset.prod_congr rfl,
  simp only [eq_self_iff_true, map_X, ring_hom.coe_of, forall_true_iff],
end

lemma rename_elementary_symmetric (n : ℕ) (e : σ ≃ τ) :
  rename e (elementary_symmetric σ R n) = elementary_symmetric τ R n :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial τ R := ring_hom.of (rename e),
  show F (elementary_symmetric σ R n) = elementary_symmetric τ R n,
  rw [elementary_symmetric, F.map_sum],
  let e' : {s : finset σ // s.card = n} ≃ {s : finset τ // s.card = n} :=
    e.finset.subtype_congr
      (by { intro, simp only [equiv.finset, equiv.coe_fn_mk, finset.card_map] }),
  rw ← finset.sum_equiv e'.symm,
  apply fintype.sum_congr,
  intro s,
  show F (∏ i in (e'.symm s : finset σ), X i) = ∏ i in (s : finset τ), X i,
  calc _ = _ : F.map_prod _ _
     ... = _ : finset.prod_map (s : finset τ) _ _
     ... = _ : _,
  apply finset.prod_congr rfl,
  intros,
  simp only [rename_X, equiv.apply_symm_apply, ring_hom.coe_of, equiv.to_embedding_coe_fn],
end

lemma elementary_symmetric_is_symmetric (n : ℕ) :
  is_symmetric (elementary_symmetric σ R n) :=
rename_elementary_symmetric n

end

section
variables [fintype σ] [comm_ring R]

lemma aeval_elementary_symmetric_is_symmetric (φ : mv_polynomial ℕ R) :
  is_symmetric (aeval _ _ (elementary_symmetric σ R) φ) :=
begin
  apply mv_polynomial.induction_on φ,
  { intro r, rw aeval_C, apply is_symmetric.C },
  { intros φ ψ h₁ h₂, rw alg_hom.map_add, exact h₁.add h₂ },
  { intros φ n h, rw [alg_hom.map_mul, aeval_X], exact h.mul (elementary_symmetric_is_symmetric n) }
end

end

section
/-!
## Power-sum symmetric polynomials
-/
variables (σ R) [fintype σ] [fintype τ] [comm_semiring R] [comm_semiring S]

/-- `powersum_symmetric σ R n` is the `n`th power-sum symmetric polynomial
with variables indexed by `σ` and coefficients in `R`.
It is defined as the sum of all `n`th powers of all variables. -/
noncomputable def powersum_symmetric (n : ℕ) : mv_polynomial σ R :=
∑ i : σ, (X i)^n

variables {σ R}

lemma map_powersum_symmetric (n : ℕ) (f : R →+* S) :
  map f (powersum_symmetric σ R n) = powersum_symmetric σ S n :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial σ S := ring_hom.of (map f),
  show F (powersum_symmetric σ R n) = powersum_symmetric σ S n,
  rw [powersum_symmetric, F.map_sum],
  apply fintype.sum_congr,
  intro,
  rw [F.map_pow, ring_hom.coe_of, map_X],
end

lemma rename_powersum_symmetric (n : ℕ) (e : σ ≃ τ) :
  rename e (powersum_symmetric σ R n) = powersum_symmetric τ R n :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial τ R := ring_hom.of (rename e),
  show F (powersum_symmetric σ R n) = powersum_symmetric τ R n,
  rw [powersum_symmetric, F.map_sum],
  rw ← finset.sum_equiv e.symm,
  apply fintype.sum_congr,
  intro s,
  show F (X ((e.symm) s) ^ n) = X s ^ n,
  rw [F.map_pow, ring_hom.coe_of, rename_X, equiv.apply_symm_apply],
end

lemma powersum_symmetric_is_symmetric (n : ℕ) :
  is_symmetric (powersum_symmetric σ R n) :=
rename_powersum_symmetric n

end

section
/-!
## Complete homogeneous symmetric polynomials
-/
variables (σ R) [fintype σ] [fintype τ] [comm_semiring R] [comm_semiring S]

noncomputable def complete_homogeneous.support_fintype (n : ℕ) :
  fintype {d : σ →₀ ℕ // ∑ i, d i = n} :=
set.finite.fintype $
begin
  let f : σ →₀ ℕ := finsupp.equiv_fun_on_fintype.symm (λ _, n),
  apply set.finite_subset (finsupp.finite_le_nat f),
  intros d hd i,
  calc d i ≤ ∑ i, d i : finset.single_le_sum (λ _ _, nat.zero_le _) (finset.mem_univ _)
       ... = n        : hd
       ... = f i      : rfl
end

local attribute [instance] complete_homogeneous.support_fintype

/-- `complete_homogeneous σ R n` is the `n`th complete homogeneous symmetric polynomial
with variables indexed by `σ` and coefficients in `R`.
It is defined as the sum of all monomials of degree `n`. -/
noncomputable def complete_homogeneous (n : ℕ) : mv_polynomial σ R :=
∑ d : {d : σ →₀ ℕ // ∑ i, d i = n}, monomial d 1

@[simp] lemma complete_homogeneous_zero :
  complete_homogeneous σ R 0 = 1 :=
begin
  letI : unique {d : σ →₀ ℕ // ∑ i, d i = 0} :=
  { default := ⟨0, by simp only [finsupp.zero_apply, finset.sum_const_zero]⟩,
    uniq := by { rintro ⟨d, hd⟩, rw subtype.ext, ext i,
                 rw [finset.sum_eq_zero_iff] at hd,
                 exact hd _ (finset.mem_univ _) } },
  simp only [complete_homogeneous, univ_unique, finset.sum_singleton],
  refl
end

variables {σ R}

lemma map_complete_homogeneous (n : ℕ) (f : R →+* S) :
  map f (complete_homogeneous σ R n) = complete_homogeneous σ S n :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial σ S := ring_hom.of (map f),
  show F (complete_homogeneous σ R n) = complete_homogeneous σ S n,
  rw [complete_homogeneous, F.map_sum],
  apply fintype.sum_congr,
  intro,
  rw [ring_hom.coe_of, map_monomial, f.map_one],
end

lemma rename_complete_homogeneous (n : ℕ) (e : σ ≃ τ) :
  rename e (complete_homogeneous σ R n) = complete_homogeneous τ R n :=
begin
  let F : mv_polynomial σ R →+* mv_polynomial τ R := ring_hom.of (rename e),
  show F (complete_homogeneous σ R n) = complete_homogeneous τ R n,
  rw [complete_homogeneous, F.map_sum],
  let e' : {d : σ →₀ ℕ // ∑ i, d i = n} ≃ {d : τ →₀ ℕ // ∑ i, d i = n} :=
    e.finsupp.subtype_congr
      (by { intro d,
            rw ← finset.sum_equiv e,
            show (∑ i, d i = n) ↔ (∑ i, (d.emb_domain e.to_embedding) (e.to_embedding i)) = n,
            simp only [finsupp.emb_domain_apply], }),
  rw ← finset.sum_equiv e'.symm,
  apply fintype.sum_congr,
  intro d,
  show F (monomial (e'.symm d) 1) = monomial d 1,
  rw [ring_hom.coe_of, rename_monomial],
  congr,
  ext i,
  simp only [finsupp.map_domain, finsupp.sum_apply, finsupp.single_apply],
  rw [finsupp.sum, finset.sum_eq_single (e.symm i)],
  { simpa only [e', equiv.finsupp, equiv.subtype_congr, if_true, equiv.coe_fn_symm_mk,
      eq_self_iff_true, equiv.apply_symm_apply, subtype.coe_mk]
      using finsupp.emb_domain_apply e.symm.to_embedding _ _ },
  { rintro j h hj, rw if_neg, rintro rfl, simpa using hj },
  { simp only [finsupp.not_mem_support_iff, imp_self, if_true,
      eq_self_iff_true, equiv.apply_symm_apply], }
end

lemma complete_homogeneous_is_symmetric (n : ℕ) :
  is_symmetric (complete_homogeneous σ R n) :=
rename_complete_homogeneous n

end

section
variables (σ R) [fintype σ] [comm_ring R]

lemma alternating_sum_elementary_symmetric_mul_complete_homogeneous (n : ℕ) :
  ∑ ij in (finset.nat.antidiagonal n),
    C (-1)^ij.1 * elementary_symmetric σ R ij.1 * complete_homogeneous σ R ij.2 = 0 :=
begin
  rw mv_polynomial.ext_iff,
  intro d,
  rw [coeff_sum, coeff_zero],
  conv_lhs { apply_congr, skip, rw [mul_assoc, ← C_pow, coeff_C_mul, coeff_mul, finset.mul_sum] },
  rw finset.sum_comm,
  let L := d.antidiagonal.support.filter (λ p : (σ →₀ ℕ) × (σ →₀ ℕ), p.1.sum (λ _, id) % 2 = 0),
  let R := d.antidiagonal.support.filter (λ p : (σ →₀ ℕ) × (σ →₀ ℕ), p.1.sum (λ _, id) % 2 = 1),
  classical,
  have hLR : d.antidiagonal.support = L ∪ R,
  { ext p,
    simp only [finsupp.mem_antidiagonal_support, finset.mem_union, finset.mem_filter],
    have := nat.mod_two_eq_zero_or_one (p.1.sum (λ _, id)),
    rw classical.or_iff_not_imp_left at this,
    tauto },
  have LR_disjoint : disjoint L R,
  { rw finset.disjoint_filter, intros p hp h0, rw h0, exact zero_ne_one },
  rw [hLR, finset.sum_union LR_disjoint],
end

end

end mv_polynomial

#lint
