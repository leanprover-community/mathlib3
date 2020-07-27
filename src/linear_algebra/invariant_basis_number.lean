/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import linear_algebra.finite_dimensional
import ring_theory.ideals

/-!
# Invariant basis number property

We say that a ring `R` satisfies the invariant basis number property if there is a well-defined
notion of the rank of a finitely generated free (left) `R`-module. Since a finitely generated free
module with a basis consisting of `n` elements is linearly equivalent to `fin n → R`, it is
sufficient that `(fin n → R) ≃ₗ[R] (fin m → R)` implies `n = m`.

## Main definitions

`invariant_basis_number R` is a type class stating that `R` has the invariant basis number property.

## Main results

We show that every nontrivial commutative ring has the invariant basis number property.

## Future work

So far, there is no API at all for the `invariant_basis_number` class. There are several natural
ways to formulate that a module `M` is finitely generated and free, for example
`M ≃ₗ[R] (fin n → R)`, `M ≃ₗ[R] (ι → R)`, where `ι` is a fintype, or prividing a basis indexed by
a finite type. There should be lemmas applying the invariant basis number property to each
situation.

The finite version of the invariant basis number property implies the inifite analogue, i.e., that
`(ι →₀ R) ≃ₗ[R] (ι' →₀ R)` implies that `cardinal.mk ι = cardinal.mk ι'`. This fact (and its
variants) should be formalized.

## References

* https://en.wikipedia.org/wiki/Invariant_basis_number

## Tags

free module, rank, invariant basis number, IBN

-/

noncomputable theory

open_locale classical big_operators

universes u v w

section
variables (R : Type u) [ring R]

/-- We say that `R` has the invariant basis number property if `(fin n → R) ≃ₗ[R] (fin m → R)`
    implies `n = m`. This gives rise to a well-defined notion of rank of a finitely generated free
    module. -/
class invariant_basis_number : Prop :=
(eq_of_fin_equiv : ∀ {n m : ℕ}, ((fin n → R) ≃ₗ[R] (fin m → R)) → n = m)

end

section
variables (R : Type u) [ring R] [invariant_basis_number R]

lemma eq_of_fin_equiv {n m : ℕ} : ((fin n → R) ≃ₗ[R] (fin m → R)) → n = m :=
invariant_basis_number.eq_of_fin_equiv

lemma nontrivial_of_invariant_basis_number : nontrivial R :=
begin
  by_contra h,
  refine zero_ne_one (eq_of_fin_equiv R _),
  haveI := not_nontrivial_iff_subsingleton.1 h,
  haveI : subsingleton (fin 1 → R) := ⟨λ a b, funext $ λ x, subsingleton.elim _ _⟩,
  refine { .. }; { intros, exact 0 } <|> tidy
end

end

section
open finite_dimensional

/-- A field has invariant basis number. This will be superseded below by the fact that any nonzero
    commutative ring has invariant basis number. -/
lemma invariant_basis_number_field {K : Type u} [field K] : invariant_basis_number K :=
⟨λ n m e,
  calc n = fintype.card (fin n) : eq.symm $ fintype.card_fin n
     ... = findim K (fin n → K) : eq.symm $ findim_eq_card_basis (pi.is_basis_fun K (fin n))
     ... = findim K (fin m → K) : linear_equiv.findim_eq e
     ... = fintype.card (fin m) : findim_eq_card_basis (pi.is_basis_fun K (fin m))
     ... = m                    : fintype.card_fin m⟩

end

/-!
  We want to show that nontrivial commutative rings have invariant basis number. The idea is to
  take a maximal ideal `I` of `R` and use an isomorphism `R^n ≃ R^m` of `R` modules to produce an
  isomorphism `(R/I)^n ≃ (R/I)^m` of `R/I`-modules, which will imply `n = m` since `R/I` is a field
  and we know that fields have invariant basis number.

  We construct the isomorphism in two steps:
  1. We construct the ring `R^n/I^n`, show that it is an `R/I`-module and show that there is an
     isomorphism of `R/I`-modules `R^n/I^n ≃ (R/I)^n`.
  2. We construct an isomorphism of `R/I`-modules `R^n/I^n ≃ R^m/I^m` using the isomorphism
     `R^n ≃ R^m`.
-/

section
variables {R : Type u} [comm_ring R] (I : ideal R) (ι : Type v)

/-- `I^n` as an ideal of `R^n`. -/
def ideal.pi : ideal (ι → R) :=
{ carrier := { x | ∀ i, x i ∈ I },
  zero_mem' := λ i, submodule.zero_mem _,
  add_mem' := λ a b ha hb i, submodule.add_mem _ (ha i) (hb i),
  smul_mem' := λ a b hb i, ideal.mul_mem_left _ (hb i) }

lemma ideal.mem_pi (x : ι → R) : x ∈ I.pi ι ↔ ∀ i, x i ∈ I := iff.rfl

/-- `R^n/I^n` is a `R/I`-module. -/
instance ideal.module_pi : module (I.quotient) (I.pi ι).quotient :=
begin
  refine { smul := λ c m, quotient.lift_on₂' c m (λ r m, submodule.quotient.mk $ r • m) _, .. },
  { intros c₁ m₁ c₂ m₂ hc hm,
    change c₁ - c₂ ∈ I at hc,
    change m₁ - m₂ ∈ (I.pi ι) at hm,
    apply ideal.quotient.eq.2,
    have : c₁ • (m₂ - m₁) ∈ I.pi ι,
    { rw ideal.mem_pi,
      intro i,
      simp only [algebra.id.smul_eq_mul, pi.smul_apply, pi.sub_apply],
      apply ideal.mul_mem_left,
      rw ←ideal.neg_mem_iff,
      simpa only [neg_sub] using hm i },
    rw [←ideal.add_mem_iff_left (I.pi ι) this, sub_eq_add_neg, add_comm, ←add_assoc, ←smul_add,
      sub_add_cancel, ←sub_eq_add_neg, ←sub_smul, ideal.mem_pi],
    intro i,
    simp only [algebra.id.smul_eq_mul, pi.smul_apply],
    exact ideal.mul_mem_right _ hc },
  all_goals { rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ <|> rintro ⟨a⟩,
    simp only [(•), submodule.quotient.quot_mk_eq_mk, ideal.quotient.mk_eq_mk],
    change ideal.quotient.mk _ _ = ideal.quotient.mk _ _,
    congr, ext, simp [mul_assoc, mul_add, add_mul] }
end

/-- `R^n/I^n` is isomorphic to `(R/I)^n` as an `R/I`-module. -/
def ideal.pi_quot_equiv : (I.pi ι).quotient ≃ₗ[I.quotient] (ι → I.quotient) :=
{ to_fun := λ x, quotient.lift_on' x (λ f i, ideal.quotient.mk I (f i)) $
    λ a b hab, funext (λ i, ideal.quotient.eq.2 (hab i)),
  map_add' := by { rintros ⟨_⟩ ⟨_⟩, refl },
  map_smul' := by { rintros ⟨_⟩ ⟨_⟩, refl },
  inv_fun := λ x, ideal.quotient.mk (I.pi ι) $ λ i, quotient.out' (x i),
  left_inv :=
  begin
    rintro ⟨x⟩,
    exact ideal.quotient.eq.2 (λ i, ideal.quotient.eq.1 (quotient.out_eq' _))
  end,
  right_inv :=
  begin
    intro x,
    ext i,
    obtain ⟨r, hr⟩ := @quot.exists_rep _ _ (x i),
    simp_rw ←hr,
    convert quotient.out_eq' _
  end }

end

section fintype
variables {R : Type u} [comm_ring R] {ι : Type v} [fintype ι] {ι' : Type w}

/-- If `f : R^n → R^m` is an `R`-linear map and `I ⊆ R` is an ideal, then the image of `I^n` is
    contained in `I^m`. -/
lemma linear_map.map_pi_ideal (I : ideal R) (x : ι → R) (hi : ∀ i, x i ∈ I)
  (f : (ι → R) →ₗ[R] (ι' → R)) (i : ι') : f x i ∈ I :=
begin
  rw pi_eq_sum_univ x,
  simp only [finset.sum_apply, smul_eq_mul, linear_map.map_sum, pi.smul_apply, linear_map.map_smul],
  exact submodule.sum_mem _ (λ j hj, ideal.mul_mem_right _ (hi j))
end

end fintype

section

local attribute [instance] invariant_basis_number_field
local attribute [instance, priority 1] ideal.quotient.field

/-- An isomorphism of `R`-modules `R^n ≃ R^m` induces a function `R^n/I^n → R^m/I^n`. -/
private def induced_map {R : Type u} [comm_ring R] (I : ideal R) (n m : ℕ)
  (e : (fin n → R) →ₗ[R] (fin m → R)) : (I.pi (fin n)).quotient → (I.pi (fin m)).quotient :=
λ x, quotient.lift_on' x (λ y, ideal.quotient.mk _ (e y))
begin
  refine λ a b hab, ideal.quotient.eq.2 (λ h, _),
  rw ←linear_map.map_sub,
  exact linear_map.map_pi_ideal _ _ hab e h,
end

/-- An isomorphism of `R`-modules `R^n ≃ R^m` induces an isomorphism `R/I`-modules
    `R^n/I^n ≃ R^m/I^m`. -/
private def induced_equiv {R : Type u} [comm_ring R] (I : ideal R) {n m : ℕ}
  (e : (fin n → R) ≃ₗ[R] (fin m → R)) :
  (I.pi (fin n)).quotient ≃ₗ[I.quotient] (I.pi (fin m)).quotient :=
begin
  refine { to_fun := induced_map I n m e, inv_fun := induced_map I m n e.symm, .. },
  { rintro ⟨x⟩ ⟨y⟩,
    change ideal.quotient.mk (I.pi (fin m)) (e (x + y)) =
      ideal.quotient.mk _ (e x) + ideal.quotient.mk _ (e y),
    simp only [ring_hom.map_add, linear_equiv.map_add] },
  all_goals { rintro ⟨a⟩ ⟨b⟩ <|> rintro ⟨a⟩,
    change ideal.quotient.mk _ _ = ideal.quotient.mk _ _,
    congr, simp }
end

/-- Nontrivial commutative rings have the invariant basis number property. -/
@[priority 100]
instance invariant_basis_number_of_nontrivial_of_comm_ring {R : Type u} [comm_ring R]
  [nontrivial R] : invariant_basis_number R :=
⟨begin
  intros n m e,
  obtain ⟨I, ⟨hI, hI'⟩⟩ := ideal.exists_le_maximal (⊥ : ideal R) submodule.bot_ne_top,
  resetI,
  exact eq_of_fin_equiv I.quotient
    ((ideal.pi_quot_equiv _ _).symm.trans ((induced_equiv _ e).trans (ideal.pi_quot_equiv _ _)))
end⟩

end
