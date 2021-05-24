/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import ring_theory.principal_ideal_domain
import ring_theory.ideal.basic
import linear_algebra.foo

/-!
# Invariant basis number property

We say that a ring `R` satisfies the invariant basis number property if there is a well-defined
notion of the rank of a finitely generated free (left) `R`-module. Since a finitely generated free
module with a basis consisting of `n` elements is linearly equivalent to `fin n → R`, it is
sufficient that `(fin n → R) ≃ₗ[R] (fin m → R)` implies `n = m`.

It is also useful to consider two stronger conditions, namely the rank condition,
that a surjective linear map `(fin n → R) →ₗ[R] (fin m → R)` implies `m ≤ n` and
the strong rank condition, that an injective linear map `(fin n → R) →ₗ[R] (fin m → R)`
implies `n ≤ m`.

The strong rank condition implies the rank condition, and the rank condition implies
the invariant basis number property.

## Main definitions

`strong_rank_condition R` is a type class stating that `R` satisfies the strong rank condition.
`rank_condition R` is a type class stating that `R` satisfies the rank condition.
`invariant_basis_number R` is a type class stating that `R` has the invariant basis number property.

## Main results

We show that every nontrivial left-noetherian ring satisfies the rank condition,
(and so in particular every division ring or field),
and then use this to show every nontrivial commutative ring has the invariant basis number property.

## Future work

We can improve these results: in fact every nontrivial left-noetherian ring,
and every commutative rings, satisfies the strong rank condition.

So far, there is no API at all for the `invariant_basis_number` class. There are several natural
ways to formulate that a module `M` is finitely generated and free, for example
`M ≃ₗ[R] (fin n → R)`, `M ≃ₗ[R] (ι → R)`, where `ι` is a fintype, or providing a basis indexed by
a finite type. There should be lemmas applying the invariant basis number property to each
situation.

The finite version of the invariant basis number property implies the infinite analogue, i.e., that
`(ι →₀ R) ≃ₗ[R] (ι' →₀ R)` implies that `cardinal.mk ι = cardinal.mk ι'`. This fact (and its
variants) should be formalized.

## References

* https://en.wikipedia.org/wiki/Invariant_basis_number
* https://mathoverflow.net/a/2574/

## Tags

free module, rank, invariant basis number, IBN

-/

noncomputable theory

open_locale classical big_operators
open function

universes u v w

section
variables (R : Type u) [ring R]

/-- We say that `R` satisfies the strong rank condition if `(fin n → R) →ₗ[R] (fin m → R)` injective
    implies `n ≤ m`. -/
class strong_rank_condition : Prop :=
(le_of_fin_injective : ∀ {n m : ℕ} (f : (fin n → R) →ₗ[R] (fin m → R)), injective f → n ≤ m)

lemma le_of_fin_injective [strong_rank_condition R] {n m : ℕ} (f : (fin n → R) →ₗ[R] (fin m → R)) :
  injective f → n ≤ m :=
strong_rank_condition.le_of_fin_injective f

/-- We say that `R` satisfies the rank condition if `(fin n → R) →ₗ[R] (fin m → R)` surjective
    implies `m ≤ n`. -/
class rank_condition : Prop :=
(le_of_fin_surjective : ∀ {n m : ℕ} (f : (fin n → R) →ₗ[R] (fin m → R)), surjective f → m ≤ n)

lemma le_of_fin_surjective [rank_condition R] {n m : ℕ} (f : (fin n → R) →ₗ[R] (fin m → R)) :
  surjective f → m ≤ n :=
rank_condition.le_of_fin_surjective f

/--
By the universal property for free modules, any surjective map `(fin n → R) →ₗ[R] (fin m → R)`
has an injective splitting `(fin m → R) →ₗ[R] (fin n → R)`
from which the strong rank condition gives the necessary inequality for the rank condition.
-/
@[priority 100]
instance rank_condition_of_strong_rank_condition [strong_rank_condition R] : rank_condition R :=
{ le_of_fin_surjective := λ n m f s,
    le_of_fin_injective R _ (f.splitting_of_fun_on_fintype_surjective_injective s), }

/-- We say that `R` has the invariant basis number property if `(fin n → R) ≃ₗ[R] (fin m → R)`
    implies `n = m`. This gives rise to a well-defined notion of rank of a finitely generated free
    module. -/
class invariant_basis_number : Prop :=
(eq_of_fin_equiv : ∀ {n m : ℕ}, ((fin n → R) ≃ₗ[R] (fin m → R)) → n = m)

@[priority 100]
instance invariant_basis_number_of_rank_condition [rank_condition R] : invariant_basis_number R :=
{ eq_of_fin_equiv := λ n m e, le_antisymm
    (le_of_fin_surjective R e.symm.to_linear_map e.symm.surjective)
    (le_of_fin_surjective R e.to_linear_map e.surjective) }

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
variables (R : Type u) [ring R] [nontrivial R] [is_noetherian_ring R]

/--
Any nontrivial noetherian ring satisfies the strong rank condition.

An injective map `((fin n ⊕ fin (1 + m)) → R) →ₗ[R] (fin n → R)` for some left-noetherian `R`
would force `fin (1 + m) → R ≃ₗ punit` (via `is_noetherian.equiv_punit_of_prod_injective`),
which is not the case!
-/
-- Note this includes fields,
-- and we use this below to show any commutative ring has invariant basis number.
@[priority 100]
instance noetherian_ring_strong_rank_condition : strong_rank_condition R :=
begin
  fsplit,
  intros m n f i,
  by_contradiction h,
  rw [not_le, ←nat.add_one_le_iff, le_iff_exists_add] at h,
  obtain ⟨m, rfl⟩ := h,
  let e : fin (n + 1 + m) ≃ fin n ⊕ fin (1 + m) :=
    (fin_congr (add_assoc _ _ _)).trans fin_sum_fin_equiv.symm,
  let f' := f.comp ((linear_equiv.sum_arrow_lequiv_prod_arrow _ _ R R).symm.trans
    (linear_map.fun_congr_left R R e)).to_linear_map,
  have i' : injective f' := i.comp (linear_equiv.injective _),
  apply @zero_ne_one (fin (1 + m) → R) _ _,
  apply (is_noetherian.equiv_punit_of_prod_injective f' i').injective,
  ext,
end

@[priority 100]
instance noetherian_ring_rank_condition' : rank_condition R :=
@rank_condition_of_strong_rank_condition R _ (noetherian_ring_strong_rank_condition R)

/-- Any nontrivial noetherian ring satisfies the rank condition. -/
-- Note this includes fields,
-- and we use this below to show any commutative ring has invariant basis number.
@[priority 100]
instance noetherian_ring_rank_condition : rank_condition R :=
⟨begin
  intros n m f fs,
  by_contradiction h,
  rw [not_le, ←nat.add_one_le_iff, le_iff_exists_add] at h,
  obtain ⟨m, rfl⟩ := h,
  -- Let `g` be the projection map discarding the last `n` coordinates.
  let g : (fin ((n + 1) + m) → R) →ₗ[R] (fin n → R) :=
    linear_map.fun_left R R ((fin.cast_add 1).trans (fin.cast_add m)),
  have gs : function.surjective g :=
    linear_map.fun_left_surjective_of_injective _ _ _
      ((fin.cast_add m).injective.comp (fin.cast_add 1).injective),
  -- Since `g` composed with the `f` is a surjective endomorphism of
  -- a noetherian module, it is injective, and so `f` itself is injective.
  have gi : function.injective g :=
    (is_noetherian.injective_of_surjective_endomorphism (f.comp g)
      (function.surjective.comp fs gs)).of_comp,
  -- But this gives an easy contradiction.
  let i : fin (n + 1 + m) := fin.cast_add m (fin.nat_add n 0),
  let x : fin (n + 1 + m) → R := finsupp.single i 1,
  have z : g x = 0 := begin
    ext j,
    simp only [g, x, i, linear_map.fun_left_apply, pi.zero_apply],
    rw finsupp.single_eq_of_ne,
    refine fin.ne_of_vne _,
    simp only [add_zero, fin.coe_zero, fin.val_eq_coe, fin.coe_nat_add, ne.def, fin.coe_cast_add],
    exact j.2.ne.symm,
  end,
  simpa [x] using congr_fun ((g.map_eq_zero_iff gi).mp z) i,
end⟩

end

/-!
  We want to show that nontrivial commutative rings have invariant basis number. The idea is to
  take a maximal ideal `I` of `R` and use an isomorphism `R^n ≃ R^m` of `R` modules to produce an
  isomorphism `(R/I)^n ≃ (R/I)^m` of `R/I`-modules, which will imply `n = m` since `R/I` is a field
  and we know that fields have invariant basis number.

  We construct the isomorphism in two steps:
  1. We construct the ring `R^n/I^n`, show that it is an `R/I`-module and show that there is an
     isomorphism of `R/I`-modules `R^n/I^n ≃ (R/I)^n`. This isomorphism is called
    `ideal.pi_quot_equiv` and is located in the file `ring_theory/ideals.lean`.
  2. We construct an isomorphism of `R/I`-modules `R^n/I^n ≃ R^m/I^m` using the isomorphism
     `R^n ≃ R^m`.
-/

section
variables {R : Type u} [comm_ring R] (I : ideal R) {ι : Type v} [fintype ι] {ι' : Type w}

/-- An `R`-linear map `R^n → R^m` induces a function `R^n/I^n → R^m/I^m`. -/
private def induced_map (I : ideal R) (e : (ι → R) →ₗ[R] (ι' → R)) :
  (I.pi ι).quotient → (I.pi ι').quotient :=
λ x, quotient.lift_on' x (λ y, ideal.quotient.mk _ (e y))
begin
  refine λ a b hab, ideal.quotient.eq.2 (λ h, _),
  rw ←linear_map.map_sub,
  exact ideal.map_pi _ _ hab e h,
end

/-- An isomorphism of `R`-modules `R^n ≃ R^m` induces an isomorphism of `R/I`-modules
    `R^n/I^n ≃ R^m/I^m`. -/
private def induced_equiv [fintype ι'] (I : ideal R) (e : (ι → R) ≃ₗ[R] (ι' → R)) :
  (I.pi ι).quotient ≃ₗ[I.quotient] (I.pi ι').quotient :=
begin
  refine { to_fun := induced_map I e, inv_fun := induced_map I e.symm, .. },
  all_goals { rintro ⟨a⟩ ⟨b⟩ <|> rintro ⟨a⟩,
    change ideal.quotient.mk _ _ = ideal.quotient.mk _ _,
    congr, simp }
end

end

section
local attribute [instance] ideal.quotient.field

-- TODO: in fact, any nontrivial commutative ring satisfies the strong rank condition.
-- To see this, consider `f : (fin m → R) →ₗ[R] (fin n → R)`,
-- and consider the subring `A` of `R` generated by the matrix entries.
-- That subring is noetherian, and `f` induces a new linear map `f' : (fin m → A) →ₗ[R] (fin n → A)`
-- which is injective if `f` is, giving the result.

/-- Nontrivial commutative rings have the invariant basis number property. -/
@[priority 100]
instance invariant_basis_number_of_nontrivial_of_comm_ring {R : Type u} [comm_ring R]
  [nontrivial R] : invariant_basis_number R :=
⟨λ n m e, let ⟨I, hI⟩ := ideal.exists_maximal R in
  by exactI eq_of_fin_equiv I.quotient
    ((ideal.pi_quot_equiv _ _).symm.trans ((induced_equiv _ e).trans (ideal.pi_quot_equiv _ _)))⟩

end
