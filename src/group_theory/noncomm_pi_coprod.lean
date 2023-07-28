/-
Copyright (c) 2022 Joachim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import group_theory.order_of_element
import data.finset.noncomm_prod
import data.fintype.big_operators
import data.nat.gcd.big_operators
import order.sup_indep

/-!
# Canonical homomorphism from a finite family of monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the construction of the canonical homomorphism from a family of monoids.

Given a family of morphisms `ϕ i : N i →* M` for each `i : ι` where elements in the
images of different morphisms commute, we obtain a canonical morphism
`monoid_hom.noncomm_pi_coprod : (Π i, N i) →* M` that coincides with `ϕ`

## Main definitions

* `monoid_hom.noncomm_pi_coprod : (Π i, N i) →* M` is the main homomorphism
* `subgroup.noncomm_pi_coprod : (Π i, H i) →* G` is the specialization to `H i : subgroup G`
   and the subgroup embedding.

## Main theorems

* `monoid_hom.noncomm_pi_coprod` coincides with `ϕ i` when restricted to `N i`
* `monoid_hom.noncomm_pi_coprod_mrange`: The range of `monoid_hom.noncomm_pi_coprod` is
  `⨆ (i : ι), (ϕ i).mrange`
* `monoid_hom.noncomm_pi_coprod_range`: The range of `monoid_hom.noncomm_pi_coprod` is
  `⨆ (i : ι), (ϕ i).range`
* `subgroup.noncomm_pi_coprod_range`: The range of `subgroup.noncomm_pi_coprod` is `⨆ (i : ι), H i`.
* `monoid_hom.injective_noncomm_pi_coprod_of_independent`: in the case of groups, `pi_hom.hom` is
   injective if the `ϕ` are injective and the ranges of the `ϕ` are independent.
* `monoid_hom.independent_range_of_coprime_order`: If the `N i` have coprime orders, then the ranges
   of the `ϕ` are independent.
* `subgroup.independent_of_coprime_order`: If commuting normal subgroups `H i` have coprime orders,
   they are independent.

-/

open_locale big_operators

namespace subgroup

variables {G : Type*} [group G]

/-- `finset.noncomm_prod` is “injective” in `f` if `f` maps into independent subgroups.  This
generalizes (one direction of) `subgroup.disjoint_iff_mul_eq_one`. -/
@[to_additive "`finset.noncomm_sum` is “injective” in `f` if `f` maps into independent subgroups.
This generalizes (one direction of) `add_subgroup.disjoint_iff_add_eq_zero`. "]
lemma eq_one_of_noncomm_prod_eq_one_of_independent {ι : Type*} (s : finset ι) (f : ι → G) (comm)
  (K : ι → subgroup G) (hind : complete_lattice.independent K) (hmem : ∀ (x ∈ s), f x ∈ K x)
  (heq1 : s.noncomm_prod f comm = 1) : ∀ (i ∈ s), f i = 1 :=
begin
  classical,
  revert heq1,
  induction s using finset.induction_on with i s hnmem ih,
  { simp, },
  { have hcomm := comm.mono (finset.coe_subset.2 $ finset.subset_insert _ _),
    simp only [finset.forall_mem_insert] at hmem,
    have hmem_bsupr: s.noncomm_prod f hcomm ∈ ⨆ (i ∈ (s : set ι)), K i,
    { refine subgroup.noncomm_prod_mem _ _ _,
      intros x hx,
      have : K x ≤ ⨆ (i ∈ (s : set ι)), K i := le_supr₂ x hx,
      exact this (hmem.2 x hx), },
    intro heq1,
    rw finset.noncomm_prod_insert_of_not_mem _ _ _ _ hnmem at heq1,
    have hnmem' : i ∉ (s : set ι), by simpa,
    obtain ⟨heq1i : f i = 1, heq1S : s.noncomm_prod f _ = 1⟩ :=
      subgroup.disjoint_iff_mul_eq_one.mp (hind.disjoint_bsupr hnmem') hmem.1 hmem_bsupr heq1,
    intros i h,
    simp only [finset.mem_insert] at h,
    rcases h with ⟨rfl | _⟩,
    { exact heq1i },
    { exact ih hcomm hmem.2 heq1S _ h } }
end

end subgroup


section family_of_monoids

variables {M : Type*} [monoid M]

-- We have a family of monoids
-- The fintype assumption is not always used, but declared here, to keep things in order
variables {ι : Type*} [hdec : decidable_eq ι] [fintype ι]
variables {N : ι → Type*} [∀ i, monoid (N i)]

-- And morphisms ϕ into G
variables (ϕ : Π (i : ι), N i →* M)

-- We assume that the elements of different morphism commute
variables (hcomm : pairwise $ λ i j, ∀ x y, commute (ϕ i x) (ϕ j y))
include hcomm

-- We use `f` and `g` to denote elements of `Π (i : ι), N i`
variables (f g : Π (i : ι), N i)

namespace monoid_hom

/-- The canonical homomorphism from a family of monoids. -/
@[to_additive "The canonical homomorphism from a family of additive monoids.

See also `linear_map.lsum` for a linear version without the commutativity assumption."]
def noncomm_pi_coprod : (Π (i : ι), N i) →* M :=
{ to_fun := λ f, finset.univ.noncomm_prod (λ i, ϕ i (f i)) $ λ i _ j _ h, hcomm h _ _,
  map_one' := by {apply (finset.noncomm_prod_eq_pow_card _ _ _ _ _).trans (one_pow _), simp},
  map_mul' := λ f g,
  begin
    classical,
    convert @finset.noncomm_prod_mul_distrib _ _ _ _ (λ i, ϕ i (f i)) (λ i, ϕ i (g i)) _ _ _,
    { ext i, exact map_mul (ϕ i) (f i) (g i), },
    { rintros i - j - h, exact hcomm h _ _ },
  end }

variable {hcomm}

include hdec

@[simp, to_additive]
lemma noncomm_pi_coprod_mul_single (i : ι) (y : N i):
  noncomm_pi_coprod ϕ hcomm (pi.mul_single i y) = ϕ i y :=
begin
  change finset.univ.noncomm_prod (λ j, ϕ j (pi.mul_single i y j)) _ = ϕ i y,
  simp only [←finset.insert_erase (finset.mem_univ i)] {single_pass := tt},
  rw finset.noncomm_prod_insert_of_not_mem _ _ _ _ (finset.not_mem_erase i _),
  rw pi.mul_single_eq_same,
  rw finset.noncomm_prod_eq_pow_card,
  { rw one_pow, exact mul_one _  },
  { intros j hj, simp only [finset.mem_erase] at hj, simp [hj], },
end

omit hcomm

/-- The universal property of `noncomm_pi_coprod` -/
@[to_additive "The universal property of `noncomm_pi_coprod`"]
def noncomm_pi_coprod_equiv :
  {ϕ : Π i, N i →* M // pairwise (λ i j, ∀ x y, commute (ϕ i x) (ϕ j y)) }
    ≃ ((Π i, N i) →* M) :=
{ to_fun := λ ϕ, noncomm_pi_coprod ϕ.1 ϕ.2,
  inv_fun := λ f,
  ⟨ λ i, f.comp (monoid_hom.single N i),
    λ i j hij x y, commute.map (pi.mul_single_commute hij x y) f ⟩,
  left_inv := λ ϕ, by { ext, simp, },
  right_inv := λ f, pi_ext (λ i x, by simp) }

omit hdec

include hcomm

@[to_additive]
lemma noncomm_pi_coprod_mrange : (noncomm_pi_coprod ϕ hcomm).mrange = ⨆ i : ι, (ϕ i).mrange :=
begin
  classical,
  apply le_antisymm,
  { rintro x ⟨f, rfl⟩,
    refine submonoid.noncomm_prod_mem _ _ _ _ _,
    intros i hi,
    apply submonoid.mem_Sup_of_mem, { use i },
    simp, },
  { refine supr_le _,
    rintro i x ⟨y, rfl⟩,
    refine ⟨pi.mul_single i y, noncomm_pi_coprod_mul_single _ _ _⟩, },
end

end monoid_hom

end family_of_monoids

section family_of_groups

variables {G : Type*} [group G]
variables {ι : Type*} [hdec : decidable_eq ι] [hfin : fintype ι]
variables {H : ι → Type*} [∀ i, group (H i)]
variables (ϕ : Π (i : ι), H i →* G)
variables {hcomm : ∀ (i j : ι), i ≠ j → ∀ (x : H i) (y : H j), commute (ϕ i x) (ϕ j y)}
include hcomm

-- We use `f` and `g` to denote elements of `Π (i : ι), H i`
variables (f g : Π (i : ι), H i)

include hfin

namespace monoid_hom

-- The subgroup version of `noncomm_pi_coprod_mrange`
@[to_additive]
lemma noncomm_pi_coprod_range : (noncomm_pi_coprod ϕ hcomm).range = ⨆ i : ι, (ϕ i).range :=
begin
  classical,
  apply le_antisymm,
  { rintro x ⟨f, rfl⟩,
    refine subgroup.noncomm_prod_mem _ _ _,
    intros i hi,
    apply subgroup.mem_Sup_of_mem, { use i },
    simp, },
  { refine supr_le _,
    rintro i x ⟨y, rfl⟩,
    refine ⟨pi.mul_single i y, noncomm_pi_coprod_mul_single _ _ _⟩, },
end

@[to_additive]
lemma injective_noncomm_pi_coprod_of_independent
  (hind : complete_lattice.independent (λ i, (ϕ i).range))
  (hinj : ∀ i, function.injective (ϕ i)) :
  function.injective (noncomm_pi_coprod ϕ hcomm):=
begin
  classical,
  apply (monoid_hom.ker_eq_bot_iff _).mp,
  apply eq_bot_iff.mpr,
  intros f heq1,
  change finset.univ.noncomm_prod (λ i, ϕ i (f i)) _ = 1 at heq1,
  change f = 1,
  have : ∀ i, i ∈ finset.univ → ϕ i (f i) = 1 :=
    subgroup.eq_one_of_noncomm_prod_eq_one_of_independent _ _ _ _ hind (by simp) heq1,
  ext i,
  apply hinj,
  simp [this i (finset.mem_univ i)],
end

variable (hcomm)

omit hfin

@[to_additive]
lemma independent_range_of_coprime_order [finite ι] [Π i, fintype (H i)]
  (hcoprime : ∀ i j, i ≠ j → nat.coprime (fintype.card (H i)) (fintype.card (H j))) :
  complete_lattice.independent (λ i, (ϕ i).range) :=
begin
  casesI nonempty_fintype ι,
  classical,
  rintros i,
  rw disjoint_iff_inf_le,
  rintros f ⟨hxi, hxp⟩, dsimp at hxi hxp,
  rw [supr_subtype', ← noncomm_pi_coprod_range] at hxp,
  rotate, { intros _ _ hj, apply hcomm, exact hj ∘ subtype.ext },
  cases hxp with g hgf, cases hxi with g' hg'f,
  have hxi : order_of f ∣ fintype.card (H i),
  { rw ← hg'f, exact (order_of_map_dvd _ _).trans order_of_dvd_card_univ },
  have hxp : order_of f ∣ ∏ j : {j // j ≠ i}, fintype.card (H j),
  { rw [← hgf, ← fintype.card_pi], exact (order_of_map_dvd _ _).trans order_of_dvd_card_univ },
  change f = 1, rw [← pow_one f, ← order_of_dvd_iff_pow_eq_one],
  convert ← nat.dvd_gcd hxp hxi, rw ← nat.coprime_iff_gcd_eq_one,
  apply nat.coprime_prod_left, intros j _, apply hcoprime, exact j.2,
end

end monoid_hom

end family_of_groups

namespace subgroup

-- We have an family of subgroups
variables {G : Type*} [group G]
variables {ι : Type*} [hdec : decidable_eq ι] [hfin : fintype ι] {H : ι → subgroup G}

-- Elements of `Π (i : ι), H i` are called `f` and `g` here
variables (f g : Π (i : ι), H i)

section commuting_subgroups

-- We assume that the elements of different subgroups commute
variables (hcomm : ∀ (i j : ι), i ≠ j → ∀ (x y : G), x ∈ H i → y ∈ H j → commute x y)
include hcomm

@[to_additive]
lemma commute_subtype_of_commute (i j : ι) (hne : i ≠ j) :
  ∀ (x : H i) (y : H j), commute ((H i).subtype x) ((H j).subtype y) :=
by { rintros ⟨x, hx⟩ ⟨y, hy⟩, exact hcomm i j hne x y hx hy }

include hfin

/-- The canonical homomorphism from a family of subgroups where elements from different subgroups
commute -/
@[to_additive "The canonical homomorphism from a family of additive subgroups where elements from
different subgroups commute"]
def noncomm_pi_coprod : (Π (i : ι), H i) →* G :=
  monoid_hom.noncomm_pi_coprod (λ i, (H i).subtype) (commute_subtype_of_commute hcomm)

variable {hcomm}

include hdec

@[simp, to_additive]
lemma noncomm_pi_coprod_mul_single (i : ι) (y : H i) :
  noncomm_pi_coprod hcomm (pi.mul_single i y) = y :=
by apply monoid_hom.noncomm_pi_coprod_mul_single

omit hdec

@[to_additive]
lemma noncomm_pi_coprod_range : (noncomm_pi_coprod hcomm).range = ⨆ i : ι, H i :=
by simp [noncomm_pi_coprod, monoid_hom.noncomm_pi_coprod_range]

@[to_additive]
lemma injective_noncomm_pi_coprod_of_independent (hind : complete_lattice.independent H) :
  function.injective (noncomm_pi_coprod hcomm) :=
begin
  apply monoid_hom.injective_noncomm_pi_coprod_of_independent,
  { simpa using hind },
  { intro i, exact subtype.coe_injective }
end

variable (hcomm)

omit hfin

@[to_additive]
lemma independent_of_coprime_order [finite ι] [∀ i, fintype (H i)]
  (hcoprime : ∀ i j, i ≠ j → nat.coprime (fintype.card (H i)) (fintype.card (H j))) :
  complete_lattice.independent H :=
by simpa using monoid_hom.independent_range_of_coprime_order (λ i, (H i).subtype)
  (commute_subtype_of_commute hcomm) hcoprime

end commuting_subgroups

end subgroup
