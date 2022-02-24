/-
Copyright (c) 2022 Jocchim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import group_theory.order_of_element
import data.finset.noncomm_prod
import data.fintype.card

/-!
# Canonical homomorphism from a finite family of monoids

This file defines the construction of the canoncial homomorphism from a family of monoids.

Given a family of morphisms `ϕ i : N i →* M` for each `i : ι` where elements in the
image of different morphism commute, we obtain a canoncial morphism
`monoid_hom.noncomm_pi_coprod : (Π i, N i) →* M` that coincides with `ϕ`

## Main definitions

* `monoid_hom.noncomm_pi_coprod : (Π i, N i) →* M` is the main homomorphism
* `noncomm_pi_coprod_on.hom (S : finset S) : (Π (i : ι), N i) →* M` is the homomorphism
   restricted to the set `S`, and mostly of internal interest in this file, to allow inductive
   proofs (and thus in its own namespace).
* `subgroup.noncomm_pi_coprod : (Π i, H i) →* G` is the specialization to `H i : subgroup G`
   and the subgroup embedding.

## Main theorems

* `monoid_hom.noncomm_pi_coprod` conicides with `ϕ i` when restricted to `N i`
* `monoid_hom.noncomm_pi_coprod_mrange`: The range of `monoid_hom.noncomm_pi_coprod` is
  `⨆ (i : ι), (ϕ i).mrange`
* `monoid_hom.noncomm_pi_coprod_range`: The range of `monoid_hom.noncomm_pi_coprod` is
  `⨆ (i : ι), (ϕ i).range`
* `subgroup.noncomm_pi_coprod_range`: The range of `subgroup.noncomm_pi_coprod` is `⨆ (i : ι), H i`.
* `monoid_hom.injective_noncomm_pi_coprod_of_independent`: in the case of groups, `pi_hom.hom` is
   injective if the `ϕ` are injective and the ranges of the `ϕ` are independent.
* `monoid_hom.independent_range_of_coprime_order`: If the `N i` have coprime orders, then the ranges
   of the `ϕ` are independent.
* `subgroup.independent_of_coprime_order`: If commuting, normal subgroups `H i` have coprime orders,
   they are independent.

-/

open_locale big_operators

-- I think it's worth keeping it and moving to appropriate file
@[to_additive]
lemma mul_eq_one_iff_disjoint {G : Type*} [group G] {H₁ H₂ : subgroup G} :
  disjoint H₁ H₂ ↔ ∀ {x y : G}, x ∈ H₁ → y ∈ H₂ → x * y = 1 → x = 1 ∧ y = 1 :=
begin
  split,
  { intros hdis x y hx hy heq,
    obtain rfl : y = x⁻¹ := symm (inv_eq_iff_mul_eq_one.mpr heq),
    have hy := H₂.inv_mem_iff.mp hy,
    have : x ∈ H₁ ⊓ H₂, by { simp, cc },
    rw [hdis.eq_bot, subgroup.mem_bot] at this,
    subst this,
    simp },
  { rintros h x ⟨hx1, hx2⟩,
    obtain rfl : x = 1 := (h hx1 (H₂.inv_mem hx2) (mul_inv_self x)).1,
    exact rfl, },
end

section family_of_monoids

variables {M : Type*} [monoid M]

-- We have a family of monoids
-- The fintype assumption is not always used, but declared here, to keep things in order
variables {ι : Type*} [hdec : decidable_eq ι] [hfin : fintype ι]
variables {N : ι → Type*} [∀ i, monoid (N i)]

@[to_additive]
lemma _root_.finset.noncomm_prod_map {α : Type*} {β : Type*} [monoid β] (s : finset α) (f : α → β)
  (comm : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → commute (f x) (f y))
  {M : Type*} [monoid M] (g : β →* M) :
  g (s.noncomm_prod f comm) = s.noncomm_prod (λ i, g (f i))
  (λ x hx y hy, commute.map (comm x hx y hy) g)  :=
sorry

@[to_additive]
lemma _root_.finset.noncomm_prod_eq_one {α : Type*} {β : Type*} [monoid β] (s : finset α)
  (f : α → β) (comm : ∀ (x : α), x ∈ s → ∀ (y : α), y ∈ s → commute (f x) (f y))
  (h : ∀ (x : α), x ∈ s → f x = 1) : s.noncomm_prod f comm = 1 :=
sorry

@[to_additive]
lemma _root_.finset.noncomm_prod_single [decidable_eq ι] [fintype ι] (x : Π i, N i) :
  finset.univ.noncomm_prod (λ i, monoid_hom.single N i (x i))
  (λ i _ j _, by { by_cases h : i = j, { subst h, }, { exact pi.mul_single_commute i j h _ _ } })
  = x :=
begin
  ext i,
  apply (finset.univ.noncomm_prod_map (λ i, monoid_hom.single N i (x i)) _
    (pi.eval_monoid_hom _ i)).trans,
  rw (finset.insert_erase (finset.mem_univ i)).symm,
  rw finset.noncomm_prod_insert_of_not_mem',
  rw finset.noncomm_prod_eq_one,
  { simp, },
  { intros i h,  simp at h, simp [h], },
  { simp, },
end

@[to_additive]
lemma _root_.monoid_hom.pi_ext [decidable_eq ι] [fintype ι] {f g : (Π i, N i) →* M}
  (h : ∀ i x, f (monoid_hom.single N i x) = g (monoid_hom.single N i x)) :
  f = g :=
begin
  ext x,
  rw ← finset.noncomm_prod_single x,
  rw finset.univ.noncomm_prod_map _ _ f,
  rw finset.univ.noncomm_prod_map _ _ g,
  congr' 1, ext i, exact h i (x i),
end


-- And morphisms ϕ into G
variables (ϕ : Π (i : ι), N i →* M)

-- We assume that the elements of different morphism commute
variables (hcomm : ∀ (i j : ι), i ≠ j → ∀ (x : N i) (y : N j), commute (ϕ i x) (ϕ j y))
include hcomm

-- We use `f` and `g` to denote elements of `Π (i : ι), N i`
variables (f g : Π (i : ι), N i)

namespace noncomm_pi_coprod_on

-- In this section, we restrict the hom to a set S
variables (S : finset ι)

/-- The underlying function of `noncomm_pi_coprod_on.hom` -/
@[to_additive add_to_fun "The underlying function of `noncomm_pi_coprod_on.add_hom` "]
def to_fun (S : finset ι) : M := finset.noncomm_prod S (λ i, ϕ i (f i)) $
  by { rintros i - j -, by_cases h : i = j, { subst h }, { exact hcomm _ _ h _ _ } }

variable {hcomm}

@[simp, to_additive add_to_fun_empty]
lemma to_fun_empty : to_fun ϕ hcomm f ∅ = 1 := finset.noncomm_prod_empty _ _

include hdec

@[simp, to_additive add_to_fun_insert_of_not_mem]
lemma to_fun_insert_of_not_mem (S : finset ι) (i : ι) (h : i ∉ S) :
  to_fun ϕ hcomm f (insert i S) = ϕ i (f i) * to_fun ϕ hcomm f S :=
finset.noncomm_prod_insert_of_not_mem _ _ _ _ h

omit hdec

@[simp, to_additive add_to_fun_zero]
lemma to_fun_one : to_fun ϕ hcomm 1 S = 1 :=
begin
  classical,
  induction S using finset.cons_induction_on with i S hnmem ih,
  { simp }, { simp [ih, hnmem], }
end

@[to_additive add_to_fun_commutes]
lemma to_fun_commutes (i : ι) (hnmem : i ∉ S) :
  commute (ϕ i (g i)) (to_fun ϕ hcomm f S) :=
begin
  classical,
  induction S using finset.induction_on with j S hnmem' ih,
  { simp, },
  { simp only [to_fun_insert_of_not_mem _ _ _ _ hnmem'],
    have hij : i ≠ j, by {rintro rfl, apply hnmem, exact finset.mem_insert_self i S},
    have hiS : i ∉ S, by {rintro h, apply hnmem, exact finset.mem_insert_of_mem h},
    calc ϕ i (g i) * (ϕ j (f j) * (to_fun ϕ hcomm f S : M))
        = (ϕ i (g i) * ϕ j (f j)) * to_fun ϕ hcomm f S : by rw ← mul_assoc
    ... = (ϕ j (f j) * ϕ i (g i)) * to_fun ϕ hcomm f S : by { congr' 1, apply hcomm _ _ hij }
    ... = ϕ j (f j) * (ϕ i (g i) * to_fun ϕ hcomm f S) : by rw mul_assoc
    ... = ϕ j (f j) * (to_fun ϕ hcomm f S * ϕ i (g i)) : by { congr' 1, apply ih hiS }
    ... = (ϕ j (f j) * to_fun ϕ hcomm f S) * ϕ i (g i) : by rw ← mul_assoc }
end

@[simp, to_additive add_to_fun_add]
lemma to_fun_mul (S : finset ι) :
  to_fun ϕ hcomm (f * g) S = to_fun ϕ hcomm f S * to_fun ϕ hcomm g S :=
begin
  classical,
  induction S using finset.induction_on with i S hnmem ih,
  { simp, },
  { simp only [to_fun_insert_of_not_mem _ _ _ _ hnmem],
    rw ih, clear ih,
    simp only [pi.mul_apply, map_mul],
    repeat { rw mul_assoc }, congr' 1,
    repeat { rw ← mul_assoc }, congr' 1,
    exact (to_fun_commutes _ _ _ S i hnmem), }
end

@[to_additive add_to_fun_mem_bsupr_mrange]
lemma to_fun_mem_bsupr_mrange (S : finset ι) :
  to_fun ϕ hcomm f S ∈ ⨆ i ∈ S, (ϕ i).mrange :=
begin
  classical,
  induction S using finset.induction_on with i S hnmem ih,
  { simp, },
  { simp only [to_fun_insert_of_not_mem _ _ _ _ hnmem],
    refine (submonoid.mul_mem _ _ _),
    { apply submonoid.mem_Sup_of_mem, { use i }, { simp, }, },
    { refine @bsupr_le_bsupr' _ _ _ _ _ _ (λ i, (ϕ i).mrange) _ ih,
      exact λ i, finset.mem_insert_of_mem } }
end

variable (hcomm)

/-- The canonical homomorphism from a family of monoids, restricted to a subset of the index space.
-/
@[to_additive add_hom "The canonical homomorphism from a family of additive monoids, restricted to a
subset of the index space"]
def hom : (Π (i : ι), N i) →* M :=
{ to_fun := λ f, to_fun ϕ hcomm f S,
  map_one' := to_fun_one ϕ _,
  map_mul' := λ f g, to_fun_mul ϕ f g S, }

variable {hcomm}

include hdec

@[to_additive add_to_fun_single]
lemma to_fun_single (i : ι) (y : N i) (S : finset ι) :
  to_fun ϕ hcomm (monoid_hom.single _ i y) S = if i ∈ S then ϕ i y else 1 :=
begin
  induction S using finset.induction_on with j S hnmem ih,
  { simp, },
  { simp only [ to_fun_insert_of_not_mem _ _ _ _ hnmem],
    by_cases (i = j),
    { subst h, rw ih, simp [hnmem], },
    { change i ≠ j at h,
      simpa [h] using ih, } }
end

@[simp, to_additive add_hom_single]
lemma hom_single (i : ι) (y : N i):
  hom ϕ hcomm S (monoid_hom.single _ i y) = if i ∈ S then ϕ i y else 1 := to_fun_single _ _ _ _

omit hdec

@[to_additive add_mrange]
lemma mrange : (hom ϕ hcomm S).mrange = ⨆ i ∈ S, (ϕ i).mrange :=
begin
  classical,
  apply le_antisymm,
  { rintro x ⟨f, rfl⟩,
    exact (to_fun_mem_bsupr_mrange ϕ f S), },
  { refine (bsupr_le _),
    rintro i hmem x ⟨y, rfl⟩,
    use (monoid_hom.single _ i y),
    simp [hmem], }
end

end noncomm_pi_coprod_on

namespace monoid_hom

include hfin

variable (hcomm)

/-- The canonical homomorphism from a family of monoids. -/
@[to_additive "The canonical homomorphism from a family of additive monoids.

See also `linear_map.lsum` for a linear version without the commutativity assumption."]
def noncomm_pi_coprod : (Π (i : ι), N i) →* M := noncomm_pi_coprod_on.hom ϕ hcomm finset.univ

variable {hcomm}

include hdec

@[simp, to_additive]
lemma noncomm_pi_coprod_single (i : ι) (y : N i):
  noncomm_pi_coprod ϕ hcomm (monoid_hom.single _ i y) = ϕ i y :=
by { show noncomm_pi_coprod_on.hom ϕ hcomm finset.univ (monoid_hom.single _ i y) = ϕ i y, simp }

/-- The universal property of `noncomm_pi_coprod` -/
@[to_additive "The universal property of `noncomm_pi_coprod`"]
def noncomm_pi_coprod_equiv :
  {ϕ : Π i, N i →* M // pairwise (λ i j, ∀ x y, commute (ϕ i x) (ϕ j y)) }
    ≃ ((Π i, N i) →* M) :=
{ to_fun := λ ϕ, noncomm_pi_coprod ϕ.1 ϕ.2,
  inv_fun := λ f,
  ⟨ λ i, f.comp (monoid_hom.single N i),
    λ i j hij x y, commute.map (monoid_hom.single_commute i j hij x y) f ⟩,
  left_inv := λ ϕ, by {ext ι x, simp },
  right_inv := λ f, monoid_hom.pi_ext.mpr (λ i x, by simp), }

omit hdec

@[to_additive]
lemma noncomm_pi_coprod_mrange : (noncomm_pi_coprod ϕ hcomm).mrange = ⨆ i : ι, (ϕ i).mrange :=
begin
  show (noncomm_pi_coprod_on.hom ϕ hcomm finset.univ).mrange = _,
  simp [noncomm_pi_coprod_on.mrange],
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

-- The subgroup version of `noncomm_pi_coprod_on.to_fun_mem_bsupr_mrange`
@[to_additive noncomm_pi_coprod_on.add_to_fun_mem_bsupr_range]
lemma noncomm_pi_coprod_on.to_fun_mem_bsupr_range (S : finset ι) :
  noncomm_pi_coprod_on.to_fun ϕ hcomm f S ∈ ⨆ i ∈ S, (ϕ i).range :=
begin
  classical,
  induction S using finset.induction_on with i S hnmem ih,
  { simp, },
  { simp only [noncomm_pi_coprod_on.to_fun_insert_of_not_mem _ _ _ _ hnmem],
    refine (subgroup.mul_mem _ _ _),
    { apply subgroup.mem_Sup_of_mem, { use i }, { simp, }, },
    { refine @bsupr_le_bsupr' _ _ _ _ _ _ (λ i, (ϕ i).range) _ ih,
      exact λ i, finset.mem_insert_of_mem } }
end

-- The subgroup version of `noncomm_pi_coprod_on.mrange`
@[to_additive noncomm_pi_coprod_on.add_range]
lemma noncomm_pi_coprod_on.range (S : finset ι) :
  (noncomm_pi_coprod_on.hom ϕ hcomm S).range = ⨆ i ∈ S, (ϕ i).range :=
begin
  classical,
  apply le_antisymm,
  { rintro x ⟨f, rfl⟩,
    exact (noncomm_pi_coprod_on.to_fun_mem_bsupr_range ϕ f S), },
  { refine (bsupr_le _),
    rintro i hmem x ⟨y, rfl⟩,
    use (monoid_hom.single _ i y),
    simp [hmem], }
end

include hfin

namespace monoid_hom

-- The subgroup version of `noncomm_pi_coprod_mrange`
@[to_additive]
lemma noncomm_pi_coprod_range : (noncomm_pi_coprod ϕ hcomm).range = ⨆ i : ι, (ϕ i).range :=
begin
  show (noncomm_pi_coprod_on.hom ϕ hcomm finset.univ).range = _,
  simp [noncomm_pi_coprod_on.range]
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
  intro f,
  show noncomm_pi_coprod_on.to_fun ϕ hcomm f finset.univ = 1 → f = 1,
  suffices : noncomm_pi_coprod_on.to_fun ϕ hcomm f finset.univ = 1 →
    (∀ (i : ι), i ∈ finset.univ → f i = 1),
  by exact (λ h, funext (λ (i : ι), this h i (finset.mem_univ i))),
  induction (finset.univ : finset ι) using finset.induction_on with i S hnmem ih,
  { simp },
  { intro heq1,
    simp only [ noncomm_pi_coprod_on.to_fun_insert_of_not_mem _ _ _ _ hnmem] at heq1,
    have hnmem' : i ∉ (S : set ι), by simpa,
    have heq1' : ϕ i (f i) = 1 ∧ noncomm_pi_coprod_on.to_fun ϕ hcomm f S = 1,
    { apply mul_eq_one_iff_disjoint.mp (hind.disjoint_bsupr hnmem') _ _ heq1,
      { simp, },
      { apply noncomm_pi_coprod_on.to_fun_mem_bsupr_range, }, },
    rcases heq1' with ⟨ heq1i, heq1S ⟩,
    specialize ih heq1S,
    intros i h,
    simp only [finset.mem_insert] at h,
    rcases h with ⟨rfl | _⟩,
    { apply hinj i, simpa, },
    { exact (ih _ h), } }
end

variable (hcomm)


@[to_additive]
lemma independent_range_of_coprime_order [∀ i, fintype (H i)]
  (hcoprime : ∀ i j, i ≠ j → nat.coprime (fintype.card (H i)) (fintype.card (H j))) :
  complete_lattice.independent (λ i, (ϕ i).range) :=
begin
  classical,
  rintros i f ⟨hxi, hxp⟩, dsimp at hxi hxp,
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
lemma noncomm_pi_coprod_single (i : ι) (y : H i) :
  noncomm_pi_coprod hcomm (monoid_hom.single _ i y) = y :=
by apply monoid_hom.noncomm_pi_coprod_single

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

@[to_additive]
lemma independent_of_coprime_order [∀ i, fintype (H i)]
  (hcoprime : ∀ i j, i ≠ j → nat.coprime (fintype.card (H i)) (fintype.card (H j))) :
  complete_lattice.independent H :=
begin
  simpa using monoid_hom.independent_range_of_coprime_order
    (λ i, (H i).subtype) (commute_subtype_of_commute hcomm) hcoprime,
end

end commuting_subgroups

end subgroup
