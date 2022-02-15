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

Given a family of morphisms `ϕ i : N i →* M` for each `i : I` where elements in the
image of different morphism commute, we obtain a canoncial morphism
`monoid_hom.noncomm_pi_coprod : (Π (i : I), N i) →* M` that coincides with `ϕ`

## Main definitions

* `monoid_hom.noncomm_pi_coprod : (Π (i : I), N i) →* M` is the main homomorphism
* `noncomm_pi_coprod_on.hom (S : finset S) : (Π (i : I), N i) →* M` is the homomorphism
   restricted to the set `S`, and mostly of internal interest in this file, to allow inductive
   proofs (and thus in its own namespace).
* `subgroup.noncomm_pi_coprod : (Π (i : I), H i) →* G` is the specialization to `H i : subgroup G`
   and the subgroup embedding.

## Main theorems

* `monoid_hom.noncomm_pi_coprod` conicides with `ϕ i` when restricted to `N i`
* `monoid_hom.noncomm_pi_coprod_mrange`: The range of `monoid_hom.noncomm_pi_coprod` is
  `⨆ (i : I), (ϕ i).mrange`
* `monoid_hom.noncomm_pi_coprod_range`: The range of `monoid_hom.noncomm_pi_coprod` is
  `⨆ (i : I), (ϕ i).range`
* `subgroup.noncomm_pi_coprod_range`: The range of `subgroup.noncomm_pi_coprod` is `⨆ (i : I), H i`.
* `monoid_hom.injective_noncomm_pi_coprod_of_independent`: in the case of groups, `pi_hom.hom` is
   injective if the `ϕ` are injective and the ranges of the `ϕ` are independent.
* `monid_hom.independent_range_of_coprime_order`: If the `N i` have coprime orders, then the ranges
   of the `ϕ` are independent.
* `subgroup.independent_of_coprime_order`: If commuting, normal subgroups `H i` have coprime orders,
   they are independent.

-/

open_locale big_operators
open_locale classical

lemma coprime_prod_left
  {I : Type*}
  {x : ℕ} {s : I → ℕ} {t : finset I} :
  (∀ (i : I), i ∈ t → nat.coprime (s i) x) → nat.coprime (∏ (i : I) in t, s i) x :=
finset.prod_induction s (λ y, y.coprime x) (λ a b, nat.coprime.mul) (by simp)

-- I think it's worth keeping it and moving to appropriate file
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
variables {I : Type*} [hfin : fintype I]
variables {N : I → Type*} [∀ i, monoid (N i)]

-- And morphisms ϕ into G
variables (ϕ : Π (i : I), N i →* M)

-- We assume that the elements of different morphism commute
variables (hcomm : ∀ (i j : I), i ≠ j → ∀ (x : N i) (y : N j), commute (ϕ i x) (ϕ j y))
include hcomm

-- We use `f` and `g` to denote elements of `Π (i : I), N i`
variables (f g : Π (i : I), N i)

namespace noncomm_pi_coprod_on

-- In this section, we restrict the hom to a set S
variables (S : finset I)

/-- The underlying function of `pi_hom_restr.hom` -/
def to_fun (S : finset I) : M := finset.noncomm_prod S (λ i, ϕ i (f i)) $
  by { rintros i - j -, by_cases h : i = j, { subst h }, { exact hcomm _ _ h _ _ } }

variable {hcomm}

@[simp]
lemma to_fun_empty : to_fun ϕ hcomm f ∅ = 1 := finset.noncomm_prod_empty _ _

@[simp]
lemma to_fun_insert_of_not_mem (S : finset I) (i : I) (h : i ∉ S) :
  to_fun ϕ hcomm f (insert i S) = ϕ i (f i) * to_fun ϕ hcomm f S :=
finset.noncomm_prod_insert_of_not_mem _ _ _ _ h

@[simp]
lemma to_fun_one : to_fun ϕ hcomm 1 S = 1 :=
begin
  induction S using finset.cons_induction_on with i S hnmem ih,
  { simp }, { simp [ih, hnmem], }
end

lemma to_fun_commutes (i : I) (hnmem : i ∉ S) :
  commute (ϕ i (g i)) (to_fun ϕ hcomm f S) :=
begin
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

@[simp]
lemma to_fun_mul (S : finset I) :
  to_fun ϕ hcomm (f * g) S = to_fun ϕ hcomm f S * to_fun ϕ hcomm g S :=
begin
  induction S using finset.induction_on with i S hnmem ih,
  { simp, },
  { simp only [to_fun_insert_of_not_mem _ _ _ _ hnmem],
    rw ih, clear ih,
    simp only [pi.mul_apply, map_mul],
    repeat { rw mul_assoc }, congr' 1,
    repeat { rw ← mul_assoc }, congr' 1,
    exact (to_fun_commutes _ _ _ S i hnmem), }
end

lemma to_fun_in_sup_mrange (S : finset I) :
  to_fun ϕ hcomm f S ∈ ⨆ i ∈ S, (ϕ i).mrange :=
begin
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
def hom : (Π (i : I), N i) →* M :=
{ to_fun := λ f, to_fun ϕ hcomm f S,
  map_one' := to_fun_one ϕ _,
  map_mul' := λ f g, to_fun_mul ϕ f g S, }

variable {hcomm}

lemma to_fun_single (i : I) (y : N i) (S : finset I) :
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

@[simp]
lemma hom_single (i : I) (y : N i):
  hom ϕ hcomm S (monoid_hom.single _ i y) = if i ∈ S then ϕ i y else 1 := to_fun_single _ _ _ _

lemma mrange : (hom ϕ hcomm S).mrange = ⨆ i ∈ S, (ϕ i).mrange :=
begin
  apply le_antisymm,
  { rintro x ⟨f, rfl⟩,
    exact (to_fun_in_sup_mrange ϕ f S), },
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
def noncomm_pi_coprod : (Π (i : I), N i) →* M := noncomm_pi_coprod_on.hom ϕ hcomm finset.univ

variable {hcomm}

@[simp]
lemma noncomm_pi_coprod_single (i : I) (y : N i):
  noncomm_pi_coprod ϕ hcomm (monoid_hom.single _ i y) = ϕ i y :=
by { show noncomm_pi_coprod_on.hom ϕ hcomm finset.univ (monoid_hom.single _ i y) = ϕ i y, simp }

lemma noncomm_pi_coprod_mrange : (noncomm_pi_coprod ϕ hcomm).mrange = ⨆ i : I, (ϕ i).mrange :=
begin
  show (noncomm_pi_coprod_on.hom ϕ hcomm finset.univ).mrange = _,
  simp [noncomm_pi_coprod_on.mrange],
end

end monoid_hom

end family_of_monoids

section family_of_groups

variables {G : Type*} [group G]
variables {I : Type*} [hfin : fintype I]
variables {H : I → Type*} [∀ i, group (H i)]
variables (ϕ : Π (i : I), H i →* G)
variables {hcomm : ∀ (i j : I), i ≠ j → ∀ (x : H i) (y : H j), commute (ϕ i x) (ϕ j y)}
include hcomm

-- We use `f` and `g` to denote elements of `Π (i : I), H i`
variables (f g : Π (i : I), H i)

-- The subgroup version of `noncomm_pi_coprod_on.to_fun_in_sup_mrange`
lemma noncomm_pi_coprod_on.to_fun_in_sup_range (S : finset I) :
  noncomm_pi_coprod_on.to_fun ϕ hcomm f S ∈ ⨆ i ∈ S, (ϕ i).range :=
begin
  induction S using finset.induction_on with i S hnmem ih,
  { simp, },
  { simp only [noncomm_pi_coprod_on.to_fun_insert_of_not_mem _ _ _ _ hnmem],
    refine (subgroup.mul_mem _ _ _),
    { apply subgroup.mem_Sup_of_mem, { use i }, { simp, }, },
    { refine @bsupr_le_bsupr' _ _ _ _ _ _ (λ i, (ϕ i).range) _ ih,
      exact λ i, finset.mem_insert_of_mem } }
end

-- The subgroup version of `noncomm_pi_coprod_on.mrange`
lemma noncomm_pi_coprod_on.range (S : finset I) :
  (noncomm_pi_coprod_on.hom ϕ hcomm S).range = ⨆ i ∈ S, (ϕ i).range :=
begin
  apply le_antisymm,
  { rintro x ⟨f, rfl⟩,
    exact (noncomm_pi_coprod_on.to_fun_in_sup_range ϕ f S), },
  { refine (bsupr_le _),
    rintro i hmem x ⟨y, rfl⟩,
    use (monoid_hom.single _ i y),
    simp [hmem], }
end

include hfin

namespace monoid_hom

-- The subgroup version of `noncomm_pi_coprod_on_mrange`
lemma noncomm_pi_coprod_range : (noncomm_pi_coprod ϕ hcomm).range = ⨆ i : I, (ϕ i).range :=
begin
  show (noncomm_pi_coprod_on.hom ϕ hcomm finset.univ).range = _,
  simp [noncomm_pi_coprod_on.range]
end

lemma injective_noncomm_pi_coprod_of_independent
  (hind : complete_lattice.independent (λ i, (ϕ i).range))
  (hinj : ∀ i, function.injective (ϕ i)) :
  function.injective (noncomm_pi_coprod ϕ hcomm):=
begin
  apply (monoid_hom.ker_eq_bot_iff _).mp,
  apply eq_bot_iff.mpr,
  intro f,
  show noncomm_pi_coprod_on.to_fun ϕ hcomm f finset.univ = 1 → f = 1,
  suffices : noncomm_pi_coprod_on.to_fun ϕ hcomm f finset.univ = 1 →
    (∀ (i : I), i ∈ finset.univ → f i = 1),
  by exact (λ h, funext (λ (i : I), this h i (finset.mem_univ i))),
  induction (finset.univ : finset I) using finset.induction_on with i S hnmem ih,
  { simp },
  { intro heq1,
    simp only [ noncomm_pi_coprod_on.to_fun_insert_of_not_mem _ _ _ _ hnmem] at heq1,
    have hnmem' : i ∉ (S : set I), by simpa,
    have heq1' : ϕ i (f i) = 1 ∧ noncomm_pi_coprod_on.to_fun ϕ hcomm f S = 1,
    { apply mul_eq_one_iff_disjoint.mp (hind.disjoint_bsupr hnmem') _ _ heq1,
      { simp, },
      { apply noncomm_pi_coprod_on.to_fun_in_sup_range, }, },
    rcases heq1' with ⟨ heq1i, heq1S ⟩,
    specialize ih heq1S,
    intros i h,
    simp only [finset.mem_insert] at h,
    rcases h with ⟨rfl | _⟩,
    { apply hinj i, simpa, },
    { exact (ih _ h), } }
end

variable (hcomm)
lemma independent_range_of_coprime_order [∀ i, fintype (H i)]
  (hcoprime : ∀ i j, i ≠ j → nat.coprime (fintype.card (H i)) (fintype.card (H j))) :
  complete_lattice.independent (λ i, (ϕ i).range) :=
begin
  rintros i f ⟨hxi, hxp⟩, dsimp at hxi hxp,
  rw [supr_subtype', ← @noncomm_pi_coprod_range _ _ _ _ _ _ _ _] at hxp,
  rotate, apply_instance,
  { intros _ _ hj, apply hcomm, exact hj ∘ subtype.ext },
  cases hxp with g hgf, cases hxi with g' hg'f,
  have hxi : order_of f ∣ fintype.card (H i),
  { rw ← hg'f, exact (map_order _ _).trans order_of_dvd_card_univ },
  have hxp : order_of f ∣ ∏ j : {j // j ≠ i}, fintype.card (H j),
  { rw [← hgf, ← fintype.card_pi], exact (map_order _ _).trans order_of_dvd_card_univ },
  change f = 1, rw [← pow_one f, ← order_of_dvd_iff_pow_eq_one],
  convert ← nat.dvd_gcd hxp hxi, rw ← nat.coprime_iff_gcd_eq_one,
  apply coprime_prod_left, intros j _, apply hcoprime, exact j.2,
end

end monoid_hom

end family_of_groups

namespace subgroup

-- We have an family of subgroups
variables {G : Type*} [group G]
variables {I : Type*} [hfin : fintype I] [hdec : decidable_eq I] {H : I → subgroup G}

-- Elements of `Π (i : I), H i` are called `f` and `g` here
variables (f g : Π (i : I), H i)

section commuting_subgroups

-- We assume that the elements of different subgroups commute
variables (hcomm : ∀ (i j : I), i ≠ j → ∀ (x y : G), x ∈ H i → y ∈ H j → commute x y)
include hcomm

lemma hcomm_subtype (i j : I) (hne : i ≠ j) :
  ∀ (x : H i) (y : H j), commute ((H i).subtype x) ((H j).subtype y) :=
by { rintros ⟨x, hx⟩ ⟨y, hy⟩, exact hcomm i j hne x y hx hy }

include hfin

/-- The canonical homomorphism from a pi group of subgroups -/
def noncomm_pi_coprod : (Π (i : I), H i) →* G :=
  monoid_hom.noncomm_pi_coprod (λ i, (H i).subtype) (hcomm_subtype hcomm)

variable {hcomm}

@[simp]
lemma noncomm_pi_coprod_single (i : I) (y : H i) :
  noncomm_pi_coprod hcomm (monoid_hom.single _ i y) = y :=
by apply monoid_hom.noncomm_pi_coprod_single

lemma range : (noncomm_pi_coprod hcomm).range = ⨆ i : I, H i :=
by simp [noncomm_pi_coprod, monoid_hom.noncomm_pi_coprod_range]

lemma injective_of_independent (hind : complete_lattice.independent H) :
  function.injective (noncomm_pi_coprod hcomm) :=
begin
  apply monoid_hom.injective_noncomm_pi_coprod_of_independent,
  { simpa using hind },
  { intro i, exact subtype.coe_injective }
end

lemma _root_.independent_of_coprime_order [∀ i, fintype (H i)]
  (hcoprime : ∀ i j, i ≠ j → nat.coprime (fintype.card (H i)) (fintype.card (H j))) :
  complete_lattice.independent H :=
begin
  simpa using monoid_hom.independent_range_of_coprime_order
    (λ i, (H i).subtype) (hcomm_subtype hcomm) hcoprime,
end

end commuting_subgroups

end subgroup
