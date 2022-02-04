/-
Copyright (c) 2022 Jocchim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import group_theory.general_commutator
import group_theory.order_of_element
import data.finset.noncomm_prod
import ring_theory.coprime.lemmas

/-!
# Canonical homomorphism from a pi group

This file defines the construction of the canoncial homomorphism from a product group.

Given a family of morphisms `ϕ i : H i →* G` for each `i : I` where elements in the
image of different morphism commute, we obtain a canoncial morphism
`pi_hom.hom : (Π (i : I), H i) →* G` that coincides with `ϕ``

## Main definitions

* `pi_hom.hom : (Π (i : I), H i) →* G` is the main homomorphism
* `pi_hom_restr.hom (S : finset S) : (Π (i : I), H i) →* G` is the homomorphism restricted to the
   set `S`, and mostly of internal interest in this file, to allow inductive proofs.
* `subgroup_pi_hom.hom : (Π (i : I), H i) →* G` is the specialization to `H i : subgroup G` and
   the subgroup embedding.

## Main theorems

* `pi_hom.hom` conicides with each `ϕ`
* `pi_hom.range`: The range of `pi_hom.hom` is `⨆ (i : I), (ϕ i).range`
* The range of `subgroup_pi_hom.hom` is `⨆ (i : I), H i`
* `pi_hom.pow`: `pi_hom.hom` commutes with potentation.
* `pi_hom.injective_of_independent`: `pi_hom.hom` is injective if the `ϕ` are injective and the
   ranges of the `ϕ` are independent.
* `independent_range_of_coprime_order`: If the `ϕ` are injective and the `H i` have coprime orders,
   then the ranges are independent.
* `independent_of_coprime_order`: If commuting, normal `H i` have coprime orders, they are
   independent.

-/

open_locale big_operators
open_locale classical

-- A lot of faff just to transport `is_coprime.prod_left` from ℤ to ℕ
lemma coprime_prod_left
  {I : Type*}
  {x : ℕ} {s : I → ℕ} {t : finset I} :
  (∀ (i : I), i ∈ t → nat.coprime (s i) x) → nat.coprime (∏ (i : I) in t, s i) x :=
begin
  intro h,
  rw ← nat.is_coprime_iff_coprime,
  have := @nat.cast_prod _ ℤ _ s t,
  simp [ -nat.cast_prod ] at this,
  rw this,
  apply is_coprime.prod_left,
  intros i hi,
  rw nat.is_coprime_iff_coprime,
  apply h i hi,
end

section with_group

parameters {G : Type*} [group G]

-- TODO: Move to suitable file
@[simp]
lemma order_of_inv (x : G) : order_of x⁻¹ = order_of x :=
begin
  apply nat.dvd_antisymm; rewrite order_of_dvd_iff_pow_eq_one,
  { rw [inv_pow, pow_order_of_eq_one, one_inv], },
  { nth_rewrite 0 ← (inv_inv x), rw [inv_pow, pow_order_of_eq_one, one_inv], }
end

-- TODO: Move to suitable file? Or too specialized?
lemma mul_eq_one_of_disjoint
  {H₁ H₂ : subgroup G} (hdis : disjoint H₁ H₂) {x y : G} (hx : x ∈ H₁) (hy : y ∈ H₂)
  (heq : x * y = 1) : x = 1 ∧ y = 1 :=
begin
  have : y = x⁻¹ := symm (inv_eq_iff_mul_eq_one.mpr heq),
  subst this,
  have hy := H₂.inv_mem_iff.mp hy,
  have : x ∈ H₁ ⊓ H₂, by { simp, cc },
  rw [hdis.eq_bot, subgroup.mem_bot] at this,
  subst this,
  simp
end

section family_of_groups

-- We have an family of groups
parameters {I : Type*} [hfin : fintype I]
parameters {H : I → Type*} [∀ i, group (H i)]

-- And morphism ϕ into G
parameters (ϕ : Π (i : I), H i →* G)

-- We assume that the elements of different morphism commute
-- Since we need this all over the place we wrap it up in `fact`
-- TODO: Worth making this a real `class` over `ϕ`?
parameters [hcomm : fact (∀ (i j : I), i ≠ j → ∀ (x : H i) (y : H j), commute (ϕ i x) (ϕ j y))]
include hcomm

-- Elements of `Π (i : I), H i` are called `f` and `g` here
variables (f g : Π (i : I), H i)

namespace pi_hom_restr

-- In this section, we restrict the hom to a set S
variables (S : finset I)

/-- The underlying function of `pi_hom_restr.hom` -/
def to_fun (S : finset I) : G := finset.noncomm_prod S (λ i, ϕ i (f i)) $
  by { rintros i - j -, by_cases (i = j), { subst h }, { exact hcomm.elim _ _ h _ _} }

@[simp]
lemma to_fun_empty : to_fun f ∅ = 1 := by simp [to_fun]

@[simp]
lemma to_fun_insert_of_not_mem (S : finset I) (i : I) (h : i ∉ S) :
  to_fun f (insert i S) = ϕ i (f i) * to_fun f S :=
finset.noncomm_prod_insert_of_not_mem _ _ _ _ h

@[simp]
lemma to_fun_one : to_fun 1 S = 1 :=
begin
   induction S using finset.cons_induction_on with i S hnmem ih,
   { simp }, { simp [ih, hnmem], }
end

lemma to_fun_commutes (i : I) (hnmem : i ∉ S) :
  commute (ϕ i (g i)) (to_fun f S) :=
begin
  induction S using finset.induction_on with j S hnmem' ih,
  { simp, },
  { simp only [to_fun_insert_of_not_mem _ _ _ _ hnmem'],

    have hij : i ≠ j, by {simp at hnmem, tauto},
    have hiS : i ∉ S, by {simp at hnmem, tauto},
    calc ϕ i (g i) * (ϕ j (f j) * (to_fun ϕ f S : G)) -- TODO: Why do I have to mention `ϕ`?
        = (ϕ i (g i) * ϕ j (f j)) * to_fun ϕ f S : by rw ← mul_assoc
    ... = (ϕ j (f j) * ϕ i (g i)) * to_fun ϕ f S : by {congr' 1, apply (fact.elim hcomm _ _ hij)}
    ... = ϕ j (f j) * (ϕ i (g i) * to_fun ϕ f S) : by rw mul_assoc
    ... = ϕ j (f j) * (to_fun ϕ f S * ϕ i (g i)) : by { congr' 1, apply (ih hiS) }
    ... = (ϕ j (f j) * to_fun ϕ f S) * ϕ i (g i) : by rw ← mul_assoc }
end

@[simp]
lemma to_fun_mul (S : finset I) : to_fun (f * g) S = to_fun f S * to_fun g S :=
begin
  induction S using finset.induction_on with i S hnmem ih,
  { simp, },
  { simp only [ to_fun_insert_of_not_mem _ _ _ _ hnmem],
    rw ih, clear ih,
    simp only [pi.mul_apply, map_mul],
    repeat { rw mul_assoc }, congr' 1,
    repeat { rw ← mul_assoc }, congr' 1,
    exact (to_fun_commutes _ _ _ S i hnmem), }
end

lemma to_fun_in_sup_range (S : finset I) :
  to_fun f S ∈ ⨆ i ∈ S, (ϕ i).range :=
begin
  induction S using finset.induction_on with i S hnmem ih,
  { simp, },
  { simp only [ to_fun_insert_of_not_mem _ _ _ _ hnmem],
    refine (subgroup.mul_mem _ _ _),
    { apply (subgroup.mem_Sup_of_mem), { use i }, { simp, }, },
    { refine (@bsupr_le_bsupr' _ _ _ _ _ _ (λ i, (ϕ i).range) _ ih),
      by { intro, simp, intro h, right, exact h}, } }
end

/-- The canonical homomorphism from a pi group, restricted to a subset  -/
def hom : (Π (i : I), H i) →* G :=
{ to_fun := λ f, to_fun f S,
  map_one' := to_fun_one _,
  map_mul' := λ f g, to_fun_mul f g S, }

lemma to_fun_update_one (i : I) (y : H i) (S : finset I) :
  to_fun (function.update 1 i y) S = if i ∈ S then ϕ i y else 1 :=
begin
  induction S using finset.induction_on with j S hnmem ih,
  { simp, },
  { simp only [ to_fun_insert_of_not_mem _ _ _ _ hnmem],
    by_cases (i = j),
    { subst h, rw ih, simp [hnmem], },
    { change i ≠ j at h,
      simp [h, hnmem, function.update_noteq (ne_comm.mp h)],
      exact ih, } }
end

@[simp]
lemma hom_update_one (i : I) (y : H i):
  hom S (function.update 1 i y) = if i ∈ S then ϕ i y else 1 := to_fun_update_one _ _ _

lemma range : (hom S).range = ⨆ i ∈ S, (ϕ i).range :=
begin
  apply le_antisymm,
  { rintro x ⟨f, rfl⟩,
    exact (to_fun_in_sup_range ϕ f S), },
  { refine (bsupr_le _),
    rintro i hmem x ⟨y, rfl⟩,
    use (function.update 1 i y),
    simp [hmem], }
end

lemma pow (k : ℕ) : (hom S f) ^ k = hom S (f ^ k) :=
begin
  change (to_fun ϕ f S) ^ k = to_fun ϕ (f ^ k) S,
  induction S using finset.induction_on with i S hnmem ih,
  { simp },
  { simp only [ to_fun_insert_of_not_mem _ _ _ _ hnmem],
    rw [(to_fun_commutes ϕ f f S i hnmem).mul_pow, ih, pi.pow_apply, map_pow] },
end

lemma hom_eq_one_of_eq_one (h : ∀ x ∈ S, f x = 1) : hom S f = 1 :=
begin
  change to_fun ϕ f S = 1,
  induction S using finset.induction_on with i S hnmem ih,
  { simp },
  { simp only [ to_fun_insert_of_not_mem _ _ _ _ hnmem],
    rw [h _ (finset.mem_insert_self _ _), ih (λ i h', h i (finset.mem_insert_of_mem h'))],
    simp, },
end

lemma order_of_hom_dvd_prod_card [hfin : ∀ i, fintype (H i)]:
  order_of (hom S f) ∣ (∏ i in S, fintype.card (H i)) :=
begin
  rw order_of_dvd_iff_pow_eq_one,
  rw pow,
  apply hom_eq_one_of_eq_one,
  intros i hmem,
  simp only [pi.pow_apply, pi.one_apply],
  rw ← order_of_dvd_iff_pow_eq_one,
  calc order_of (f i) ∣ fintype.card (H i) : order_of_dvd_card_univ
    ... ∣ (∏ (i : I) in S, fintype.card (H i)) : finset.dvd_prod_of_mem _ hmem,
end

end pi_hom_restr

namespace pi_hom

include hfin

/-- The product of `ϕ i (f i)` for all `i : I` -/
def to_fun : G := pi_hom_restr.to_fun ϕ f finset.univ

/-- The canonical homomorphism from a pi group -/
def hom : (Π (i : I), H i) →* G := pi_hom_restr.hom ϕ finset.univ

@[simp]
lemma hom_update_one (i : I) (y : H i): hom (function.update 1 i y) = ϕ i y :=
by { change pi_hom_restr.hom ϕ finset.univ (function.update 1 i y) = ϕ i y, simp }

lemma range : hom.range = ⨆ i : I, (ϕ i).range :=
by { show (pi_hom_restr.hom ϕ finset.univ).range = _, simp [pi_hom_restr.range] }

lemma pow (k : ℕ) : (hom f) ^ k = hom (f ^ k) := pi_hom_restr.pow _ _ _ _

lemma injective_of_independent
  (hind : complete_lattice.independent (λ i, (ϕ i).range))
  (hinj : ∀ i, function.injective (ϕ i)) :
  function.injective hom :=
begin
  apply (monoid_hom.ker_eq_bot_iff _).mp,
  apply eq_bot_iff.mpr,
  intro f,
  show pi_hom_restr.to_fun ϕ f finset.univ = 1 → f = 1,
  suffices : pi_hom_restr.to_fun ϕ f finset.univ = 1 → (∀ (i : I), i ∈ finset.univ → f i = 1),
  by exact (λ h, funext (λ (i : I), this h i (finset.mem_univ i))),
  induction (finset.univ : finset I) using finset.induction_on with i S hnmem ih,
  { simp },
  { intro heq1,
    simp only [ pi_hom_restr.to_fun_insert_of_not_mem _ _ _ _ hnmem] at heq1,
    have hnmem' : i ∉ (S : set I), by simpa,
    have heq1' : ϕ i (f i) = 1 ∧ pi_hom_restr.to_fun ϕ f S = 1,
    { apply mul_eq_one_of_disjoint (hind.disjoint_bsupr hnmem') _ _ heq1,
      { simp, },
      { apply pi_hom_restr.to_fun_in_sup_range, }, },
    rcases heq1' with ⟨ heq1i, heq1S ⟩,
    specialize ih heq1S,
    intros i h,
    simp only [finset.mem_insert] at h,
    rcases h with ⟨rfl | _⟩,
    { apply hinj i, simpa, },
    { exact (ih _ h), } }
end

end pi_hom

include hfin

lemma independent_range_of_coprime_order [∀ i, fintype (H i)]
  (hcoprime : ∀ i j, i ≠ j → nat.coprime (fintype.card (H i)) (fintype.card (H j)))
  (hinj : ∀ i, function.injective (ϕ i)) :
  complete_lattice.independent (λ i, (ϕ i).range) :=
begin
  rintros i f ⟨hxi, hxp⟩,
  simp only [ne.def, subgroup.coe_to_submonoid, set_like.mem_coe,
    monoid_hom.coe_range, set.mem_range] at hxi hxp,
  rcases hxi with ⟨ y, rfl ⟩,
  let S := finset.erase finset.univ i,
  have hnmem : i ∉ S := finset.not_mem_erase i finset.univ,
  have : (⨆ (j : I) (x : ¬j = i), (ϕ j).range) = (⨆ j ∈ S, (ϕ j).range) :=
  begin
    congr' 1,
    ext i,
    congr' 2,
    apply supr_congr_Prop,
    { simp [S] },
    { exact λ _, rfl }
  end,
  rw this at hxp, clear this,
  rw ← pi_hom_restr.range at hxp,
  cases hxp with f heq1,

  let x := ϕ i y,
  let z := pi_hom_restr.hom ϕ S f,
  change z = x at heq1,
  let p := ∏ (i : I) in S, fintype.card (H i),
  have h1 := calc order_of x = order_of y : order_of_injective _ (hinj i) _
    ... ∣ fintype.card (H i) : order_of_dvd_card_univ,
  have h2 := calc order_of x = order_of z : by rw heq1
    ... ∣ p : pi_hom_restr.order_of_hom_dvd_prod_card ϕ f S ,
  have hcop : p.coprime (fintype.card (H i)),
  { apply coprime_prod_left, intros j hmem, apply hcoprime, rintro rfl, contradiction, },
  have hx : ϕ i y = 1,
  { have := nat.dvd_gcd h2 h1,
    unfold nat.coprime at hcop,
    simpa [hcop] using this, },
  simpa using hx,
end

end family_of_groups

namespace subgroup_pi_hom

section subgroup_pi_hom

-- We have an family of subgroups
parameters {I : Type*} [hfin : fintype I] [hdec : decidable_eq I] {H : I → subgroup G}

-- Elements of `Π (i : I), H i` are called `f` and `g` here
variables (f g : Π (i : I), H i)

section commuting_subgroups

-- We assume that the elements of different subgroups commute
parameters (hcomm : ∀ (i j : I), i ≠ j → ∀ (x y : G), x ∈ H i → y ∈ H j → commute x y)
include hcomm

lemma hcomm_subtype :
  fact (∀ (i j : I), i ≠ j → ∀ (x : H i) (y : H j), commute ((H i).subtype x) ((H j).subtype y)) :=
fact.mk begin
  rintros i j hne ⟨x, hx⟩ ⟨y, hy⟩,
  simp only [subgroup.coe_subtype, subgroup.coe_mk],
  exact hcomm i j hne x y hx hy,
end

include hfin

/-- The canonical homomorphism from a pi group of subgroups -/
def hom : (Π (i : I), H i) →* G :=
  let _ := hcomm_subtype in by exactI pi_hom.hom (λ i, (H i).subtype)

@[simp]
lemma hom_update_one (i : I) (y : H i): hom (function.update 1 i y) = y :=
by apply pi_hom.hom_update_one

lemma range : hom.range = ⨆ i : I, H i :=
by { unfold hom, simp [pi_hom.range] }

lemma pow (k : ℕ) : (hom f) ^ k = hom (f ^ k) :=
by apply pi_hom_restr.pow

lemma injective_of_independent (hind : complete_lattice.independent H) :
  function.injective hom :=
begin
  apply pi_hom.injective_of_independent,
  { simpa using hind },
  { intro i, exact subtype.coe_injective }
end

lemma _root_.independent_of_coprime_order [∀ i, fintype (H i)]
  (hcoprime : ∀ i j, i ≠ j → nat.coprime (fintype.card (H i)) (fintype.card (H j))) :
  complete_lattice.independent H :=
begin
  haveI := hcomm_subtype hcomm,
  have := independent_range_of_coprime_order (λ i, (H i).subtype) hcoprime
    (λ i , subtype.coe_injective),
  simpa using this,
end

end commuting_subgroups

end subgroup_pi_hom

end subgroup_pi_hom

end with_group
