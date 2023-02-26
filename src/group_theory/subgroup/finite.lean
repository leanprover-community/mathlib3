/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/

import data.set.finite
import group_theory.subgroup.basic
import group_theory.submonoid.membership

/-!
# Subgroups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides some result on multiplicative and additive subgroups in the finite context.

## Tags
subgroup, subgroups
-/

open_locale big_operators

variables {G : Type*} [group G]
variables {A : Type*} [add_group A]

namespace subgroup

@[to_additive]
instance (K : subgroup G) [d : decidable_pred (∈ K)] [fintype G] : fintype K :=
show fintype {g : G // g ∈ K}, from infer_instance

@[to_additive]
instance (K : subgroup G) [finite G] : finite K :=
subtype.finite

end subgroup

/-!
### Conversion to/from `additive`/`multiplicative`
-/
namespace subgroup

variables (H K : subgroup G)

/-- Product of a list of elements in a subgroup is in the subgroup. -/
@[to_additive "Sum of a list of elements in an `add_subgroup` is in the `add_subgroup`."]
protected lemma list_prod_mem {l : list G} : (∀ x ∈ l, x ∈ K) → l.prod ∈ K :=
list_prod_mem

/-- Product of a multiset of elements in a subgroup of a `comm_group` is in the subgroup. -/
@[to_additive "Sum of a multiset of elements in an `add_subgroup` of an `add_comm_group`
is in the `add_subgroup`."]
protected lemma multiset_prod_mem {G} [comm_group G] (K : subgroup G) (g : multiset G) :
  (∀ a ∈ g, a ∈ K) → g.prod ∈ K := multiset_prod_mem g

@[to_additive]
lemma multiset_noncomm_prod_mem (K : subgroup G) (g : multiset G) (comm) :
  (∀ a ∈ g, a ∈ K) → g.noncomm_prod comm ∈ K :=
K.to_submonoid.multiset_noncomm_prod_mem g comm

/-- Product of elements of a subgroup of a `comm_group` indexed by a `finset` is in the
    subgroup. -/
@[to_additive "Sum of elements in an `add_subgroup` of an `add_comm_group` indexed by a `finset`
is in the `add_subgroup`."]
protected lemma prod_mem {G : Type*} [comm_group G] (K : subgroup G)
  {ι : Type*} {t : finset ι} {f : ι → G} (h : ∀ c ∈ t, f c ∈ K) :
  ∏ c in t, f c ∈ K :=
prod_mem h

@[to_additive]
lemma noncomm_prod_mem (K : subgroup G) {ι : Type*} {t : finset ι} {f : ι → G} (comm) :
  (∀ c ∈ t, f c ∈ K) → t.noncomm_prod f comm ∈ K :=
K.to_submonoid.noncomm_prod_mem t f comm

@[simp, norm_cast, to_additive] theorem coe_list_prod (l : list H) :
  (l.prod : G) = (l.map coe).prod :=
submonoid_class.coe_list_prod l

@[simp, norm_cast, to_additive] theorem coe_multiset_prod {G} [comm_group G] (H : subgroup G)
  (m : multiset H) : (m.prod : G) = (m.map coe).prod :=
submonoid_class.coe_multiset_prod m

@[simp, norm_cast, to_additive] theorem coe_finset_prod {ι G} [comm_group G] (H : subgroup G)
  (f : ι → H) (s : finset ι) :
  ↑(∏ i in s, f i) = (∏ i in s, f i : G) :=
submonoid_class.coe_finset_prod f s

@[to_additive] instance fintype_bot : fintype (⊥ : subgroup G) := ⟨{1},
by {rintro ⟨x, ⟨hx⟩⟩, exact finset.mem_singleton_self _}⟩

/- curly brackets `{}` are used here instead of instance brackets `[]` because
  the instance in a goal is often not the same as the one inferred by type class inference.  -/
@[simp, to_additive] lemma card_bot {_ : fintype ↥(⊥ : subgroup G)} :
  fintype.card (⊥ : subgroup G)  = 1 :=
fintype.card_eq_one_iff.2
  ⟨⟨(1 : G), set.mem_singleton 1⟩, λ ⟨y, hy⟩, subtype.eq $ subgroup.mem_bot.1 hy⟩

@[to_additive] lemma eq_top_of_card_eq [fintype H] [fintype G]
  (h : fintype.card H = fintype.card G) : H = ⊤ :=
begin
  haveI : fintype (H : set G) := ‹fintype H›,
  rw [set_like.ext'_iff, coe_top, ← finset.coe_univ, ← (H : set G).coe_to_finset, finset.coe_inj,
    ← finset.card_eq_iff_eq_univ, ← h, set.to_finset_card],
  congr
end

@[to_additive] lemma eq_top_of_le_card [fintype H] [fintype G]
  (h : fintype.card G ≤ fintype.card H) : H = ⊤ :=
eq_top_of_card_eq H (le_antisymm (fintype.card_le_of_injective coe subtype.coe_injective) h)

@[to_additive] lemma eq_bot_of_card_le [fintype H] (h : fintype.card H ≤ 1) : H = ⊥ :=
let _ := fintype.card_le_one_iff_subsingleton.mp h in by exactI eq_bot_of_subsingleton H

@[to_additive] lemma eq_bot_of_card_eq [fintype H] (h : fintype.card H = 1) : H = ⊥ :=
H.eq_bot_of_card_le (le_of_eq h)

@[to_additive] lemma card_le_one_iff_eq_bot [fintype H] : fintype.card H ≤ 1 ↔ H = ⊥ :=
⟨λ h, (eq_bot_iff_forall _).2
    (λ x hx, by simpa [subtype.ext_iff] using fintype.card_le_one_iff.1 h ⟨x, hx⟩ 1),
  λ h, by simp [h]⟩

@[to_additive] lemma one_lt_card_iff_ne_bot [fintype H] : 1 < fintype.card H ↔ H ≠ ⊥ :=
lt_iff_not_le.trans H.card_le_one_iff_eq_bot.not

end subgroup

namespace subgroup

section pi

open set

variables {η : Type*} {f : η → Type*} [∀ i, group (f i)]

@[to_additive]
lemma pi_mem_of_mul_single_mem_aux [decidable_eq η] (I : finset η) {H : subgroup (Π i, f i) }
  (x : Π i, f i) (h1 : ∀ i, i ∉ I → x i = 1) (h2 : ∀ i, i ∈ I → pi.mul_single i (x i) ∈ H ) :
  x ∈ H :=
begin
  induction I using finset.induction_on with i I hnmem ih generalizing x,
  { convert one_mem H,
    ext i,
    exact (h1 i (not_mem_empty i)) },
  { have : x = function.update x i 1 * pi.mul_single i (x i),
    { ext j,
      by_cases heq : j = i,
      { subst heq, simp, },
      { simp [heq], }, },
    rw this, clear this,
    apply mul_mem,
    { apply ih; clear ih,
      { intros j hj,
        by_cases heq : j = i,
        { subst heq, simp, },
        { simp [heq], apply h1 j, simpa [heq] using hj, } },
      { intros j hj,
        have : j ≠ i, by { rintro rfl, contradiction },
        simp [this],
        exact h2 _ (finset.mem_insert_of_mem hj), }, },
    { apply h2, simp, } }
end

@[to_additive]
lemma pi_mem_of_mul_single_mem [finite η] [decidable_eq η] {H : subgroup (Π i, f i)}
  (x : Π i, f i) (h : ∀ i, pi.mul_single i (x i) ∈ H) : x ∈ H :=
by { casesI nonempty_fintype η,
   exact pi_mem_of_mul_single_mem_aux finset.univ x (by simp) (λ i _, h i) }

/-- For finite index types, the `subgroup.pi` is generated by the embeddings of the groups.  -/
@[to_additive "For finite index types, the `subgroup.pi` is generated by the embeddings of the
additive groups."]
lemma pi_le_iff [decidable_eq η] [finite η] {H : Π i, subgroup (f i)} {J : subgroup (Π i, f i)} :
  pi univ H ≤ J ↔ ∀ i : η, map (monoid_hom.single f i) (H i) ≤ J :=
begin
  split,
  { rintros h i _ ⟨x, hx, rfl⟩, apply h, simpa using hx },
  { exact λ h x hx, pi_mem_of_mul_single_mem  x (λ i, h i (mem_map_of_mem _ (hx i trivial))), }
end

end pi

end subgroup

namespace subgroup

section normalizer

lemma mem_normalizer_fintype {S : set G} [finite S] {x : G}
  (h : ∀ n, n ∈ S → x * n * x⁻¹ ∈ S) : x ∈ subgroup.set_normalizer S :=
by haveI := classical.prop_decidable; casesI nonempty_fintype S;
haveI := set.fintype_image S (λ n, x * n * x⁻¹); exact
λ n, ⟨h n, λ h₁,
have heq : (λ n, x * n * x⁻¹) '' S = S := set.eq_of_subset_of_card_le
  (λ n ⟨y, hy⟩, hy.2 ▸ h y hy.1) (by rw set.card_image_of_injective S conj_injective),
have x * n * x⁻¹ ∈ (λ n, x * n * x⁻¹) '' S := heq.symm ▸ h₁,
let ⟨y, hy⟩ := this in conj_injective hy.2 ▸ hy.1⟩

end normalizer

end subgroup

namespace monoid_hom

variables {N : Type*} [group N]

open subgroup

@[to_additive]
instance decidable_mem_range (f : G →* N) [fintype G] [decidable_eq N] :
  decidable_pred (∈ f.range) :=
λ x, fintype.decidable_exists_fintype

-- this instance can't go just after the definition of `mrange` because `fintype` is
-- not imported at that stage

/-- The range of a finite monoid under a monoid homomorphism is finite.
Note: this instance can form a diamond with `subtype.fintype` in the
presence of `fintype N`. -/
@[to_additive "The range of a finite additive monoid under an additive monoid homomorphism is
finite.

Note: this instance can form a diamond with `subtype.fintype` or `subgroup.fintype` in the
presence of `fintype N`."]
instance fintype_mrange {M N : Type*} [monoid M] [monoid N] [fintype M] [decidable_eq N]
  (f : M →* N) : fintype (mrange f) :=
set.fintype_range f

/-- The range of a finite group under a group homomorphism is finite.

Note: this instance can form a diamond with `subtype.fintype` or `subgroup.fintype` in the
presence of `fintype N`. -/
@[to_additive "The range of a finite additive group under an additive group homomorphism is finite.

Note: this instance can form a diamond with `subtype.fintype` or `subgroup.fintype` in the
presence of `fintype N`."]
instance fintype_range  [fintype G] [decidable_eq N] (f : G →* N) : fintype (range f) :=
set.fintype_range f

end monoid_hom
