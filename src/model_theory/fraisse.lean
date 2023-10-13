/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import model_theory.finitely_generated
import model_theory.direct_limit
import model_theory.bundled

/-!
# Fraïssé Classes and Fraïssé Limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file pertains to the ages of countable first-order structures. The age of a structure is the
class of all finitely-generated structures that embed into it.

Of particular interest are Fraïssé classes, which are exactly the ages of countable
ultrahomogeneous structures. To each is associated a unique (up to nonunique isomorphism)
Fraïssé limit - the countable ultrahomogeneous structure with that age.

## Main Definitions
* `first_order.language.age` is the class of finitely-generated structures that embed into a
particular structure.
* A class `K` has the `first_order.language.hereditary` when all finitely-generated
structures that embed into structures in `K` are also in `K`.
* A class `K` has the `first_order.language.joint_embedding` when for every `M`, `N` in
`K`, there is another structure in `K` into which both `M` and `N` embed.
* A class `K` has the `first_order.language.amalgamation` when for any pair of embeddings
of a structure `M` in `K` into other structures in `K`, those two structures can be embedded into a
fourth structure in `K` such that the resulting square of embeddings commutes.
* `first_order.language.is_fraisse` indicates that a class is nonempty, isomorphism-invariant,
essentially countable, and satisfies the hereditary, joint embedding, and amalgamation properties.
* `first_order.language.is_fraisse_limit` indicates that a structure is a Fraïssé limit for a given
class.

## Main Results
* We show that the age of any structure is isomorphism-invariant and satisfies the hereditary and
joint-embedding properties.
* `first_order.language.age.countable_quotient` shows that the age of any countable structure is
essentially countable.
* `first_order.language.exists_countable_is_age_of_iff` gives necessary and sufficient conditions
for a class to be the age of a countable structure in a language with countably many functions.

## Implementation Notes
* Classes of structures are formalized with `set (bundled L.Structure)`.
* Some results pertain to countable limit structures, others to countably-generated limit
structures. In the case of a language with countably many function symbols, these are equivalent.

## References
- [W. Hodges, *A Shorter Model Theory*][Hodges97]
- [K. Tent, M. Ziegler, *A Course in Model Theory*][Tent_Ziegler]

## TODO
* Show existence and uniqueness of Fraïssé limits

-/

universes u v w w'

open_locale first_order
open set category_theory

namespace first_order
namespace language
open Structure substructure

variables (L : language.{u v})

/-! ### The Age of a Structure and Fraïssé Classes-/

/-- The age of a structure `M` is the class of finitely-generated structures that embed into it. -/
def age (M : Type w) [L.Structure M] : set (bundled.{w} L.Structure) :=
{ N | Structure.fg L N ∧ nonempty (N ↪[L] M) }

variables {L} (K : set (bundled.{w} L.Structure))

/-- A class `K` has the hereditary property when all finitely-generated structures that embed into
  structures in `K` are also in `K`.  -/
def hereditary : Prop :=
∀ (M : bundled.{w} L.Structure), M ∈ K → L.age M ⊆ K

/-- A class `K` has the joint embedding property when for every `M`, `N` in `K`, there is another
  structure in `K` into which both `M` and `N` embed. -/
def joint_embedding : Prop :=
directed_on (λ M N : bundled.{w} L.Structure, nonempty (M ↪[L] N)) K

/-- A class `K` has the amalgamation property when for any pair of embeddings of a structure `M` in
  `K` into other structures in `K`, those two structures can be embedded into a fourth structure in
  `K` such that the resulting square of embeddings commutes. -/
def amalgamation : Prop :=
∀ (M N P : bundled.{w} L.Structure) (MN : M ↪[L] N) (MP : M ↪[L] P), M ∈ K → N ∈ K → P ∈ K →
  ∃ (Q : bundled.{w} L.Structure) (NQ : N ↪[L] Q) (PQ : P ↪[L] Q), Q ∈ K ∧ NQ.comp MN = PQ.comp MP

/-- A Fraïssé class is a nonempty, isomorphism-invariant, essentially countable class of structures
satisfying the hereditary, joint embedding, and amalgamation properties. -/
class is_fraisse : Prop :=
(is_nonempty : K.nonempty)
(fg : ∀ M : bundled.{w} L.Structure, M ∈ K → Structure.fg L M)
(is_equiv_invariant : ∀ (M N : bundled.{w} L.Structure), nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K))
(is_essentially_countable : (quotient.mk '' K).countable)
(hereditary : hereditary K)
(joint_embedding : joint_embedding K)
(amalgamation : amalgamation K)

variables {K} (L) (M : Type w) [L.Structure M]

lemma age.is_equiv_invariant (N P : bundled.{w} L.Structure) (h : nonempty (N ≃[L] P)) :
  N ∈ L.age M ↔ P ∈ L.age M :=
and_congr h.some.fg_iff
  ⟨nonempty.map (λ x, embedding.comp x h.some.symm.to_embedding),
  nonempty.map (λ x, embedding.comp x h.some.to_embedding)⟩

variables {L} {M} {N : Type w} [L.Structure N]

lemma embedding.age_subset_age (MN : M ↪[L] N) : L.age M ⊆ L.age N :=
λ _, and.imp_right (nonempty.map MN.comp)

lemma equiv.age_eq_age (MN : M ≃[L] N) : L.age M = L.age N :=
le_antisymm MN.to_embedding.age_subset_age MN.symm.to_embedding.age_subset_age

lemma Structure.fg.mem_age_of_equiv {M N : bundled L.Structure} (h : Structure.fg L M)
  (MN : nonempty (M ≃[L] N)) : N ∈ L.age M :=
⟨MN.some.fg_iff.1 h, ⟨MN.some.symm.to_embedding⟩⟩

lemma hereditary.is_equiv_invariant_of_fg (h : hereditary K)
  (fg : ∀ (M : bundled.{w} L.Structure), M ∈ K → Structure.fg L M)
  (M N : bundled.{w} L.Structure) (hn : nonempty (M ≃[L] N)) : M ∈ K ↔ N ∈ K :=
⟨λ MK, h M MK ((fg M MK).mem_age_of_equiv hn),
  λ NK, h N NK ((fg N NK).mem_age_of_equiv ⟨hn.some.symm⟩)⟩

variable (M)

lemma age.nonempty : (L.age M).nonempty :=
⟨bundled.of (substructure.closure L (∅ : set M)),
  (fg_iff_Structure_fg _).1 (fg_closure set.finite_empty), ⟨substructure.subtype _⟩⟩

lemma age.hereditary : hereditary (L.age M) :=
λ N hN P hP, hN.2.some.age_subset_age hP

lemma age.joint_embedding : joint_embedding (L.age M) :=
λ N hN P hP, ⟨bundled.of ↥(hN.2.some.to_hom.range ⊔ hP.2.some.to_hom.range),
  ⟨(fg_iff_Structure_fg _).1 ((hN.1.range hN.2.some.to_hom).sup (hP.1.range hP.2.some.to_hom)),
  ⟨subtype _⟩⟩,
  ⟨embedding.comp (inclusion le_sup_left) hN.2.some.equiv_range.to_embedding⟩,
  ⟨embedding.comp (inclusion le_sup_right) hP.2.some.equiv_range.to_embedding⟩⟩

/-- The age of a countable structure is essentially countable (has countably many isomorphism
classes). -/
lemma age.countable_quotient [h : countable M] :
  (quotient.mk '' L.age M).countable :=
begin
  classical,
  refine (congr_arg _ (set.ext $ forall_quotient_iff.2 $ λ N, _)).mp
    (countable_range $ λ s : finset M, ⟦⟨closure L (s : set M), infer_instance⟩⟧),
  simp only [mem_image, mem_range, mem_set_of_eq, quotient.eq],
  split,
  { rintro ⟨s, hs⟩,
    use bundled.of ↥(closure L (s : set M)),
    exact ⟨⟨(fg_iff_Structure_fg _).1 (fg_closure s.finite_to_set), ⟨subtype _⟩⟩, hs⟩ },
  { rintro ⟨P, ⟨⟨s, hs⟩, ⟨PM⟩⟩, hP2⟩,
    refine ⟨s.image PM, setoid.trans _ hP2⟩,
    rw [← embedding.coe_to_hom, finset.coe_image, closure_image PM.to_hom, hs, ← hom.range_eq_map],
    exact ⟨PM.equiv_range.symm⟩ }
end

/-- The age of a direct limit of structures is the union of the ages of the structures. -/
@[simp] theorem age_direct_limit {ι : Type w} [preorder ι] [is_directed ι (≤)] [nonempty ι]
  (G : ι → Type (max w w')) [Π i, L.Structure (G i)]
  (f : Π i j, i ≤ j → G i ↪[L] G j) [directed_system G (λ i j h, f i j h)] :
  L.age (direct_limit G f) = ⋃ (i : ι), L.age (G i) :=
begin
  classical,
  ext M,
  simp only [mem_Union],
  split,
  { rintro ⟨Mfg, ⟨e⟩⟩,
    obtain ⟨s, hs⟩ := Mfg.range e.to_hom,
    let out := @quotient.out _ (direct_limit.setoid G f),
    obtain ⟨i, hi⟩ := finset.exists_le (s.image (sigma.fst ∘ out)),
    have e' := ((direct_limit.of L ι G f i).equiv_range.symm.to_embedding),
    refine ⟨i, Mfg, ⟨e'.comp ((substructure.inclusion _).comp e.equiv_range.to_embedding)⟩⟩,
    rw [← hs, closure_le],
    intros x hx,
    refine ⟨f (out x).1 i (hi (out x).1 (finset.mem_image_of_mem _ hx)) (out x).2, _⟩,
    rw [embedding.coe_to_hom, direct_limit.of_apply, quotient.mk_eq_iff_out,
      direct_limit.equiv_iff G f _
      (hi (out x).1 (finset.mem_image_of_mem _ hx)), directed_system.map_self],
    refl },
  { rintro ⟨i, Mfg, ⟨e⟩⟩,
    exact ⟨Mfg, ⟨embedding.comp (direct_limit.of L ι G f i) e⟩⟩ }
end

/-- Sufficient conditions for a class to be the age of a countably-generated structure. -/
theorem exists_cg_is_age_of (hn : K.nonempty)
  (h : ∀ (M N : bundled.{w} L.Structure), nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K))
  (hc : (quotient.mk '' K).countable)
  (fg : ∀ (M : bundled.{w} L.Structure), M ∈ K → Structure.fg L M)
  (hp : hereditary K)
  (jep : joint_embedding K) :
  ∃ (M : bundled.{w} L.Structure), Structure.cg L M ∧ L.age M = K :=
begin
  obtain ⟨F, hF⟩ := hc.exists_eq_range (hn.image _),
  simp only [set.ext_iff, forall_quotient_iff, mem_image, mem_range, quotient.eq] at hF,
  simp_rw [quotient.eq_mk_iff_out] at hF,
  have hF' : ∀ n : ℕ, (F n).out ∈ K,
  { intro n,
    obtain ⟨P, hP1, hP2⟩ := (hF (F n).out).2 ⟨n, setoid.refl _⟩,
    exact (h _ _ hP2).1 hP1 },
  choose P hPK hP hFP using (λ (N : K) (n : ℕ), jep N N.2 (F (n + 1)).out (hF' _)),
  let G : ℕ → K := @nat.rec (λ _, K) (⟨(F 0).out, hF' 0⟩) (λ n N, ⟨P N n, hPK N n⟩),
  let f : Π (i j), i ≤ j → G i ↪[L] G j :=
    directed_system.nat_le_rec (λ n, (hP _ n).some),
  refine ⟨bundled.of (direct_limit (λ n, G n) f), direct_limit.cg _ (λ n, (fg _ (G n).2).cg),
    (age_direct_limit _ _).trans (subset_antisymm
      (Union_subset (λ n N hN, hp (G n) (G n).2 hN)) (λ N KN, _))⟩,
  obtain ⟨n, ⟨e⟩⟩ := (hF N).1 ⟨N, KN, setoid.refl _⟩,
  refine mem_Union_of_mem n ⟨fg _ KN, ⟨embedding.comp _ e.symm.to_embedding⟩⟩,
  cases n,
  { exact embedding.refl _ _ },
  { exact (hFP _ n).some }
end

theorem exists_countable_is_age_of_iff [countable (Σl, L.functions l)] :
  (∃ (M : bundled.{w} L.Structure), countable M ∧ L.age M = K) ↔
    K.nonempty ∧
    (∀ (M N : bundled.{w} L.Structure), nonempty (M ≃[L] N) → (M ∈ K ↔ N ∈ K)) ∧
    (quotient.mk '' K).countable ∧
    (∀ (M : bundled.{w} L.Structure), M ∈ K → Structure.fg L M) ∧
    hereditary K ∧
    joint_embedding K :=
begin
  split,
  { rintros ⟨M, h1, h2, rfl⟩,
    resetI,
    refine ⟨age.nonempty M, age.is_equiv_invariant L M, age.countable_quotient M, λ N hN, hN.1,
      age.hereditary M, age.joint_embedding M⟩, },
  { rintros ⟨Kn, eqinv, cq, hfg, hp, jep⟩,
    obtain ⟨M, hM, rfl⟩ := exists_cg_is_age_of Kn eqinv cq hfg hp jep,
    exact ⟨M, Structure.cg_iff_countable.1 hM, rfl⟩ }
end

variables {K} (L) (M)

/-- A structure `M` is ultrahomogeneous if every embedding of a finitely generated substructure
into `M` extends to an automorphism of `M`. -/
def is_ultrahomogeneous : Prop :=
∀ (S : L.substructure M) (hs : S.fg) (f : S ↪[L] M),
  ∃ (g : M ≃[L] M), f = g.to_embedding.comp S.subtype

variables {L} (K)

/-- A structure `M` is a Fraïssé limit for a class `K` if it is countably generated,
ultrahomogeneous, and has age `K`. -/
@[protect_proj] structure is_fraisse_limit [countable (Σl, L.functions l)]
  [countable M] : Prop :=
(ultrahomogeneous : is_ultrahomogeneous L M)
(age : L.age M = K)

variables {L} {M}

lemma is_ultrahomogeneous.amalgamation_age (h : L.is_ultrahomogeneous M) :
  amalgamation (L.age M) :=
begin
  rintros N P Q NP NQ ⟨Nfg, ⟨NM⟩⟩ ⟨Pfg, ⟨PM⟩⟩ ⟨Qfg, ⟨QM⟩⟩,
  obtain ⟨g, hg⟩ := h ((PM.comp NP).to_hom.range) (Nfg.range _)
    ((QM.comp NQ).comp (PM.comp NP).equiv_range.symm.to_embedding),
  let s := (g.to_hom.comp PM.to_hom).range ⊔ QM.to_hom.range,
  refine ⟨bundled.of s, embedding.comp (substructure.inclusion le_sup_left)
      ((g.to_embedding.comp PM).equiv_range).to_embedding,
    embedding.comp (substructure.inclusion le_sup_right) QM.equiv_range.to_embedding,
    ⟨(fg_iff_Structure_fg _).1 (fg.sup (Pfg.range _) (Qfg.range _)), ⟨substructure.subtype _⟩⟩, _⟩,
  ext n,
  have hgn := (embedding.ext_iff.1 hg) ((PM.comp NP).equiv_range n),
  simp only [embedding.comp_apply, equiv.coe_to_embedding, equiv.symm_apply_apply,
    substructure.coe_subtype, embedding.equiv_range_apply] at hgn,
  simp only [embedding.comp_apply, equiv.coe_to_embedding, substructure.coe_inclusion,
    set.coe_inclusion, embedding.equiv_range_apply, hgn],
end

lemma is_ultrahomogeneous.age_is_fraisse [countable M]
  (h : L.is_ultrahomogeneous M) :
  is_fraisse (L.age M) :=
⟨age.nonempty M, λ _ hN, hN.1, age.is_equiv_invariant L M, age.countable_quotient M,
  age.hereditary M, age.joint_embedding M, h.amalgamation_age⟩

namespace is_fraisse_limit

/-- If a class has a Fraïssé limit, it must be Fraïssé. -/
theorem is_fraisse [countable (Σl, L.functions l)] [countable M] (h : is_fraisse_limit K M) :
  is_fraisse K :=
(congr rfl h.age).mp h.ultrahomogeneous.age_is_fraisse

end is_fraisse_limit

end language
end first_order
