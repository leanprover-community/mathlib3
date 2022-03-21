/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import model_theory.finitely_generated
import model_theory.direct_limit

/-!
# Fraïssé Classes and Fraïssé Limits

This file pertains to the ages of countable first-order structures. The age of a structure is the
class of all finitely-generated structures that embed into it.

Of particular interest are Fraïssé classes, which are exactly the ages of countable
ultrahomogeneous structures. To each is associated a unique (up to nonunique isomorphism)
Fraïssé limit - the countable structure with that age.

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

## Main Results
* We show that the age of any structure is isomorphism-invariant and satisfies the hereditary and
joint-embedding properties.
* `first_order.language.age.countable_quotient` shows that the age of any countable structure is
essentially countable.


## Implementation Notes
* Classes of structures are formalized with `set (bundled L.Structure)`.
* Some results pertain to countable limit structures, others to countably-generated limit
structures. In the case of a language with countably many function symbols, these are equivalent.

## References
- [W. Hodges, *A Shorter Model Theory*][Hodges97]
- [K. Tent, M. Ziegler, *A Course in Model Theory*][Tent_Ziegler]

## TODO
* Define Fraïssé limits
* Define ultrahomogeneous structures
* Show that any two Fraïssé limits of a Fraïssé class are isomorphic
* Show that any Fraïssé limit is ultrahomogeneous
* Show that the age of any ultrahomogeneous countable structure is Fraïssé

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
∀ (M N : bundled.{w} L.Structure), nonempty (M ↪[L] N) → Structure.fg L M → N ∈ K → M ∈ K

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

variable {L}

lemma age.hereditary : hereditary (L.age M) :=
λ N P NP Nfg h, ⟨Nfg, nonempty.map (λ x, embedding.comp x NP.some) h.2⟩

lemma age.joint_embedding : joint_embedding (L.age M) :=
λ N hN P hP, ⟨bundled.of ↥(hN.2.some.to_hom.range ⊔ hP.2.some.to_hom.range),
  ⟨(fg_iff_Structure_fg _).1 ((hN.1.range hN.2.some.to_hom).sup (hP.1.range hP.2.some.to_hom)),
  ⟨subtype _⟩⟩,
  ⟨embedding.comp (inclusion le_sup_left) hN.2.some.equiv_range.to_embedding⟩,
  ⟨embedding.comp (inclusion le_sup_right) hP.2.some.equiv_range.to_embedding⟩⟩

/-- The age of a countable structure is essentially countable (has countably many isomorphism
classes). -/
lemma age.countable_quotient (h : (univ : set M).countable) :
  (quotient.mk '' (L.age M)).countable :=
begin
  refine eq.mp (congr rfl (set.ext _)) ((countable_set_of_finite_subset h).image
    (λ s, ⟦⟨closure L s, infer_instance⟩⟧)),
  rw forall_quotient_iff,
  intro N,
  simp only [subset_univ, and_true, mem_image, mem_set_of_eq, quotient.eq],
  split,
  { rintro ⟨s, hs1, hs2⟩,
    use bundled.of ↥(closure L s),
    exact ⟨⟨(fg_iff_Structure_fg _).1 (fg_closure hs1), ⟨subtype _⟩⟩, hs2⟩ },
  { rintro ⟨P, ⟨⟨s, hs⟩, ⟨PM⟩⟩, hP2⟩,
    refine ⟨PM '' s, set.finite.image PM s.finite_to_set, setoid.trans _ hP2⟩,
    rw [← embedding.coe_to_hom, closure_image PM.to_hom, hs, ← hom.range_eq_map],
    exact ⟨PM.equiv_range.symm⟩ }
end

end language
end first_order
