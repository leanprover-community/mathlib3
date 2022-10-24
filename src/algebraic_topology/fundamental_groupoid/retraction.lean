/-
Copyright (c) 2022 Mark Lavrentyev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Lavrentyev
-/
import topology.homotopy.equiv
import category_theory.equivalence
import algebraic_topology.fundamental_groupoid.product
import algebra.category.Group.basic
import algebra.category.Group.epi_mono

/-!
# A retraction from a space to a subspace is a split epimorphism

## Main definitions

  - `is_retraction r` A continuous map `r : X → A` (where `A` is a subspace of `X`) is a retraction
    when the restriction of r to A is the identity. Equivalently, composing r with the inclusion
    `i : A → X` is just the identity map on A.
  - `top_retraction X A` is the bundled version of `is_retraction`.

  - `fundamental_groupoid_split_mono` The induced map on `fundamental_groupoid X`
    of the inclusion `i : A → X` is a split mono in the category Groupoid.
  - `fundamental_groupoid_split_epi` The induced map on `fundamental_groupoid X`
    of the retraction `r : X → A` is a split epi in the category Groupoid.

  - `not_epi_of_unit_to_int f` The group homomorphism `unit → ℤ` is not an epimorphism in Group.
-/

noncomputable theory

universe u

open fundamental_groupoid category_theory fundamental_groupoid_functor

open_locale fundamental_groupoid unit_interval

-- TODO: move to other file.
/-- Helper to convert a continuous map to an arrow in the category Top. -/
def Top.hom_of_continuous_map
  {X Y : Type*} [topological_space X] [topological_space Y] (f : C(X, Y)) : Top.of X ⟶ Top.of Y := f


section unbundled

variables {X : Type*} {A : set X} [topological_space X]

/-- The inclusion map `i : A → X` for `A ⊆ X` is just the restriction of `id X` to A. -/
def inclusion (X : Type*) (A : set X) [topological_space X] :
  C(A, X) := ⟨set.restrict A id⟩

/-- A continuous map `r : X → A` for `A ⊆ X` is a topological retraction when it is the identity
when restricted to A. -/
structure is_top_retraction (r : X → A) extends continuous r : Prop :=
(id_of_retraction_of_inclusion : r ∘ (inclusion X A) = id)

/-- A topological retraction is continuous by definition. -/
lemma is_top_retraction.continuous {r : X → A} (hr : is_top_retraction r) :
  continuous r := hr.to_continuous

end unbundled


/-- The bundled form of `is_top_retraction`. -/
structure top_retraction (X : Type*) (A : set X) [topological_space X] :=
(to_fun : X → A)
(top_retraction' : is_top_retraction to_fun)


namespace top_retraction

variables {X : Type*} {A : set X} [topological_space X]

/-- Helper to coerce a topological retraction to a continuous map. -/
def to_continuous_map (r : top_retraction X A) : C(X, subtype A) :=
{ to_fun := r.to_fun,
  continuous_to_fun := r.top_retraction'.continuous }

/-- Coercing a topological retraction `to_fun` is the same as coercing it to a continuous map
and then to a function. -/
lemma coe_continuous_map_eq_to_fun (r : top_retraction X A) :
  ⇑r.to_continuous_map = r.to_fun := rfl

/-- A topological retraction is a continuous map. -/
@[priority 100]
instance top_retraction.continuous_map_class :
  continuous_map_class (top_retraction X A) X (subtype A) :=
{ coe := top_retraction.to_fun,
  coe_injective' := λ r s h, by { cases r, cases s, congr' },
  map_continuous := λ r, r.top_retraction'.continuous }

/-- The identity function, interpreted as a top_retraction. -/
protected def id : top_retraction X set.univ :=
{ to_fun := (equiv.set.univ X).symm,
  top_retraction' := by obviously }

/-- There is always a top_retraction from a space to itself, namely `id`. -/
instance : inhabited (top_retraction X set.univ) := ⟨top_retraction.id⟩

/-- We show that if a topological retraction `r : X → A` exists, then the inclusion map `i : A → X`
is a split monomorphism in the category Top. -/
def split_mono_of_inclusion (r : top_retraction X A) :
  split_mono (Top.hom_of_continuous_map (inclusion X A)) :=
{ retraction := r.to_continuous_map,
  id' := begin
    apply fun_like.ext,
    exact λ x, congr_fun r.top_retraction'.id_of_retraction_of_inclusion x,
  end, }

/-- We show that a topological retraction `r : X → A` is a split epimorphism in the category Top. -/
def split_epi_of_retraction (r : top_retraction X A) :
  split_epi (Top.hom_of_continuous_map r.to_continuous_map) :=
{ section_ := inclusion X A,
  id' := begin
    apply fun_like.ext,
    exact λ x, congr_fun r.top_retraction'.id_of_retraction_of_inclusion x,
  end, }

/-- We show that if a topological retraction `r : X → A` exists, then the induced arrow between
fundamental groupoids of the inclusion map `i : A → X` is split monomorphism in the category
Groupoid. -/
def fundamental_groupoid_split_mono (r : top_retraction X A) :
  split_mono (πₘ (Top.hom_of_continuous_map (inclusion X A))) :=
split_mono.map (split_mono_of_inclusion r) fundamental_groupoid_functor

/-- We show that the induced arrow between fundamental groupoids of the topological retraction
`r : X → A` is a split epimorphism in the category Groupoid. -/
def fundamental_groupoid_split_epi (r : top_retraction X A) :
  split_epi (πₘ (Top.hom_of_continuous_map r.to_continuous_map)) :=
split_epi.map (split_epi_of_retraction r) fundamental_groupoid_functor

/-- We show that the induced arrow of the topological retraction `r : X → A` in the fundamental
groupoid is an epimorphism. -/
lemma fundamental_groupoid_epi_of_top_retraction (r : top_retraction X A) :
  epi (πₘ (Top.hom_of_continuous_map r.to_continuous_map)) :=
split_epi.epi (fundamental_groupoid_split_epi r)

end top_retraction


section surjection

/-- We show that there is no surjective homomorphism from the trivial group to ℤ. -/
lemma not_surj_hom_of_unit_to_int (f : unit →* (multiplicative ℤ)) : ¬function.surjective f :=
not_surjective_finite_infinite f

/-- We show that there is no surjection from the trivial group to ℤ by showing that the arrow
between these objects in Group is not an epimorphism. -/
lemma not_epi_of_unit_to_int (f : Group.of unit ⟶ Group.of (multiplicative ℤ)) : ¬epi f :=
begin
  rw Group.epi_iff_surjective,
  exact not_surj_hom_of_unit_to_int f,
end

end surjection
