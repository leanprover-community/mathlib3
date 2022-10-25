/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.star.pi
import algebra.star.prod
import topology.algebra.group

/-!
# Continuity of `star`

This file defines the `has_continuous_star` typeclass, along with instances on `pi`, `prod`,
`mul_opposite`, and `units`.
-/


open_locale filter topological_space
open filter

universes u

variables {ι α R S : Type*}

/-- Basic hypothesis to talk about a topological space with a continuous `star` operator. -/
class has_continuous_star (R : Type u) [topological_space R] [has_star R] : Prop :=
(continuous_star : continuous (star : R → R))

export has_continuous_star (continuous_star)

section continuity

variables [topological_space R] [has_star R] [has_continuous_star R]

lemma continuous_on_star {s : set R} : continuous_on star s :=
continuous_star.continuous_on

lemma continuous_within_at_star {s : set R} {x : R} : continuous_within_at star s x :=
continuous_star.continuous_within_at

lemma continuous_at_star {x : R} : continuous_at star x :=
continuous_star.continuous_at

lemma tendsto_star (a : R) : tendsto star (𝓝 a) (𝓝 (star a)) :=
continuous_at_star

lemma filter.tendsto.star {f : α → R} {l : filter α} {y : R} (h : tendsto f l (𝓝 y)) :
  tendsto (λ x, star (f x)) l (𝓝 (star y)) :=
(continuous_star.tendsto y).comp h

variables [topological_space α] {f : α → R} {s : set α} {x : α}

@[continuity]
lemma continuous.star (hf : continuous f) : continuous (λ x, star (f x)) :=
continuous_star.comp hf

lemma continuous_at.star (hf : continuous_at f x) : continuous_at (λ x, star (f x)) x :=
continuous_at_star.comp hf

lemma continuous_on.star (hf : continuous_on f s) : continuous_on (λ x, star (f x)) s :=
continuous_star.comp_continuous_on hf

lemma continuous_within_at.star (hf : continuous_within_at f s x) :
  continuous_within_at (λ x, star (f x)) s x :=
hf.star

/-- The star operation bundled as a continuous map. -/
@[simps] def star_continuous_map : C(R, R) := ⟨star, continuous_star⟩

end continuity

section instances

instance [has_star R] [has_star S] [topological_space R] [topological_space S]
  [has_continuous_star R] [has_continuous_star S] : has_continuous_star (R × S) :=
⟨(continuous_star.comp continuous_fst).prod_mk (continuous_star.comp continuous_snd)⟩

instance {C : ι → Type*} [∀ i, topological_space (C i)]
  [∀ i, has_star (C i)] [∀ i, has_continuous_star (C i)] : has_continuous_star (Π i, C i) :=
{ continuous_star := continuous_pi (λ i, continuous.star (continuous_apply i)) }

instance [has_star R] [topological_space R] [has_continuous_star R] : has_continuous_star Rᵐᵒᵖ :=
⟨mul_opposite.continuous_op.comp $ mul_opposite.continuous_unop.star⟩

instance [monoid R] [star_semigroup R] [topological_space R] [has_continuous_star R] :
  has_continuous_star Rˣ :=
⟨continuous_induced_rng.2 units.continuous_embed_product.star⟩

end instances
