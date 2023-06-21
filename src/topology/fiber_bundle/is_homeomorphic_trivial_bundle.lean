/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.homeomorph

/-!
# Maps equivariantly-homeomorphic to projection in a product

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains the definition `is_homeomorphic_trivial_fiber_bundle F p`, a Prop saying that a
map `p : Z → B` between topological spaces is a "trivial fiber bundle" in the sense that there
exists a homeomorphism `h : Z ≃ₜ B × F` such that `proj x = (h x).1`.  This is an abstraction which
is occasionally convenient in showing that a map is open, a quotient map, etc.

This material was formerly linked to the main definition of fiber bundles, but after a series of
refactors, there is no longer a direct connection.
-/

variables {B : Type*} (F : Type*) {Z : Type*} [topological_space B] [topological_space F]
  [topological_space Z]

/-- A trivial fiber bundle with fiber `F` over a base `B` is a space `Z`
projecting on `B` for which there exists a homeomorphism to `B × F` that sends `proj`
to `prod.fst`. -/
def is_homeomorphic_trivial_fiber_bundle (proj : Z → B) : Prop :=
∃ e : Z ≃ₜ (B × F), ∀ x, (e x).1 = proj x

namespace is_homeomorphic_trivial_fiber_bundle
variables {F} {proj : Z → B}

protected lemma proj_eq (h : is_homeomorphic_trivial_fiber_bundle F proj) :
  ∃ e : Z ≃ₜ (B × F), proj = prod.fst ∘ e :=
⟨h.some, (funext h.some_spec).symm⟩

/-- The projection from a trivial fiber bundle to its base is surjective. -/
protected lemma surjective_proj [nonempty F] (h : is_homeomorphic_trivial_fiber_bundle F proj) :
  function.surjective proj :=
begin
  obtain ⟨e, rfl⟩ := h.proj_eq,
  exact prod.fst_surjective.comp e.surjective,
end

/-- The projection from a trivial fiber bundle to its base is continuous. -/
protected lemma continuous_proj (h : is_homeomorphic_trivial_fiber_bundle F proj) :
  continuous proj :=
begin
  obtain ⟨e, rfl⟩ := h.proj_eq,
  exact continuous_fst.comp e.continuous,
end

/-- The projection from a trivial fiber bundle to its base is open. -/
protected lemma is_open_map_proj (h : is_homeomorphic_trivial_fiber_bundle F proj) :
  is_open_map proj :=
begin
  obtain ⟨e, rfl⟩ := h.proj_eq,
  exact is_open_map_fst.comp e.is_open_map,
end

/-- The projection from a trivial fiber bundle to its base is open. -/
protected lemma quotient_map_proj [nonempty F] (h : is_homeomorphic_trivial_fiber_bundle F proj) :
  quotient_map proj :=
h.is_open_map_proj.to_quotient_map h.continuous_proj h.surjective_proj

end is_homeomorphic_trivial_fiber_bundle

/-- The first projection in a product is a trivial fiber bundle. -/
lemma is_homeomorphic_trivial_fiber_bundle_fst :
  is_homeomorphic_trivial_fiber_bundle F (prod.fst : B × F → B) :=
⟨homeomorph.refl _, λ x, rfl⟩

/-- The second projection in a product is a trivial fiber bundle. -/
lemma is_homeomorphic_trivial_fiber_bundle_snd :
  is_homeomorphic_trivial_fiber_bundle F (prod.snd : F × B → B) :=
⟨homeomorph.prod_comm _ _, λ x, rfl⟩
