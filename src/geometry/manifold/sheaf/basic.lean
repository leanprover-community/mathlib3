/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.local_invariant_properties
import topology.sheaves.local_predicate

/-! # Generic construction of a sheaf from a `local_invariant_prop` on a manifold -/

open_locale manifold topology
open set topological_space structure_groupoid structure_groupoid.local_invariant_prop opposite

universe u

variables {H : Type*} [topological_space H] {H' : Type*} [topological_space H']
  {G : structure_groupoid H} {G' : structure_groupoid H'}
  {P : (H → H') → (set H) → H → Prop}
  (M : Type u) [topological_space M] [charted_space H M]
  (M' : Type u) [topological_space M'] [charted_space H' M']

instance Top.of.charted_space : charted_space H (Top.of M) := (infer_instance : charted_space H M)

instance Top.of.has_groupoid [has_groupoid M G] : has_groupoid (Top.of M) G :=
(infer_instance : has_groupoid M G)

/-- Let `P` be a `local_invariant_prop` for functions between spaces with the groupoids `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupoids.  Then there is
an induced `local_predicate` on the functions from `M` to `M'`, given by `lift_prop P`. -/
def local_predicate_of_local_invariant_prop (hG : local_invariant_prop G G' P) :
  Top.local_predicate (λ (x : Top.of M), M') :=
{ pred := λ {U : opens (Top.of M)}, λ (f : U → M'), lift_prop P f,
  res := begin
    intros U V i f h x,
    have hUV : U ≤ V := category_theory.le_of_hom i,
    show lift_prop_at P (f ∘ set.inclusion hUV) x,
    rw ← hG.lift_prop_at_iff_comp_inclusion hUV,
    apply h,
  end,
  locality := begin
    intros V f h x,
    obtain ⟨U, hxU, i, hU : lift_prop P (f ∘ i)⟩ := h x,
    let x' : U := ⟨x, hxU⟩,
    have hUV : U ≤ V := category_theory.le_of_hom i,
    have : lift_prop_at P f (inclusion hUV x'),
    { rw hG.lift_prop_at_iff_comp_inclusion hUV,
      exact hU x' },
    convert this,
    ext1,
    refl
  end }

/-- Let `P` be a `local_invariant_prop` for functions between spaces with the groupoids `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupoids.  Then there is
a presheaf of types on `M` which, to each open set `U` in `M`, associates the type of bundled
functions from `U` to `M'` satisfying the lift of `P`. -/
def structure_groupoid.local_invariant_prop.sheaf (hG : local_invariant_prop G G' P) :
  Top.sheaf (Type u) (Top.of M) :=
Top.subsheaf_to_Types (local_predicate_of_local_invariant_prop M M' hG)

instance structure_groupoid.local_invariant_prop.sheaf_has_coe_to_fun
  (hG : local_invariant_prop G G' P) (U : (opens (Top.of M))ᵒᵖ) :
  has_coe_to_fun ((hG.sheaf M M').val.obj U) (λ _, (unop U) → M') :=
{ coe := λ a, a.1 }

lemma structure_groupoid.local_invariant_prop.section_spec (hG : local_invariant_prop G G' P)
  (U : (opens (Top.of M))ᵒᵖ) (f : (hG.sheaf M M').val.obj U) :
  lift_prop P f :=
f.2
