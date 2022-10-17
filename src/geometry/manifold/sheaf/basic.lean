/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.local_invariant_properties
import topology.sheaves.local_predicate

/-! # Generic construction of a sheaf from a `local_invariant_prop` on a manifold -/

open_locale manifold topological_space
open set topological_space structure_groupoid structure_groupoid.local_invariant_prop opposite

variables {H : Type*} [topological_space H]
  {H' : Type*} [topological_space H']
  {G : structure_groupoid H} [closed_under_restriction G] {G' : structure_groupoid H'}
  (M : Type) [topological_space M] [charted_space H M] [has_groupoid M G]
  (M' : Type) [topological_space M'] [charted_space H' M'] [has_groupoid M' G']
  {P : (H → H') → (set H) → H → Prop}

instance Top.of.charted_space : charted_space H (Top.of M) :=
(by apply_instance : charted_space H M)

instance Top.of.has_groupoid : has_groupoid (Top.of M) G := (by apply_instance : has_groupoid M G)

/-- Let `M`, `M'` be charted spaces with transition functions in the groupoids `G`, `G'`, and let
`P` be a `local_invariant_prop` for functions between spaces with these groupoids.  Then there is an
induced `local_predicate` for the sheaf of functions from `M` to `M'`. -/
def local_predicate_of_local_invariant_prop (hG : local_invariant_prop G G' P) :
  Top.local_predicate (λ (x : Top.of M), M') :=
{ pred := λ {U : opens (Top.of M)}, λ (f : U → M'), lift_prop P f,
  res := begin
    intros U V i f h x,
    have hUV : U ≤ V := category_theory.le_of_hom i,
    let I : U → V := set.inclusion hUV,
    obtain ⟨h₁, h₂⟩ := h (I x),
    refine ⟨h₁.comp (continuous_inclusion hUV).continuous_within_at (maps_to_univ _ _), _⟩,
    sorry
    -- rw lift_prop_at at *,
    -- rw lift_prop_within_at at *,
    -- refine lift_prop_at_congr_of_eventually_eq hG (h (I x)) _,
    -- refine filter.eventually_eq_of_mem (is_open.mem_nhds U.prop hx) _,
    -- intros y hy,
    -- unfold extend,
    -- rw dif_pos hy,
    -- rw dif_pos (hUV hy),
    -- refl,
  end,
  locality := begin
    intros V f h x,
    sorry
    -- rcases h ⟨x, hx⟩ with ⟨U, hx, i, hU⟩,
    -- have hUV : U ≤ V := category_theory.le_of_hom i,
    -- refine lift_prop_at_congr_of_eventually_eq hG (hU x hx) _,
    -- refine filter.eventually_eq_of_mem (is_open.mem_nhds U.prop hx) _,
    -- intros y hy,
    -- unfold extend,
    -- rw dif_pos hy,
    -- rw dif_pos (hUV hy),
    -- refl,
  end }

def structure_groupoid.local_invariant_prop.sheaf (hG : local_invariant_prop G G' P) :
  Top.sheaf Type (Top.of M) :=
Top.subsheaf_to_Types (local_predicate_of_local_invariant_prop M M' hG)

instance (hG : local_invariant_prop G G' P) (U : (opens (Top.of M))ᵒᵖ) :
  has_coe_to_fun ((hG.sheaf M M').val.obj U) (λ _, (unop U) → M') :=
{ coe := λ a, a.1 }
