/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.local_invariant_properties
import topology.sheaves.sheaf_condition.unique_gluing

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

/-- Let `P` be a `local_invariant_prop` for functions between spaces with the groupoids `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupoids.  Then there is
a presheaf of types on `M` which, to each open set `U` in `M`, associates the type of bundled
functions from `U` to `M'` satisfying `P`. -/
noncomputable def structure_groupoid.local_invariant_prop.presheaf
  (hG : local_invariant_prop G G' P) : Top.presheaf (Type u) (Top.of M) :=
{ obj := λ U, hG.bundled_functions (unop U : opens M) M',
  map := λ V U i f,
  { to_fun := f ∘ i.unop,
    property' := begin
      intros x,
      have hUV : unop U ≤ unop V := category_theory.le_of_hom i.unop,
      show lift_prop_at P (f ∘ set.inclusion hUV) x,
      rw ← hG.lift_prop_at_iff_comp_inclusion hUV,
      exact f.property _,
    end } }

/-- Let `P` be a `local_invariant_prop` for functions between spaces with the groupoids `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupoids.  Then the
presheaf of types `hG.presheaf M M'` on `M` satisfies the sheaf condition. -/
lemma structure_groupoid.local_invariant_prop.is_sheaf (hG : local_invariant_prop G G' P) :
  (hG.presheaf M M').is_sheaf :=
(hG.presheaf M M').is_sheaf_of_is_sheaf_unique_gluing_types $ λ ι U sf sf_comp,
begin
  -- We show the sheaf condition in terms of unique gluing.
  -- First we obtain a family of sections for the underlying sheaf of functions,
  -- by forgetting that the predicate holds
  let sf' : Π i : ι, U i → M' := λ i, ⇑(id (sf i) : hG.bundled_functions (U i) M'),
  -- Since our original family is compatible, this one is as well
  have sf'_comp :
    ∀ (i j : ι) (x : M) (hxi : x ∈ ↑(U i)) (hxj : x ∈ ↑(U j)), sf' i ⟨x, hxi⟩ = sf' j ⟨x, hxj⟩,
  { intros i j x hxi hxj,
    let X : (U i ⊓ U j : opens M) := ⟨x, ⟨hxi, hxj⟩⟩,
    exact congr_arg (λ f, f X : hG.bundled_functions (U i ⊓ U j : opens M) M' → M') (sf_comp i j) },
  have hU : ((supr U : opens M) : set M) = ⋃ i : ι, ((id (U i) : opens M) : set M) :=
    topological_space.opens.coe_supr _,
  -- So, we can obtain a candidate unique gluing `gl` from the `set.Union_lift` construction
  let gl := set.Union_lift _ sf' sf'_comp _ hU.le,
  have gl_eq : ∀ (i : ι) (x : U i), gl (opens.le_supr U i x) = sf' i x,
  { intros i x,
    exact Union_lift_inclusion _ (le_supr U i) },
  refine ⟨⟨gl, _⟩, _, _⟩,
  { -- condition 1: `gl` satisfies `lift_prop P`
    rintros ⟨x, mem : x ∈ supr U⟩,
    -- At any particular point `x` in `supr U`, we can select some open set `x ∈ U i`.
    choose i hi using opens.mem_supr.mp mem,
    have h : U i ≤ supr U := le_supr U i,
    -- We claim that the predicate holds in `U i`
    show lift_prop_at P gl (inclusion h ⟨x, hi⟩),
    rw hG.lift_prop_at_iff_comp_inclusion h,
    -- This follows, since our original family `sf` satisfies the predicate
    convert (sf i).property ⟨x, hi⟩ using 1,
    exact funext (gl_eq i) },
  { -- condition 2: `gl` is really a gluing for the subsheaf
    intro i,
    ext x,
    exact gl_eq i x },
  { -- condition 3: `gl` is unique
    intros gl' hgl',
    ext1 ⟨x, hx : x ∈ ((supr U : opens M) : set M)⟩,
    rw [hU, mem_Union] at hx,
    obtain ⟨i, hi⟩ := hx,
    let X : U i := ⟨x, hi⟩,
    refine (congr_arg (λ f, f X : hG.bundled_functions (U i : opens M) M' → M') (hgl' i)).trans _,
    exact (gl_eq i X).symm },
end

/-- Let `P` be a `local_invariant_prop` for functions between spaces with the groupoids `G`, `G'`
and let `M`, `M'` be charted spaces modelled on the model spaces of those groupoids.  Then there is
a presheaf of types on `M` which, to each open set `U` in `M`, associates the type of bundled
functions from `U` to `M'` satisfying `P`. -/
noncomputable def structure_groupoid.local_invariant_prop.sheaf (hG : local_invariant_prop G G' P) :
  Top.sheaf (Type u) (Top.of M) :=
{ val := hG.presheaf M M',
  cond := hG.is_sheaf M M' }

noncomputable instance structure_groupoid.local_invariant_prop.sheaf_has_coe_to_fun
  (hG : local_invariant_prop G G' P) (U : (opens (Top.of M))ᵒᵖ) :
  has_coe_to_fun ((hG.sheaf M M').val.obj U) (λ _, (unop U : opens M) → M') :=
structure_groupoid.local_invariant_prop.bundled_functions.has_coe_to_fun hG (unop U : opens M) M'

lemma structure_groupoid.local_invariant_prop.section_spec (hG : local_invariant_prop G G' P)
  (U : (opens (Top.of M))ᵒᵖ) (f : (hG.sheaf M M').val.obj U) :
  lift_prop P f :=
f.property
