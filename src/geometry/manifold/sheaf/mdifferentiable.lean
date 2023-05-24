/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.sheaf.basic
import geometry.manifold.algebra.mdifferentiable
import category_theory.sites.whiskering

/-! # The sheaf of differentiable functions on a manifold -/

noncomputable theory
open_locale manifold
open topological_space opposite

universe u

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
variables {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
(M : Type u) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(M' : Type u) [topological_space M'] [charted_space H' M']

section type
variables [smooth_manifold_with_corners I' M']

/-- The sheaf of differentiable functions from `M` to `M'`, as a sheaf of types. -/
def mdifferentiable_sheaf : Top.sheaf (Type u) (Top.of M) :=
(differentiable_within_at_local_invariant_prop I I').sheaf M M'

instance mdifferentiable_sheaf.has_coe_to_fun (U : (opens (Top.of M))ᵒᵖ) :
  has_coe_to_fun ((mdifferentiable_sheaf I I' M M').val.obj U) (λ _, unop U → M') :=
obj.has_coe_to_fun M M' _ U

lemma mdifferentiable_sheaf.section_spec
  (U : (opens (Top.of M))ᵒᵖ) (f : (mdifferentiable_sheaf I I' M M').val.obj U) :
  mdifferentiable I I' f :=
begin
  intro x,
  rw mdifferentiable_at_iff_lift_prop_at,
  exact (differentiable_within_at_local_invariant_prop I I').section_spec _ _ _ _ x
end

variables {I I' M M'}

lemma mdifferentiable_section {U : (opens (Top.of M))ᵒᵖ}
  (f : (mdifferentiable_sheaf I I' M M').val.obj U) :
  mdifferentiable I I' f :=
begin
  intros x,
  rw mdifferentiable_at_iff_lift_prop_at,
  exact f.2 x,
end

instance Top.of.smooth_manifold_with_corners : smooth_manifold_with_corners I (Top.of M) :=
(by apply_instance : smooth_manifold_with_corners I M)

end type

section lie_group
variables [group M'] [lie_group I' M']

instance (U : (opens (Top.of M))ᵒᵖ) : group ((mdifferentiable_sheaf I I' M M').val.obj U) :=
subgroup.to_group $
  differentiable_within_at_local_invariant_prop_subgroup I ((unop U : opens (Top.of M))) I' M'

/-- The presheaf of differentiable functions from `M` to `M'`, for `M'` a Lie group, as a presheaf
of groups. -/
def mdifferentiable_presheaf_Group : Top.presheaf Group.{u} (Top.of M) :=
{ obj := λ U, Group.of ((mdifferentiable_sheaf I I' M M').val.obj U),
  map := λ U V h, Group.of_hom $
    differentiable_within_at_local_invariant_prop_subgroup_restrict I I' M' $
    category_theory.le_of_hom h.unop,
  map_id' := begin
    intro U,
    ext ⟨_,_⟩ ⟨_,_⟩,
    refl,
  end,
  map_comp' := begin
    intros U V W f g,
    ext1,
    refl,
  end }

/-- The sheaf of differentiable functions from `M` to `M'`, for `M'` a Lie group, as a sheaf of
groups. -/
def mdifferentiable_sheaf_Group : Top.sheaf Group.{u} (Top.of M) :=
{ val := mdifferentiable_presheaf_Group I I' M M',
  cond := begin
    change category_theory.presheaf.is_sheaf _ _,
    rw category_theory.presheaf.is_sheaf_iff_is_sheaf_forget _ _ (category_theory.forget Group),
    { exact category_theory.Sheaf.cond (mdifferentiable_sheaf I I' M M') },
    { apply_instance },
  end }

end lie_group

section comm_lie_group
variables [comm_group M'] [lie_group I' M']

instance (U : (opens (Top.of M))ᵒᵖ) : comm_group ((mdifferentiable_sheaf I I' M M').val.obj U) :=
subgroup.to_comm_group $
  differentiable_within_at_local_invariant_prop_subgroup I ((unop U : opens (Top.of M))) I' M'

/-- The presheaf of differentiable functions from `M` to `M'`, for `M'` an abelian Lie group, as a
presheaf of abelian groups. -/
def mdifferentiable_presheaf_CommGroup : Top.presheaf CommGroup.{u} (Top.of M) :=
{ obj := λ U, CommGroup.of ((mdifferentiable_sheaf I I' M M').val.obj U),
  map := λ U V h, CommGroup.of_hom $
    differentiable_within_at_local_invariant_prop_subgroup_restrict I I' M' $
    category_theory.le_of_hom h.unop,
  map_id' := begin
    intro U,
    ext ⟨_,_⟩ ⟨_,_⟩,
    refl,
  end,
  map_comp' := begin
    intros U V W f g,
    ext1,
    refl,
  end }

/-- The sheaf of differentiable functions from `M` to `M'`, for `M'` an abelian Lie group, as a
sheaf of abelian groups. -/
def mdifferentiable_sheaf_CommGroup : Top.sheaf CommGroup.{u} (Top.of M) :=
{ val := mdifferentiable_presheaf_CommGroup I I' M M',
  cond := begin
    change category_theory.presheaf.is_sheaf _ _,
    rw category_theory.presheaf.is_sheaf_iff_is_sheaf_forget _ _ (category_theory.forget CommGroup),
    { exact category_theory.Sheaf.cond (mdifferentiable_sheaf I I' M M') },
    { apply_instance },
  end }

end comm_lie_group

section smooth_ring
variables [ring M'] [smooth_ring I' M']

instance (U : (opens (Top.of M))ᵒᵖ) : ring ((mdifferentiable_sheaf I I' M M').val.obj U) :=
subring.to_ring $
  differentiable_within_at_local_invariant_prop_subring I ((unop U : opens (Top.of M))) I' M'

/-- The presheaf of differentiable functions from `M` to `M'`, for `M'` a smooth ring, as a presheaf
of rings. -/
def mdifferentiable_presheaf_Ring : Top.presheaf Ring.{u} (Top.of M) :=
{ obj := λ U, Ring.of ((mdifferentiable_sheaf I I' M M').val.obj U),
  map := λ U V h, Ring.of_hom $
    differentiable_within_at_local_invariant_prop_subring_restrict I I' M' $
    category_theory.le_of_hom h.unop,
  map_id' := begin
    intro U,
    ext ⟨_,_⟩ ⟨_,_⟩,
    refl,
  end,
  map_comp' := begin
    intros U V W f g,
    ext1,
    refl,
  end }

/-- The sheaf of differentiable functions from `M` to `M'`, for `M'` a smooth ring, as a sheaf of
rings. -/
def mdifferentiable_sheaf_Ring : Top.sheaf Ring.{u} (Top.of M) :=
{ val := mdifferentiable_presheaf_Ring I I' M M',
  cond := begin
    change category_theory.presheaf.is_sheaf _ _,
    rw category_theory.presheaf.is_sheaf_iff_is_sheaf_forget _ _ (category_theory.forget Ring),
    { exact category_theory.Sheaf.cond (mdifferentiable_sheaf I I' M M') },
    { apply_instance },
  end }

example : (category_theory.Sheaf_compose _ (category_theory.forget Ring)).obj
  (mdifferentiable_sheaf_Ring.{u} I I' M M') =
  (mdifferentiable_sheaf I I' M M') := rfl

end smooth_ring
