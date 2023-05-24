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
{HM : Type*} [topological_space HM] (IM : model_with_corners 𝕜 E HM)
variables {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E' H)
(M : Type u) [topological_space M] [charted_space HM M] [smooth_manifold_with_corners IM M]
(N G A R : Type u) [topological_space N] [charted_space H N]
[topological_space G] [charted_space H G] [topological_space A] [charted_space H A]
[topological_space R] [charted_space H R]

section type
variables [smooth_manifold_with_corners I N]

/-- The sheaf of differentiable functions from `M` to `N`, as a sheaf of types. -/
def mdifferentiable_sheaf : Top.sheaf (Type u) (Top.of M) :=
(differentiable_within_at_local_invariant_prop IM I).sheaf M N

instance mdifferentiable_sheaf.has_coe_to_fun (U : (opens (Top.of M))ᵒᵖ) :
  has_coe_to_fun ((mdifferentiable_sheaf IM I M N).val.obj U) (λ _, unop U → N) :=
obj.has_coe_to_fun M N _ U

lemma mdifferentiable_sheaf.section_spec
  (U : (opens (Top.of M))ᵒᵖ) (f : (mdifferentiable_sheaf IM I M N).val.obj U) :
  mdifferentiable IM I f :=
begin
  intro x,
  rw mdifferentiable_at_iff_lift_prop_at,
  exact (differentiable_within_at_local_invariant_prop IM I).section_spec _ _ _ _ x
end

variables {IM I M N}

lemma mdifferentiable_section {U : (opens (Top.of M))ᵒᵖ}
  (f : (mdifferentiable_sheaf IM I M N).val.obj U) :
  mdifferentiable IM I f :=
begin
  intros x,
  rw mdifferentiable_at_iff_lift_prop_at,
  exact f.2 x,
end

instance Top.of.smooth_manifold_with_corners : smooth_manifold_with_corners IM (Top.of M) :=
(by apply_instance : smooth_manifold_with_corners IM M)

end type

section lie_group
variables [group G] [lie_group I G]

@[to_additive]
instance (U : (opens (Top.of M))ᵒᵖ) : group ((mdifferentiable_sheaf IM I M G).val.obj U) :=
subgroup.to_group $
  differentiable_within_at_local_invariant_prop_subgroup IM ((unop U : opens (Top.of M))) I G

/-- The presheaf of differentiable functions from `M` to `G`, for `G` a Lie group, as a presheaf
of groups. -/
@[to_additive mdifferentiable_presheaf_AddGroup]
def mdifferentiable_presheaf_Group : Top.presheaf Group.{u} (Top.of M) :=
{ obj := λ U, Group.of ((mdifferentiable_sheaf IM I M G).val.obj U),
  map := λ U V h, Group.of_hom $
    differentiable_within_at_local_invariant_prop_subgroup_restrict IM I G $
    category_theory.le_of_hom h.unop,
  map_id' := begin
    intro U,
    ext ⟨_, _⟩ ⟨_, _⟩,
    refl,
  end,
  map_comp' := begin
    intros U V W f g,
    ext1,
    refl,
  end }

/-- The sheaf of differentiable functions from `M` to `G`, for `G` a Lie group, as a sheaf of
groups. -/
@[to_additive mdifferentiable_sheaf_AddGroup]
def mdifferentiable_sheaf_Group : Top.sheaf Group.{u} (Top.of M) :=
{ val := mdifferentiable_presheaf_Group IM I M G,
  cond := begin
    change category_theory.presheaf.is_sheaf _ _,
    rw category_theory.presheaf.is_sheaf_iff_is_sheaf_forget _ _ (category_theory.forget Group),
    { exact category_theory.Sheaf.cond (mdifferentiable_sheaf IM I M G) },
    { apply_instance },
  end }

end lie_group

section comm_lie_group
variables [comm_group A] [lie_group I A]

@[to_additive]
instance (U : (opens (Top.of M))ᵒᵖ) : comm_group ((mdifferentiable_sheaf IM I M A).val.obj U) :=
subgroup.to_comm_group $
  differentiable_within_at_local_invariant_prop_subgroup IM ((unop U : opens (Top.of M))) I A

/-- The presheaf of differentiable functions from `M` to `A`, for `A` an abelian Lie group, as a
presheaf of abelian groups. -/
@[to_additive mdifferentiable_presheaf_AddCommGroup "The presheaf of differentiable functions from
`M` to `A`, for `A` an abelian additive Lie group, as a presheaf of abelian additive groups."]
def mdifferentiable_presheaf_CommGroup : Top.presheaf CommGroup.{u} (Top.of M) :=
{ obj := λ U, CommGroup.of ((mdifferentiable_sheaf IM I M A).val.obj U),
  map := λ U V h, CommGroup.of_hom $
    differentiable_within_at_local_invariant_prop_subgroup_restrict IM I A $
    category_theory.le_of_hom h.unop,
  map_id' := begin
    intro U,
    ext ⟨_, _⟩ ⟨_, _⟩,
    refl,
  end,
  map_comp' := begin
    intros U V W f g,
    ext1,
    refl,
  end }

/-- The sheaf of differentiable functions from `M` to `A`, for `A` an abelian Lie group, as a
sheaf of abelian groups. -/
@[to_additive mdifferentiable_sheaf_AddCommGroup "The sheaf of differentiable functions from `M` to
`A`, for `A` an abelian additive Lie group, as a sheaf of abelian additive groups."]
def mdifferentiable_sheaf_CommGroup : Top.sheaf CommGroup.{u} (Top.of M) :=
{ val := mdifferentiable_presheaf_CommGroup IM I M A,
  cond := begin
    change category_theory.presheaf.is_sheaf _ _,
    rw category_theory.presheaf.is_sheaf_iff_is_sheaf_forget _ _ (category_theory.forget CommGroup),
    { exact category_theory.Sheaf.cond (mdifferentiable_sheaf IM I M A) },
    { apply_instance },
  end }

end comm_lie_group

section smooth_ring
variables [ring R] [smooth_ring I R]

instance (U : (opens (Top.of M))ᵒᵖ) : ring ((mdifferentiable_sheaf IM I M R).val.obj U) :=
subring.to_ring $
  differentiable_within_at_local_invariant_prop_subring IM ((unop U : opens (Top.of M))) I R

/-- The presheaf of differentiable functions from `M` to `R`, for `R` a smooth ring, as a presheaf
of rings. -/
def mdifferentiable_presheaf_Ring : Top.presheaf Ring.{u} (Top.of M) :=
{ obj := λ U, Ring.of ((mdifferentiable_sheaf IM I M R).val.obj U),
  map := λ U V h, Ring.of_hom $
    differentiable_within_at_local_invariant_prop_subring_restrict IM I R $
    category_theory.le_of_hom h.unop,
  map_id' := begin
    intro U,
    ext ⟨_, _⟩ ⟨_, _⟩,
    refl,
  end,
  map_comp' := begin
    intros U V W f g,
    ext1,
    refl,
  end }

/-- The sheaf of differentiable functions from `M` to `R`, for `R` a smooth ring, as a sheaf of
rings. -/
def mdifferentiable_sheaf_Ring : Top.sheaf Ring.{u} (Top.of M) :=
{ val := mdifferentiable_presheaf_Ring IM I M R,
  cond := begin
    change category_theory.presheaf.is_sheaf _ _,
    rw category_theory.presheaf.is_sheaf_iff_is_sheaf_forget _ _ (category_theory.forget Ring),
    { exact category_theory.Sheaf.cond (mdifferentiable_sheaf IM I M R) },
    { apply_instance },
  end }

example : (category_theory.Sheaf_compose _ (category_theory.forget Ring)).obj
  (mdifferentiable_sheaf_Ring.{u} IM I M R) =
  (mdifferentiable_sheaf IM I M R) := rfl

end smooth_ring
