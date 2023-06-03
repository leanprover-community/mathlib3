/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.sheaf.basic
import geometry.manifold.algebra.smooth_functions
import category_theory.sites.whiskering

/-! # The sheaf of smooth functions on a manifold -/

noncomputable theory
open_locale manifold
open topological_space opposite

universe u

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{EM : Type*} [normed_add_comm_group EM] [normed_space 𝕜 EM]
{HM : Type*} [topological_space HM] (IM : model_with_corners 𝕜 EM HM)
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E H')
(M : Type u) [topological_space M] [charted_space HM M]
(N G A A' R : Type u) [topological_space N] [charted_space H N]
[topological_space G] [charted_space H G] [topological_space A] [charted_space H A]
[topological_space A'] [charted_space H' A'] [topological_space R] [charted_space H R]

section type

/-- The sheaf of smooth functions from `M` to `N`, as a sheaf of types. -/
def smooth_sheaf : Top.sheaf (Type u) (Top.of M) :=
(cont_diff_within_at_local_invariant_prop IM I ⊤).sheaf M N

instance smooth_sheaf.has_coe_to_fun (U : (opens (Top.of M))ᵒᵖ) :
  has_coe_to_fun ((smooth_sheaf IM I M N).val.obj U) (λ _, unop U → N) :=
(cont_diff_within_at_local_invariant_prop IM I ⊤).sheaf_has_coe_to_fun _ _ _

/-- The object of `smooth_sheaf IM I M N` for the open set `U` in `M` is
`C^∞⟮IM, (unop U : opens M); I, N⟯`, the `(IM, I)`-smooth functions from `U` to `N`.  This is not
just a "moral" equality but a literal and definitional equality! -/
lemma smooth_sheaf.obj_eq (U : (opens (Top.of M))ᵒᵖ) :
  (smooth_sheaf IM I M N).val.obj U = C^∞⟮IM, (unop U : opens M); I, N⟯ := rfl

lemma smooth_sheaf.section_spec (U : (opens (Top.of M))ᵒᵖ) (f : (smooth_sheaf IM I M N).val.obj U) :
  smooth IM I f :=
(cont_diff_within_at_local_invariant_prop IM I ⊤).section_spec _ _ _ _

variables {IM I M N}

lemma smooth_section {U : (opens (Top.of M))ᵒᵖ} (f : (smooth_sheaf IM I M N).val.obj U) :
  smooth IM I f :=
(cont_diff_within_at_local_invariant_prop IM I ⊤).section_spec _ _ _ _

end type

section lie_group
variables [group G] [lie_group I G]

@[to_additive]
instance (U : (opens (Top.of M))ᵒᵖ) : group ((smooth_sheaf IM I M G).val.obj U) :=
(smooth_map.group : group C^∞⟮IM, (unop U : opens M); I, G⟯)

/-- The presheaf of smooth functions from `M` to `G`, for `G` a Lie group, as a presheaf
of groups. -/
@[to_additive smooth_presheaf_AddGroup "The presheaf of smooth functions from `M` to `G`, for `G` an
additive Lie group, as a presheaf of additive groups."]
def smooth_presheaf_Group : Top.presheaf Group.{u} (Top.of M) :=
{ obj := λ U, Group.of ((smooth_sheaf IM I M G).val.obj U),
  map := λ U V h, Group.of_hom $
    smooth_map.restrict_monoid_hom IM I G $ category_theory.le_of_hom h.unop,
  map_id' := begin
    intro U,
    ext ⟨_, _⟩ ⟨_, _⟩,
    refl,
  end,
  map_comp' := λ U V W f g, rfl }

/-- The sheaf of smooth functions from `M` to `G`, for `G` a Lie group, as a sheaf of
groups. -/
@[to_additive smooth_sheaf_AddGroup "The sheaf of smooth functions from `M` to `G`, for `G` an
additive Lie group, as a sheaf of additive groups."]
def smooth_sheaf_Group : Top.sheaf Group.{u} (Top.of M) :=
{ val := smooth_presheaf_Group IM I M G,
  cond := begin
    change category_theory.presheaf.is_sheaf _ _,
    rw category_theory.presheaf.is_sheaf_iff_is_sheaf_forget _ _ (category_theory.forget Group),
    { exact category_theory.Sheaf.cond (smooth_sheaf IM I M G) },
    { apply_instance },
  end }

end lie_group

section comm_lie_group
variables [comm_group A] [comm_group A'] [lie_group I A] [lie_group I' A']

@[to_additive]
instance (U : (opens (Top.of M))ᵒᵖ) : comm_group ((smooth_sheaf IM I M A).val.obj U) :=
(smooth_map.comm_group : comm_group C^∞⟮IM, (unop U : opens M); I, A⟯)

/-- The presheaf of smooth functions from `M` to `A`, for `A` an abelian Lie group, as a
presheaf of abelian groups. -/
@[to_additive smooth_presheaf_AddCommGroup "The presheaf of smooth functions from
`M` to `A`, for `A` an abelian additive Lie group, as a presheaf of abelian additive groups."]
def smooth_presheaf_CommGroup : Top.presheaf CommGroup.{u} (Top.of M) :=
{ obj := λ U, CommGroup.of ((smooth_sheaf IM I M A).val.obj U),
  map := λ U V h, CommGroup.of_hom $
    smooth_map.restrict_monoid_hom IM I A $ category_theory.le_of_hom h.unop,
  map_id' := begin
    intro U,
    ext ⟨_, _⟩ ⟨_, _⟩,
    refl,
  end,
  map_comp' := λ U V W f g, rfl }

/-- The sheaf of smooth functions from `M` to `A`, for `A` an abelian Lie group, as a
sheaf of abelian groups. -/
@[to_additive smooth_sheaf_AddCommGroup "The sheaf of smooth functions from `M` to
`A`, for `A` an abelian additive Lie group, as a sheaf of abelian additive groups."]
def smooth_sheaf_CommGroup : Top.sheaf CommGroup.{u} (Top.of M) :=
{ val := smooth_presheaf_CommGroup IM I M A,
  cond := begin
    change category_theory.presheaf.is_sheaf _ _,
    rw category_theory.presheaf.is_sheaf_iff_is_sheaf_forget _ _ (category_theory.forget CommGroup),
    { exact category_theory.Sheaf.cond (smooth_sheaf IM I M A) },
    { apply_instance },
  end }

/-- For a manifold `M` and a smooth homomorphism `φ` between abelian Lie groups `A`, `A'`, the
'left-composition-by-`φ`' morphism of sheaves from `smooth_sheaf_CommGroup IM I M A` to
`smooth_sheaf_CommGroup IM I' M A'`. -/
@[to_additive "For a manifold `M` and a smooth homomorphism `φ` between abelian additive Lie groups
`A`, `A'`, the 'left-composition-by-`φ`' morphism of sheaves from
`smooth_sheaf_AddCommGroup IM I M A` to `smooth_sheaf_AddCommGroup IM I' M A'`."]
def smooth_sheaf_CommGroup.comp_left (φ : A →* A') (hφ : smooth I I' φ) :
  smooth_sheaf_CommGroup IM I M A ⟶ smooth_sheaf_CommGroup IM I' M A' :=
category_theory.Sheaf.hom.mk $
{ app := λ U, CommGroup.of_hom $ smooth_map.comp_left_monoid_hom _ _ φ hφ,
  naturality' := λ U V f, rfl }

end comm_lie_group

section smooth_ring
variables [ring R] [smooth_ring I R]

instance (U : (opens (Top.of M))ᵒᵖ) : ring ((smooth_sheaf IM I M R).val.obj U) :=
(smooth_map.ring : ring C^∞⟮IM, (unop U : opens M); I, R⟯)

/-- The presheaf of smooth functions from `M` to `R`, for `R` a smooth ring, as a presheaf
of rings. -/
def smooth_presheaf_Ring : Top.presheaf Ring.{u} (Top.of M) :=
{ obj := λ U, Ring.of ((smooth_sheaf IM I M R).val.obj U),
  map := λ U V h, Ring.of_hom $
    smooth_map.restrict_ring_hom IM I R $ category_theory.le_of_hom h.unop,
  map_id' := begin
    intro U,
    ext ⟨_, _⟩ ⟨_, _⟩,
    refl,
  end,
  map_comp' := λ U V W f g, rfl }

/-- The sheaf of smooth functions from `M` to `R`, for `R` a smooth ring, as a sheaf of
rings. -/
def smooth_sheaf_Ring : Top.sheaf Ring.{u} (Top.of M) :=
{ val := smooth_presheaf_Ring IM I M R,
  cond := begin
    change category_theory.presheaf.is_sheaf _ _,
    rw category_theory.presheaf.is_sheaf_iff_is_sheaf_forget _ _ (category_theory.forget Ring),
    { exact category_theory.Sheaf.cond (smooth_sheaf IM I M R) },
    { apply_instance },
  end }

end smooth_ring

section smooth_comm_ring
variables [comm_ring R] [smooth_ring I R]

instance (U : (opens (Top.of M))ᵒᵖ) : comm_ring ((smooth_sheaf IM I M R).val.obj U) :=
(smooth_map.comm_ring : comm_ring C^∞⟮IM, (unop U : opens M); I, R⟯)

/-- The presheaf of smooth functions from `M` to `R`, for `R` a smooth commutative ring, as a
presheaf of commutative rings. -/
def smooth_presheaf_CommRing : Top.presheaf CommRing.{u} (Top.of M) :=
{ obj := λ U, CommRing.of ((smooth_sheaf IM I M R).val.obj U),
  map := λ U V h, CommRing.of_hom $
    smooth_map.restrict_ring_hom IM I R $ category_theory.le_of_hom h.unop,
  map_id' := begin
    intro U,
    ext ⟨_, _⟩ ⟨_, _⟩,
    refl,
  end,
  map_comp' := λ U V W f g, rfl }

/-- The sheaf of smooth functions from `M` to `R`, for `R` a smooth commutative ring, as a sheaf of
commutative rings. -/
def smooth_sheaf_CommRing : Top.sheaf CommRing.{u} (Top.of M) :=
{ val := smooth_presheaf_CommRing IM I M R,
  cond := begin
    change category_theory.presheaf.is_sheaf _ _,
    rw category_theory.presheaf.is_sheaf_iff_is_sheaf_forget _ _ (category_theory.forget CommRing),
    { exact category_theory.Sheaf.cond (smooth_sheaf IM I M R) },
    { apply_instance },
  end }

-- sanity check: applying the `CommRing`-to-`Type` forgetful functor to the sheaf-of-rings of smooth
-- functions gives the sheaf-of-types of smooth functions.
example : (category_theory.Sheaf_compose _ (category_theory.forget CommRing)).obj
  (smooth_sheaf_CommRing.{u} IM I M R) =
  (smooth_sheaf IM I M R) := rfl

end smooth_comm_ring
