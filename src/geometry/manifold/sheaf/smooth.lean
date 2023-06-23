/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import geometry.manifold.sheaf.basic
import geometry.manifold.algebra.smooth_functions
import category_theory.sites.whiskering
import algebra.category.Ring.filtered_colimits
import algebra.category.Ring.colimits

/-! # The sheaf of smooth functions on a manifold

The sheaf of `𝕜`-smooth functions from a manifold `M` to a manifold `N` can be defined as a sheaf of
types using the construction `structure_groupoid.local_invariant_prop.sheaf` from the file
`geometry.manifold.sheaf.basic`.  In this file we write that down (a one-liner), then do the work of
upgrading this to a sheaf of [groups]/[abelian groups]/[rings]/[commutative rings] when `N` carries
more algebraic structure.  For example, if `N` is `𝕜` then the sheaf of smooth functions from `M` to
`𝕜` is a sheaf of commutative rings, the *structure sheaf* of `M`.

## Main definitions

* `smooth_sheaf`: The sheaf of smooth functions from `M` to `N`, as a sheaf of types
* `smooth_sheaf.eval`: Canonical map onto `N` from the stalk of `smooth_sheaf IM I M N` at `x`,
  given by evaluating sections at `x`
* `smooth_sheaf_Group`, `smooth_sheaf_CommGroup`, `smooth_sheaf_Ring`, `smooth_sheaf_CommRing`: The
  sheaf of smooth functions into a [Lie group]/[abelian Lie group]/[smooth ring]/[smooth commutative
  ring], as a sheaf of [groups]/[abelian groups]/[rings]/[commutative rings]
* `smooth_sheaf_CommGroup.comp_left`: For a manifold `M` and a smooth homomorphism `φ` between
  abelian Lie groups `A`, `A'`, the 'postcomposition-by-`φ`' morphism of sheaves from
  `smooth_sheaf_CommGroup IM I M A` to `smooth_sheaf_CommGroup IM I' M A'`

## TODO

There are variants of `smooth_sheaf_CommGroup.comp_left` for `Group`, `Ring`, `CommRing`; this is
just boilerplate and can be added as needed.

The canonical "evaluation" map `smooth_sheaf.eval` from the stalk at `x:M` of the sheaf of smooth
functions `M → N` should be upgraded in the presence of algebraic structure on `N`: a group
homomorphism for `smooth_sheaf_Group` and `smooth_sheaf_CommGroup`, a ring homomorphism for
`smooth_sheaf_Ring` and `smooth_sheaf_CommRing`. This is blocked by some category theory TODOs: one
needs to identify as types the stalk at `x` of `smooth_sheaf_Group` (and similarly for the other
algebraic categories) with the stalk at `x` of `smooth_sheaf`, which should come from the fact that
the forgetful functor preserves filtered colimits.

Currently there is a universe restriction: one can consider the sheaf of smooth functions from `M`
to `N` only if `M` and `N` are in the same universe.  For example, since `ℂ` is in `Type`, we can
only consider the structure sheaf of complex manifolds in `Type`, which is unsatisfactory. The
obstacle here is in the underlying category theory constructions, and there is WIP (as of June 2023)
to fix this.  See
https://github.com/leanprover-community/mathlib/pull/19153
and cross-references there.
-/

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

variables {M}

instance smooth_sheaf.has_coe_to_fun (U : (opens (Top.of M))ᵒᵖ) :
  has_coe_to_fun ((smooth_sheaf IM I M N).val.obj U) (λ _, unop U → N) :=
(cont_diff_within_at_local_invariant_prop IM I ⊤).sheaf_has_coe_to_fun _ _ _

/-- The object of `smooth_sheaf IM I M N` for the open set `U` in `M` is
`C^∞⟮IM, (unop U : opens M); I, N⟯`, the `(IM, I)`-smooth functions from `U` to `N`.  This is not
just a "moral" equality but a literal and definitional equality! -/
lemma smooth_sheaf.obj_eq (U : (opens (Top.of M))ᵒᵖ) :
  (smooth_sheaf IM I M N).val.obj U = C^∞⟮IM, (unop U : opens M); I, N⟯ := rfl

/-- Canonical map from the stalk of `smooth_sheaf IM I M N` at `x` to `N`, given by evaluating
sections at `x`. -/
def smooth_sheaf.eval (x : M) : (smooth_sheaf IM I M N).presheaf.stalk x → N :=
Top.stalk_to_fiber _ x

/-- The `eval` map is surjective at `x`. -/
lemma smooth_sheaf.eval_surjective (x : M) : function.surjective (smooth_sheaf.eval IM I N x) :=
begin
  apply Top.stalk_to_fiber_surjective,
  intros n,
  exact ⟨⊤, λ _, n, smooth_const, rfl⟩,
end

variables {IM I N}

@[simp] lemma smooth_sheaf.eval_germ (U : opens (Top.of M)) (x : U)
  (f : (smooth_sheaf IM I M N).val.obj (op U)) :
  smooth_sheaf.eval IM I N (x : Top.of M) ((smooth_sheaf IM I M N).presheaf.germ x f)
  = f x :=
Top.stalk_to_fiber_germ _ U x f

lemma smooth_sheaf.smooth_section {U : (opens (Top.of M))ᵒᵖ}
  (f : (smooth_sheaf IM I M N).val.obj U) :
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

open category_theory
open category_theory.limits

-- TODO: rename
def eval_at (x : Top.of M) (U : open_nhds x) :
  (smooth_sheaf IM I M R).val.obj (opposite.op U.1) →+* R :=
{ to_fun := λ f, f ⟨x, U.2⟩,
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  map_add' := λ_ _, rfl }

def smooth_sheaf_CommRing.eval (x : Top.of M) :
  (smooth_sheaf_CommRing IM I M R).presheaf.stalk x ⟶
  CommRing.of R :=
begin
  refine category_theory.limits.colimit.desc _ ⟨_, ⟨λ U, _, _⟩⟩,
  { exact eval_at _ _ _ _ _ _ },
  { tidy }
end

-- The def above is a ring hom.
example (x : Top.of M) :
  (smooth_sheaf_CommRing IM I M R).presheaf.stalk x →+*
  CommRing.of R := smooth_sheaf_CommRing.eval _ _ _ _ _

def smooth_sheaf_CommRing.forget_stalk (x : Top.of M) :
  (category_theory.forget _).obj ((smooth_sheaf_CommRing IM I M R).presheaf.stalk x) ≅
  (smooth_sheaf IM I M R).presheaf.stalk x :=
category_theory.preserves_colimit_iso _ _

@[simp, reassoc, elementwise]
lemma smooth_sheaf_CommRing.forget_stalk_inv_comp_eval (x : Top.of M) :
  category_theory.category_struct.comp -- TODO: notation clash for `≫`
  (smooth_sheaf_CommRing.forget_stalk IM I M R x).inv (smooth_sheaf_CommRing.eval IM I M R x) =
  smooth_sheaf.eval _ _ _ _ :=
begin
  apply limits.colimit.hom_ext,
  intro U,
  dsimp only [smooth_sheaf_CommRing.forget_stalk],
  -- TODO: need to add some API to avoid these `erw`'s.
  erw [limits.colimit.ι_desc],
  erw [limits.colimit.ι_desc_assoc],
  erw [← (forget CommRing).map_comp],
  erw [limits.colimit.ι_desc],
  ext, refl
end

@[simp, reassoc, elementwise]
lemma smooth_sheaf_CommRing.forget_stalk_hom_comp_eval (x : Top.of M) :
  category_theory.category_struct.comp -- TODO: notation clash for `≫`
  (smooth_sheaf_CommRing.forget_stalk IM I M R x).hom (smooth_sheaf.eval IM I R x) =
  smooth_sheaf_CommRing.eval _ _ _ _ _ :=
begin
  rw ← category_theory.iso.eq_inv_comp,
  simp,
end

lemma smooth_sheaf_CommRing.eval_surjective (x) :
  function.surjective (smooth_sheaf_CommRing.eval IM I M R x) :=
begin
  intro r,
  obtain ⟨y, rfl⟩ := smooth_sheaf.eval_surjective IM I R x r,
  use (smooth_sheaf_CommRing.forget_stalk IM I M R x).inv y,
  simp,
end

-- sanity check: applying the `CommRing`-to-`Type` forgetful functor to the sheaf-of-rings of smooth
-- functions gives the sheaf-of-types of smooth functions.
example : (category_theory.Sheaf_compose _ (category_theory.forget CommRing)).obj
  (smooth_sheaf_CommRing.{u} IM I M R) =
  (smooth_sheaf IM I M R) := rfl

end smooth_comm_ring
