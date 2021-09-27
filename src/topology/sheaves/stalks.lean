/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Justus Springer
-/
import topology.category.Top.open_nhds
import topology.sheaves.presheaf
import topology.sheaves.sheaf_condition.unique_gluing
import category_theory.limits.types
import category_theory.limits.preserves.filtered
import tactic.elementwise

/-!
# Stalks

For a presheaf `F` on a topological space `X`, valued in some category `C`, the *stalk* of `F`
at the point `x : X` is defined as the colimit of the following functor

(nhds x)ᵒᵖ ⥤ (opens X)ᵒᵖ ⥤ C

where the functor on the left is the inclusion of categories and the functor on the right is `F`.
For an open neighborhood `U` of `x`, we define the map `F.germ x : F.obj (op U) ⟶ F.stalk x` as the
canonical morphism into this colimit.

Taking stalks is functorial: For every point `x : X` we define a functor `stalk_functor C x`,
sending presheaves on `X` to objects of `C`. Furthermore, for a map `f : X ⟶ Y` between
topological spaces, we define `stalk_pushforward` as the induced map on the stalks
`(f _* ℱ).stalk (f x) ⟶ ℱ.stalk x`.

Some lemmas about stalks and germs only hold for certain classes of concrete categories. A basic
property of forgetful functors of categories of algebraic structures (like `Mon`, `CommRing`,...)
is that they preserve filtered colimits. Since stalks are filtered colimits, this ensures that
the stalks of presheaves valued in these categories behave exactly as for `Type`-valued presheaves.
For example, in `germ_exist` we prove that in such a category, every element of the stalk is the
germ of a section.

Furthermore, if we require the forgetful functor to reflect isomorphisms and preserve limits (as
is the case for most algebraic structures), we have access to the unique gluing API and can prove
further properties. Most notably, in `is_iso_iff_stalk_functor_map_iso`, we prove that in such
a category, a morphism of sheaves is an isomorphism if and only if all of its stalk maps are
isomorphisms.

See also the definition of "algebraic structures" in the stacks project:
https://stacks.math.columbia.edu/tag/007L

-/

noncomputable theory

universes v u v' u'

open category_theory
open Top
open category_theory.limits
open topological_space
open opposite

variables {C : Type u} [category.{v} C]

variables [has_colimits.{v} C]

variables {X Y Z : Top.{v}}

namespace Top.presheaf

variables (C)
/-- Stalks are functorial with respect to morphisms of presheaves over a fixed `X`. -/
def stalk_functor (x : X) : X.presheaf C ⥤ C :=
((whiskering_left _ _ C).obj (open_nhds.inclusion x).op) ⋙ colim

variables {C}

/--
The stalk of a presheaf `F` at a point `x` is calculated as the colimit of the functor
nbhds x ⥤ opens F.X ⥤ C
-/
def stalk (ℱ : X.presheaf C) (x : X) : C :=
(stalk_functor C x).obj ℱ -- -- colimit ((open_nhds.inclusion x).op ⋙ ℱ)

@[simp] lemma stalk_functor_obj (ℱ : X.presheaf C) (x : X) :
  (stalk_functor C x).obj ℱ = ℱ.stalk x := rfl

/--
The germ of a section of a presheaf over an open at a point of that open.
-/
def germ (F : X.presheaf C) {U : opens X} (x : U) : F.obj (op U) ⟶ stalk F x :=
colimit.ι ((open_nhds.inclusion x.1).op ⋙ F) (op ⟨U, x.2⟩)

@[simp, elementwise]
lemma germ_res (F : X.presheaf C) {U V : opens X} (i : U ⟶ V) (x : U) :
  F.map i.op ≫ germ F x = germ F (i x : V) :=
let i' : (⟨U, x.2⟩ : open_nhds x.1) ⟶ ⟨V, (i x : V).2⟩ := i in
colimit.w ((open_nhds.inclusion x.1).op ⋙ F) i'.op

/--
A morphism from the stalk of `F` at `x` to some object `Y` is completely determined by its
composition with the `germ` morphisms.
-/
lemma stalk_hom_ext (F : X.presheaf C) {x} {Y : C} {f₁ f₂ : F.stalk x ⟶ Y}
  (ih : ∀ (U : opens X) (hxU : x ∈ U), F.germ ⟨x, hxU⟩ ≫ f₁ = F.germ ⟨x, hxU⟩ ≫ f₂) : f₁ = f₂ :=
colimit.hom_ext $ λ U, by { op_induction U, cases U with U hxU, exact ih U hxU }

@[simp, reassoc, elementwise]
lemma stalk_functor_map_germ {F G : X.presheaf C} (U : opens X) (x : U)
  (f : F ⟶ G) : germ F x ≫ (stalk_functor C x.1).map f = f.app (op U) ≫ germ G x :=
colimit.ι_map (whisker_left ((open_nhds.inclusion x.1).op) f) (op ⟨U, x.2⟩)

variables (C)

/--
For a presheaf `F` on a space `X`, a continuous map `f : X ⟶ Y` induces a morphisms between the
stalk of `f _ * F` at `f x` and the stalk of `F` at `x`.
-/
def stalk_pushforward (f : X ⟶ Y) (F : X.presheaf C) (x : X) : (f _* F).stalk (f x) ⟶ F.stalk x :=
begin
  -- This is a hack; Lean doesn't like to elaborate the term written directly.
  transitivity,
  swap,
  exact colimit.pre _ (open_nhds.map f x).op,
  exact colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) F),
end

@[simp, elementwise, reassoc]
lemma stalk_pushforward_germ (f : X ⟶ Y) (F : X.presheaf C) (U : opens Y)
  (x : (opens.map f).obj U) :
  (f _* F).germ ⟨f x, x.2⟩ ≫ F.stalk_pushforward C f x = F.germ x :=
begin
  rw [stalk_pushforward, germ, colimit.ι_map_assoc, colimit.ι_pre, whisker_right_app],
  erw [category_theory.functor.map_id, category.id_comp],
  refl,
end

-- Here are two other potential solutions, suggested by @fpvandoorn at
-- <https://github.com/leanprover-community/mathlib/pull/1018#discussion_r283978240>
-- However, I can't get the subsequent two proofs to work with either one.

-- def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) :
--   (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- colim.map ((functor.associator _ _ _).inv ≫
--   whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ) ≫
-- colimit.pre ((open_nhds.inclusion x).op ⋙ ℱ) (open_nhds.map f x).op

-- def stalk_pushforward (f : X ⟶ Y) (ℱ : X.presheaf C) (x : X) :
--   (f _* ℱ).stalk (f x) ⟶ ℱ.stalk x :=
-- (colim.map (whisker_right (nat_trans.op (open_nhds.inclusion_map_iso f x).inv) ℱ) :
--   colim.obj ((open_nhds.inclusion (f x) ⋙ opens.map f).op ⋙ ℱ) ⟶ _) ≫
-- colimit.pre ((open_nhds.inclusion x).op ⋙ ℱ) (open_nhds.map f x).op

namespace stalk_pushforward
local attribute [tidy] tactic.op_induction'

@[simp] lemma id (ℱ : X.presheaf C) (x : X) :
  ℱ.stalk_pushforward C (𝟙 X) x = (stalk_functor C x).map ((pushforward.id ℱ).hom) :=
begin
  dsimp [stalk_pushforward, stalk_functor],
  ext1,
  tactic.op_induction',
  cases j, cases j_val,
  rw [colimit.ι_map_assoc, colimit.ι_map, colimit.ι_pre, whisker_left_app, whisker_right_app,
       pushforward.id_hom_app, eq_to_hom_map, eq_to_hom_refl],
  dsimp,
  -- FIXME A simp lemma which unfortunately doesn't fire:
  erw [category_theory.functor.map_id],
end

-- This proof is sadly not at all robust:
-- having to use `erw` at all is a bad sign.
@[simp] lemma comp (ℱ : X.presheaf C) (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  ℱ.stalk_pushforward C (f ≫ g) x =
  ((f _* ℱ).stalk_pushforward C g (f x)) ≫ (ℱ.stalk_pushforward C f x) :=
begin
  dsimp [stalk_pushforward, stalk_functor],
  ext U,
  op_induction U,
  cases U,
  cases U_val,
  simp only [colimit.ι_map_assoc, colimit.ι_pre_assoc,
             whisker_right_app, category.assoc],
  dsimp,
  -- FIXME: Some of these are simp lemmas, but don't fire successfully:
  erw [category_theory.functor.map_id, category.id_comp, category.id_comp, category.id_comp,
       colimit.ι_pre, colimit.ι_pre],
  refl,
end

end stalk_pushforward

section concrete

variables {C}
variables [concrete_category.{v} C]

local attribute [instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

@[ext]
lemma germ_ext (F : X.presheaf C) {U V : opens X} {x : X} {hxU : x ∈ U} {hxV : x ∈ V}
  (W : opens X) (hxW : x ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V) {sU : F.obj (op U)} {sV : F.obj (op V)}
  (ih : F.map iWU.op sU = F.map iWV.op sV) :
  F.germ ⟨x, hxU⟩ sU = F.germ ⟨x, hxV⟩ sV :=
by erw [← F.germ_res iWU ⟨x, hxW⟩,
    ← F.germ_res iWV ⟨x, hxW⟩, comp_apply, comp_apply, ih]

variables [preserves_filtered_colimits (forget C)]

/--
For presheaves valued in a concrete category whose forgetful functor preserves filtered colimits,
every element of the stalk is the germ of a section.
-/
lemma germ_exist (F : X.presheaf C) (x : X) (t : stalk F x) :
  ∃ (U : opens X) (m : x ∈ U) (s : F.obj (op U)), F.germ ⟨x, m⟩ s = t :=
begin
  obtain ⟨U, s, e⟩ := types.jointly_surjective _
    (is_colimit_of_preserves (forget C) (colimit.is_colimit _)) t,
  revert s e,
  rw [(show U = op (unop U), from rfl)],
  generalize : unop U = V, clear U,
  cases V with V m,
  intros s e,
  exact ⟨V, m, s, e⟩,
end

lemma germ_eq (F : X.presheaf C) {U V : opens X} (x : X) (mU : x ∈ U) (mV : x ∈ V)
  (s : F.obj (op U)) (t : F.obj (op V))
  (h : germ F ⟨x, mU⟩ s = germ F ⟨x, mV⟩ t) :
  ∃ (W : opens X) (m : x ∈ W) (iU : W ⟶ U) (iV : W ⟶ V), F.map iU.op s = F.map iV.op t :=
begin
  obtain ⟨W, iU, iV, e⟩ := (types.filtered_colimit.is_colimit_eq_iff _
    (is_colimit_of_preserves _ (colimit.is_colimit ((open_nhds.inclusion x).op ⋙ F)))).mp h,
  exact ⟨(unop W).1, (unop W).2, iU.unop, iV.unop, e⟩,
end

lemma stalk_functor_map_injective_of_app_injective {F G : presheaf C X} (f : F ⟶ G)
  (h : ∀ U : opens X, function.injective (f.app (op U))) (x : X) :
  function.injective ((stalk_functor C x).map f) := λ s t hst,
begin
  rcases germ_exist F x s with ⟨U₁, hxU₁, s, rfl⟩,
  rcases germ_exist F x t with ⟨U₂, hxU₂, t, rfl⟩,
  simp only [stalk_functor_map_germ_apply _ ⟨x,_⟩] at hst,
  obtain ⟨W, hxW, iWU₁, iWU₂, heq⟩ := G.germ_eq x hxU₁ hxU₂ _ _ hst,
  rw [← comp_apply, ← comp_apply, ← f.naturality, ← f.naturality, comp_apply, comp_apply] at heq,
  replace heq := h W heq,
  convert congr_arg (F.germ ⟨x,hxW⟩) heq,
  exacts [(F.germ_res_apply iWU₁ ⟨x,hxW⟩ s).symm,
          (F.germ_res_apply iWU₂ ⟨x,hxW⟩ t).symm],
end


variables [has_limits C] [preserves_limits (forget C)] [reflects_isomorphisms (forget C)]

/--
Let `F` be a sheaf valued in a concrete category, whose forgetful functor reflects isomorphisms,
preserves limits and filtered colimits. Then two sections who agree on every stalk must be equal.
-/
lemma section_ext (F : sheaf C X) (U : opens X) (s t : F.presheaf.obj (op U))
  (h : ∀ x : U, F.presheaf.germ x s = F.presheaf.germ x t) :
  s = t :=
begin
  -- We use `germ_eq` and the axiom of choice, to pick for every point `x` a neighbourhood
  -- `V x`, such that the restrictions of `s` and `t` to `V x` coincide.
  choose V m i₁ i₂ heq using λ x : U, F.presheaf.germ_eq x.1 x.2 x.2 s t (h x),
  -- Since `F` is a sheaf, we can prove the equality locally, if we can show that these
  -- neighborhoods form a cover of `U`.
  apply F.eq_of_locally_eq' V U i₁,
  { intros x hxU,
    rw [subtype.val_eq_coe, opens.mem_coe, opens.mem_supr],
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩ },
  { intro x,
    rw [heq, subsingleton.elim (i₁ x) (i₂ x)] }
end

/-
Note that the analogous statement for surjectivity is false: Surjectivity on stalks does not
imply surjectivity of the components of a sheaf morphism. However it does imply that the morphism
is an epi, but this fact is not yet formalized.
-/
lemma app_injective_of_stalk_functor_map_injective {F : sheaf C X} {G : presheaf C X}
  (f : F.presheaf ⟶ G) (h : ∀ x : X, function.injective ((stalk_functor C x).map f))
  (U : opens X) :
  function.injective (f.app (op U)) :=
λ s t hst, section_ext F _ _ _ $ λ x, h x.1 $ by
  rw [stalk_functor_map_germ_apply, stalk_functor_map_germ_apply, hst]

lemma app_injective_iff_stalk_functor_map_injective {F : sheaf C X}
  {G : presheaf C X} (f : F.presheaf ⟶ G) :
  (∀ x : X, function.injective ((stalk_functor C x).map f)) ↔
  (∀ U : opens X, function.injective (f.app (op U))) :=
⟨app_injective_of_stalk_functor_map_injective f, stalk_functor_map_injective_of_app_injective f⟩

lemma app_surjective_of_stalk_functor_map_bijective {F G : sheaf C X} (f : F ⟶ G)
  (h : ∀ x : X, function.bijective ((stalk_functor C x).map f)) (U : opens X) :
  function.surjective (f.app (op U)) :=
begin
  intro t,
  -- For surjectivity, we are given an arbitrary section `t` and need to find a preimage for it.
  -- We claim that it suffices to find preimages *locally*. That is, for each `x : U` we construct
  -- a neighborhood `V ≤ U` and a section `s : F.obj (op V))` such that `f.app (op V) s` and `t`
  -- agree on `V`.
  suffices : ∀ x : U, ∃ (V : opens X) (m : x.1 ∈ V) (iVU : V ⟶ U) (s : F.presheaf.obj (op V)),
    f.app (op V) s = G.presheaf.map iVU.op t,
  { -- We use the axiom of choice to pick around each point `x` an open neighborhood `V` and a
    -- preimage under `f` on `V`.
    choose V mV iVU sf heq using this,
    -- These neighborhoods clearly cover all of `U`.
    have V_cover : U ≤ supr V,
    { intros x hxU,
      rw [subtype.val_eq_coe, opens.mem_coe, opens.mem_supr],
      exact ⟨⟨x, hxU⟩, mV ⟨x, hxU⟩⟩ },
    -- Since `F` is a sheaf, we can glue all the local preimages together to get a global preimage.
    obtain ⟨s, s_spec, -⟩ := F.exists_unique_gluing' V U iVU V_cover sf _,
    { use s,
      apply G.eq_of_locally_eq' V U iVU V_cover,
      intro x,
      rw [← comp_apply, ← f.naturality, comp_apply, s_spec, heq] },
    { intros x y,
      -- What's left to show here is that the secions `sf` are compatible, i.e. they agree on
      -- the intersections `V x ⊓ V y`. We prove this by showing that all germs are equal.
      apply section_ext,
      intro z,
      -- Here, we need to use injectivity of the stalk maps.
      apply (h z).1,
      erw [stalk_functor_map_germ_apply, stalk_functor_map_germ_apply],
      dsimp,
      simp_rw [← comp_apply, f.naturality, comp_apply, heq, ← comp_apply, ← G.presheaf.map_comp],
      refl, } },

  intro x,
  -- Now we need to prove our initial claim: That we can find preimages of `t` locally.
  -- Since `f` is surjective on stalks, we can find a preimage `s₀` of the germ of `t` at `x`
  obtain ⟨s₀,hs₀⟩ := (h x).2 (G.presheaf.germ x t),
  -- ... and this preimage must come from some section `s₁` defined on some open neighborhood `V₁`
  obtain ⟨V₁,hxV₁,s₁,hs₁⟩ := F.presheaf.germ_exist x.1 s₀,
  subst hs₁, rename hs₀ hs₁,
  erw stalk_functor_map_germ_apply V₁ ⟨x.1,hxV₁⟩ f s₁ at hs₁,
  -- Now, the germ of `f.app (op V₁) s₁` equals the germ of `t`, hence they must coincide on
  -- some open neighborhood `V₂`.
  obtain ⟨V₂, hxV₂, iV₂V₁, iV₂U, heq⟩ := G.presheaf.germ_eq x.1 hxV₁ x.2 _ _ hs₁,
  -- The restriction of `s₁` to that neighborhood is our desired local preimage.
  use [V₂, hxV₂, iV₂U, F.presheaf.map iV₂V₁.op s₁],
  rw [← comp_apply, f.naturality, comp_apply, heq],
end

lemma app_bijective_of_stalk_functor_map_bijective {F G : sheaf C X} (f : F ⟶ G)
  (h : ∀ x : X, function.bijective ((stalk_functor C x).map f)) (U : opens X) :
  function.bijective (f.app (op U)) :=
⟨app_injective_of_stalk_functor_map_injective f (λ x, (h x).1) U,
  app_surjective_of_stalk_functor_map_bijective f h U⟩

/--
Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functor reflects
isomorphisms, preserves limits and filtered colimits. Then if the stalk maps of a morphism
`f : F ⟶ G` are all isomorphisms, `f` must be an isomorphism.
-/
-- Making this an instance would cause a loop in typeclass resolution with `functor.map_is_iso`
lemma is_iso_of_stalk_functor_map_iso {F G : sheaf C X} (f : F ⟶ G)
  [∀ x : X, is_iso ((stalk_functor C x).map f)] : is_iso f :=
begin
  -- Since the inclusion functor from sheaves to presheaves is fully faithful, it suffices to
  -- show that `f`, as a morphism between _presheaves_, is an isomorphism.
  suffices : is_iso ((induced_functor sheaf.presheaf).map f),
  { exactI is_iso_of_fully_faithful (induced_functor sheaf.presheaf) f },
  -- We show that all components of `f` are isomorphisms.
  suffices : ∀ U : (opens X)ᵒᵖ, is_iso (f.app U),
  { exact @nat_iso.is_iso_of_is_iso_app _ _ _ _ F.presheaf G.presheaf f this, },
  intro U, op_induction U,
  -- Since the forgetful functor of `C` reflects isomorphisms, it suffices to see that the
  -- underlying map between types is an isomorphism, i.e. bijective.
  suffices : is_iso ((forget C).map (f.app (op U))),
  { exactI is_iso_of_reflects_iso (f.app (op U)) (forget C) },
  rw is_iso_iff_bijective,
  apply app_bijective_of_stalk_functor_map_bijective,
  intro x,
  apply (is_iso_iff_bijective _).mp,
  exact functor.map_is_iso (forget C) ((stalk_functor C x).map f),
end

/--
Let `F` and `G` be sheaves valued in a concrete category, whose forgetful functor reflects
isomorphisms, preserves limits and filtered colimits. Then a morphism `f : F ⟶ G` is an
isomorphism if and only if all of its stalk maps are isomorphisms.
-/
lemma is_iso_iff_stalk_functor_map_iso {F G : sheaf C X} (f : F ⟶ G) :
  is_iso f ↔ ∀ x : X, is_iso ((stalk_functor C x).map f) :=
begin
  split,
  { intros h x, resetI,
    exact @functor.map_is_iso _ _ _ _ _ _ (stalk_functor C x) f
      ((induced_functor sheaf.presheaf).map_is_iso f) },
  { intro h,
    exactI is_iso_of_stalk_functor_map_iso f }
end

end concrete

end Top.presheaf
