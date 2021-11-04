/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.local_predicate
import topology.sheaves.stalks

/-!
# Sheafification of `Type` valued presheaves

We construct the sheafification of a `Type` valued presheaf,
as the subsheaf of dependent functions into the stalks
consisting of functions which are locally germs.

We show that the stalks of the sheafification are isomorphic to the original stalks,
via `stalk_to_fiber` which evaluates a germ of a dependent function at a point.

We construct a morphism `to_sheafify` from a presheaf to (the underlying presheaf of)
its sheafification, given by sending a section to its collection of germs.

Sheafification forms a functor `sheafify_functor : X.presheaf (Type v) ⥤ X.sheaf (Type v)`,
and this functor is left adjoint to `forget` as shown in `sheafify_adjunction`.
-/

universes v

noncomputable theory

open Top
open opposite
open topological_space

variables {X : Top.{v}} (F : presheaf (Type v) X)

namespace Top.presheaf

namespace sheafify

/--
The prelocal predicate on functions into the stalks, asserting that the function is equal to a germ.
-/
def is_germ : prelocal_predicate (λ x, F.stalk x) :=
{ pred := λ U f, ∃ (g : F.obj (op U)), ∀ x : U, f x = F.germ x g,
  res := λ V U i f ⟨g, p⟩, ⟨F.map i.op g, λ x, (p (i x)).trans (F.germ_res_apply _ _ _).symm⟩, }

/--
The local predicate on functions into the stalks,
asserting that the function is locally equal to a germ.
-/
def is_locally_germ : local_predicate (λ x, F.stalk x) := (is_germ F).sheafify

end sheafify

/--
The sheafification of a `Type` valued presheaf, defined as the functions into the stalks which
are locally equal to germs.
-/
def sheafify : sheaf (Type v) X :=
subsheaf_to_Types (sheafify.is_locally_germ F)

/--
The morphism from a presheaf to its sheafification,
sending each section to its germs.
(This forms the unit of the adjunction.)
-/
def to_sheafify : F ⟶ F.sheafify.1 :=
{ app := λ U f, ⟨λ x, F.germ x f, prelocal_predicate.sheafify_of ⟨f, λ x, rfl⟩⟩,
  naturality' := λ U U' f, by { ext x ⟨u, m⟩, exact germ_res_apply F f.unop ⟨u, m⟩ x } }

/--
The natural morphism from the stalk of the sheafification to the original stalk.
In `sheafify_stalk_iso` we show this is an isomorphism.
-/
def stalk_to_fiber (x : X) : F.sheafify.1.stalk x ⟶ F.stalk x :=
stalk_to_fiber (sheafify.is_locally_germ F) x

lemma stalk_to_fiber_surjective (x : X) : function.surjective (F.stalk_to_fiber x) :=
begin
  apply stalk_to_fiber_surjective,
  intro t,
  obtain ⟨U, m, s, rfl⟩ := F.germ_exist _ t,
  { use ⟨U, m⟩,
    fsplit,
    { exact λ y, F.germ y s, },
    { exact ⟨prelocal_predicate.sheafify_of ⟨s, (λ _, rfl)⟩, rfl⟩, }, },
end

lemma stalk_to_fiber_injective (x : X) : function.injective (F.stalk_to_fiber x) :=
begin
  apply stalk_to_fiber_injective,
  intros,
  rcases hU ⟨x, U.2⟩ with ⟨U', mU, iU, gU, wU⟩,
  rcases hV ⟨x, V.2⟩ with ⟨V', mV, iV, gV, wV⟩,
  have wUx := wU ⟨x, mU⟩,
  dsimp at wUx, erw wUx at e, clear wUx,
  have wVx := wV ⟨x, mV⟩,
  dsimp at wVx, erw wVx at e, clear wVx,
  rcases F.germ_eq x mU mV gU gV e with ⟨W, mW, iU', iV', e'⟩,
  dsimp at e',
  use ⟨W ⊓ (U' ⊓ V'), ⟨mW, mU, mV⟩⟩,
  refine ⟨_, _, _⟩,
  { change W ⊓ (U' ⊓ V') ⟶ U.val,
    exact (opens.inf_le_right _ _) ≫ (opens.inf_le_left _ _) ≫ iU, },
  { change W ⊓ (U' ⊓ V') ⟶ V.val,
    exact (opens.inf_le_right _ _) ≫ (opens.inf_le_right _ _) ≫ iV, },
  { intro w,
    dsimp,
    specialize wU ⟨w.1, w.2.2.1⟩,
    dsimp at wU,
    specialize wV ⟨w.1, w.2.2.2⟩,
    dsimp at wV,
    erw [wU, ←F.germ_res iU' ⟨w, w.2.1⟩, wV, ←F.germ_res iV' ⟨w, w.2.1⟩,
      category_theory.types_comp_apply, category_theory.types_comp_apply, e'] },
end

/--
The isomorphism betweeen a stalk of the sheafification and the original stalk.
-/
def sheafify_stalk_iso (x : X) : F.sheafify.1.stalk x ≅ F.stalk x :=
(equiv.of_bijective _ ⟨stalk_to_fiber_injective _ _, stalk_to_fiber_surjective _ _⟩).to_iso

open category_theory

instance stalk_to_fiber_is_iso (x : X) : is_iso (F.stalk_to_fiber x) :=
(is_iso_iff_bijective _).mpr
  ⟨stalk_to_fiber_injective _ _, stalk_to_fiber_surjective _ _⟩

@[simp, reassoc] lemma stalk_functor_sheafify_comp_stalk_to_fiber (x : X) :
  (stalk_functor (Type v) x).map F.to_sheafify ≫ F.stalk_to_fiber x = 𝟙 _ :=
begin
  ext U s,
  induction U using opposite.rec,
  cases U,
  delta stalk_functor to_sheafify stalk_to_fiber Top.stalk_to_fiber presheaf.germ sheafify,
  simpa
end

@[simp, reassoc] lemma stalk_to_fiber_comp_stalk_functor_sheafify (x : X) :
  F.stalk_to_fiber x ≫ (stalk_functor (Type v) x).map F.to_sheafify = 𝟙 _ :=
is_iso.inv_eq_of_inv_hom_id (stalk_functor_sheafify_comp_stalk_to_fiber F x) ▸
      is_iso.hom_inv_id _

/-- A morphsim of presheaves `F ⟶ G`, can be lifted to a morphism of sheaves `F♯ ⟶ G♯`. -/
def sheafify_map {F G : presheaf (Type v) X} (α : F ⟶ G) :
  F.sheafify ⟶ G.sheafify :=
{ app := λ U s, ⟨λ x, (stalk_functor _ x.val).map α (s.val x),
  begin
    intro x,
    rcases s.2 x with ⟨V, hV, i, a, ha⟩,
    refine ⟨V, hV, i, (α.app _) a, _⟩,
    intro y, have : s.1 _ = _ := ha y,
    dsimp only,
    rw this,
    erw functor.comp_map,
    rw whiskering_left_obj_map,
    erw limits.types.colimit.ι_map_apply,
    congr
  end⟩,
  naturality' := λ A B f,
  begin
    ext y, cases y,
    delta presheaf.sheafify subsheaf_to_Types subpresheaf_to_Types presheaf.stalk_functor,
    simp only [types_comp_apply, subtype.coe_mk],
    congr
  end }

variable (X)

/-- The sheafification functor from presheaves of types to sheaves of types. -/
def sheafify_functor : X.presheaf (Type v) ⥤ X.sheaf (Type v) :=
{ obj := λ F, F.sheafify,
  map := λ _ _ f, sheafify_map f,
  map_id' := λ F, by { unfold sheafify_map, simpa },
  map_comp' := λ F G H α β, by { unfold sheafify_map, simpa } }

variable {X}

@[simp, reassoc]
lemma sheafify_naturality (F G : presheaf (Type v) X) (α : F ⟶ G) :
  F.to_sheafify ≫ (sheafify_functor _).map α = α ≫ G.to_sheafify :=
begin
  change F.to_sheafify ≫ sheafify_map α = _,
  delta to_sheafify sheafify_map presheaf.stalk_functor presheaf.germ,
  ext,
  simp only [functor_to_types.comp, subtype.coe_mk],
  erw limits.types.colimit.ι_map_apply,
  congr
end

instance _root_.Top.sheaf.to_sheafify_is_iso (F : sheaf (Type v) X) :
  is_iso F.val.to_sheafify :=
begin
  rw is_iso_iff_is_iso',
  rw is_iso_iff_stalk_functor_map_iso,
  intro x,
  rw ←is_iso.inv_eq_of_inv_hom_id (stalk_functor_sheafify_comp_stalk_to_fiber F.val x),
  exact is_iso.inv_is_iso
end

/-- A sheaf is isomorphic to its sheafification. -/
@[simps] def _root_.Top.sheaf.iso_sheafify (F : sheaf (Type v) X) : F ≅ F.val.sheafify :=
@as_iso (sheaf (Type v) X) _ _ _ F.val.to_sheafify
  ((is_iso_iff_is_iso' _ _ F.val.to_sheafify).mp F.to_sheafify_is_iso)

/-- A morphsim `F ⟶ G` into a sheaf factors through the sheafification `F♯ ⟶ G`. -/
def sheafify_lift {F : presheaf (Type v) X} {G : sheaf (Type v) X} (α : F ⟶ G.val) :
  F.sheafify ⟶ G := (sheafify_functor _).map α ≫ G.iso_sheafify.inv

@[simp] lemma sheafify_lift_fac {F : presheaf (Type v) X} {G : sheaf (Type v) X} (α : F ⟶ G.val) :
  F.to_sheafify ≫ sheafify_lift α = α :=
by erw [sheafify_naturality_assoc, G.iso_sheafify.hom_inv_id, category.comp_id]

@[simp] lemma sheafify_lift_comp {F : presheaf (Type v) X} (G H : sheaf (Type v) X)
  (α : F ⟶ G.val) (β : G ⟶ H) : sheafify_lift (α ≫ β) = sheafify_lift α ≫ β :=
begin
  unfold sheafify_lift,
  simp only [functor.map_comp, category.assoc, Top.sheaf.iso_sheafify_inv],
  congr' 1,
  simp only [is_iso.eq_inv_comp, is_iso.comp_inv_eq, category.assoc],
  exact sheafify_naturality _ _ _
end

lemma to_sheafify_mono (F : presheaf (Type v) X) (G : sheaf (Type v) X) (α β : F.sheafify ⟶ G)
  (H : F.to_sheafify ≫ α = F.to_sheafify ≫ β) : α = β :=
hom_section_ext _ _
  (λ x, by simpa using congr_arg (λ f, F.stalk_to_fiber x ≫ (stalk_functor (Type v) x).map f) H)

@[simp] lemma sheafify_map_to_sheafify (F : presheaf (Type v) X) :
  sheafify_map F.to_sheafify = F.sheafify.val.to_sheafify :=
to_sheafify_mono _ _ _ _ (sheafify_naturality _ _ (F.to_sheafify))

@[simp] lemma sheafify_lift_to_sheafify (F : presheaf (Type v) X) :
  sheafify_lift F.to_sheafify = 𝟙 _ :=
by { delta sheafify_lift sheafify_functor, simpa }

/-- Sheafification is left adjoint to the forgetful functor. -/
def sheafify_adjunction : sheafify_functor X ⊣ sheaf.forget (Type v) X :=
{ hom_equiv := λ F G,
  { to_fun := λ α, F.to_sheafify ≫ α,
    inv_fun := λ α, sheafify_lift α,
    left_inv := λ α, by simp,
    right_inv := λ α, by simp },
  unit := { app := λ F, F.to_sheafify,
    naturality' := λ _ _ f, by { simp [sheafify_naturality _ _ f], } },
  counit := { app := λ F, F.iso_sheafify.inv,
    naturality' := λ F G f, by { simp, exact sheafify_naturality _ _ _ } } }

end Top.presheaf
