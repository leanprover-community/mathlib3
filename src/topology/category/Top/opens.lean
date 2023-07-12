/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.category.preorder
import category_theory.eq_to_hom
import topology.category.Top.epi_mono
import topology.sets.opens

/-!
# The category of open sets in a topological space.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `to_Top : opens X ⥤ Top` and
`map (f : X ⟶ Y) : opens Y ⥤ opens X`, given by taking preimages of open sets.

Unfortunately `opens` isn't (usefully) a functor `Top ⥤ Cat`.
(One can in fact define such a functor,
but using it results in unresolvable `eq.rec` terms in goals.)

Really it's a 2-functor from (spaces, continuous functions, equalities)
to (categories, functors, natural isomorphisms).
We don't attempt to set up the full theory here, but do provide the natural isomorphisms
`map_id : map (𝟙 X) ≅ 𝟭 (opens X)` and
`map_comp : map (f ≫ g) ≅ map g ⋙ map f`.

Beyond that, there's a collection of simp lemmas for working with these constructions.
-/

open category_theory
open topological_space
open opposite

universe u

namespace topological_space.opens

variables {X Y Z : Top.{u}}

/-!
Since `opens X` has a partial order, it automatically receives a `category` instance.
Unfortunately, because we do not allow morphisms in `Prop`,
the morphisms `U ⟶ V` are not just proofs `U ≤ V`, but rather
`ulift (plift (U ≤ V))`.
-/

instance opens_hom_has_coe_to_fun {U V : opens X} : has_coe_to_fun (U ⟶ V) (λ f, U → V) :=
⟨λ f x, ⟨x, f.le x.2⟩⟩

/-!
We now construct as morphisms various inclusions of open sets.
-/
-- This is tedious, but necessary because we decided not to allow Prop as morphisms in a category...

/--
The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
def inf_le_left (U V : opens X) : U ⊓ V ⟶ U := inf_le_left.hom

/--
The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
def inf_le_right (U V : opens X) : U ⊓ V ⟶ V := inf_le_right.hom

/--
The inclusion `U i ⟶ supr U` as a morphism in the category of open sets.
-/
def le_supr {ι : Type*} (U : ι → opens X) (i : ι) : U i ⟶ supr U := (le_supr U i).hom

/--
The inclusion `⊥ ⟶ U` as a morphism in the category of open sets.
-/
def bot_le (U : opens X) : ⊥ ⟶ U := bot_le.hom

/--
The inclusion `U ⟶ ⊤` as a morphism in the category of open sets.
-/
def le_top (U : opens X) : U ⟶ ⊤ := le_top.hom

-- We do not mark this as a simp lemma because it breaks open `x`.
-- Nevertheless, it is useful in `sheaf_of_functions`.
lemma inf_le_left_apply (U V : opens X) (x) :
  (inf_le_left U V) x = ⟨x.1, (@_root_.inf_le_left _ _ U V : _ ≤ _) x.2⟩ :=
rfl

@[simp]
lemma inf_le_left_apply_mk (U V : opens X) (x) (m) :
  (inf_le_left U V) ⟨x, m⟩ = ⟨x, (@_root_.inf_le_left _ _ U V : _ ≤ _) m⟩ :=
rfl

@[simp]
lemma le_supr_apply_mk {ι : Type*} (U : ι → opens X) (i : ι) (x) (m) :
  (le_supr U i) ⟨x, m⟩ = ⟨x, (_root_.le_supr U i : _) m⟩ :=
rfl

/--
The functor from open sets in `X` to `Top`,
realising each open set as a topological space itself.
-/
def to_Top (X : Top.{u}) : opens X ⥤ Top :=
{ obj := λ U, ⟨U, infer_instance⟩,
  map := λ U V i, ⟨λ x, ⟨x.1, i.le x.2⟩,
    (embedding.continuous_iff embedding_subtype_coe).2 continuous_induced_dom⟩ }

@[simp]
lemma to_Top_map (X : Top.{u}) {U V : opens X} {f : U ⟶ V} {x} {h} :
  ((to_Top X).map f) ⟨x, h⟩ = ⟨x, f.le h⟩ :=
rfl

/--
The inclusion map from an open subset to the whole space, as a morphism in `Top`.
-/
@[simps { fully_applied := ff }]
def inclusion {X : Top.{u}} (U : opens X) : (to_Top X).obj U ⟶ X :=
{ to_fun := _,
  continuous_to_fun := continuous_subtype_coe }

lemma open_embedding {X : Top.{u}} (U : opens X) : open_embedding (inclusion U) :=
is_open.open_embedding_subtype_coe U.2

/--
The inclusion of the top open subset (i.e. the whole space) is an isomorphism.
-/
def inclusion_top_iso (X : Top.{u}) : (to_Top X).obj ⊤ ≅ X :=
{ hom := inclusion ⊤,
  inv := ⟨λ x, ⟨x, trivial⟩, continuous_def.2 $ λ U ⟨S, hS, hSU⟩, hSU ▸ hS⟩ }

/-- `opens.map f` gives the functor from open sets in Y to open set in X,
    given by taking preimages under f. -/
def map (f : X ⟶ Y) : opens Y ⥤ opens X :=
{ obj := λ U, ⟨ f ⁻¹' U, U.is_open.preimage f.continuous ⟩,
  map := λ U V i, ⟨ ⟨ λ x h, i.le h ⟩ ⟩ }.

lemma map_coe (f : X ⟶ Y) (U : opens Y) :
  ↑((map f).obj U) = f ⁻¹' U :=
rfl

@[simp] lemma map_obj (f : X ⟶ Y) (U) (p) :
  (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, p.preimage f.continuous⟩ := rfl

@[simp] lemma map_id_obj (U : opens X) : (map (𝟙 X)).obj U = U :=
let ⟨_,_⟩ := U in rfl

@[simp] lemma map_id_obj' (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=
rfl

@[simp] lemma map_id_obj_unop (U : (opens X)ᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U :=
let ⟨_,_⟩ := U.unop in rfl
@[simp] lemma op_map_id_obj (U : (opens X)ᵒᵖ) : (map (𝟙 X)).op.obj U = U :=
by simp

/--
The inclusion `U ⟶ (map f).obj ⊤` as a morphism in the category of open sets.
-/
def le_map_top (f : X ⟶ Y) (U : opens X) : U ⟶ (map f).obj ⊤ :=
le_top U

@[simp] lemma map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (map (f ≫ g)).obj U = (map f).obj ((map g).obj U) :=
rfl

@[simp] lemma map_comp_obj' (f : X ⟶ Y) (g : Y ⟶ Z) (U) (p) :
  (map (f ≫ g)).obj ⟨U, p⟩ = (map f).obj ((map g).obj ⟨U, p⟩) :=
rfl

@[simp] lemma map_comp_map (f : X ⟶ Y) (g : Y ⟶ Z) {U V} (i : U ⟶ V) :
  (map (f ≫ g)).map i = (map f).map ((map g).map i) :=
rfl

@[simp] lemma map_comp_obj_unop (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (map (f ≫ g)).obj (unop U) = (map f).obj ((map g).obj (unop U)) :=
rfl

@[simp] lemma op_map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (map (f ≫ g)).op.obj U = (map f).op.obj ((map g).op.obj U) :=
rfl

lemma map_supr (f : X ⟶ Y) {ι : Type*} (U : ι → opens Y) :
  (map f).obj (supr U) = supr ((map f).obj ∘ U) :=
begin
  ext1, rw [supr_def, supr_def, map_obj],
  dsimp, rw set.preimage_Union, refl,
end

section
variable (X)

/--
The functor `opens X ⥤ opens X` given by taking preimages under the identity function
is naturally isomorphic to the identity functor.
-/
@[simps]
def map_id : map (𝟙 X) ≅ 𝟭 (opens X) :=
{ hom := { app := λ U, eq_to_hom (map_id_obj U) },
  inv := { app := λ U, eq_to_hom (map_id_obj U).symm } }

lemma map_id_eq : map (𝟙 X) = 𝟭 (opens X) :=
by { unfold map, congr, ext, refl, ext }

end

/--
The natural isomorphism between taking preimages under `f ≫ g`, and the composite
of taking preimages under `g`, then preimages under `f`.
-/
@[simps]
def map_comp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
{ hom := { app := λ U, eq_to_hom (map_comp_obj f g U) },
  inv := { app := λ U, eq_to_hom (map_comp_obj f g U).symm } }

lemma map_comp_eq (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map g ⋙ map f :=
rfl

/--
If two continuous maps `f g : X ⟶ Y` are equal,
then the functors `opens Y ⥤ opens X` they induce are isomorphic.
-/
-- We could make `f g` implicit here, but it's nice to be able to see when
-- they are the identity (often!)
def map_iso (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
nat_iso.of_components (λ U, eq_to_iso (congr_fun (congr_arg functor.obj (congr_arg map h)) U) )
  (by obviously)

lemma map_eq (f g : X ⟶ Y) (h : f = g) : map f = map g :=
by { unfold map, congr, ext, rw h, rw h, assumption' }

@[simp] lemma map_iso_refl (f : X ⟶ Y) (h) : map_iso f f h = iso.refl (map _) := rfl

@[simp] lemma map_iso_hom_app (f g : X ⟶ Y) (h : f = g) (U : opens Y) :
  (map_iso f g h).hom.app U = eq_to_hom (congr_fun (congr_arg functor.obj (congr_arg map h)) U) :=
rfl

@[simp] lemma map_iso_inv_app (f g : X ⟶ Y) (h : f = g) (U : opens Y) :
  (map_iso f g h).inv.app U =
     eq_to_hom (congr_fun (congr_arg functor.obj (congr_arg map h.symm)) U) :=
rfl

/-- A homeomorphism of spaces gives an equivalence of categories of open sets.

TODO: define `order_iso.equivalence`, use it.
-/
@[simps] def map_map_iso {X Y : Top.{u}} (H : X ≅ Y) : opens Y ≌ opens X :=
{ functor := map H.hom,
  inverse := map H.inv,
  unit_iso := nat_iso.of_components (λ U, eq_to_iso (by simp [map, set.preimage_preimage]))
    (by { intros _ _ _, simp }),
  counit_iso := nat_iso.of_components (λ U, eq_to_iso (by simp [map, set.preimage_preimage]))
    (by { intros _ _ _, simp }) }

end topological_space.opens

/--
An open map `f : X ⟶ Y` induces a functor `opens X ⥤ opens Y`.
-/
@[simps]
def is_open_map.functor {X Y : Top} {f : X ⟶ Y} (hf : is_open_map f) :
  opens X ⥤ opens Y :=
{ obj := λ U, ⟨f '' U, hf U U.2⟩,
  map := λ U V h, ⟨⟨set.image_subset _ h.down.down⟩⟩ }

/--
An open map `f : X ⟶ Y` induces an adjunction between `opens X` and `opens Y`.
-/
def is_open_map.adjunction {X Y : Top} {f : X ⟶ Y} (hf : is_open_map f) :
  adjunction hf.functor (topological_space.opens.map f) :=
adjunction.mk_of_unit_counit
{ unit := { app := λ U, hom_of_le $ λ x hxU, ⟨x, hxU, rfl⟩ },
  counit := { app := λ V, hom_of_le $ λ y ⟨x, hfxV, hxy⟩, hxy ▸ hfxV } }

instance is_open_map.functor_full_of_mono {X Y : Top} {f : X ⟶ Y} (hf : is_open_map f)
  [H : mono f] : full hf.functor :=
{ preimage := λ U V i, hom_of_le (λ x hx, by
  { obtain ⟨y, hy, eq⟩ := i.le ⟨x, hx, rfl⟩, exact (Top.mono_iff_injective f).mp H eq ▸ hy }) }

instance is_open_map.functor_faithful {X Y : Top} {f : X ⟶ Y} (hf : is_open_map f) :
  faithful hf.functor := {}

namespace topological_space.opens
open topological_space

@[simp] lemma open_embedding_obj_top {X : Top} (U : opens X) :
  U.open_embedding.is_open_map.functor.obj ⊤ = U :=
by { ext1, exact set.image_univ.trans subtype.range_coe }

@[simp] lemma inclusion_map_eq_top {X : Top} (U : opens X) :
  (opens.map U.inclusion).obj U = ⊤ :=
by { ext1, exact subtype.coe_preimage_self _ }

@[simp]
lemma adjunction_counit_app_self {X : Top} (U : opens X) :
  U.open_embedding.is_open_map.adjunction.counit.app U = eq_to_hom (by simp) :=
by ext

lemma inclusion_top_functor (X : Top) :
  (@opens.open_embedding X ⊤).is_open_map.functor =
  map (inclusion_top_iso X).inv :=
begin
  apply functor.hext, intro, abstract obj_eq { ext,
  exact ⟨ λ ⟨⟨_,_⟩,h,rfl⟩, h, λ h, ⟨⟨x,trivial⟩,h,rfl⟩ ⟩ },
  intros, apply subsingleton.helim, congr' 1,
  iterate 2 {apply inclusion_top_functor.obj_eq},
end

lemma functor_obj_map_obj {X Y : Top} {f : X ⟶ Y} (hf : is_open_map f) (U : opens Y) :
  hf.functor.obj ((opens.map f).obj U) = hf.functor.obj ⊤ ⊓ U :=
begin
  ext, split,
  { rintros ⟨x, hx, rfl⟩, exact ⟨⟨x, trivial, rfl⟩, hx⟩ },
  { rintros ⟨⟨x, -, rfl⟩, hx⟩, exact ⟨x, hx, rfl⟩ }
end

@[simp] lemma functor_map_eq_inf {X : Top} (U V : opens X) :
  U.open_embedding.is_open_map.functor.obj ((opens.map U.inclusion).obj V) = V ⊓ U :=
by { ext1, refine set.image_preimage_eq_inter_range.trans _, simpa }

lemma map_functor_eq' {X U : Top} (f : U ⟶ X) (hf : _root_.open_embedding f) (V) :
  ((opens.map f).obj $ hf.is_open_map.functor.obj V) = V :=
opens.ext $ set.preimage_image_eq _ hf.inj

@[simp] lemma map_functor_eq {X : Top} {U : opens X} (V : opens U) :
  ((opens.map U.inclusion).obj $ U.open_embedding.is_open_map.functor.obj V) = V :=
topological_space.opens.map_functor_eq' _ U.open_embedding V

@[simp] lemma adjunction_counit_map_functor {X : Top} {U : opens X} (V : opens U) :
  U.open_embedding.is_open_map.adjunction.counit.app (U.open_embedding.is_open_map.functor.obj V)
    = eq_to_hom (by { conv_rhs { rw ← V.map_functor_eq }, refl }) :=
by ext

end topological_space.opens
