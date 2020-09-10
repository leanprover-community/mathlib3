/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.category.Top.basic
import category_theory.eq_to_hom
import category_theory.limits.preserves
import category_theory.limits.lattice
import topology.opens

/-!
# The category of open sets in a topological space.

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
open category_theory.limits
open topological_space
open opposite

universes v u

namespace topological_space.opens

variables {X Y Z : Top.{u}}

/-!
Since `opens X` has a partial order, it automatically receives a `category` instance.
Unfortunately, because we do not allow morphisms in `Prop`,
the morphisms `U ⟶ V` are not just proofs `U ≤ V`, but rather
`ulift (plift (U ≤ V))`.
-/

instance opens_hom_has_coe_to_fun {U V : opens X} : has_coe_to_fun (U ⟶ V) :=
{ F := λ f, U → V,
  coe := λ f x, ⟨x, (le_of_hom f) x.2⟩ }

/-!
We now construct as morphisms various inclusions of open sets.
-/
-- This is tedious, but necessary because we decided not to allow Prop as morphisms in a category...

/--
The inclusion `U ⊓ V ⟶ U` as a morphism in the category of open sets.
-/
def inf_le_left (U V : opens X) : U ⊓ V ⟶ U :=
hom_of_le inf_le_left

/--
The inclusion `U ⊓ V ⟶ V` as a morphism in the category of open sets.
-/
def inf_le_right (U V : opens X) : U ⊓ V ⟶ V :=
hom_of_le inf_le_right

/--
The inclusion `U i ⟶ supr U` as a morphism in the category of open sets.
-/
def le_supr {ι : Type*} (U : ι → opens X) (i : ι) : U i ⟶ supr U :=
hom_of_le (le_supr U i)

/--
The functor from open sets in `X` to `Top`,
realising each open set as a topological space itself.
-/
def to_Top (X : Top.{u}) : opens X ⥤ Top :=
{ obj := λ U, ⟨U.val, infer_instance⟩,
  map := λ U V i, ⟨λ x, ⟨x.1, (le_of_hom i) x.2⟩,
    (embedding.continuous_iff embedding_subtype_coe).2 continuous_induced_dom⟩ }

lemma eq_of_iso {U V : opens X} (i : U ≅ V) : U = V :=
opens.ext (set.ext (λ x, ⟨λ h, i.hom.down.down h, λ h, i.inv.down.down h⟩))

lemma op_eq_of_iso {U V : (opens X)ᵒᵖ} (i : U ≅ V) : U = V :=
begin
  -- TODO why isn't the op_induction tactic working here?
  revert i,
  revert U,
  apply @opposite.op_induction (opens X) (λ U, (U ≅ V) → (U = V)),
  intro U,
  revert V,
  apply @opposite.op_induction (opens X) (λ V, ((op U) ≅ V) → ((op U) = V)),
  intro V,
  intro i,
  congr,
  apply eq_of_iso,
  exact i.unop.symm,
end

@[simp]
lemma to_Top_map (X : Top.{u}) {U V : opens X} {f : U ⟶ V} {x} {h} :
  ((to_Top X).map f) ⟨x, h⟩ = ⟨x, (le_of_hom f) h⟩ :=
rfl

/--
The inclusion map from an open subset to the whole space, as a morphism in `Top`.
-/
@[simps]
def inclusion {X : Top.{u}} (U : opens X) : (to_Top X).obj U ⟶ X :=
{ to_fun := _,
  continuous_to_fun := continuous_subtype_coe }

lemma inclusion_open_embedding {X : Top.{u}} (U : opens X) : open_embedding (inclusion U) :=
is_open.open_embedding_subtype_coe U.2

/-- `opens.map f` gives the functor from open sets in Y to open set in X,
    given by taking preimages under f. -/
def map (f : X ⟶ Y) : opens Y ⥤ opens X :=
{ obj := λ U, ⟨ f ⁻¹' U.val, f.continuous _ U.property ⟩,
  map := λ U V i, ⟨ ⟨ λ a b, (le_of_hom i) b ⟩ ⟩ }.

@[simp] lemma map_obj (f : X ⟶ Y) (U) (p) : (map f).obj ⟨U, p⟩ = ⟨f ⁻¹' U, f.continuous _ p⟩ :=
rfl

@[simp] lemma map_obj_val (f : X ⟶ Y) (U) : ((map f).obj U).val = f.val ⁻¹' U.val := rfl

@[simp] lemma map_id_obj' (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=

@[simp] lemma map_id_obj (U : opens X) : (map (𝟙 X)).obj U = U :=
by { ext, refl } -- not quite `rfl`, since we don't have eta for records

@[simp] lemma map_id_obj' (U) (p) : (map (𝟙 X)).obj ⟨U, p⟩ = ⟨U, p⟩ :=
rfl

@[simp] lemma map_id_obj_unop (U : (opens X)ᵒᵖ) : (map (𝟙 X)).obj (unop U) = unop U :=
by simp
@[simp] lemma op_map_id_obj (U : (opens X)ᵒᵖ) : (map (𝟙 X)).op.obj U = U :=
by simp

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

end

@[simp] lemma map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (map (f ≫ g)).obj U = (map f).obj ((map g).obj U) :=
by { ext, refl } -- not quite `rfl`, since we don't have eta for records

@[simp] lemma map_comp_obj' (f : X ⟶ Y) (g : Y ⟶ Z) (U) (p) :
  (map (f ≫ g)).obj ⟨U, p⟩ = (map f).obj ((map g).obj ⟨U, p⟩) :=
rfl

@[simp] lemma map_comp_obj_unop (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (map (f ≫ g)).obj (unop U) = (map f).obj ((map g).obj (unop U)) :=
by simp
@[simp] lemma op_map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (map (f ≫ g)).op.obj U = (map f).op.obj ((map g).op.obj U) :=
by simp

/--
The natural isomorphism between taking preimages under `f ≫ g`, and the composite
of taking preimages under `g`, then preimages under `f`.
-/
@[simps]
def map_comp (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
{ hom := { app := λ U, eq_to_hom (map_comp_obj f g U) },
  inv := { app := λ U, eq_to_hom (map_comp_obj f g U).symm } }

@[simp] lemma map_comp_hom_app (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (map_comp f g).hom.app U = eq_to_hom (map_comp_obj f g U) := rfl
@[simp] lemma map_comp_inv_app (f : X ⟶ Y) (g : Y ⟶ Z) (U) :
  (map_comp f g).inv.app U = eq_to_hom (map_comp_obj f g U).symm := rfl

/-- The preimage of a union is the union of the preimages. -/
-- TODO surely we can just use this fact, already proved somewhere about sets...
lemma map_supr (f : X ⟶ Y) {α} (ι : α → opens Y) : (map f).obj (lattice.supr ι) = lattice.supr ((map f).obj ∘ ι) :=
begin
  ext,
  split,
  { rintro ⟨_, ⟨⟨_, ⟨⟨z, rfl⟩, rfl⟩⟩, p⟩⟩,
    exact opens.mem_of_subset_of_mem (lattice.le_supr ((map f).obj ∘ ι) z) p },
  { rintro ⟨U, ⟨V, ⟨⟨t, rfl⟩, rfl⟩⟩, q⟩,
    apply set.mem_of_subset_of_mem (lattice.le_supr ι t) q, }
end

def is_colimit_iff_supr {J : Type u} [small_category J] {F : J ⥤ opens X} (c : cocone F) :
  is_colimit c ≃ c.X = lattice.supr F.obj :=
{ to_fun := λ h, eq_of_iso (cocones.forget.map_iso (is_colimit.unique h (colimit.is_colimit F))),
  inv_fun := λ h, is_colimit.of_iso_colimit (colimit.is_colimit F)
    { hom := { hom := begin rw h, exact 𝟙 _, end }, inv := { hom := begin rw h, exact 𝟙 _, end } },
  left_inv := by tidy,
  right_inv := by tidy, }

instance (f : X ⟶ Y) : preserves_colimits (map f) :=
⟨λ J 𝒥, by exactI ⟨λ K, ⟨λ c is_colimit, begin
  apply (is_colimit_iff_supr _).inv_fun,
  have t := congr_arg (map f).obj ((is_colimit_iff_supr c).to_fun is_colimit),
  rw map_supr at t,
  exact t,
end⟩⟩⟩

-- We could make `f g` implicit here, but it's nice to be able to see when
-- they are the identity (often!)
def map_iso (f g : X ⟶ Y) (h : f = g) : map f ≅ map g :=
nat_iso.of_components (λ U, eq_to_iso (congr_fun (congr_arg functor.obj (congr_arg map h)) U) )
  (by obviously)

@[simp] lemma map_iso_refl (f : X ⟶ Y) (h) : map_iso f f h = iso.refl (map _) := rfl

@[simp] lemma map_iso_hom_app (f g : X ⟶ Y) (h : f = g) (U : opens Y) :
  (map_iso f g h).hom.app U = eq_to_hom (congr_fun (congr_arg functor.obj (congr_arg map h)) U) :=
rfl

@[simp] lemma map_iso_inv_app (f g : X ⟶ Y) (h : f = g) (U : opens Y) :
  (map_iso f g h).inv.app U =
     eq_to_hom (congr_fun (congr_arg functor.obj (congr_arg map h.symm)) U) :=
rfl

end topological_space.opens

/--
An open map `f : X ⟶ Y` induces a functor `opens X ⥤ opens Y`.
-/
@[simps]
def is_open_map.functor {X Y : Top} {f : X ⟶ Y} (hf : is_open_map f) :
  opens X ⥤ opens Y :=
{ obj := λ U, ⟨f '' U, hf U U.2⟩,
  map := λ U V h, ⟨⟨set.image_subset _ h.down.down⟩⟩ }
