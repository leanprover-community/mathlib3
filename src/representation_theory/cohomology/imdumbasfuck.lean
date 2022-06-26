/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Calle Sönne
-/
#exit
import topology.category.Profinite
import algebra.category.Group.limits
import topology.algebra.continuous_monoid_hom
import representation_theory.cohomology.probablywastingmytime
import
/-!
# The category of Profinite Groups
-/

universes v u

open category_theory

/-- The type of profinite topological spaces. -/
structure ProfiniteGroup :=
(to_Profinite : Profinite)
[is_group : group to_Profinite]
[is_topological_group : topological_group to_Profinite]

namespace ProfiniteGroup

instance : has_coe_to_sort (ProfiniteGroup) (Type*) := ⟨λ X, X.to_Profinite⟩
instance (X : ProfiniteGroup) : group X := X.is_group
instance (X : ProfiniteGroup) : topological_group X := X.is_topological_group

def to_Group (X : ProfiniteGroup) : Group := Group.of X
def of_Profinite (X : Profinite) [group X] [topological_group X] : ProfiniteGroup := ⟨X⟩
def of_Group (X : Group) [topological_space X] [compact_space X] [t2_space X]
  [totally_disconnected_space X] [topological_group X] : ProfiniteGroup :=
{ to_Profinite := Profinite.of X,
  is_group := X.group,
  is_topological_group := by assumption }

instance : inhabited ProfiniteGroup := ⟨@ProfiniteGroup.of_Profinite (Profinite.of unit) sorry sorry⟩

instance : category.{v} ProfiniteGroup :=
{ hom := λ M N, continuous_monoid_hom M N,
  id := λ M, continuous_monoid_hom.id (M : Type*),
  comp := λ M N K f g, continuous_monoid_hom.comp g f,
  comp_id' := by intros; ext; refl,
  id_comp' := by intros; ext; refl,
  assoc' := by intros; refl }

def of_Profinite_hom {G H : ProfiniteGroup} (f : G.to_Profinite ⟶ H.to_Profinite)
  (hf : ∀ g h : G, f (g * h) = f g * f h) :
  G ⟶ H := ⟨monoid_hom.mk' f hf, f.2⟩

def of_Profinite_iso {G H : ProfiniteGroup.{u}} (f : G.to_Profinite ≅ H.to_Profinite)
  (hf : ∀ g h : G, f.hom (g * h) = f.hom g * f.hom h) : G ≅ H :=
{ hom := of_Profinite_hom f.hom hf,
  inv := ⟨monoid_hom.inverse (monoid_hom.mk' f.hom hf) f.inv f.hom_inv_id_apply f.inv_hom_id_apply,
    f.inv.2⟩,
  hom_inv_id' := by ext; exact f.hom_inv_id_apply _,
  inv_hom_id' := by ext; exact f.inv_hom_id_apply _ }

def of_Group_iso {G H : ProfiniteGroup} (f : G.to_Group ≅ H.to_Group)
  (hf : @continuous G H _ _ f.hom) : G ≅ H :=
{ hom := ⟨f.hom, hf⟩,
  inv := ⟨f.inv, sorry⟩,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

instance concrete_category : concrete_category.{v} ProfiniteGroup :=
{ forget := { obj := λ X, X, map := λ X Y f, f },
  forget_faithful := ⟨λ X Y f g hfg, by ext; exact congr_fun hfg x⟩ }

instance has_forget_to_Profinite : has_forget₂ ProfiniteGroup Profinite :=
{ forget₂ := { obj := λ X, X.to_Profinite, map := λ X Y f, ⟨f, f.2⟩ } }

instance has_forget_to_Group : has_forget₂ ProfiniteGroup Group :=
{ forget₂ := { obj := λ X, X.to_Group, map := λ X Y f, f.1 } }

instance {X : ProfiniteGroup} : totally_disconnected_space X := infer_instance

@[simp]
lemma coe_to_Profinite {X : ProfiniteGroup} : (X.to_Profinite : Type*) = X :=
rfl
@[simp]
lemma coe_to_Group {X : ProfiniteGroup} : (X.to_Group : Type*) = X :=
rfl

@[simp] lemma coe_id (X : ProfiniteGroup) : (𝟙 X : X → X) = id := rfl

@[simp] lemma coe_comp {X Y Z : ProfiniteGroup}
  (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f := rfl

end ProfiniteGroup

@[simps, derive [faithful]]
def ProfiniteGroup_to_Profinite : ProfiniteGroup ⥤ Profinite := forget₂ _ _

@[simps, derive [faithful]]
def ProfiniteGroup.to_Comphaus : ProfiniteGroup ⥤ CompHaus :=
ProfiniteGroup_to_Profinite ⋙ Profinite_to_CompHaus

@[simps, derive [faithful]]
def ProfiniteGroup.to_Top : ProfiniteGroup ⥤ Top :=
ProfiniteGroup_to_Profinite ⋙ Profinite.to_Top

@[simps, derive [faithful]]
def ProfiniteGroup_to_Group : ProfiniteGroup ⥤ Group := forget₂ _ _

def FinGroup.discrete_topology (A : FinGroup) : topological_space A := ⊥

section discrete_topology
local attribute [instance] FinGroup.discrete_topology

def discrete_topology.topological_group (G : Type*) [group G] [topological_space G]
  [discrete_topology G] : topological_group G :=
{ continuous_mul := continuous_of_discrete_topology,
  continuous_inv := continuous_of_discrete_topology }

@[simps] def FinGroup.to_ProfiniteGroup : FinGroup ⥤ ProfiniteGroup :=
{ obj := λ A, @ProfiniteGroup.of_Profinite (Fintype.to_Profinite.obj A.to_Fintype) (FinGroup.group _)
  (discrete_topology.topological_group _),
  map := λ _ _ f, ⟨f, continuous_of_discrete_topology⟩ }

end discrete_topology

namespace ProfiniteGroup
variables {J : Type u} [small_category J] (F : J ⥤ ProfiniteGroup.{u})

instance thingy_group {J : Type u} [small_category J] (F : J ⥤ ProfiniteGroup.{u}) :
  group ((Profinite.limit_cone.{u} (F ⋙ ProfiniteGroup_to_Profinite)).X) :=
begin
  show group ({u : Π j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j}),
  exact (Group.sections_subgroup.{u u} (F ⋙ ProfiniteGroup_to_Group)).to_group,
end

instance {J : Type u} [small_category J] (F : J ⥤ ProfiniteGroup.{u}) :
  topological_group ((Profinite.limit_cone.{u} (F ⋙ ProfiniteGroup_to_Profinite)).X) :=
{ continuous_mul := sorry,
  continuous_inv := sorry }

def limit_cone_cone {J : Type u} [small_category J] (F : J ⥤ ProfiniteGroup) :
  limits.cone F :=
{ X :=
  { to_Profinite := (Profinite.limit_cone.{u} (F ⋙ ProfiniteGroup_to_Profinite)).X,
    is_group := by apply_instance,
    is_topological_group := by apply_instance },
  π := { app := λ X, of_Profinite_hom
    ((Profinite.limit_cone.{u} (F ⋙ ProfiniteGroup_to_Profinite)).π.app X) sorry }}

def limit_cone_is_limit {J : Type u} [small_category J] (F : J ⥤ ProfiniteGroup) :
  limits.is_limit (limit_cone_cone F) :=
{ lift := λ S, of_Profinite_hom ((Profinite.limit_cone_is_limit.{u} (F ⋙ ProfiniteGroup_to_Profinite)).lift
    (ProfiniteGroup_to_Profinite.map_cone S)) sorry,
  uniq' := λ S m h, sorry }

def limit_cone {J : Type u} [small_category J] (F : J ⥤ ProfiniteGroup) :
  limits.limit_cone F := ⟨limit_cone_cone F, limit_cone_is_limit F⟩

noncomputable def iso_of_bij {G H : ProfiniteGroup.{u}} (f : G ⟶ H) (hf : function.bijective f) :
  G ≅ H :=
ProfiniteGroup.of_Profinite_iso (Profinite.iso_of_bijective
  (ProfiniteGroup_to_Profinite.map f) hf) $ f.1.3

lemma is_iso_of_bij {G H : ProfiniteGroup.{u}} (f : G ⟶ H) (hf : function.bijective f) :
  is_iso f :=
{ out := ⟨(iso_of_bij f hf).inv, sorry⟩ }

lemma is_iso_of_is_Profinite_iso {G H : ProfiniteGroup} (f : G.to_Profinite ⟶ H.to_Profinite)
  (hf : ∀ g h : G, f (g * h) = f g * f h) (h : is_iso f) :
  is_iso (of_Profinite_hom f hf) :=
is_iso_of_bij (of_Profinite_hom f hf) sorry

lemma of_Profinite_hom_of_hom {G H : ProfiniteGroup} (f : G ⟶ H) :
  of_Profinite_hom ((forget₂ ProfiniteGroup Profinite).map f) f.1.3 = f :=
by ext; refl

lemma is_iso_of_is_Profinite_iso' {G H : ProfiniteGroup} (f : G ⟶ H)
  (h : is_iso $ (forget₂ _ Profinite).map f) :
  is_iso f :=
by rw ←of_Profinite_hom_of_hom f at *; exact is_iso_of_is_Profinite_iso _ f.1.3 h

instance : reflects_isomorphisms (forget ProfiniteGroup.{u}) :=
⟨by introsI A B f hf; exact is_iso_of_bij _ ((is_iso_iff_bijective f).mp hf)⟩

instance : reflects_isomorphisms (forget₂ ProfiniteGroup Profinite) :=
{ reflects := λ A B f hf, is_iso_of_is_Profinite_iso' f hf }
open category_theory.limits

instance : preserves_limits (forget₂ ProfiniteGroup Profinite) := sorry


/-
  have G.to_Profinite ≅ lim (disc_quot ⥤ Profinite)
  and forget.map (discquotgrp ⥤ ProfiniteGroup) is a limit in Profinite
  know my lim surjects


-/

#exit
def hmmm (G : Profinite) :
  G.to_Profinite ≅ (forget₂ ProfiniteGroup Profinite).map_cone (limit_cone )


end ProfiniteGroup
