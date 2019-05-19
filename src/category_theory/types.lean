-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl

import category_theory.functor_category
import category_theory.fully_faithful
import data.equiv.basic

namespace category_theory

universes v v' w u u' -- declare the `v`'s first; see `category_theory.category` for an explanation

instance types : large_category (Sort u) :=
{ hom     := λ a b, (a → b),
  id      := λ a, id,
  comp    := λ _ _ _ f g, g ∘ f }

@[simp] lemma types_hom {α β : Sort u} : (α ⟶ β) = (α → β) := rfl
@[simp] lemma types_id (X : Sort u) : 𝟙 X = id := rfl
@[simp] lemma types_comp {X Y Z : Sort u} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = g ∘ f := rfl

namespace functor_to_types
variables {C : Sort u} [𝒞 : category.{v} C] (F G H : C ⥤ Sort w) {X Y Z : C}
include 𝒞
variables (σ : F ⟶ G) (τ : G ⟶ H)

@[simp] lemma map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) : (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) :=
by simp

@[simp] lemma map_id (a : F.obj X) : (F.map (𝟙 X)) a = a :=
by simp

lemma naturality (f : X ⟶ Y) (x : F.obj X) : σ.app Y ((F.map f) x) = (G.map f) (σ.app X x) :=
congr_fun (σ.naturality f) x

@[simp] lemma comp (x : F.obj X) : (σ ≫ τ).app X x = τ.app X (σ.app X x) := rfl

variables {D : Sort u'} [𝒟 : category.{u'} D] (I J : D ⥤ C) (ρ : I ⟶ J) {W : D}

@[simp] lemma hcomp (x : (I ⋙ F).obj W) : (ρ ◫ σ).app W x = (G.map (ρ.app W)) (σ.app (I.obj W) x) := rfl

end functor_to_types

def ulift_trivial (V : Type u) : ulift.{u} V ≅ V := by tidy

def ulift_functor : Type u ⥤ Type (max u v) :=
{ obj := λ X, ulift.{v} X,
  map := λ X Y f, λ x : ulift.{v} X, ulift.up (f x.down) }

@[simp] lemma ulift_functor.map {X Y : Type u} (f : X ⟶ Y) (x : ulift.{v} X) :
  ulift_functor.map f x = ulift.up (f x.down) := rfl

instance ulift_functor_faithful : fully_faithful ulift_functor :=
{ preimage := λ X Y f x, (f (ulift.up x)).down,
  injectivity' := λ X Y f g p, funext $ λ x,
    congr_arg ulift.down ((congr_fun p (ulift.up x)) : ((ulift.up (f x)) = (ulift.up (g x)))) }

def hom_of_element {X : Type u} (x : X) : punit ⟶ X := λ _, x

lemma hom_of_element_eq_iff {X : Type u} (x y : X) :
  hom_of_element x = hom_of_element y ↔ x = y :=
⟨λ H, congr_fun H punit.star, by cc⟩

lemma mono_iff_injective {X Y : Type u} (f : X ⟶ Y) : mono f ↔ function.injective f :=
begin
  split,
  { intros H x x' h,
    resetI,
    rw ←hom_of_element_eq_iff at ⊢ h,
    exact (cancel_mono f).mp h },
  { refine λ H, ⟨λ Z g h H₂, _⟩,
    ext z,
    replace H₂ := congr_fun H₂ z,
    exact H H₂ }
end

lemma epi_iff_surjective {X Y : Type u} (f : X ⟶ Y) : epi f ↔ function.surjective f :=
begin
  split,
  { intros H,
    let g : Y ⟶ ulift Prop := λ y, ⟨true⟩,
    let h : Y ⟶ ulift Prop := λ y, ⟨∃ x, f x = y⟩,
    suffices : f ≫ g = f ≫ h,
    { resetI,
      rw cancel_epi at this,
      intro y,
      replace this := congr_fun this y,
      replace this : true = ∃ x, f x = y := congr_arg ulift.down this,
      rw ←this,
      trivial },
    ext x,
    change true ↔ ∃ x', f x' = f x,
    rw true_iff,
    exact ⟨x, rfl⟩ },
  { intro H,
    constructor,
    intros Z g h H₂,
    apply funext,
    rw ←forall_iff_forall_surj H,
    intro x,
    exact (congr_fun H₂ x : _) }
end

end category_theory

-- Isomorphisms in Type and equivalences.

namespace equiv

universe u

variables {X Y : Sort u}

def to_iso (e : X ≃ Y) : X ≅ Y :=
{ hom := e.to_fun,
  inv := e.inv_fun,
  hom_inv_id' := funext e.left_inv,
  inv_hom_id' := funext e.right_inv }

@[simp] lemma to_iso_hom {e : X ≃ Y} : e.to_iso.hom = e := rfl
@[simp] lemma to_iso_inv {e : X ≃ Y} : e.to_iso.inv = e.symm := rfl

end equiv

namespace category_theory.iso

universe u

variables {X Y : Sort u}

def to_equiv (i : X ≅ Y) : X ≃ Y :=
{ to_fun := i.hom,
  inv_fun := i.inv,
  left_inv := λ x, congr_fun i.hom_inv_id x,
  right_inv := λ y, congr_fun i.inv_hom_id y }

@[simp] lemma to_equiv_fun (i : X ≅ Y) : (i.to_equiv : X → Y) = i.hom := rfl
@[simp] lemma to_equiv_symm_fun (i : X ≅ Y) : (i.to_equiv.symm : Y → X) = i.inv := rfl

end category_theory.iso
