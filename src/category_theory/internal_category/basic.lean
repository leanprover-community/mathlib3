/-
Copyright (c) 2023 Zach Murray. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zach Murray
-/
import category_theory.category.basic
import category_theory.limits.shapes.pullbacks
open category_theory
open category_theory.limits

/-!
# Internal Categories

In this file we define categories internal to other categories.

A category internal to a category `𝔸` consists of the following data in `𝔸`:
* An object `Obj : 𝔸` of objects,
* An object `Arr : 𝔸` of arrows,
* Source and target morphisms `s,t : Arr ⟶ Obj`,
* An identity-assigning morphism `e : Obj ⟶ Arr`, and
* A composition morphism `c : Arr ₜ×ₛ Arr ⟶ Arr`,

satisfying the typical category axioms. We do not ask that `𝔸` have all pullbacks, only those used
in specifying the contents and axioms of an internal category.

## Notation

To make the axioms more readable, we implement a number of notations, such as `e_x_id₁` for
`e × 𝟙 C₁ : Obj × Arr ⟶ Arr` and
`Arr_x_Arr_x_Arrₗ` for `(Arr × Arr) × Arr`.
-/

noncomputable theory

namespace category_theory

universes v u

/--
A quiver internal to a category `𝔸`.
-/
structure internal_quiver (𝔸 : Type u) [category.{v} 𝔸] :=
(Obj Arr : 𝔸)
(s t : Arr ⟶ Obj)

open internal_quiver

/--
An internal category without the composition axioms. Defining
this first allows us to define functions to simply state the
axioms of an internal category.
-/
structure internal_category_struct (𝔸 : Type u) [category.{v} 𝔸]
extends internal_quiver 𝔸 :=
(e : Obj ⟶ Arr)
(has_comp' : has_pullback t s)
(c : pullback t s ⟶ Arr)
(has_assocₗ' : has_pullback (c ≫ t) s)
(has_assocᵣ': has_pullback t (c ≫ s))
(id_source' : e ≫ s = 𝟙 Obj . obviously)
(id_target' : e ≫ t = 𝟙 Obj . obviously)
(comp_source' : c ≫ s = pullback.fst ≫ s . obviously)
(comp_target' : c ≫ t = pullback.snd ≫ t . obviously)

open internal_category_struct

restate_axiom internal_category_struct.has_comp'
restate_axiom internal_category_struct.has_assocₗ'
restate_axiom internal_category_struct.has_assocᵣ'
restate_axiom internal_category_struct.id_source'
restate_axiom internal_category_struct.id_target'
restate_axiom internal_category_struct.comp_source'
restate_axiom internal_category_struct.comp_target'
attribute [simp] internal_category_struct.id_source
attribute [simp] internal_category_struct.id_target
attribute [simp] internal_category_struct.comp_source
attribute [simp] internal_category_struct.comp_target

section

variables {𝔸 : Type u} [category.{v} 𝔸]

section

variable (𝔻 : internal_category_struct 𝔸)

instance comp : has_pullback 𝔻.t 𝔻.s := 𝔻.has_comp'
instance assocₗ : has_pullback (𝔻.c ≫ 𝔻.t) 𝔻.s := 𝔻.has_assocₗ'
instance assocᵣ : has_pullback 𝔻.t (𝔻.c ≫ 𝔻.s) := 𝔻.has_assocᵣ'

/--
The object `𝔻.Arr ×[𝔻.Obj] 𝔻.Arr`.
-/
def Arr_x_Arr' : 𝔸 := pullback 𝔻.t 𝔻.s

/--
The object `(𝔻.Arr ×[𝔻.Obj] 𝔻.Arr) ×[𝔻.Obj] 𝔻.Arr`.
-/
def Arr_x_Arr_x_Arrₗ' : 𝔸 := pullback (𝔻.c ≫ 𝔻.t) 𝔻.s

/--
The object `𝔻.Arr ×[𝔻.Obj] (𝔻.Arr ×[𝔻.Obj] 𝔻.Arr)`.
-/
def Arr_x_Arr_x_Arrᵣ' : 𝔸 := pullback 𝔻.t (𝔻.c ≫ 𝔻.s)

/--
The unique arrow `(𝔻.Arr ×[𝔻.Obj] 𝔻.Arr) ×[𝔻.Obj] 𝔻.Arr ⟶ 𝔻.Arr ×[𝔻.Obj] 𝔻.Arr`
induced by `pullback.fst ≫ pullback.snd` and `pullback.snd`.
-/
def l_to_r_pair : Arr_x_Arr_x_Arrₗ' 𝔻 ⟶ Arr_x_Arr' 𝔻 :=
pullback.lift (pullback.fst ≫ pullback.snd) pullback.snd
(by {simp only [category.assoc, ← 𝔻.comp_target], exact pullback.condition})

/--
The associator to be used in the definition of an internal category.
-/
def associator' : Arr_x_Arr_x_Arrₗ' 𝔻 ⟶ Arr_x_Arr_x_Arrᵣ' 𝔻 :=
pullback.lift (pullback.fst ≫ pullback.fst) (l_to_r_pair 𝔻)
(by {
  rw category.assoc,
  have h : l_to_r_pair 𝔻 ≫ pullback.fst = pullback.fst ≫ pullback.snd,
  by apply pullback.lift_fst,
  rw [pullback.condition, ← category.assoc, ← h, category.assoc, ← 𝔻.comp_source]})

/--
Given the composition `c` to be used in an internal category `𝔻`, define the unique
morphism `(𝔻.Arr ×[𝔻.Obj] 𝔻.Arr) ×[𝔻.Obj] 𝔻.Arr ⟶ 𝔻.Arr ×[𝔻.Obj] 𝔻.Arr`
induced by `pullback.fst ≫ c` and `pullback.snd`.
-/
def c_x_id₁' : Arr_x_Arr_x_Arrₗ' 𝔻 ⟶ Arr_x_Arr' 𝔻 :=
pullback.lift (pullback.fst ≫ 𝔻.c) pullback.snd
(by {simp only [category.assoc, ← 𝔻.comp_target], apply pullback.condition})

/--
Given the composition `c` to be used in an internal category `𝔻`, define the unique
morphism `𝔻.Arr ×[𝔻.Obj] (𝔻.Arr ×[𝔻.Obj] 𝔻.Arr) ⟶ 𝔻.Arr ×[𝔻.Obj] 𝔻.Arr`
induced by `pullback.fst` and `pullback.snd ≫ c`.
-/
def id₁_x_c' : Arr_x_Arr_x_Arrᵣ' 𝔻 ⟶ Arr_x_Arr' 𝔻 :=
pullback.lift pullback.fst (pullback.snd ≫ 𝔻.c)
(by {simp only [category.assoc, ← 𝔻.comp_target], apply pullback.condition})

/--
Given the source `s` and identity-assigning morphism `e` to be used in an internal
category `𝔻`, define the unique morphism `𝔻.Arr ⟶ 𝔻.Arr ×[𝔻.Obj] 𝔻.Arr` induced
by `s ≫ e` and `𝟙 𝔻.Arr`.
-/
def e_x_id₁' : 𝔻.Arr ⟶ Arr_x_Arr' 𝔻 :=
pullback.lift (𝔻.s ≫ 𝔻.e) (𝟙 𝔻.Arr) (by simp)

/--
Given the target `t` and identity-assigning morphism `e` to be used in an internal
category `𝔻`, define the unique morphism `𝔻.Arr ⟶ 𝔻.Arr ×[𝔻.Obj] 𝔻.Arr` induced
by `𝟙 𝔻.Arr` and `t ≫ e`.
-/
def id₁_x_e' : 𝔻.Arr ⟶ Arr_x_Arr' 𝔻 :=
pullback.lift (𝟙 𝔻.Arr) (𝔻.t ≫ 𝔻.e) (by simp)

end

/--
Defines a category internal to a category `𝔸`.
-/
structure internal_category (𝔸 : Type u) [category.{v} 𝔸]
extends internal_category_struct 𝔸 :=
(assoc' : associator' _ ≫ id₁_x_c' _ ≫ c = c_x_id₁' _ ≫ c . obviously)
(id_left' : e_x_id₁' _≫ c = 𝟙 Arr . obviously)
(id_right' : id₁_x_e' _ ≫ c = 𝟙 Arr . obviously)

restate_axiom internal_category.assoc'
restate_axiom internal_category.id_left'
restate_axiom internal_category.id_right'
attribute [simp] internal_category.id_left
attribute [simp] internal_category.id_right

open internal_category

section

variables (𝔻 : internal_category 𝔸)

/--
The un-ticked version of `Arr_x_Arr'`, intended for `internal_category`
rather than `internal_category_struct`.
-/
def Arr_x_Arr : 𝔸 := Arr_x_Arr' 𝔻.to_internal_category_struct

/--
The un-ticked version of `Arr_x_Arr_x_Arrₗ'`, intended for `internal_category`
rather than `internal_category_struct`.
-/
def Arr_x_Arr_x_Arrₗ : 𝔸 := Arr_x_Arr_x_Arrₗ' 𝔻.to_internal_category_struct

/--
The un-ticked version of `Arr_x_Arr_x_Arrᵣ'`, intended for `internal_category`
rather than `internal_category_struct`.
-/
def Arr_x_Arr_x_Arrᵣ : 𝔸 := Arr_x_Arr_x_Arrᵣ' 𝔻.to_internal_category_struct

/--
The un-ticked version of `id₁_x_e'`, intended for `internal_category`
rather than `internal_category_struct`.
-/
def id₁_x_e := id₁_x_e' 𝔻.to_internal_category_struct

/--
The un-ticked version of `e_x_id₁'`, intended for `internal_category`
rather than `internal_category_struct`.
-/
def e_x_id₁ := e_x_id₁' 𝔻.to_internal_category_struct

/--
The un-ticked version of `c_x_id₁'`, intended for `internal_category`
rather than `internal_category_struct`.
-/
def c_x_id₁ := c_x_id₁' 𝔻.to_internal_category_struct

/--
The un-ticked version of `id₁_x_c'`, intended for `internal_category`
rather than `internal_category_struct`.
-/
def id₁_x_c := id₁_x_c' 𝔻.to_internal_category_struct

/--
The un-ticked version of `associator'`, intended for `internal_category`
rather than `internal_category_struct`.
-/
def associator := associator' 𝔻.to_internal_category_struct

@[simp]
lemma internal_category.id_left₂ : e_x_id₁ 𝔻 ≫ 𝔻.c = 𝟙 𝔻.Arr :=
𝔻.id_left

@[simp]
lemma internal_category.id_right₂ : id₁_x_e 𝔻 ≫ 𝔻.c = 𝟙 𝔻.Arr :=
𝔻.id_right

end

section

variables {𝔻 𝔼 : internal_category 𝔸}
          {X : 𝔸} (f g h : X ⟶ 𝔼.Arr)
          (h₁ : f ≫ 𝔼.t = g ≫ 𝔼.s) (h₂ : g ≫ 𝔼.t = h ≫ 𝔼.s)

include h₁ h₂

lemma pullback.lift_associate_comp_left :
  pullback.lift (pullback.lift f g h₁) h (by simpa) ≫ c_x_id₁ 𝔼 =
  pullback.lift (pullback.lift f g h₁ ≫ 𝔼.c) h (by simpa) :=
begin
  apply pullback.lift_unique,
  repeat {
    dunfold c_x_id₁,
    dunfold c_x_id₁',
   simp }
end

lemma pullback.lift_associate_comp_right :
  pullback.lift f (pullback.lift g h h₂) (by simpa) ≫ id₁_x_c 𝔼 =
  pullback.lift f (pullback.lift g h h₂ ≫ 𝔼.c) (by simpa) :=
begin
  apply pullback.lift_unique,
  repeat {
    dunfold id₁_x_c,
    dunfold id₁_x_c',
    simp }
end

lemma pullback.lift_associator :
  pullback.lift (pullback.lift f g h₁) h (by simpa) ≫ associator 𝔼 =
  pullback.lift f (pullback.lift g h h₂) (by simpa) :=
begin
  apply pullback.lift_unique,

  repeat {
    dunfold associator,
    dunfold associator',
    simp },
  dunfold l_to_r_pair,
  rw ← pullback.lift_comp,
  simp
end

@[simp]
lemma pullback.lift_assoc :
  pullback.lift (pullback.lift f g h₁ ≫ 𝔼.c) h (by simpa) ≫ 𝔼.c =
  pullback.lift f (pullback.lift g h h₂ ≫ 𝔼.c) (by simpa) ≫ 𝔼.c :=
begin
  rw [← pullback.lift_associate_comp_left, ← pullback.lift_associate_comp_right,
      ← pullback.lift_associator],
  dunfold associator,
  dunfold c_x_id₁,
  dunfold id₁_x_c,
  simp only [category.assoc, 𝔼.assoc]
end

end

section

variables {𝔻 𝔼 : internal_category 𝔸}

@[simp]
lemma pullback.lift_id_left {X : 𝔸} (f : X ⟶ 𝔼.Arr) :
  pullback.lift (f ≫ 𝔼.s ≫ 𝔼.e) f (by simp) = f ≫ e_x_id₁ 𝔼 :=
begin
  symmetry,
  apply pullback.lift_unique,
  repeat {
    dunfold e_x_id₁,
    dunfold e_x_id₁',
    simp }
end

@[simp]
lemma pullback.lift_id_right {X : 𝔸} (f : X ⟶ 𝔼.Arr) :
  pullback.lift f (f ≫ 𝔼.t ≫ 𝔼.e) (by simp) = f ≫ id₁_x_e 𝔼 :=
begin
  symmetry,
  apply pullback.lift_unique,
  repeat {
    dunfold id₁_x_e,
    dunfold id₁_x_e',
    simp }
end

end

end

end category_theory
#lint
