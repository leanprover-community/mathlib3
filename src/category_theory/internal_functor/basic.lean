/-
Copyright (c) 2023 Zach Murray. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zach Murray
-/
import category_theory.category.basic
import category_theory.limits.shapes.pullbacks
import category_theory.internal_category.basic
open category_theory
open category_theory.limits

/-!
# Internal Functors

Defines a functor of internal categories.

# Notation

Each notation for internal functors has a corresponding internal prefunctor notation
ending with an apostrophe.
  - `⟹` : Internal functor arrow.
  - `ι` : Identity internal functor.
  - `›` : Diagrammatically-written composition of internal functors.
  - `arr_x_arr` : Given an internal functor `F : 𝔻 ⟹ 𝔼`, returns
     the arrow `F₁ × F₁ : 𝔻₁ × 𝔻₁ ⟶ 𝔼₁ × 𝔼₁`.
-/

noncomputable theory

namespace category_theory

universes v u

variables {𝔸 : Type u} [category.{v} 𝔸]

/--
A morphism of internal quivers `𝔻` and `𝔼`, denoted by `𝔻 ⟹' 𝔼`.
-/
structure internal_prefunctor (𝔻 𝔼 : internal_quiver 𝔸) :=
(obj : 𝔻.Obj ⟶ 𝔼.Obj)
(arr : 𝔻.Arr ⟶ 𝔼.Arr)
(resp_source' : 𝔻.s ≫ obj = arr ≫ 𝔼.s . obviously)
(resp_target' : 𝔻.t ≫ obj = arr ≫ 𝔼.t . obviously)

open internal_prefunctor

restate_axiom internal_prefunctor.resp_source'
restate_axiom internal_prefunctor.resp_target'
attribute [simp, reassoc] internal_prefunctor.resp_source
attribute [simp, reassoc] internal_prefunctor.resp_target

infixr ` ⟹' ` : 26 := internal_prefunctor

/--
The identity internal prefunctor of an internal quiver `𝔻`, given by `ι' 𝔻`.
-/
def id_internal_prefunctor (𝔻 : internal_quiver 𝔸) : 𝔻 ⟹' 𝔻 :=
{ obj := 𝟙 𝔻.Obj,
  arr := 𝟙 𝔻.Arr }

notation `ι'` := id_internal_prefunctor

@[simp]
lemma id_internal_prefunctor.obj (𝔻 : internal_quiver 𝔸) :
  (ι' 𝔻).obj = 𝟙 𝔻.Obj := rfl

@[simp]
lemma id_internal_prefunctor.arr (𝔻 : internal_quiver 𝔸) :
  (ι' 𝔻).arr = 𝟙 𝔻.Arr := rfl

instance (𝔻 : internal_quiver 𝔸) : inhabited (internal_prefunctor 𝔻 𝔻) :=
⟨id_internal_prefunctor 𝔻⟩

section

variables {𝔻 𝔼 𝔽 : internal_quiver 𝔸}

/--
Helper function for defining composition of internal prefunctors.
-/
private def comp_helper (F : 𝔻 ⟹' 𝔼) (G : 𝔼 ⟹' 𝔽) :
  ∀ {f : 𝔻.Arr ⟶ 𝔻.Obj} {g : 𝔼.Arr ⟶ 𝔼.Obj} {h : 𝔽.Arr ⟶ 𝔽.Obj},
  f ≫ F.obj = F.arr ≫ g →
  g ≫ G.obj = G.arr ≫ h →
  f ≫ (F.obj ≫ G.obj) = (F.arr ≫ G.arr) ≫ h :=
begin
  intros f g h h₁ h₂,
  rw [← category.assoc, h₁, category.assoc, h₂, ← category.assoc],
end

/--
The composition of internal prefunctors `F` and `G`, given by `F ›' G`.
-/
def internal_prefunctor_comp (F : 𝔻 ⟹' 𝔼) (G : 𝔼 ⟹' 𝔽) : 𝔻 ⟹' 𝔽 :=
{ obj := F.obj ≫ G.obj,
  arr := F.arr ≫ G.arr,
  resp_source' := by {rw ← category.assoc, simp [F.resp_source, G.resp_source]},
  resp_target' := by {rw ← category.assoc, simp [F.resp_target, G.resp_target]} }

infixr ` ›' `:80 := internal_prefunctor_comp

section

variables {F : 𝔻 ⟹' 𝔼} {G : 𝔼 ⟹' 𝔽}

@[simp]
lemma internal_prefunctor_comp.obj : (F ›' G).obj = F.obj ≫ G.obj := rfl

@[simp]
lemma internal_prefunctor_comp.arr : (F ›' G).arr = F.arr ≫ G.arr := rfl

end

end

section

variables {𝔻 𝔼 : internal_category 𝔸}

/--
Given an internal prefunctor `F` of `𝔻 𝔼 : internal_category 𝔸`, returns the
unique morphism `arr_x_arr' F : Arr_x_Arr 𝔻 ⟶ Arr_x_Arr 𝔼`, i.e.
`F₁ × F₁ : 𝔻.Arr ×[𝔻.Obj] 𝔻.Arr ⟶ 𝔼.Arr ×[𝔼.Obj] 𝔼.Arr`, induced by
`pullback.fst ≫ F.arr` and `pullback.snd ≫ F.arr`.
-/
def arr_x_arr' (F : 𝔻.to_internal_quiver ⟹' 𝔼.to_internal_quiver) :
  Arr_x_Arr 𝔻 ⟶ Arr_x_Arr 𝔼 :=
pullback.lift (pullback.fst ≫ F.arr) (pullback.snd ≫ F.arr)
(by {
  rw [category.assoc, ← F.resp_target, ← category.assoc, pullback.condition],
  simp [F.resp_source] })

end

/--
Given internal categories `𝔻` and `𝔼`, defines internal functors `𝔻 ⟹ 𝔼`.
-/
structure internal_functor (𝔻 𝔼 : internal_category 𝔸)
extends internal_prefunctor 𝔻.to_internal_quiver 𝔼.to_internal_quiver :=
(resp_id' : 𝔻.e ≫ arr = obj ≫ 𝔼.e . obviously)
(resp_comp' : 𝔻.c ≫ arr = arr_x_arr' to_internal_prefunctor ≫ 𝔼.c . obviously)

restate_axiom internal_functor.resp_id'
restate_axiom internal_functor.resp_comp'

infixr ` ⟹ `:26 := internal_functor

open internal_functor

section

variables {𝔻 𝔼 : internal_category 𝔸}

/--
Given an internal functor `F` of `𝔻 𝔼 : internal_category 𝔸`, returns the
unique morphism `arr_x_arr' F : Arr_x_Arr 𝔻 ⟶ Arr_x_Arr 𝔼`, i.e.
`F₁ × F₁ : 𝔻.Arr ×[𝔻.Obj] 𝔻.Arr ⟶ 𝔼.Arr ×[𝔼.Obj] 𝔼.Arr`, induced by
`pullback.fst ≫ F.arr` and `pullback.snd ≫ F.arr`.
-/
def arr_x_arr (F : 𝔻 ⟹ 𝔼) : Arr_x_Arr 𝔻 ⟶ Arr_x_Arr 𝔼 :=
arr_x_arr' F.to_internal_prefunctor

@[simp]
lemma arr_x_arr.fst (F : 𝔻 ⟹ 𝔼) :
  arr_x_arr F ≫ pullback.fst = pullback.fst ≫ F.arr :=
by {apply pullback.lift_fst}

@[simp]
lemma arr_x_arr.snd (F : 𝔻 ⟹ 𝔼) :
  arr_x_arr F ≫ pullback.snd = pullback.snd ≫ F.arr :=
by apply pullback.lift_snd

end

@[simp]
lemma id_internal_prefunctor_to_identity (𝔻 : internal_category 𝔸) :
  arr_x_arr' (ι' 𝔻.to_internal_quiver) = 𝟙 (Arr_x_Arr 𝔻) :=
begin
  symmetry,
  apply pullback.lift_unique,
  repeat {simp}
end

/--
The identity internal prefunctor of an internal category `𝔻`, given by `ι 𝔻`.
-/
def id_internal_functor (𝔻 : internal_category 𝔸) : 𝔻 ⟹ 𝔻 :=
{ obj := (ι' 𝔻.to_internal_quiver).obj,
  arr := (ι' 𝔻.to_internal_quiver).arr,
  resp_comp' := by {
    have h : 𝔻.c ≫ (ι' 𝔻.to_internal_quiver).arr =
      arr_x_arr' (ι' 𝔻.to_internal_quiver) ≫ 𝔻.c,
    by {simp, dunfold Arr_x_Arr, dunfold Arr_x_Arr', simp},
    exact h } }

notation `ι` := id_internal_functor

@[simp]
lemma id_internal_functor.obj (𝔻 : internal_category 𝔸) :
  (ι 𝔻).obj = 𝟙 𝔻.Obj := rfl

@[simp]
lemma id_internal_functor.arr (𝔻 : internal_category 𝔸) :
  (ι 𝔻).arr = 𝟙 𝔻.Arr := rfl

instance (𝔻 : internal_category 𝔸) : inhabited (internal_functor 𝔻 𝔻) :=
⟨id_internal_functor 𝔻⟩

section

variables {𝔻 𝔼 𝔽 : internal_category 𝔸}

@[simp]
lemma comp_arr_x_arr'
  (F : 𝔻.to_internal_quiver ⟹' 𝔼.to_internal_quiver)
  (G : 𝔼.to_internal_quiver ⟹' 𝔽.to_internal_quiver) :
  arr_x_arr' (F ›' G) = arr_x_arr' F ≫ arr_x_arr' G :=
begin
  symmetry,
  apply pullback.lift_unique,
  repeat {dunfold arr_x_arr', simp}
end

/--
The composition of internal functors `F` and `G`, given by `F › G`.
-/
def internal_functor_comp (F : 𝔻 ⟹ 𝔼) (G : 𝔼 ⟹ 𝔽) : 𝔻 ⟹ 𝔽 :=
{ obj := F.obj ≫ G.obj,
  arr := F.arr ≫ G.arr,
  resp_source' := comp_helper _ _ F.resp_source G.resp_source,
  resp_target' := comp_helper _ _ F.resp_target G.resp_target,
  resp_id' := by {
    rw ← category.assoc,
    simp [F.resp_id, G.resp_id],
  },
  resp_comp' := calc
    𝔻.c ≫ F.arr ≫ G.arr
        = (arr_x_arr' F.to_internal_prefunctor ≫ 𝔼.c) ≫ G.arr : by simp [← F.resp_comp]
    ... = arr_x_arr' (_ ›' _) ≫ 𝔽.c                             : by simp [G.resp_comp] }

infixr ` › `:80 := internal_functor_comp

@[simp]
lemma internal_functor_comp.obj (F : 𝔻 ⟹ 𝔼) (G : 𝔼 ⟹ 𝔽) :
  (F › G).obj = F.obj ≫ G.obj := rfl

@[simp]
lemma internal_functor_comp.arr (F : 𝔻 ⟹ 𝔼) (G : 𝔼 ⟹ 𝔽) :
  (F › G).arr = F.arr ≫ G.arr := rfl

@[simp]
lemma pullback.lift.internal_map.left
  (F : 𝔼 ⟹ 𝔽) (f g : 𝔻.Arr ⟶ 𝔼.Arr) (h : f ≫ 𝔼.t = g ≫ 𝔼.s) :
  pullback.lift f g h ≫ arr_x_arr F =
  pullback.lift (f ≫ F.arr) (g ≫ F.arr)
    (by {simp only [category.assoc, ← F.resp_source, ← F.resp_target], rw [← category.assoc],
         simp [h]}) :=
begin
  apply pullback.lift_unique,
  repeat {simp}
end

end

@[ext]
lemma internal_prefunctor.ext {𝔻 𝔼 : internal_quiver 𝔸} {F G : 𝔻 ⟹' 𝔼}
  (h₁ : F.obj = G.obj) (h₂ : F.arr = G.arr) : F = G :=
begin
  cases F,
  cases G,
  congr'
end

section

variables {𝔻 𝔼 : internal_category 𝔸}

lemma internal_prefunctor_to_functor_equality {F G : 𝔻 ⟹ 𝔼} :
  F = G ↔ F.to_internal_prefunctor = G.to_internal_prefunctor :=
begin
  split,

  rintros rfl, refl,

  intro h,
  cases F,
  cases G,
  congr'
end

@[ext]
lemma internal_functor.ext {F G : 𝔻 ⟹ 𝔼}
  (h₁ : F.obj = G.obj) (h₂ : F.arr = G.arr) : F = G :=
begin
  rw internal_prefunctor_to_functor_equality,
  apply internal_prefunctor.ext,
  exact h₁,
  exact h₂
end

lemma internal_functor_comp_idₗ (F : 𝔻 ⟹ 𝔼) : ι 𝔻 › F = F :=
begin
  ext,
  repeat {simp}
end

lemma internal_functor_comp_idᵣ (F : 𝔻 ⟹ 𝔼) : F › ι 𝔼 = F :=
begin
  ext,
  repeat {simp}
end

end

lemma internal_functor_comp_assoc {𝔻 𝔼 𝔽 𝔾 : internal_category 𝔸}
  (F : 𝔻 ⟹ 𝔼) (G : 𝔼 ⟹ 𝔽) (H : 𝔽 ⟹ 𝔾) :
  (F › G) › H = F › G › H :=
begin
  ext,
  repeat {simp}
end

end category_theory
