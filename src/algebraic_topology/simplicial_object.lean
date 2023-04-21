/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import algebraic_topology.simplex_category
import category_theory.arrow
import category_theory.limits.functor_category
import category_theory.opposites

/-!
# Simplicial objects in a category.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A simplicial object in a category `C` is a `C`-valued presheaf on `simplex_category`.
(Similarly a cosimplicial object is functor `simplex_category ⥤ C`.)

Use the notation `X _[n]` in the `simplicial` locale to obtain the `n`-th term of a
(co)simplicial object `X`, where `n` is a natural number.

-/

open opposite
open category_theory
open category_theory.limits

universes v u v' u'

namespace category_theory

variables (C : Type u) [category.{v} C]

/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from `simplex_category` to `C`. -/
@[derive category, nolint has_nonempty_instance]
def simplicial_object := simplex_categoryᵒᵖ ⥤ C

namespace simplicial_object

localized "notation (name := simplicial_object.at) X ` _[`:1000 n `]` :=
  (X : category_theory.simplicial_object hole!).obj (opposite.op (simplex_category.mk n))"
  in simplicial

instance {J : Type v} [small_category J] [has_limits_of_shape J C] :
  has_limits_of_shape J (simplicial_object C) := by {dsimp [simplicial_object], apply_instance}

instance [has_limits C] : has_limits (simplicial_object C) := ⟨infer_instance⟩

instance {J : Type v} [small_category J] [has_colimits_of_shape J C] :
  has_colimits_of_shape J (simplicial_object C) := by {dsimp [simplicial_object], apply_instance}

instance [has_colimits C] : has_colimits (simplicial_object C) := ⟨infer_instance⟩

variables {C} (X : simplicial_object C)

/-- Face maps for a simplicial object. -/
def δ {n} (i : fin (n+2)) : X _[n+1] ⟶ X _[n] :=
X.map (simplex_category.δ i).op

/-- Degeneracy maps for a simplicial object. -/
def σ {n} (i : fin (n+1)) : X _[n] ⟶ X _[n+1] :=
X.map (simplex_category.σ i).op


/-- Isomorphisms from identities in ℕ. -/
def eq_to_iso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
X.map_iso (eq_to_iso (by rw h))

@[simp] lemma eq_to_iso_refl {n : ℕ} (h : n = n) : X.eq_to_iso h = iso.refl _ :=
by { ext, simp [eq_to_iso], }


/-- The generic case of the first simplicial identity -/
@[reassoc]
lemma δ_comp_δ {n} {i j : fin (n+2)} (H : i ≤ j) :
  X.δ j.succ ≫ X.δ i = X.δ i.cast_succ ≫ X.δ j :=
by { dsimp [δ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_δ H] }

@[reassoc]
lemma δ_comp_δ' {n} {i : fin (n+2)} {j : fin (n+3)} (H : i.cast_succ < j) :
  X.δ j ≫ X.δ i = X.δ i.cast_succ ≫
    X.δ (j.pred (λ hj, by simpa only [hj, fin.not_lt_zero] using H)) :=
by { dsimp [δ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_δ' H] }

@[reassoc]
lemma δ_comp_δ'' {n} {i : fin (n+3)} {j : fin (n+2)} (H : i ≤ j.cast_succ) :
  X.δ j.succ ≫ X.δ (i.cast_lt (nat.lt_of_le_of_lt (fin.le_iff_coe_le_coe.mp H) j.is_lt)) =
    X.δ i ≫ X.δ j :=
by { dsimp [δ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_δ'' H] }

/-- The special case of the first simplicial identity -/
@[reassoc]
lemma δ_comp_δ_self {n} {i : fin (n+2)} : X.δ i.cast_succ ≫ X.δ i = X.δ i.succ ≫ X.δ i :=
by { dsimp [δ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_δ_self] }

@[reassoc]
lemma δ_comp_δ_self' {n} {j : fin (n+3)} {i : fin (n+2)} (H : j = i.cast_succ) :
  X.δ j ≫ X.δ i = X.δ i.succ ≫ X.δ i :=
by { subst H, rw δ_comp_δ_self, }

/-- The second simplicial identity -/
@[reassoc]
lemma δ_comp_σ_of_le {n} {i : fin (n+2)} {j : fin (n+1)} (H : i ≤ j.cast_succ) :
  X.σ j.succ ≫ X.δ i.cast_succ = X.δ i ≫ X.σ j :=
by { dsimp [δ, σ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_of_le H] }

/-- The first part of the third simplicial identity -/
@[reassoc]
lemma δ_comp_σ_self {n} {i : fin (n+1)} :
  X.σ i ≫ X.δ i.cast_succ = 𝟙 _ :=
begin
  dsimp [δ, σ],
  simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_self, op_id, X.map_id],
end

@[reassoc]
lemma δ_comp_σ_self' {n} {j : fin (n+2)} {i : fin (n+1)} (H : j = i.cast_succ):
  X.σ i ≫ X.δ j = 𝟙 _ := by { subst H, rw δ_comp_σ_self, }

/-- The second part of the third simplicial identity -/
@[reassoc]
lemma δ_comp_σ_succ {n} {i : fin (n+1)} :
  X.σ i ≫ X.δ i.succ = 𝟙 _ :=
begin
  dsimp [δ, σ],
  simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_succ, op_id, X.map_id],
end

@[reassoc]
lemma δ_comp_σ_succ' {n} {j : fin (n+2)} {i : fin (n+1)} (H : j = i.succ) :
  X.σ i ≫ X.δ j = 𝟙 _ := by { subst H, rw δ_comp_σ_succ, }

/-- The fourth simplicial identity -/
@[reassoc]
lemma δ_comp_σ_of_gt {n} {i : fin (n+2)} {j : fin (n+1)} (H : j.cast_succ < i) :
  X.σ j.cast_succ ≫ X.δ i.succ = X.δ i ≫ X.σ j :=
by { dsimp [δ, σ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_of_gt H] }

@[reassoc]
lemma δ_comp_σ_of_gt' {n} {i : fin (n+3)} {j : fin (n+2)} (H : j.succ < i) :
  X.σ j ≫ X.δ i = X.δ (i.pred (λ hi, by simpa only [fin.not_lt_zero, hi] using H)) ≫
    X.σ (j.cast_lt ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le
      (by simpa only [fin.val_eq_coe, ← fin.coe_succ]
        using fin.lt_iff_coe_lt_coe.mp H) i.is_le))) :=
by { dsimp [δ, σ], simpa only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_of_gt' H], }

/-- The fifth simplicial identity -/
@[reassoc]
lemma σ_comp_σ {n} {i j : fin (n+1)} (H : i ≤ j) :
  X.σ j ≫ X.σ i.cast_succ = X.σ i ≫ X.σ j.succ :=
by { dsimp [δ, σ], simp only [←X.map_comp, ←op_comp, simplex_category.σ_comp_σ H] }

open_locale simplicial

@[simp, reassoc]
lemma δ_naturality {X' X : simplicial_object C} (f : X ⟶ X') {n : ℕ} (i : fin (n+2)) :
  X.δ i ≫ f.app (op [n]) = f.app (op [n+1]) ≫ X'.δ i := f.naturality _

@[simp, reassoc]
lemma σ_naturality {X' X : simplicial_object C} (f : X ⟶ X') {n : ℕ} (i : fin (n+1)) :
  X.σ i ≫ f.app (op [n+1]) = f.app (op [n]) ≫ X'.σ i := f.naturality _

variable (C)

/-- Functor composition induces a functor on simplicial objects. -/
@[simps]
def whiskering (D : Type*) [category D] :
  (C ⥤ D) ⥤ simplicial_object C ⥤ simplicial_object D :=
whiskering_right _ _ _

/-- Truncated simplicial objects. -/
@[derive category, nolint has_nonempty_instance]
def truncated (n : ℕ) := (simplex_category.truncated n)ᵒᵖ ⥤ C

variable {C}

namespace truncated

instance {n} {J : Type v} [small_category J] [has_limits_of_shape J C] :
  has_limits_of_shape J (simplicial_object.truncated C n) := by {dsimp [truncated], apply_instance}

instance {n} [has_limits C] : has_limits (simplicial_object.truncated C n) := ⟨infer_instance⟩

instance {n} {J : Type v} [small_category J] [has_colimits_of_shape J C] :
  has_colimits_of_shape J (simplicial_object.truncated C n) :=
by {dsimp [truncated], apply_instance}

instance {n} [has_colimits C] : has_colimits (simplicial_object.truncated C n) := ⟨infer_instance⟩

variable (C)

/-- Functor composition induces a functor on truncated simplicial objects. -/
@[simps]
def whiskering {n} (D : Type*) [category D] :
  (C ⥤ D) ⥤ truncated C n ⥤ truncated D n :=
whiskering_right _ _ _

variable {C}

end truncated

section skeleton

/-- The skeleton functor from simplicial objects to truncated simplicial objects. -/
def sk (n : ℕ) : simplicial_object C ⥤ simplicial_object.truncated C n :=
(whiskering_left _ _ _).obj simplex_category.truncated.inclusion.op

end skeleton

variable (C)

/-- The constant simplicial object is the constant functor. -/
abbreviation const : C ⥤ simplicial_object C := category_theory.functor.const _

/-- The category of augmented simplicial objects, defined as a comma category. -/
@[derive category, nolint has_nonempty_instance]
def augmented := comma (𝟭 (simplicial_object C)) (const C)

variable {C}

namespace augmented

/-- Drop the augmentation. -/
@[simps]
def drop : augmented C ⥤ simplicial_object C := comma.fst _ _

/-- The point of the augmentation. -/
@[simps]
def point : augmented C ⥤ C := comma.snd _ _

/-- The functor from augmented objects to arrows. -/
@[simps]
def to_arrow : augmented C ⥤ arrow C :=
{ obj := λ X,
  { left := (drop.obj X) _[0],
    right := (point.obj X),
    hom := X.hom.app _ },
  map := λ X Y η,
  { left := (drop.map η).app _,
    right := (point.map η),
    w' := begin
      dsimp,
      rw ← nat_trans.comp_app,
      erw η.w,
      refl,
    end } }

/-- The compatibility of a morphism with the augmentation, on 0-simplices -/
@[reassoc]
lemma w₀ {X Y : augmented C} (f : X ⟶ Y) :
  (augmented.drop.map f).app (op (simplex_category.mk 0)) ≫
    Y.hom.app (op (simplex_category.mk 0)) =
  X.hom.app (op (simplex_category.mk 0)) ≫ augmented.point.map f :=
by convert congr_app f.w (op (simplex_category.mk 0))

variable (C)

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simp]
def whiskering_obj (D : Type*) [category D] (F : C ⥤ D) :
  augmented C ⥤ augmented D :=
{ obj := λ X,
  { left := ((whiskering _ _).obj F).obj (drop.obj X),
    right := F.obj (point.obj X),
    hom := whisker_right X.hom F ≫ (functor.const_comp _ _ _).hom },
  map := λ X Y η,
  { left := whisker_right η.left _,
    right := F.map η.right,
    w' := begin
      ext,
      dsimp,
      rw [category.comp_id, category.comp_id, ← F.map_comp, ← F.map_comp, ← nat_trans.comp_app],
      erw η.w,
      refl,
    end } }

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simps]
def whiskering (D : Type u') [category.{v'} D] :
  (C ⥤ D) ⥤ augmented C ⥤ augmented D :=
{ obj := whiskering_obj _ _,
  map := λ X Y η,
  { app := λ A,
    { left := whisker_left _ η,
      right := η.app _,
      w' := begin
        ext n,
        dsimp,
        rw [category.comp_id, category.comp_id, η.naturality],
      end }, }, }

variable {C}

end augmented

/-- Augment a simplicial object with an object. -/
@[simps]
def augment (X : simplicial_object C) (X₀ : C) (f : X _[0] ⟶ X₀)
  (w : ∀ (i : simplex_category) (g₁ g₂ : [0] ⟶ i),
    X.map g₁.op ≫ f = X.map g₂.op ≫ f) : simplicial_object.augmented C :=
{ left := X,
  right := X₀,
  hom :=
  { app := λ i, X.map (simplex_category.const i.unop 0).op ≫ f,
    naturality' := begin
      intros i j g,
      dsimp,
      rw ← g.op_unop,
      simpa only [← X.map_comp, ← category.assoc, category.comp_id, ← op_comp] using w _ _ _,
    end } }

@[simp]
lemma augment_hom_zero (X : simplicial_object C) (X₀ : C) (f : X _[0] ⟶ X₀) (w) :
  (X.augment X₀ f w).hom.app (op [0]) = f :=
by { dsimp, rw [simplex_category.hom_zero_zero ([0].const 0), op_id, X.map_id, category.id_comp] }

end simplicial_object

/-- Cosimplicial objects. -/
@[derive category, nolint has_nonempty_instance]
def cosimplicial_object := simplex_category ⥤ C

namespace cosimplicial_object

localized "notation (name := cosimplicial_object.at) X ` _[`:1000 n `]` :=
  (X : category_theory.cosimplicial_object hole!).obj (simplex_category.mk n)" in simplicial

instance {J : Type v} [small_category J] [has_limits_of_shape J C] :
  has_limits_of_shape J (cosimplicial_object C) := by {dsimp [cosimplicial_object], apply_instance}

instance [has_limits C] : has_limits (cosimplicial_object C) := ⟨infer_instance⟩

instance {J : Type v} [small_category J] [has_colimits_of_shape J C] :
  has_colimits_of_shape J (cosimplicial_object C) :=
by {dsimp [cosimplicial_object], apply_instance}

instance [has_colimits C] : has_colimits (cosimplicial_object C) := ⟨infer_instance⟩

variables {C} (X : cosimplicial_object C)

/-- Coface maps for a cosimplicial object. -/
def δ {n} (i : fin (n+2)) : X _[n] ⟶ X _[n+1] :=
X.map (simplex_category.δ i)

/-- Codegeneracy maps for a cosimplicial object. -/
def σ {n} (i : fin (n+1)) : X _[n+1] ⟶ X _[n] :=
X.map (simplex_category.σ i)

/-- Isomorphisms from identities in ℕ. -/
def eq_to_iso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
X.map_iso (eq_to_iso (by rw h))

@[simp] lemma eq_to_iso_refl {n : ℕ} (h : n = n) : X.eq_to_iso h = iso.refl _ :=
by { ext, simp [eq_to_iso], }

/-- The generic case of the first cosimplicial identity -/
@[reassoc]
lemma δ_comp_δ {n} {i j : fin (n+2)} (H : i ≤ j) :
  X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ i.cast_succ :=
by { dsimp [δ], simp only [←X.map_comp, simplex_category.δ_comp_δ H], }

@[reassoc]
lemma δ_comp_δ' {n} {i : fin (n+2)} {j : fin (n+3)} (H : i.cast_succ < j) :
  X.δ i ≫ X.δ j = X.δ (j.pred (λ hj, by simpa only [hj, fin.not_lt_zero] using H)) ≫
    X.δ i.cast_succ :=
by { dsimp [δ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_δ' H] }

@[reassoc]
lemma δ_comp_δ'' {n} {i : fin (n+3)} {j : fin (n+2)} (H : i ≤ j.cast_succ) :
  X.δ (i.cast_lt (nat.lt_of_le_of_lt (fin.le_iff_coe_le_coe.mp H) j.is_lt)) ≫ X.δ j.succ =
    X.δ j ≫ X.δ i :=
by { dsimp [δ], simp only [←X.map_comp, ←op_comp, simplex_category.δ_comp_δ'' H] }

/-- The special case of the first cosimplicial identity -/
@[reassoc]
lemma δ_comp_δ_self {n} {i : fin (n+2)} : X.δ i ≫ X.δ i.cast_succ = X.δ i ≫ X.δ i.succ :=
by { dsimp [δ], simp only [←X.map_comp, simplex_category.δ_comp_δ_self] }

@[reassoc]
lemma δ_comp_δ_self' {n} {i : fin (n+2)} {j : fin (n+3)} (H : j = i.cast_succ) :
  X.δ i ≫ X.δ j = X.δ i ≫ X.δ i.succ :=
by { subst H, rw δ_comp_δ_self, }

/-- The second cosimplicial identity -/
@[reassoc]
lemma δ_comp_σ_of_le {n} {i : fin (n+2)} {j : fin (n+1)} (H : i ≤ j.cast_succ) :
  X.δ i.cast_succ ≫ X.σ j.succ = X.σ j ≫ X.δ i :=
by { dsimp [δ, σ], simp only [←X.map_comp, simplex_category.δ_comp_σ_of_le H] }

/-- The first part of the third cosimplicial identity -/
@[reassoc]
lemma δ_comp_σ_self {n} {i : fin (n+1)} :
  X.δ i.cast_succ ≫ X.σ i = 𝟙 _ :=
begin
  dsimp [δ, σ],
  simp only [←X.map_comp, simplex_category.δ_comp_σ_self, X.map_id],
end

@[reassoc]
lemma δ_comp_σ_self' {n} {j : fin (n+2)} {i : fin (n+1)} (H : j = i.cast_succ) :
  X.δ j ≫ X.σ i = 𝟙 _ :=
by { subst H, rw δ_comp_σ_self, }

/-- The second part of the third cosimplicial identity -/
@[reassoc]
lemma δ_comp_σ_succ {n} {i : fin (n+1)} :
  X.δ i.succ ≫ X.σ i = 𝟙 _ :=
begin
  dsimp [δ, σ],
  simp only [←X.map_comp, simplex_category.δ_comp_σ_succ, X.map_id],
end

@[reassoc]
lemma δ_comp_σ_succ' {n} {j : fin (n+2)} {i : fin (n+1)} (H : j = i.succ) :
  X.δ j ≫ X.σ i = 𝟙 _ :=
by { subst H, rw δ_comp_σ_succ, }

/-- The fourth cosimplicial identity -/
@[reassoc]
lemma δ_comp_σ_of_gt {n} {i : fin (n+2)} {j : fin (n+1)} (H : j.cast_succ < i) :
  X.δ i.succ ≫ X.σ j.cast_succ = X.σ j ≫ X.δ i :=
by { dsimp [δ, σ], simp only [←X.map_comp, simplex_category.δ_comp_σ_of_gt H] }

@[reassoc]
lemma δ_comp_σ_of_gt' {n} {i : fin (n+3)} {j : fin (n+2)} (H : j.succ < i) :
  X.δ i ≫ X.σ j = X.σ (j.cast_lt ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le
      (by simpa only [fin.val_eq_coe, ← fin.coe_succ]
        using fin.lt_iff_coe_lt_coe.mp H) i.is_le))) ≫
    X.δ (i.pred (λ hi, by simpa only [fin.not_lt_zero, hi] using H)) :=
by { dsimp [δ, σ], simpa only [←X.map_comp, ←op_comp, simplex_category.δ_comp_σ_of_gt' H], }

/-- The fifth cosimplicial identity -/
@[reassoc]
lemma σ_comp_σ {n} {i j : fin (n+1)} (H : i ≤ j) :
  X.σ i.cast_succ ≫ X.σ j = X.σ j.succ ≫ X.σ i :=
by { dsimp [δ, σ], simp only [←X.map_comp, simplex_category.σ_comp_σ H] }

@[simp, reassoc]
lemma δ_naturality {X' X : cosimplicial_object C} (f : X ⟶ X') {n : ℕ} (i : fin (n+2)) :
  X.δ i ≫ f.app (simplex_category.mk (n+1)) =
    f.app (simplex_category.mk n) ≫ X'.δ i := f.naturality _

@[simp, reassoc]
lemma σ_naturality {X' X : cosimplicial_object C} (f : X ⟶ X') {n : ℕ} (i : fin (n+1)) :
  X.σ i ≫ f.app (simplex_category.mk n) =
    f.app (simplex_category.mk (n+1)) ≫ X'.σ i := f.naturality _

variable (C)

/-- Functor composition induces a functor on cosimplicial objects. -/
@[simps]
def whiskering (D : Type*) [category D] :
  (C ⥤ D) ⥤ cosimplicial_object C ⥤ cosimplicial_object D :=
whiskering_right _ _ _

/-- Truncated cosimplicial objects. -/
@[derive category, nolint has_nonempty_instance]
def truncated (n : ℕ) := simplex_category.truncated n ⥤ C

variable {C}

namespace truncated

instance {n} {J : Type v} [small_category J] [has_limits_of_shape J C] :
  has_limits_of_shape J (cosimplicial_object.truncated C n) :=
by {dsimp [truncated], apply_instance}

instance {n} [has_limits C] : has_limits (cosimplicial_object.truncated C n) := ⟨infer_instance⟩

instance {n} {J : Type v} [small_category J] [has_colimits_of_shape J C] :
  has_colimits_of_shape J (cosimplicial_object.truncated C n) :=
by {dsimp [truncated], apply_instance}

instance {n} [has_colimits C] : has_colimits (cosimplicial_object.truncated C n) := ⟨infer_instance⟩

variable (C)

/-- Functor composition induces a functor on truncated cosimplicial objects. -/
@[simps]
def whiskering {n} (D : Type*) [category D] :
  (C ⥤ D) ⥤ truncated C n ⥤ truncated D n :=
whiskering_right _ _ _

variable {C}

end truncated

section skeleton

/-- The skeleton functor from cosimplicial objects to truncated cosimplicial objects. -/
def sk (n : ℕ) : cosimplicial_object C ⥤ cosimplicial_object.truncated C n :=
(whiskering_left _ _ _).obj simplex_category.truncated.inclusion

end skeleton

variable (C)

/-- The constant cosimplicial object. -/
abbreviation const : C ⥤ cosimplicial_object C := category_theory.functor.const _

/-- Augmented cosimplicial objects. -/
@[derive category, nolint has_nonempty_instance]
def augmented := comma (const C) (𝟭 (cosimplicial_object C))

variable {C}

namespace augmented

/-- Drop the augmentation. -/
@[simps]
def drop : augmented C ⥤ cosimplicial_object C := comma.snd _ _

/-- The point of the augmentation. -/
@[simps]
def point : augmented C ⥤ C := comma.fst _ _

/-- The functor from augmented objects to arrows. -/
@[simps]
def to_arrow : augmented C ⥤ arrow C :=
{ obj := λ X,
  { left := (point.obj X),
    right := (drop.obj X) _[0],
    hom := X.hom.app _ },
  map := λ X Y η,
  { left := (point.map η),
    right := (drop.map η).app _,
    w' := begin
      dsimp,
      rw ← nat_trans.comp_app,
      erw ← η.w,
      refl,
    end } }

variable (C)

/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simp]
def whiskering_obj (D : Type*) [category D] (F : C ⥤ D) :
  augmented C ⥤ augmented D :=
{ obj := λ X,
  { left := F.obj (point.obj X),
    right := ((whiskering _ _).obj F).obj (drop.obj X),
    hom := (functor.const_comp _ _ _).inv ≫ whisker_right X.hom F },
  map := λ X Y η,
  { left := F.map η.left,
    right := whisker_right η.right _,
    w' := begin
      ext,
      dsimp,
      rw [category.id_comp, category.id_comp, ← F.map_comp, ← F.map_comp, ← nat_trans.comp_app],
      erw ← η.w,
      refl,
    end } }

/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simps]
def whiskering (D : Type u') [category.{v'} D] :
  (C ⥤ D) ⥤ augmented C ⥤ augmented D :=
{ obj := whiskering_obj _ _,
  map := λ X Y η,
  { app := λ A,
    { left := η.app _,
      right := whisker_left _ η,
      w' := begin
        ext n,
        dsimp,
        rw [category.id_comp, category.id_comp, η.naturality],
      end }, }, }

variable {C}

end augmented

open_locale simplicial

/-- Augment a cosimplicial object with an object. -/
@[simps]
def augment (X : cosimplicial_object C) (X₀ : C) (f : X₀ ⟶ X.obj [0])
  (w : ∀ (i : simplex_category) (g₁ g₂ : [0] ⟶ i),
    f ≫ X.map g₁ = f ≫ X.map g₂) : cosimplicial_object.augmented C :=
{ left := X₀,
  right := X,
  hom :=
  { app := λ i, f ≫ X.map (simplex_category.const i 0),
  naturality' := begin
    intros i j g,
    dsimp,
    simpa [← X.map_comp] using w _ _ _,
  end } }

@[simp]
lemma augment_hom_zero (X : cosimplicial_object C) (X₀ : C) (f : X₀ ⟶ X.obj [0]) (w) :
  (X.augment X₀ f w).hom.app [0] = f :=
by { dsimp, rw [simplex_category.hom_zero_zero ([0].const 0), X.map_id, category.comp_id] }

end cosimplicial_object

/-- The anti-equivalence between simplicial objects and cosimplicial objects. -/
@[simps]
def simplicial_cosimplicial_equiv : (simplicial_object C)ᵒᵖ ≌ (cosimplicial_object Cᵒᵖ) :=
functor.left_op_right_op_equiv _ _

/-- The anti-equivalence between cosimplicial objects and simplicial objects. -/
@[simps]
def cosimplicial_simplicial_equiv : (cosimplicial_object C)ᵒᵖ ≌ (simplicial_object Cᵒᵖ) :=
functor.op_unop_equiv _ _

variable {C}

/-- Construct an augmented cosimplicial object in the opposite
category from an augmented simplicial object. -/
@[simps]
def simplicial_object.augmented.right_op (X : simplicial_object.augmented C) :
  cosimplicial_object.augmented Cᵒᵖ :=
{ left := opposite.op X.right,
  right := X.left.right_op,
  hom := X.hom.right_op }

/-- Construct an augmented simplicial object from an augmented cosimplicial
object in the opposite category. -/
@[simps]
def cosimplicial_object.augmented.left_op (X : cosimplicial_object.augmented Cᵒᵖ) :
  simplicial_object.augmented C :=
{ left := X.right.left_op,
  right := X.left.unop,
  hom := X.hom.left_op }

/-- Converting an augmented simplicial object to an augmented cosimplicial
object and back is isomorphic to the given object. -/
@[simps]
def simplicial_object.augmented.right_op_left_op_iso (X : simplicial_object.augmented C) :
  X.right_op.left_op ≅ X :=
comma.iso_mk X.left.right_op_left_op_iso (eq_to_iso $ by simp) (by tidy)

/-- Converting an augmented cosimplicial object to an augmented simplicial
object and back is isomorphic to the given object. -/
@[simps]
def cosimplicial_object.augmented.left_op_right_op_iso (X : cosimplicial_object.augmented Cᵒᵖ) :
  X.left_op.right_op ≅ X :=
comma.iso_mk (eq_to_iso $ by simp) X.right.left_op_right_op_iso (by tidy)

variable (C)

/-- A functorial version of `simplicial_object.augmented.right_op`. -/
@[simps]
def simplicial_to_cosimplicial_augmented :
  (simplicial_object.augmented C)ᵒᵖ ⥤ cosimplicial_object.augmented Cᵒᵖ :=
{ obj := λ X, X.unop.right_op,
  map := λ X Y f,
  { left := f.unop.right.op,
    right := f.unop.left.right_op,
    w' := begin
      ext x,
      dsimp,
      simp_rw ← op_comp,
      congr' 1,
      exact (congr_app f.unop.w (op x)).symm,
    end } }

/-- A functorial version of `cosimplicial_object.augmented.left_op`. -/
@[simps]
def cosimplicial_to_simplicial_augmented :
  cosimplicial_object.augmented Cᵒᵖ ⥤ (simplicial_object.augmented C)ᵒᵖ :=
{ obj := λ X, opposite.op X.left_op,
  map := λ X Y f, quiver.hom.op $
  { left := f.right.left_op,
    right := f.left.unop,
    w' := begin
      ext x,
      dsimp,
      simp_rw ← unop_comp,
      congr' 1,
      exact (congr_app f.w x.unop).symm,
    end} }

/-- The contravariant categorical equivalence between augmented simplicial
objects and augmented cosimplicial objects in the opposite category. -/
@[simps functor inverse]
def simplicial_cosimplicial_augmented_equiv :
  (simplicial_object.augmented C)ᵒᵖ ≌ cosimplicial_object.augmented Cᵒᵖ :=
equivalence.mk
  (simplicial_to_cosimplicial_augmented _)
  (cosimplicial_to_simplicial_augmented _)
  (nat_iso.of_components (λ X, X.unop.right_op_left_op_iso.op) $ λ X Y f,
    by { dsimp, rw ←f.op_unop, simp_rw ← op_comp, congr' 1, tidy })
  (nat_iso.of_components (λ X, X.left_op_right_op_iso) $ by tidy)

end category_theory
