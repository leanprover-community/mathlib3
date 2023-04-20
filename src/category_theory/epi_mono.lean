/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import category_theory.opposites
import category_theory.groupoid

/-!
# Facts about epimorphisms and monomorphisms.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The definitions of `epi` and `mono` are in `category_theory.category`,
since they are used by some lemmas for `iso`, which is used everywhere.
-/

universes v₁ v₂ u₁ u₂

namespace category_theory

variables {C : Type u₁} [category.{v₁} C]

instance unop_mono_of_epi {A B : Cᵒᵖ} (f : A ⟶ B) [epi f] : mono f.unop :=
⟨λ Z g h eq, quiver.hom.op_inj ((cancel_epi f).1 (quiver.hom.unop_inj eq))⟩

instance unop_epi_of_mono {A B : Cᵒᵖ} (f : A ⟶ B) [mono f] : epi f.unop :=
⟨λ Z g h eq, quiver.hom.op_inj ((cancel_mono f).1 (quiver.hom.unop_inj eq))⟩

instance op_mono_of_epi {A B : C} (f : A ⟶ B) [epi f] : mono f.op :=
⟨λ Z g h eq, quiver.hom.unop_inj ((cancel_epi f).1 (quiver.hom.op_inj eq))⟩

instance op_epi_of_mono {A B : C} (f : A ⟶ B) [mono f] : epi f.op :=
⟨λ Z g h eq, quiver.hom.unop_inj ((cancel_mono f).1 (quiver.hom.op_inj eq))⟩

/--
A split monomorphism is a morphism `f : X ⟶ Y` with a given retraction `retraction f : Y ⟶ X`
such that `f ≫ retraction f = 𝟙 X`.

Every split monomorphism is a monomorphism.
-/
@[ext, nolint has_nonempty_instance]
structure split_mono {X Y : C} (f : X ⟶ Y) :=
(retraction : Y ⟶ X)
(id' : f ≫ retraction = 𝟙 X . obviously)

restate_axiom split_mono.id'
attribute [simp, reassoc] split_mono.id

/-- `is_split_mono f` is the assertion that `f` admits a retraction -/
class is_split_mono {X Y : C} (f : X ⟶ Y) : Prop :=
(exists_split_mono : nonempty (split_mono f))

/-- A constructor for `is_split_mono f` taking a `split_mono f` as an argument -/
lemma is_split_mono.mk' {X Y : C} {f : X ⟶ Y} (sm : split_mono f) :
  is_split_mono f := ⟨nonempty.intro sm⟩

/--
A split epimorphism is a morphism `f : X ⟶ Y` with a given section `section_ f : Y ⟶ X`
such that `section_ f ≫ f = 𝟙 Y`.
(Note that `section` is a reserved keyword, so we append an underscore.)

Every split epimorphism is an epimorphism.
-/
@[ext, nolint has_nonempty_instance]
structure split_epi {X Y : C} (f : X ⟶ Y) :=
(section_ : Y ⟶ X)
(id' : section_ ≫ f = 𝟙 Y . obviously)

restate_axiom split_epi.id'
attribute [simp, reassoc] split_epi.id

/-- `is_split_epi f` is the assertion that `f` admits a section -/
class is_split_epi {X Y : C} (f : X ⟶ Y) : Prop :=
(exists_split_epi : nonempty (split_epi f))

/-- A constructor for `is_split_epi f` taking a `split_epi f` as an argument -/
lemma is_split_epi.mk' {X Y : C} {f : X ⟶ Y} (se : split_epi f) :
  is_split_epi f := ⟨nonempty.intro se⟩

/-- The chosen retraction of a split monomorphism. -/
noncomputable def retraction {X Y : C} (f : X ⟶ Y) [hf : is_split_mono f] : Y ⟶ X :=
hf.exists_split_mono.some.retraction

@[simp, reassoc]
lemma is_split_mono.id {X Y : C} (f : X ⟶ Y) [hf : is_split_mono f] : f ≫ retraction f = 𝟙 X :=
hf.exists_split_mono.some.id

/-- The retraction of a split monomorphism has an obvious section. -/
def split_mono.split_epi {X Y : C} {f : X ⟶ Y} (sm : split_mono f) : split_epi (sm.retraction) :=
{ section_ := f, }

/-- The retraction of a split monomorphism is itself a split epimorphism. -/
instance retraction_is_split_epi {X Y : C} (f : X ⟶ Y) [hf : is_split_mono f] :
is_split_epi (retraction f) :=
is_split_epi.mk' (split_mono.split_epi _)

/-- A split mono which is epi is an iso. -/
lemma is_iso_of_epi_of_is_split_mono {X Y : C} (f : X ⟶ Y) [is_split_mono f] [epi f] : is_iso f :=
⟨⟨retraction f, ⟨by simp, by simp [← cancel_epi f]⟩⟩⟩

/--
The chosen section of a split epimorphism.
(Note that `section` is a reserved keyword, so we append an underscore.)
-/
noncomputable def section_ {X Y : C} (f : X ⟶ Y) [hf : is_split_epi f] : Y ⟶ X :=
hf.exists_split_epi.some.section_

@[simp, reassoc]
lemma is_split_epi.id {X Y : C} (f : X ⟶ Y) [hf : is_split_epi f] : section_ f ≫ f = 𝟙 Y :=
hf.exists_split_epi.some.id

/-- The section of a split epimorphism has an obvious retraction. -/
def split_epi.split_mono {X Y : C} {f : X ⟶ Y} (se : split_epi f) : split_mono (se.section_) :=
{ retraction := f, }

/-- The section of a split epimorphism is itself a split monomorphism. -/
instance section_is_split_mono {X Y : C} (f : X ⟶ Y) [hf : is_split_epi f] :
  is_split_mono (section_ f) :=
is_split_mono.mk' (split_epi.split_mono _)

/-- A split epi which is mono is an iso. -/
lemma is_iso_of_mono_of_is_split_epi {X Y : C} (f : X ⟶ Y) [mono f] [is_split_epi f] : is_iso f :=
⟨⟨section_ f, ⟨by simp [← cancel_mono f], by simp⟩⟩⟩

/-- Every iso is a split mono. -/
@[priority 100]
instance is_split_mono.of_iso {X Y : C} (f : X ⟶ Y) [is_iso f] : is_split_mono f :=
is_split_mono.mk' { retraction := inv f }

/-- Every iso is a split epi. -/
@[priority 100]
instance is_split_epi.of_iso {X Y : C} (f : X ⟶ Y) [is_iso f] : is_split_epi f :=
is_split_epi.mk' { section_ := inv f }

lemma split_mono.mono {X Y : C} {f : X ⟶ Y} (sm : split_mono f) : mono f :=
{ right_cancellation := λ Z g h w, begin replace w := w =≫ sm.retraction, simpa using w, end }

/-- Every split mono is a mono. -/
@[priority 100]
instance is_split_mono.mono {X Y : C} (f : X ⟶ Y) [hf : is_split_mono f] : mono f :=
hf.exists_split_mono.some.mono

lemma split_epi.epi {X Y : C} {f : X ⟶ Y} (se : split_epi f) : epi f :=
{ left_cancellation := λ Z g h w, begin replace w := se.section_ ≫= w, simpa using w, end }

/-- Every split epi is an epi. -/
@[priority 100]
instance is_split_epi.epi {X Y : C} (f : X ⟶ Y) [hf : is_split_epi f] : epi f :=
hf.exists_split_epi.some.epi

/-- Every split mono whose retraction is mono is an iso. -/
lemma is_iso.of_mono_retraction' {X Y : C} {f : X ⟶ Y} (hf : split_mono f)
  [mono $ hf.retraction] : is_iso f :=
⟨⟨hf.retraction, ⟨by simp, (cancel_mono_id $ hf.retraction).mp (by simp)⟩⟩⟩

/-- Every split mono whose retraction is mono is an iso. -/
lemma is_iso.of_mono_retraction {X Y : C} (f : X ⟶ Y) [hf : is_split_mono f]
  [hf' : mono $ retraction f] : is_iso f :=
@is_iso.of_mono_retraction' _ _ _ _ _ hf.exists_split_mono.some hf'

/-- Every split epi whose section is epi is an iso. -/
lemma is_iso.of_epi_section' {X Y : C} {f : X ⟶ Y} (hf : split_epi f)
  [epi $ hf.section_] : is_iso f :=
⟨⟨hf.section_, ⟨(cancel_epi_id $ hf.section_).mp (by simp), by simp⟩⟩⟩

/-- Every split epi whose section is epi is an iso. -/
lemma is_iso.of_epi_section {X Y : C} (f : X ⟶ Y) [hf : is_split_epi f]
  [hf' : epi $ section_ f] : is_iso f :=
@is_iso.of_epi_section' _ _ _ _ _ hf.exists_split_epi.some hf'

/-- A category where every morphism has a `trunc` retraction is computably a groupoid. -/
-- FIXME this has unnecessarily become noncomputable!
noncomputable
def groupoid.of_trunc_split_mono
  (all_split_mono : ∀ {X Y : C} (f : X ⟶ Y), trunc (is_split_mono f)) :
  groupoid.{v₁} C :=
begin
  apply groupoid.of_is_iso,
  intros X Y f,
  trunc_cases all_split_mono f,
  trunc_cases all_split_mono (retraction f),
  apply is_iso.of_mono_retraction,
end

section
variables (C)

/-- A split mono category is a category in which every monomorphism is split. -/
class split_mono_category :=
(is_split_mono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [mono f], is_split_mono f)

/-- A split epi category is a category in which every epimorphism is split. -/
class split_epi_category :=
(is_split_epi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [epi f], is_split_epi f)

end

/-- In a category in which every monomorphism is split, every monomorphism splits. This is not an
    instance because it would create an instance loop. -/
lemma is_split_mono_of_mono [split_mono_category C] {X Y : C} (f : X ⟶ Y) [mono f] :
  is_split_mono f :=
split_mono_category.is_split_mono_of_mono _

/-- In a category in which every epimorphism is split, every epimorphism splits. This is not an
    instance because it would create an instance loop. -/
lemma is_split_epi_of_epi [split_epi_category C] {X Y : C} (f : X ⟶ Y) [epi f] :
  is_split_epi f := split_epi_category.is_split_epi_of_epi _

section
variables {D : Type u₂} [category.{v₂} D]

/-- Split monomorphisms are also absolute monomorphisms. -/
@[simps]
def split_mono.map {X Y : C} {f : X ⟶ Y} (sm : split_mono f) (F : C ⥤ D ) :
  split_mono (F.map f) :=
{ retraction := F.map (sm.retraction),
  id' := by { rw [←functor.map_comp, split_mono.id, functor.map_id], } }

/-- Split epimorphisms are also absolute epimorphisms. -/
@[simps]
def split_epi.map {X Y : C} {f : X ⟶ Y} (se : split_epi f) (F : C ⥤ D ) :
  split_epi (F.map f) :=
{ section_ := F.map (se.section_),
  id' := by { rw [←functor.map_comp, split_epi.id, functor.map_id], } }

instance {X Y : C} (f : X ⟶ Y) [hf : is_split_mono f] (F : C ⥤ D) : is_split_mono (F.map f) :=
is_split_mono.mk' (hf.exists_split_mono.some.map F)

instance {X Y : C} (f : X ⟶ Y) [hf : is_split_epi f] (F : C ⥤ D) : is_split_epi (F.map f) :=
is_split_epi.mk' (hf.exists_split_epi.some.map F)

end

end category_theory
