/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import algebra.category.Ring.basic
import algebra.category.Group.filtered_colimits

/-!
# The forgetful functor from (commutative) (semi-) rings preserves filtered colimits.

Forgetful functors from algebraic categories usually don't preserve colimits. However, they tend
to preserve _filtered_ colimits.

In this file, we start with a small filtered category `J` and a functor `F : J ⥤ SemiRing`.
We show that the colimit of `F ⋙ forget₂ SemiRing Mon` (in `Mon`) carries the structure of a
semiring, thereby showing that the forgetful functor `forget₂ SemiRing Mon` preserves filtered
colimits. In particular, this implies that `forget SemiRing` preserves filtered colimits.
Similarly for `CommSemiRing`, `Ring` and `CommRing`.

-/

universes v u

noncomputable theory
open_locale classical

open category_theory
open category_theory.limits
open category_theory.is_filtered (renaming max → max') -- avoid name collision with `_root_.max`.

open AddMon.filtered_colimits (colimit_zero_eq colimit_add_mk_eq)
open Mon.filtered_colimits (colimit_one_eq colimit_mul_mk_eq)

namespace SemiRing.filtered_colimits

section

-- We use parameters here, mainly so we can have the abbreviations `R` and `R.mk` below, without
-- passing around `F` all the time.
parameters {J : Type v} [small_category J] (F : J ⥤ SemiRing.{max v u})

-- This instance is needed below in `colimit_semiring`, during the verification of the
-- semiring axioms.
instance semiring_obj (j : J) :
  semiring (((F ⋙ forget₂ SemiRing Mon.{max v u}) ⋙ forget Mon).obj j) :=
show semiring (F.obj j), by apply_instance

variables [is_filtered J]

/--
The colimit of `F ⋙ forget₂ SemiRing Mon` in the category `Mon`.
In the following, we will show that this has the structure of a semiring.
-/
abbreviation R : Mon := Mon.filtered_colimits.colimit (F ⋙ forget₂ SemiRing Mon.{max v u})

instance colimit_semiring : semiring R :=
{ mul_zero := λ x, begin
    apply quot.induction_on x, clear x, intro x,
    cases x with j x,
    erw [colimit_zero_eq _ j, colimit_mul_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)],
    rw [category_theory.functor.map_id, id_apply, id_apply, mul_zero x],
    refl,
  end,
  zero_mul := λ x, begin
    apply quot.induction_on x, clear x, intro x,
    cases x with j x,
    erw [colimit_zero_eq _ j, colimit_mul_mk_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)],
    rw [category_theory.functor.map_id, id_apply, id_apply, zero_mul x],
    refl,
  end,
  left_distrib := λ x y z, begin
    apply quot.induction_on₃ x y z, clear x y z, intros x y z,
    cases x with j₁ x, cases y with j₂ y, cases z with j₃ z,
    let k := max₃ j₁ j₂ j₃,
    let f := first_to_max₃ j₁ j₂ j₃,
    let g := second_to_max₃ j₁ j₂ j₃,
    let h := third_to_max₃ j₁ j₂ j₃,
    erw [colimit_add_mk_eq _ ⟨j₂, _⟩ ⟨j₃, _⟩ k g h, colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨k, _⟩ k f (𝟙 k),
      colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₂, _⟩ k f g, colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₃, _⟩ k f h,
      colimit_add_mk_eq _ ⟨k, _⟩ ⟨k, _⟩ k (𝟙 k) (𝟙 k)],
    simp only [category_theory.functor.map_id, id_apply],
    erw left_distrib (F.map f x) (F.map g y) (F.map h z),
    refl,
  end,
  right_distrib := λ x y z, begin
    apply quot.induction_on₃ x y z, clear x y z, intros x y z,
    cases x with j₁ x, cases y with j₂ y, cases z with j₃ z,
    let k := max₃ j₁ j₂ j₃,
    let f := first_to_max₃ j₁ j₂ j₃,
    let g := second_to_max₃ j₁ j₂ j₃,
    let h := third_to_max₃ j₁ j₂ j₃,
    erw [colimit_add_mk_eq _ ⟨j₁, _⟩ ⟨j₂, _⟩ k f g, colimit_mul_mk_eq _ ⟨k, _⟩ ⟨j₃, _⟩ k (𝟙 k) h,
      colimit_mul_mk_eq _ ⟨j₁, _⟩ ⟨j₃, _⟩ k f h, colimit_mul_mk_eq _ ⟨j₂, _⟩ ⟨j₃, _⟩ k g h,
      colimit_add_mk_eq _ ⟨k, _⟩ ⟨k, _⟩ k (𝟙 k) (𝟙 k)],
    simp only [category_theory.functor.map_id, id_apply],
    erw right_distrib (F.map f x) (F.map g y) (F.map h z),
    refl,
  end,
  ..R.monoid,
  ..AddCommMon.filtered_colimits.colimit_add_comm_monoid
    (F ⋙ forget₂ SemiRing AddCommMon.{max v u}) }

/-- The bundled semiring giving the filtered colimit of a diagram. -/
def colimit : SemiRing := SemiRing.of R

/-- The cocone over the proposed colimit semiring. -/
def colimit_cocone : cocone F :=
{ X := colimit,
  ι :=
  { app := λ j,
    { ..(Mon.filtered_colimits.colimit_cocone (F ⋙ forget₂ SemiRing Mon.{max v u})).ι.app j,
      ..(AddCommMon.filtered_colimits.colimit_cocone
        (F ⋙ forget₂ SemiRing AddCommMon.{max v u})).ι.app j },
    naturality' := λ j j' f,
      (ring_hom.coe_inj ((types.colimit_cocone (F ⋙ forget SemiRing)).ι.naturality f)) } }

/-- The proposed colimit cocone is a colimit in `SemiRing`. -/
def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := λ t,
  { .. (Mon.filtered_colimits.colimit_cocone_is_colimit
    (F ⋙ forget₂ SemiRing Mon.{max v u})).desc ((forget₂ SemiRing Mon.{max v u}).map_cocone t),
    .. (AddCommMon.filtered_colimits.colimit_cocone_is_colimit
    (F ⋙ forget₂ SemiRing AddCommMon.{max v u})).desc
      ((forget₂ SemiRing AddCommMon.{max v u}).map_cocone t), },
  fac' := λ t j, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget SemiRing)).fac ((forget SemiRing).map_cocone t) j,
  uniq' := λ t m h, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget SemiRing)).uniq ((forget SemiRing).map_cocone t) m
    (λ j, funext $ λ x, ring_hom.congr_fun (h j) x) }

instance forget₂_Mon_preserves_filtered_colimits :
  preserves_filtered_colimits (forget₂ SemiRing Mon.{u}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit.{u u} F)
      (Mon.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ SemiRing Mon.{u})) } }

instance forget_preserves_filtered_colimits :
  preserves_filtered_colimits (forget SemiRing.{u}) :=
limits.comp_preserves_filtered_colimits (forget₂ SemiRing Mon) (forget Mon.{u})

end

end SemiRing.filtered_colimits


namespace CommSemiRing.filtered_colimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
parameters {J : Type v} [small_category J] [is_filtered J] (F : J ⥤ CommSemiRing.{max v u})

/--
The colimit of `F ⋙ forget₂ CommSemiRing SemiRing` in the category `SemiRing`.
In the following, we will show that this has the structure of a _commutative_ semiring.
-/
abbreviation R : SemiRing :=
SemiRing.filtered_colimits.colimit (F ⋙ forget₂ CommSemiRing SemiRing.{max v u})

instance colimit_comm_semiring : comm_semiring R :=
{ ..R.semiring,
  ..CommMon.filtered_colimits.colimit_comm_monoid (F ⋙ forget₂ CommSemiRing CommMon.{max v u}) }

/-- The bundled commutative semiring giving the filtered colimit of a diagram. -/
def colimit : CommSemiRing := CommSemiRing.of R

/-- The cocone over the proposed colimit commutative semiring. -/
def colimit_cocone : cocone F :=
{ X := colimit,
  ι :=
  { ..(SemiRing.filtered_colimits.colimit_cocone
      (F ⋙ forget₂ CommSemiRing SemiRing.{max v u})).ι } }

/-- The proposed colimit cocone is a colimit in `CommSemiRing`. -/
def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := λ t,
  (SemiRing.filtered_colimits.colimit_cocone_is_colimit
    (F ⋙ forget₂ CommSemiRing SemiRing.{max v u})).desc
    ((forget₂ CommSemiRing SemiRing).map_cocone t),
  fac' := λ t j, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget CommSemiRing)).fac
    ((forget CommSemiRing).map_cocone t) j,
  uniq' := λ t m h, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget CommSemiRing)).uniq
    ((forget CommSemiRing).map_cocone t) m (λ j, funext $ λ x, ring_hom.congr_fun (h j) x) }

instance forget₂_SemiRing_preserves_filtered_colimits :
  preserves_filtered_colimits (forget₂ CommSemiRing SemiRing.{u}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit.{u u} F)
      (SemiRing.filtered_colimits.colimit_cocone_is_colimit
        (F ⋙ forget₂ CommSemiRing SemiRing.{u})) } }

instance forget_preserves_filtered_colimits :
  preserves_filtered_colimits (forget CommSemiRing.{u}) :=
limits.comp_preserves_filtered_colimits (forget₂ CommSemiRing SemiRing) (forget SemiRing.{u})

end

end CommSemiRing.filtered_colimits


namespace Ring.filtered_colimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
parameters {J : Type v} [small_category J] [is_filtered J] (F : J ⥤ Ring.{max v u})

/--
The colimit of `F ⋙ forget₂ Ring SemiRing` in the category `SemiRing`.
In the following, we will show that this has the structure of a ring.
-/
abbreviation R : SemiRing :=
SemiRing.filtered_colimits.colimit (F ⋙ forget₂ Ring SemiRing.{max v u})

instance colimit_ring : ring R :=
{ ..R.semiring,
  ..AddCommGroup.filtered_colimits.colimit_add_comm_group
    (F ⋙ forget₂ Ring AddCommGroup.{max v u}) }

/-- The bundled ring giving the filtered colimit of a diagram. -/
def colimit : Ring := Ring.of R

/-- The cocone over the proposed colimit ring. -/
def colimit_cocone : cocone F :=
{ X := colimit,
  ι := { ..(SemiRing.filtered_colimits.colimit_cocone (F ⋙ forget₂ Ring SemiRing.{max v u})).ι } }

/-- The proposed colimit cocone is a colimit in `Ring`. -/
def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := λ t,
  (SemiRing.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ Ring SemiRing.{max v u})).desc
    ((forget₂ Ring SemiRing).map_cocone t),
  fac' := λ t j, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget Ring)).fac ((forget Ring).map_cocone t) j,
  uniq' := λ t m h, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget Ring)).uniq
    ((forget Ring).map_cocone t) m (λ j, funext $ λ x, ring_hom.congr_fun (h j) x) }

instance forget₂_SemiRing_preserves_filtered_colimits :
  preserves_filtered_colimits (forget₂ Ring SemiRing.{u}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit.{u u} F)
      (SemiRing.filtered_colimits.colimit_cocone_is_colimit
        (F ⋙ forget₂ Ring SemiRing.{u})) } }

instance forget_preserves_filtered_colimits :
  preserves_filtered_colimits (forget Ring.{u}) :=
limits.comp_preserves_filtered_colimits (forget₂ Ring SemiRing) (forget SemiRing.{u})

end

end Ring.filtered_colimits


namespace CommRing.filtered_colimits

section

-- We use parameters here, mainly so we can have the abbreviation `R` below, without
-- passing around `F` all the time.
parameters {J : Type v} [small_category J] [is_filtered J] (F : J ⥤ CommRing.{max v u})

/--
The colimit of `F ⋙ forget₂ CommRing Ring` in the category `Ring`.
In the following, we will show that this has the structure of a _commutative_ ring.
-/
abbreviation R : Ring :=
Ring.filtered_colimits.colimit (F ⋙ forget₂ CommRing Ring.{max v u})

instance colimit_comm_ring : comm_ring R :=
{ ..R.ring,
  ..CommSemiRing.filtered_colimits.colimit_comm_semiring
    (F ⋙ forget₂ CommRing CommSemiRing.{max v u}) }

/-- The bundled commutative ring giving the filtered colimit of a diagram. -/
def colimit : CommRing := CommRing.of R

/-- The cocone over the proposed colimit commutative ring. -/
def colimit_cocone : cocone F :=
{ X := colimit,
  ι := { ..(Ring.filtered_colimits.colimit_cocone (F ⋙ forget₂ CommRing Ring.{max v u})).ι } }

/-- The proposed colimit cocone is a colimit in `CommRing`. -/
def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := λ t,
  (Ring.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ CommRing Ring.{max v u})).desc
    ((forget₂ CommRing Ring).map_cocone t),
  fac' := λ t j, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget CommRing)).fac ((forget CommRing).map_cocone t) j,
  uniq' := λ t m h, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget CommRing)).uniq
    ((forget CommRing).map_cocone t) m (λ j, funext $ λ x, ring_hom.congr_fun (h j) x) }

instance forget₂_Ring_preserves_filtered_colimits :
  preserves_filtered_colimits (forget₂ CommRing Ring.{u}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit.{u u} F)
      (Ring.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ CommRing Ring.{u})) } }

instance forget_preserves_filtered_colimits :
  preserves_filtered_colimits (forget CommRing.{u}) :=
limits.comp_preserves_filtered_colimits (forget₂ CommRing Ring) (forget Ring.{u})

end

end CommRing.filtered_colimits
