/-
Copyright (c) 2021 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
import algebra.category.CommRing.basic
import algebra.category.Group.filtered_colimits
import category_theory.limits.concrete_category
import category_theory.limits.preserves.filtered

/-!
# The forgetful functor `Ring ⥤ Type` preserves filtered colimits.

-/

universe v

noncomputable theory
open_locale classical

open category_theory
open category_theory.limits
open category_theory.is_filtered (renaming max → max') -- avoid name collision with `_root_.max`.

-- dummy
namespace AddMon.filtered_colimits

end AddMon.filtered_colimits

open AddMon.filtered_colimits (colimit_zero colimit_zero_eq colimit_add colimit_add_eq)
open Mon.filtered_colimits (colimit_one colimit_one_eq colimit_mul colimit_mul_eq)

namespace SemiRing.filtered_colimits

section

parameters {J : Type v} [small_category J] [is_filtered J] (F : J ⥤ SemiRing.{v})

abbreviation R : Mon := Mon.filtered_colimits.colimit (F ⋙ forget₂ SemiRing Mon)

abbreviation R.mk : (Σ j, F.obj j) → R := quot.mk (types.quot.rel (F ⋙ forget SemiRing))

instance semiring_obj (j : J) : semiring (((F ⋙ forget₂ SemiRing Mon.{v}) ⋙ forget Mon).obj j) :=
begin change semiring (F.obj j), apply_instance end

lemma R.mk_eq (x y : Σ j, F.obj j)
  (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
  R.mk x = R.mk y :=
quot.eqv_gen_sound (types.filtered_colimit.eqv_gen_quot_rel_of_rel (F ⋙ forget SemiRing) x y h)

instance colimit_semiring : semiring R :=
{ mul_zero := λ x, begin
    apply quot.induction_on x, clear x, intro x,
    cases x with j x,
    erw [colimit_zero_eq _ j, colimit_mul_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)],
    rw [category_theory.functor.map_id, id_apply, id_apply, mul_zero x],
    refl,
  end,
  zero_mul := λ x, begin
    apply quot.induction_on x, clear x, intro x,
    cases x with j x,
    erw [colimit_zero_eq _ j, colimit_mul_eq _ ⟨j, _⟩ ⟨j, _⟩ j (𝟙 j) (𝟙 j)],
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
    erw [colimit_add_eq _ ⟨j₂, _⟩ ⟨j₃, _⟩ k g h, colimit_mul_eq _ ⟨j₁, _⟩ ⟨k, _⟩ k f (𝟙 k),
      colimit_mul_eq _ ⟨j₁, _⟩ ⟨j₂, _⟩ k f g, colimit_mul_eq _ ⟨j₁, _⟩ ⟨j₃, _⟩ k f h,
      colimit_add_eq _ ⟨k, _⟩ ⟨k, _⟩ k (𝟙 k) (𝟙 k)],
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
    erw [colimit_add_eq _ ⟨j₁, _⟩ ⟨j₂, _⟩ k f g, colimit_mul_eq _ ⟨k, _⟩ ⟨j₃, _⟩ k (𝟙 k) h,
      colimit_mul_eq _ ⟨j₁, _⟩ ⟨j₃, _⟩ k f h, colimit_mul_eq _ ⟨j₂, _⟩ ⟨j₃, _⟩ k g h,
      colimit_add_eq _ ⟨k, _⟩ ⟨k, _⟩ k (𝟙 k) (𝟙 k)],
    simp only [category_theory.functor.map_id, id_apply],
    erw right_distrib (F.map f x) (F.map g y) (F.map h z),
    refl,
  end,
  ..R.monoid,
  ..AddCommMon.filtered_colimits.colimit_add_comm_monoid (F ⋙ forget₂ SemiRing AddCommMon) }

def colimit : SemiRing := ⟨R, by apply_instance⟩

def colimit_cocone : cocone F :=
{ X := colimit,
  ι :=
  { app := λ j,
    { ..(Mon.filtered_colimits.colimit_cocone (F ⋙ forget₂ SemiRing Mon)).ι.app j,
      ..(AddCommMon.filtered_colimits.colimit_cocone (F ⋙ forget₂ SemiRing AddCommMon)).ι.app j },
    naturality' := λ j j' f,
      (ring_hom.coe_inj ((types.colimit_cocone (F ⋙ forget SemiRing)).ι.naturality f)) } }

def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := λ t,
  { .. (Mon.filtered_colimits.colimit_cocone_is_colimit
    (F ⋙ forget₂ SemiRing Mon)).desc ((forget₂ SemiRing Mon).map_cocone t),
    .. (AddCommMon.filtered_colimits.colimit_cocone_is_colimit
    (F ⋙ forget₂ SemiRing AddCommMon)).desc ((forget₂ SemiRing AddCommMon).map_cocone t), },
  fac' := λ t j, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget SemiRing)).fac ((forget SemiRing).map_cocone t) j,
  uniq' := λ t m h, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget SemiRing)).uniq ((forget SemiRing).map_cocone t) m
    (λ j, funext $ λ x, ring_hom.congr_fun (h j) x) }

instance forget₂_Mon_preserves_filtered_colimits :
  preserves_filtered_colimits (forget₂ SemiRing Mon.{v}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F)
      (Mon.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ SemiRing Mon.{v})) } }

instance forget_preserves_filtered_colimits : preserves_filtered_colimits (forget SemiRing) :=
limits.comp_preserves_filtered_colimits (forget₂ SemiRing Mon) (forget Mon)

end

end SemiRing.filtered_colimits


namespace CommSemiRing.filtered_colimits

section

parameters {J : Type v} [small_category J] [is_filtered J] (F : J ⥤ CommSemiRing.{v})

abbreviation R : SemiRing :=
SemiRing.filtered_colimits.colimit (F ⋙ forget₂ CommSemiRing SemiRing)

abbreviation R.mk : (Σ j, F.obj j) → R := quot.mk (types.quot.rel (F ⋙ forget CommSemiRing))

instance semiring_obj (j : J) : comm_semiring
(((F ⋙ forget₂ CommSemiRing SemiRing.{v}) ⋙ forget SemiRing).obj j) :=
begin change comm_semiring (F.obj j), apply_instance end

lemma R.mk_eq (x y : Σ j, F.obj j)
  (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
  R.mk x = R.mk y :=
quot.eqv_gen_sound (types.filtered_colimit.eqv_gen_quot_rel_of_rel (F ⋙ forget CommSemiRing) x y h)

instance colimit_comm_semiring : comm_semiring R :=
{ ..R.semiring,
  ..CommMon.filtered_colimits.colimit_comm_monoid (F ⋙ forget₂ CommSemiRing CommMon) }

def colimit : CommSemiRing := ⟨R, by apply_instance⟩

def colimit_cocone : cocone F :=
{ X := colimit,
  ι := { ..(SemiRing.filtered_colimits.colimit_cocone (F ⋙ forget₂ CommSemiRing SemiRing)).ι } }

def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := λ t,
  (SemiRing.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ CommSemiRing SemiRing)).desc
    ((forget₂ CommSemiRing SemiRing).map_cocone t),
  fac' := λ t j, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget CommSemiRing)).fac
    ((forget CommSemiRing).map_cocone t) j,
  uniq' := λ t m h, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget CommSemiRing)).uniq
    ((forget CommSemiRing).map_cocone t) m (λ j, funext $ λ x, ring_hom.congr_fun (h j) x) }

instance forget₂_SemiRing_preserves_filtered_colimits :
  preserves_filtered_colimits (forget₂ CommSemiRing SemiRing.{v}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F)
      (SemiRing.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ CommSemiRing SemiRing.{v})) } }

instance forget_preserves_filtered_colimits : preserves_filtered_colimits (forget CommSemiRing) :=
limits.comp_preserves_filtered_colimits (forget₂ CommSemiRing SemiRing) (forget SemiRing)

end

end CommSemiRing.filtered_colimits


namespace Ring.filtered_colimits

section

parameters {J : Type v} [small_category J] [is_filtered J] (F : J ⥤ Ring.{v})

abbreviation R : SemiRing :=
SemiRing.filtered_colimits.colimit (F ⋙ forget₂ Ring SemiRing)

abbreviation R.mk : (Σ j, F.obj j) → R := quot.mk (types.quot.rel (F ⋙ forget Ring))

instance ring_obj (j : J) : ring
(((F ⋙ forget₂ Ring SemiRing.{v}) ⋙ forget SemiRing).obj j) :=
begin change ring (F.obj j), apply_instance end

lemma R.mk_eq (x y : Σ j, F.obj j)
  (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
  R.mk x = R.mk y :=
quot.eqv_gen_sound (types.filtered_colimit.eqv_gen_quot_rel_of_rel (F ⋙ forget Ring) x y h)

instance colimit_ring : ring R :=
{ ..R.semiring,
  ..AddCommGroup.filtered_colimits.colimit_add_comm_group (F ⋙ forget₂ Ring AddCommGroup) }

def colimit : Ring := ⟨R, by apply_instance⟩

def colimit_cocone : cocone F :=
{ X := colimit,
  ι := { ..(SemiRing.filtered_colimits.colimit_cocone (F ⋙ forget₂ Ring SemiRing)).ι } }

def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := λ t,
  (SemiRing.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ Ring SemiRing)).desc
    ((forget₂ Ring SemiRing).map_cocone t),
  fac' := λ t j, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget Ring)).fac ((forget Ring).map_cocone t) j,
  uniq' := λ t m h, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget Ring)).uniq
    ((forget Ring).map_cocone t) m (λ j, funext $ λ x, ring_hom.congr_fun (h j) x) }

instance forget₂_SemiRing_preserves_filtered_colimits :
  preserves_filtered_colimits (forget₂ Ring SemiRing.{v}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F)
      (SemiRing.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ Ring SemiRing.{v})) } }

instance forget_preserves_filtered_colimits : preserves_filtered_colimits (forget Ring) :=
limits.comp_preserves_filtered_colimits (forget₂ Ring SemiRing) (forget SemiRing)

end

end Ring.filtered_colimits


namespace CommRing.filtered_colimits

section

parameters {J : Type v} [small_category J] [is_filtered J] (F : J ⥤ CommRing.{v})

abbreviation R : Ring :=
Ring.filtered_colimits.colimit (F ⋙ forget₂ CommRing Ring)

abbreviation R.mk : (Σ j, F.obj j) → R := quot.mk (types.quot.rel (F ⋙ forget CommRing))

instance semiring_obj (j : J) : comm_ring
(((F ⋙ forget₂ CommRing Ring.{v}) ⋙ forget Ring).obj j) :=
begin change comm_ring (F.obj j), apply_instance end

lemma R.mk_eq (x y : Σ j, F.obj j)
  (h : ∃ (k : J) (f : x.1 ⟶ k) (g : y.1 ⟶ k), F.map f x.2 = F.map g y.2) :
  R.mk x = R.mk y :=
quot.eqv_gen_sound (types.filtered_colimit.eqv_gen_quot_rel_of_rel (F ⋙ forget CommRing) x y h)

instance colimit_comm_semiring : comm_ring R :=
{ ..R.ring,
  ..CommSemiRing.filtered_colimits.colimit_comm_semiring (F ⋙ forget₂ CommRing CommSemiRing) }

def colimit : CommRing := ⟨R, by apply_instance⟩

def colimit_cocone : cocone F :=
{ X := colimit,
  ι := { ..(Ring.filtered_colimits.colimit_cocone (F ⋙ forget₂ CommRing Ring)).ι } }

def colimit_cocone_is_colimit : is_colimit colimit_cocone :=
{ desc := λ t,
  (Ring.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ CommRing Ring)).desc
    ((forget₂ CommRing Ring).map_cocone t),
  fac' := λ t j, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget CommRing)).fac ((forget CommRing).map_cocone t) j,
  uniq' := λ t m h, ring_hom.coe_inj $
  (types.colimit_cocone_is_colimit (F ⋙ forget CommRing)).uniq
    ((forget CommRing).map_cocone t) m (λ j, funext $ λ x, ring_hom.congr_fun (h j) x) }

instance forget₂_Ring_preserves_filtered_colimits :
  preserves_filtered_colimits (forget₂ CommRing Ring.{v}) :=
{ preserves_filtered_colimits := λ J _ _, by exactI
  { preserves_colimit := λ F, preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F)
      (Ring.filtered_colimits.colimit_cocone_is_colimit (F ⋙ forget₂ CommRing Ring.{v})) } }

instance forget_preserves_filtered_colimits : preserves_filtered_colimits (forget CommRing) :=
limits.comp_preserves_filtered_colimits (forget₂ CommRing Ring) (forget Ring)

end

end CommRing.filtered_colimits
