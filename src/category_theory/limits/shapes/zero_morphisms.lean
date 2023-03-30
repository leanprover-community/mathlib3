/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.pi.algebra
import category_theory.limits.shapes.products
import category_theory.limits.shapes.images
import category_theory.isomorphism_classes
import category_theory.limits.shapes.zero_objects

/-!
# Zero morphisms and zero objects

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. (Notice this is extra
structure, not merely a property.)

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object.

## References

* https://en.wikipedia.org/wiki/Zero_morphism
* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

noncomputable theory

universes v u
universes v' u'

open category_theory
open category_theory.category
open_locale classical

namespace category_theory.limits

variables (C : Type u) [category.{v} C]
variables (D : Type u') [category.{v'} D]

/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
class has_zero_morphisms :=
[has_zero : Π X Y : C, has_zero (X ⟶ Y)]
(comp_zero' : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) . obviously)
(zero_comp' : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) . obviously)

attribute [instance] has_zero_morphisms.has_zero
restate_axiom has_zero_morphisms.comp_zero'
restate_axiom has_zero_morphisms.zero_comp'

variables {C}

@[simp] lemma comp_zero [has_zero_morphisms C] {X Y : C} {f : X ⟶ Y} {Z : C} :
  f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) := has_zero_morphisms.comp_zero f Z
@[simp] lemma zero_comp [has_zero_morphisms C] {X : C} {Y Z : C} {f : Y ⟶ Z} :
  (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) := has_zero_morphisms.zero_comp X f

instance has_zero_morphisms_pempty : has_zero_morphisms (discrete pempty) :=
{ has_zero := by tidy }

instance has_zero_morphisms_punit : has_zero_morphisms (discrete punit) :=
{ has_zero := by tidy }

namespace has_zero_morphisms
variables {C}

/-- This lemma will be immediately superseded by `ext`, below. -/
private lemma ext_aux (I J : has_zero_morphisms C)
  (w : ∀ X Y : C, (@has_zero_morphisms.has_zero _ _ I X Y).zero =
    (@has_zero_morphisms.has_zero _ _ J X Y).zero) : I = J :=
begin
  casesI I, casesI J,
  congr,
  { ext X Y,
    exact w X Y },
  { apply proof_irrel_heq, },
  { apply proof_irrel_heq, }
end

/--
If you're tempted to use this lemma "in the wild", you should probably
carefully consider whether you've made a mistake in allowing two
instances of `has_zero_morphisms` to exist at all.

See, particularly, the note on `zero_morphisms_of_zero_object` below.
-/
lemma ext (I J : has_zero_morphisms C) : I = J :=
begin
  apply ext_aux,
  intros X Y,
  rw ←@has_zero_morphisms.comp_zero _ _ I X X (@has_zero_morphisms.has_zero _ _ J X X).zero,
  rw @has_zero_morphisms.zero_comp _ _ J,
end

instance : subsingleton (has_zero_morphisms C) :=
⟨ext⟩

end has_zero_morphisms

open opposite has_zero_morphisms

instance has_zero_morphisms_opposite [has_zero_morphisms C] :
  has_zero_morphisms Cᵒᵖ :=
{ has_zero := λ X Y, ⟨(0 : unop Y ⟶ unop X).op⟩,
  comp_zero' := λ X Y f Z, congr_arg quiver.hom.op (has_zero_morphisms.zero_comp (unop Z) f.unop),
  zero_comp' := λ X Y Z f, congr_arg quiver.hom.op (has_zero_morphisms.comp_zero f.unop (unop X)), }

section
variables {C} [has_zero_morphisms C]

lemma zero_of_comp_mono {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z) [mono g] (h : f ≫ g = 0) : f = 0 :=
by { rw [←zero_comp, cancel_mono] at h, exact h }

lemma zero_of_epi_comp {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [epi f] (h : f ≫ g = 0) : g = 0 :=
by { rw [←comp_zero, cancel_epi] at h, exact h }

lemma eq_zero_of_image_eq_zero {X Y : C} {f : X ⟶ Y} [has_image f] (w : image.ι f = 0) : f = 0 :=
by rw [←image.fac f, w, has_zero_morphisms.comp_zero]

lemma nonzero_image_of_nonzero {X Y : C} {f : X ⟶ Y} [has_image f] (w : f ≠ 0) : image.ι f ≠ 0 :=
λ h, w (eq_zero_of_image_eq_zero h)
end

section

variables [has_zero_morphisms D]

instance : has_zero_morphisms (C ⥤ D) :=
{ has_zero := λ F G, ⟨{ app := λ X, 0, }⟩ }

@[simp] lemma zero_app (F G : C ⥤ D) (j : C) : (0 : F ⟶ G).app j = 0 := rfl

end

namespace is_zero
variables [has_zero_morphisms C]

lemma eq_zero_of_src {X Y : C} (o : is_zero X) (f : X ⟶ Y) : f = 0 :=
o.eq_of_src _ _

lemma eq_zero_of_tgt {X Y : C} (o : is_zero Y) (f : X ⟶ Y) : f = 0 :=
o.eq_of_tgt _ _

lemma iff_id_eq_zero (X : C) : is_zero X ↔ (𝟙 X = 0) :=
⟨λ h, h.eq_of_src _ _,
 λ h, ⟨
  λ Y, ⟨⟨⟨0⟩, λ f, by { rw [←id_comp f, ←id_comp default, h, zero_comp, zero_comp], }⟩⟩,
  λ Y, ⟨⟨⟨0⟩, λ f, by { rw [←comp_id f, ←comp_id default, h, comp_zero, comp_zero], }⟩⟩⟩⟩

lemma of_mono_zero (X Y : C) [mono (0 : X ⟶ Y)] : is_zero X :=
(iff_id_eq_zero X).mpr ((cancel_mono (0 : X ⟶ Y)).1 (by simp))

lemma of_epi_zero (X Y : C) [epi (0 : X ⟶ Y)] : is_zero Y :=
(iff_id_eq_zero Y).mpr ((cancel_epi (0 : X ⟶ Y)).1 (by simp))

lemma of_mono_eq_zero {X Y : C} (f : X ⟶ Y) [mono f] (h : f = 0) : is_zero X :=
by { unfreezingI { subst h, }, apply of_mono_zero X Y, }

lemma of_epi_eq_zero {X Y : C} (f : X ⟶ Y) [epi f] (h : f = 0) : is_zero Y :=
by { unfreezingI { subst h, }, apply of_epi_zero X Y, }

lemma iff_is_split_mono_eq_zero {X Y : C} (f : X ⟶ Y) [is_split_mono f] : is_zero X ↔ f = 0 :=
begin
  rw iff_id_eq_zero,
  split,
  { intro h, rw [←category.id_comp f, h, zero_comp], },
  { intro h, rw [←is_split_mono.id f], simp [h], },
end

lemma iff_is_split_epi_eq_zero {X Y : C} (f : X ⟶ Y) [is_split_epi f] : is_zero Y ↔ f = 0 :=
begin
  rw iff_id_eq_zero,
  split,
  { intro h, rw [←category.comp_id f, h, comp_zero], },
  { intro h, rw [←is_split_epi.id f], simp [h], },
end

lemma of_mono {X Y : C} (f : X ⟶ Y) [mono f] (i : is_zero Y) : is_zero X :=
begin
  unfreezingI { have hf := i.eq_zero_of_tgt f, subst hf, },
  exact is_zero.of_mono_zero X Y,
end

lemma of_epi {X Y : C} (f : X ⟶ Y) [epi f] (i : is_zero X) : is_zero Y :=
begin
  unfreezingI { have hf := i.eq_zero_of_src f, subst hf, },
  exact is_zero.of_epi_zero X Y,
end

end is_zero

/-- A category with a zero object has zero morphisms.

    It is rarely a good idea to use this. Many categories that have a zero object have zero
    morphisms for some other reason, for example from additivity. Library code that uses
    `zero_morphisms_of_zero_object` will then be incompatible with these categories because
    the `has_zero_morphisms` instances will not be definitionally equal. For this reason library
    code should generally ask for an instance of `has_zero_morphisms` separately, even if it already
    asks for an instance of `has_zero_objects`. -/
def is_zero.has_zero_morphisms {O : C} (hO : is_zero O) : has_zero_morphisms C :=
{ has_zero := λ X Y,
  { zero := hO.from X ≫ hO.to Y },
  zero_comp' := λ X Y Z f, by { rw category.assoc, congr, apply hO.eq_of_src, },
  comp_zero' := λ X Y Z f, by { rw ←category.assoc, congr, apply hO.eq_of_tgt, }}

namespace has_zero_object

variables [has_zero_object C]
open_locale zero_object

/-- A category with a zero object has zero morphisms.

    It is rarely a good idea to use this. Many categories that have a zero object have zero
    morphisms for some other reason, for example from additivity. Library code that uses
    `zero_morphisms_of_zero_object` will then be incompatible with these categories because
    the `has_zero_morphisms` instances will not be definitionally equal. For this reason library
    code should generally ask for an instance of `has_zero_morphisms` separately, even if it already
    asks for an instance of `has_zero_objects`. -/
def zero_morphisms_of_zero_object : has_zero_morphisms C :=
{ has_zero := λ X Y,
  { zero := (default : X ⟶ 0) ≫ default },
  zero_comp' := λ X Y Z f, by { dunfold has_zero.zero, rw category.assoc, congr, },
  comp_zero' := λ X Y Z f, by { dunfold has_zero.zero, rw ←category.assoc, congr, }}

section has_zero_morphisms
variables [has_zero_morphisms C]

@[simp] lemma zero_iso_is_initial_hom {X : C} (t : is_initial X) :
  (zero_iso_is_initial t).hom = 0 :=
by ext

@[simp] lemma zero_iso_is_initial_inv {X : C} (t : is_initial X) :
  (zero_iso_is_initial t).inv = 0 :=
by ext

@[simp] lemma zero_iso_is_terminal_hom {X : C} (t : is_terminal X) :
  (zero_iso_is_terminal t).hom = 0 :=
by ext

@[simp] lemma zero_iso_is_terminal_inv {X : C} (t : is_terminal X) :
  (zero_iso_is_terminal t).inv = 0 :=
by ext

@[simp] lemma zero_iso_initial_hom [has_initial C] : zero_iso_initial.hom = (0 : 0 ⟶ ⊥_ C) :=
by ext

@[simp] lemma zero_iso_initial_inv [has_initial C] : zero_iso_initial.inv = (0 : ⊥_ C ⟶ 0) :=
by ext

@[simp] lemma zero_iso_terminal_hom [has_terminal C] : zero_iso_terminal.hom = (0 : 0 ⟶ ⊤_ C) :=
by ext

@[simp] lemma zero_iso_terminal_inv [has_terminal C] : zero_iso_terminal.inv = (0 : ⊤_ C ⟶ 0) :=
by ext

end has_zero_morphisms

open_locale zero_object

instance {B : Type*} [category B] : has_zero_object (B ⥤ C) :=
(((category_theory.functor.const B).obj (0 : C)).is_zero $ λ X, is_zero_zero _).has_zero_object

end has_zero_object

open_locale zero_object

variables {D}

@[simp] lemma is_zero.map [has_zero_object D] [has_zero_morphisms D] {F : C ⥤ D} (hF : is_zero F)
  {X Y : C} (f : X ⟶ Y) : F.map f = 0 :=
(hF.obj _).eq_of_src _ _

@[simp] lemma _root_.category_theory.functor.zero_obj [has_zero_object D]
  (X : C) : is_zero ((0 : C ⥤ D).obj X) :=
(is_zero_zero _).obj _

@[simp] lemma _root_.category_theory.zero_map [has_zero_object D] [has_zero_morphisms D]
  {X Y : C} (f : X ⟶ Y) : (0 : C ⥤ D).map f = 0 :=
(is_zero_zero _).map _

section
variables [has_zero_object C] [has_zero_morphisms C]
open_locale zero_object

@[simp]
lemma id_zero : 𝟙 (0 : C) = (0 : 0 ⟶ 0) :=
by ext

/--  An arrow ending in the zero object is zero -/
-- This can't be a `simp` lemma because the left hand side would be a metavariable.
lemma zero_of_to_zero {X : C} (f : X ⟶ 0) : f = 0 :=
by ext

lemma zero_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : f = 0 :=
begin
  have h : f = f ≫ i.hom ≫ 𝟙 0 ≫ i.inv := by simp only [iso.hom_inv_id, id_comp, comp_id],
  simpa using h,
end

/-- An arrow starting at the zero object is zero -/
lemma zero_of_from_zero {X : C} (f : 0 ⟶ X) : f = 0 :=
by ext

lemma zero_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : f = 0 :=
begin
  have h : f = i.hom ≫ 𝟙 0 ≫ i.inv ≫ f := by simp only [iso.hom_inv_id_assoc, id_comp, comp_id],
  simpa using h,
end

lemma zero_of_source_iso_zero' {X Y : C} (f : X ⟶ Y) (i : is_isomorphic X 0) : f = 0 :=
zero_of_source_iso_zero f (nonempty.some i)
lemma zero_of_target_iso_zero' {X Y : C} (f : X ⟶ Y) (i : is_isomorphic Y 0) : f = 0 :=
zero_of_target_iso_zero f (nonempty.some i)

lemma mono_of_source_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) : mono f :=
⟨λ Z g h w, by rw [zero_of_target_iso_zero g i, zero_of_target_iso_zero h i]⟩

lemma epi_of_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : Y ≅ 0) : epi f :=
⟨λ Z g h w, by rw [zero_of_source_iso_zero g i, zero_of_source_iso_zero h i]⟩

/--
An object `X` has `𝟙 X = 0` if and only if it is isomorphic to the zero object.

Because `X ≅ 0` contains data (even if a subsingleton), we express this `↔` as an `≃`.
-/
def id_zero_equiv_iso_zero (X : C) : (𝟙 X = 0) ≃ (X ≅ 0) :=
{ to_fun    := λ h, { hom := 0, inv := 0, },
  inv_fun   := λ i, zero_of_target_iso_zero (𝟙 X) i,
  left_inv  := by tidy,
  right_inv := by tidy, }

@[simp]
lemma id_zero_equiv_iso_zero_apply_hom (X : C) (h : 𝟙 X = 0) :
  ((id_zero_equiv_iso_zero X) h).hom = 0 := rfl

@[simp]
lemma id_zero_equiv_iso_zero_apply_inv (X : C) (h : 𝟙 X = 0) :
  ((id_zero_equiv_iso_zero X) h).inv = 0 := rfl

/-- If `0 : X ⟶ Y` is an monomorphism, then `X ≅ 0`. -/
@[simps]
def iso_zero_of_mono_zero {X Y : C} (h : mono (0 : X ⟶ Y)) : X ≅ 0 :=
{ hom := 0,
  inv := 0,
  hom_inv_id' := (cancel_mono (0 : X ⟶ Y)).mp (by simp) }

/-- If `0 : X ⟶ Y` is an epimorphism, then `Y ≅ 0`. -/
@[simps]
def iso_zero_of_epi_zero {X Y : C} (h : epi (0 : X ⟶ Y)) : Y ≅ 0 :=
{ hom := 0,
  inv := 0,
  hom_inv_id' := (cancel_epi (0 : X ⟶ Y)).mp (by simp) }

/-- If a monomorphism out of `X` is zero, then `X ≅ 0`. -/
def iso_zero_of_mono_eq_zero {X Y : C} {f : X ⟶ Y} [mono f] (h : f = 0) : X ≅ 0 :=
by { unfreezingI { subst h, }, apply iso_zero_of_mono_zero ‹_›, }

/-- If an epimorphism in to `Y` is zero, then `Y ≅ 0`. -/
def iso_zero_of_epi_eq_zero {X Y : C} {f : X ⟶ Y} [epi f] (h : f = 0) : Y ≅ 0 :=
by { unfreezingI { subst h, }, apply iso_zero_of_epi_zero ‹_›, }

/-- If an object `X` is isomorphic to 0, there's no need to use choice to construct
an explicit isomorphism: the zero morphism suffices. -/
def iso_of_is_isomorphic_zero {X : C} (P : is_isomorphic X 0) : X ≅ 0 :=
{ hom := 0,
  inv := 0,
  hom_inv_id' :=
  begin
    casesI P,
    rw ←P.hom_inv_id,
    rw ←category.id_comp P.inv,
    simp,
  end,
  inv_hom_id' := by simp, }

end

section is_iso
variables [has_zero_morphisms C]

/--
A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
the identities on both `X` and `Y` are zero.
-/
@[simps]
def is_iso_zero_equiv (X Y : C) : is_iso (0 : X ⟶ Y) ≃ (𝟙 X = 0 ∧ 𝟙 Y = 0) :=
{ to_fun := by { introsI i, rw ←is_iso.hom_inv_id (0 : X ⟶ Y),
    rw ←is_iso.inv_hom_id (0 : X ⟶ Y), simp },
  inv_fun := λ h, ⟨⟨(0 : Y ⟶ X), by tidy⟩⟩,
  left_inv := by tidy,
  right_inv := by tidy, }

/--
A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
the identity on `X` is zero.
-/
def is_iso_zero_self_equiv (X : C) : is_iso (0 : X ⟶ X) ≃ (𝟙 X = 0) :=
by simpa using is_iso_zero_equiv X X

variables [has_zero_object C]
open_locale zero_object

/--
A zero morphism `0 : X ⟶ Y` is an isomorphism if and only if
`X` and `Y` are isomorphic to the zero object.
-/
def is_iso_zero_equiv_iso_zero (X Y : C) : is_iso (0 : X ⟶ Y) ≃ (X ≅ 0) × (Y ≅ 0) :=
begin
  -- This is lame, because `prod` can't cope with `Prop`, so we can't use `equiv.prod_congr`.
  refine (is_iso_zero_equiv X Y).trans _,
  symmetry,
  fsplit,
  { rintros ⟨eX, eY⟩, fsplit,
    exact (id_zero_equiv_iso_zero X).symm eX,
    exact (id_zero_equiv_iso_zero Y).symm eY, },
  { rintros ⟨hX, hY⟩, fsplit,
    exact (id_zero_equiv_iso_zero X) hX,
    exact (id_zero_equiv_iso_zero Y) hY, },
  { tidy, },
  { tidy, },
end

lemma is_iso_of_source_target_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) (j : Y ≅ 0) : is_iso f :=
begin
  rw zero_of_source_iso_zero f i,
  exact (is_iso_zero_equiv_iso_zero _ _).inv_fun ⟨i, j⟩,
end

/--
A zero morphism `0 : X ⟶ X` is an isomorphism if and only if
`X` is isomorphic to the zero object.
-/
def is_iso_zero_self_equiv_iso_zero (X : C) : is_iso (0 : X ⟶ X) ≃ (X ≅ 0) :=
(is_iso_zero_equiv_iso_zero X X).trans subsingleton_prod_self_equiv

end is_iso

/-- If there are zero morphisms, any initial object is a zero object. -/
lemma has_zero_object_of_has_initial_object
  [has_zero_morphisms C] [has_initial C] : has_zero_object C :=
begin
  refine ⟨⟨⊥_ C, λ X, ⟨⟨⟨0⟩, by tidy⟩⟩, λ X, ⟨⟨⟨0⟩, λ f, _⟩⟩⟩⟩,
  calc
    f = f ≫ 𝟙 _ : (category.comp_id _).symm
    ... = f ≫ 0 : by congr
    ... = 0     : has_zero_morphisms.comp_zero _ _
end

/-- If there are zero morphisms, any terminal object is a zero object. -/
lemma has_zero_object_of_has_terminal_object
  [has_zero_morphisms C] [has_terminal C] : has_zero_object C :=
begin
  refine ⟨⟨⊤_ C, λ X, ⟨⟨⟨0⟩, λ f, _⟩⟩, λ X, ⟨⟨⟨0⟩, by tidy⟩⟩⟩⟩,
  calc
    f = 𝟙 _ ≫ f : (category.id_comp _).symm
    ... = 0 ≫ f : by congr
    ... = 0     : zero_comp
end


section image
variable [has_zero_morphisms C]

lemma image_ι_comp_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [has_image f]
  [epi (factor_thru_image f)] (h : f ≫ g = 0) : image.ι f ≫ g = 0 :=
zero_of_epi_comp (factor_thru_image f) $ by simp [h]

lemma comp_factor_thru_image_eq_zero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [has_image g]
  (h : f ≫ g = 0) : f ≫ factor_thru_image g = 0 :=
zero_of_comp_mono (image.ι g) $ by simp [h]

variables [has_zero_object C]
open_locale zero_object

/--
The zero morphism has a `mono_factorisation` through the zero object.
-/
@[simps]
def mono_factorisation_zero (X Y : C) : mono_factorisation (0 : X ⟶ Y) :=
{ I := 0, m := 0, e := 0, }

/--
The factorisation through the zero object is an image factorisation.
-/
def image_factorisation_zero (X Y : C) : image_factorisation (0 : X ⟶ Y) :=
{ F := mono_factorisation_zero X Y,
  is_image := { lift := λ F', 0 } }


instance has_image_zero {X Y : C} : has_image (0 : X ⟶ Y) :=
has_image.mk $ image_factorisation_zero _ _

/-- The image of a zero morphism is the zero object. -/
def image_zero {X Y : C} : image (0 : X ⟶ Y) ≅ 0 :=
is_image.iso_ext (image.is_image (0 : X ⟶ Y)) (image_factorisation_zero X Y).is_image

/-- The image of a morphism which is equal to zero is the zero object. -/
def image_zero' {X Y : C} {f : X ⟶ Y} (h : f = 0) [has_image f] : image f ≅ 0 :=
image.eq_to_iso h ≪≫ image_zero

@[simp]
lemma image.ι_zero {X Y : C} [has_image (0 : X ⟶ Y)] : image.ι (0 : X ⟶ Y) = 0 :=
begin
  rw ←image.lift_fac (mono_factorisation_zero X Y),
  simp,
end

/--
If we know `f = 0`,
it requires a little work to conclude `image.ι f = 0`,
because `f = g` only implies `image f ≅ image g`.
-/
@[simp]
lemma image.ι_zero' [has_equalizers C] {X Y : C} {f : X ⟶ Y} (h : f = 0) [has_image f] :
  image.ι f = 0 :=
by { rw image.eq_fac h, simp }

end image

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance is_split_mono_sigma_ι {β : Type u'} [has_zero_morphisms C] (f : β → C)
  [has_colimit (discrete.functor f)] (b : β) : is_split_mono (sigma.ι f b) := is_split_mono.mk'
{ retraction := sigma.desc $ pi.single b (𝟙 _) }

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance is_split_epi_pi_π {β : Type u'} [has_zero_morphisms C] (f : β → C)
  [has_limit (discrete.functor f)] (b : β) : is_split_epi (pi.π f b) := is_split_epi.mk'
{ section_ := pi.lift $ pi.single b (𝟙 _) }

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance is_split_mono_coprod_inl [has_zero_morphisms C] {X Y : C} [has_colimit (pair X Y)] :
  is_split_mono (coprod.inl : X ⟶ X ⨿ Y) := is_split_mono.mk'
{ retraction := coprod.desc (𝟙 X) 0, }
/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance is_split_mono_coprod_inr [has_zero_morphisms C] {X Y : C} [has_colimit (pair X Y)] :
  is_split_mono (coprod.inr : Y ⟶ X ⨿ Y) := is_split_mono.mk'
{ retraction := coprod.desc 0 (𝟙 Y), }

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance is_split_epi_prod_fst [has_zero_morphisms C] {X Y : C} [has_limit (pair X Y)] :
  is_split_epi (prod.fst : X ⨯ Y ⟶ X) := is_split_epi.mk'
{ section_ := prod.lift (𝟙 X) 0, }
/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance is_split_epi_prod_snd [has_zero_morphisms C] {X Y : C} [has_limit (pair X Y)] :
  is_split_epi (prod.snd : X ⨯ Y ⟶ Y) := is_split_epi.mk'
{ section_ := prod.lift 0 (𝟙 Y), }

end category_theory.limits
