/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import algebra.homology.exact
import algebra.homology.single
import algebra.homology.quasi_iso
import algebra.homology.homotopy_category
import algebra.homology.augment
import category_theory.types

/-!
# Projective objects and categories with enough projectives

An object `P` is called projective if every morphism out of `P` factors through every epimorphism.

A category `C` has enough projectives if every object admits an epimorphism from some
projective object.

`projective.over X` picks an arbitrary such projective object,
and `projective.π X : projective.over X ⟶ X` is the corresponding epimorphism.

Given a morphism `f : X ⟶ Y`, `projective.left f` is a projective object over `kernel f`,
and `projective.d f : projective.left f ⟶ X` is the morphism `π (kernel f) ≫ kernel.ι f`.
-/

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

/--
An object `P` is called projective if every morphism out of `P` factors through every epimorphism.
-/
class projective (P : C) : Prop :=
(factors : ∀ {E X : C} (f : P ⟶ X) (e : E ⟶ X) [epi e], ∃ f', f' ≫ e = f)

section

/--
A projective presentation of an object `X` consists of an epimorphism `f : P ⟶ X`
from some projective object `P`.
-/
@[nolint has_inhabited_instance]
structure projective_presentation (X : C) :=
(P : C)
(projective : projective P . tactic.apply_instance)
(f : P ⟶ X)
(epi : epi f . tactic.apply_instance)

variables (C)

/-- A category "has enough projectives" if for every object `X` there is a projective object `P` and
    an epimorphism `P ↠ X`. -/
class enough_projectives : Prop :=
(presentation : ∀ (X : C), nonempty (projective_presentation X))

end

namespace projective

/--
An arbitrarily chosen factorisation of a morphism out of a projective object through an epimorphism.
-/
def factor_thru {P X E : C} [projective P] (f : P ⟶ X) (e : E ⟶ X) [epi e] : P ⟶ E :=
(projective.factors f e).some

@[simp] lemma factor_thru_comp {P X E : C} [projective P] (f : P ⟶ X) (e : E ⟶ X) [epi e] :
  factor_thru f e ≫ e = f :=
(projective.factors f e).some_spec

section
local attribute [instance] has_zero_object.has_zero

instance zero_projective [has_zero_object C] [has_zero_morphisms C] : projective (0 : C) :=
{ factors := λ E X f e epi, by { use 0, ext, }}

end

lemma of_iso {P Q : C} (i : P ≅ Q) (hP : projective P) : projective Q :=
begin
  fsplit,
  introsI E X f e e_epi,
  obtain ⟨f', hf'⟩ := projective.factors (i.hom ≫ f) e,
  exact ⟨i.inv ≫ f', by simp [hf']⟩
end

lemma iso_iff {P Q : C} (i : P ≅ Q) : projective P ↔ projective Q :=
⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every type is a projective object in `Type`. -/
instance (X : Type u) : projective X :=
{ factors := λ E X' f e epi,
  ⟨λ x, ((epi_iff_surjective _).mp epi (f x)).some,
  by { ext x, exact ((epi_iff_surjective _).mp epi (f x)).some_spec, }⟩ }

instance Type_enough_projectives : enough_projectives (Type u) :=
{ presentation := λ X, ⟨{ P := X, f := 𝟙 X, }⟩, }

instance {P Q : C} [has_binary_coproduct P Q] [projective P] [projective Q] :
  projective (P ⨿ Q) :=
{ factors := λ E X' f e epi, by exactI
  ⟨coprod.desc (factor_thru (coprod.inl ≫ f) e) (factor_thru (coprod.inr ≫ f) e), by tidy⟩, }

instance {β : Type v} (g : β → C) [has_coproduct g] [∀ b, projective (g b)] :
  projective (∐ g) :=
{ factors := λ E X' f e epi, by exactI
  ⟨sigma.desc (λ b, factor_thru (sigma.ι g b ≫ f) e), by tidy⟩, }

instance {P Q : C} [has_zero_morphisms C] [has_binary_biproduct P Q]
  [projective P] [projective Q] :
  projective (P ⊞ Q) :=
{ factors := λ E X' f e epi, by exactI
  ⟨biprod.desc (factor_thru (biprod.inl ≫ f) e) (factor_thru (biprod.inr ≫ f) e), by tidy⟩, }

instance {β : Type v} [decidable_eq β] (g : β → C) [has_zero_morphisms C] [has_biproduct g]
  [∀ b, projective (g b)] : projective (⨁ g) :=
{ factors := λ E X' f e epi, by exactI
  ⟨biproduct.desc (λ b, factor_thru (biproduct.ι g b ≫ f) e), by tidy⟩, }

section enough_projectives
variables [enough_projectives C]

/--
`projective.over X` provides an arbitrarily chosen projective object equipped with
an epimorphism `projective.π : projective.over X ⟶ X`.
-/
def over (X : C) : C :=
(enough_projectives.presentation X).some.P

instance projective_over (X : C) : projective (over X) :=
(enough_projectives.presentation X).some.projective

/--
The epimorphism `projective.π : projective.over X ⟶ X`
from the arbitrarily chosen projective object over `X`.
-/
def π (X : C) : over X ⟶ X :=
(enough_projectives.presentation X).some.f

instance π_epi (X : C) : epi (π X) :=
(enough_projectives.presentation X).some.epi

section
variables [has_zero_morphisms C] {X Y : C} (f : X ⟶ Y) [has_kernel f]

/-- When `C` has enough projectives, the object `projective.left f` is
the arbitrarily chosen projective object over `kernel f`. -/
@[derive projective]
def left : C := over (kernel f)

/-- When `C` has enough projectives,
`projective.d f : projective.left f ⟶ X` is the composition
`π (kernel f) ≫ kernel.ι f`.
-/
abbreviation d : left f ⟶ X :=
π (kernel f) ≫ kernel.ι f

end

end enough_projectives

end projective

open projective

section
variables [has_zero_morphisms C] [has_equalizers C] [has_images C]

/--
Given a projective object `P` mapping via `h` into
the middle object `R` of pair of exact morphisms `f : Q ⟶ R` and `g : R ⟶ S`,
such that `h ≫ g = 0`, there is a lift of `h` to `Q`.
-/
def exact.lift {P Q R S : C} [projective P] (h : P ⟶ R) (f : Q ⟶ R) (g : R ⟶ S)
  [exact f g] (w : h ≫ g = 0) : P ⟶ Q :=
factor_thru
  (factor_thru
    (factor_thru_kernel_subobject g h w)
    (image_to_kernel f g (by simp)))
  (factor_thru_image_subobject f)

@[simp] lemma exact.lift_comp {P Q R S : C} [projective P] (h : P ⟶ R) (f : Q ⟶ R) (g : R ⟶ S)
  [exact f g] (w : h ≫ g = 0) : exact.lift h f g w ≫ f = h :=
begin
  simp [exact.lift],
  conv_lhs { congr, skip, rw ← image_subobject_arrow_comp f, },
  rw [←category.assoc, factor_thru_comp, ←image_to_kernel_arrow,
    ←category.assoc, category_theory.projective.factor_thru_comp,
    factor_thru_kernel_subobject_comp_arrow],
end

end

section
variables [has_zero_morphisms C] [has_equalizers C] [has_images C]

/--
A `ProjectiveResolution Z` consists of a bundled `ℕ`-indexed chain complex of projective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.

Except in situations where you want to provide a particular projective resolution
(for example to compute a derived functor),
you will not typically need to use this bundled object, and will instead use
* `projective_resolution Z`: the `ℕ`-indexed chain complex
  (equipped with `projective` and `exact` instances)
* `projective_resolution.π Z`: the chain map from `projective_resolution Z` to
  `(single C _ 0).obj Z` (which comes equipped with appropriate `quasi_iso` and `epi` instances)
-/
-- We implement this concretely in terms of an exact sequence,
-- not even mentioning chain complexes or quasi-isomorphisms.
@[nolint has_inhabited_instance]
structure ProjectiveResolution (Z : C) :=
(X : ℕ → C)
(d : Π n, X (n+1) ⟶ X n)
(zero : X 0 ≅ Z)
(projective : ∀ n, projective (X (n+1)))
(epi : epi (d 0))
(exact : ∀ n, exact (d (n+1)) (d n))

/--
An object admits a projective resolution.
-/
class has_projective_resolution (Z : C) : Prop :=
(out [] : nonempty (ProjectiveResolution Z))

section
variables (C)

/--
You will rarely use this typeclass directly: it is implied by the combination
`[enough_projectives C]` and `[abelian C]`.
-/
class has_projective_resolutions : Prop :=
(out : ∀ Z : C, has_projective_resolution Z)

attribute [instance] has_projective_resolutions.out

end

namespace ProjectiveResolution

variables [has_zero_object C] [has_image_maps C] [has_cokernels C]

-- TODO generalize to `chain_complex.mk`?
def exact_sequence {Z : C} (P : ProjectiveResolution Z) : chain_complex C ℕ :=
{ X := P.X,
  d := λ i j, if h : i = j + 1 then eq_to_hom (congr_arg P.X h) ≫ P.d j else 0,
  shape' := λ i j w, by rw dif_neg (ne.symm w),
  d_comp_d' := λ i j k,
  begin
    split_ifs with h h' h',
    { substs h h', simp [(P.exact k).w], },
    all_goals { simp },
  end }

instance exact'' {Z : C} (P : ProjectiveResolution Z) (n : ℕ) :
  category_theory.exact (P.exact_sequence.d (n+2) (n+1)) (P.exact_sequence.d (n+1) n) :=
begin
  dsimp [exact_sequence],
  rw [if_pos rfl, if_pos rfl],
  rw [category.id_comp, category.id_comp],
  exact P.exact n,
end

def complex {Z : C} (P : ProjectiveResolution Z) : chain_complex C ℕ :=
chain_complex.truncate.obj P.exact_sequence

instance exact' {Z : C} (P : ProjectiveResolution Z) (n : ℕ) :
  category_theory.exact (P.complex.d (n+2) (n+1)) (P.complex.d (n+1) n) :=
ProjectiveResolution.exact'' P (n+1)

instance projective' {Z : C} (P : ProjectiveResolution Z) (n : ℕ) :
  category_theory.projective (P.complex.X n) :=
P.projective n

def π {Z : C} (P : ProjectiveResolution Z) :
  P.complex ⟶ (homological_complex.single C _ 0).obj Z :=
chain_complex.truncate_to_single P.exact_sequence ≫
  ((homological_complex.single C _ 0).map_iso P.zero).hom

instance {Z : C} (P : ProjectiveResolution Z) :
  category_theory.exact (P.complex.d 1 0) (P.π.f 0) :=
begin
  -- TODO: yuck:
  dsimp [π, complex, exact_sequence,
    chain_complex.truncate_to_single, chain_complex.truncate, chain_complex.to_single_equiv],
  split_ifs,
  { rw [category.comp_id, category.id_comp, category.id_comp, category.id_comp, exact_comp_iso],
    exact P.exact 0, },
  { simpa using h, },
end

@[simp] lemma π_f_succ {Z : C} (P : ProjectiveResolution Z) (n : ℕ) :
  P.π.f (n+1) = 0 :=
begin
  -- TODO: yuck
  dsimp [π, exact_sequence, chain_complex.truncate_to_single, chain_complex.truncate,
    chain_complex.to_single_equiv],
  rw [dif_neg, zero_comp],
  simp,
end

instance quasi_iso {Z : C} (P : ProjectiveResolution Z) : quasi_iso P.π :=
begin
  dsimp [π],
  apply_instance,
end

instance {Z : C} (P : ProjectiveResolution Z) (n : ℕ) : category_theory.epi (P.π.f n) :=
begin
  induction n,
  { dsimp [π, exact_sequence,
      chain_complex.truncate_to_single, chain_complex.truncate, chain_complex.to_single_equiv],
    simp only [if_true, eq_self_iff_true, self_eq_add_left, category.comp_id, category.id_comp],
    haveI := P.epi,
    exact @epi_comp _ _ _ _ _ _ P.epi P.zero.hom _, },
  { apply_instance, }
end

-- TODO define `ProjectiveResolution.self Z` for `[projective Z]`.

/- Auxiliary construction for `lift`. -/
def lift_f_zero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  P.complex.X 0 ⟶ Q.complex.X 0 :=
factor_thru (P.π.f 0 ≫ f) (Q.π.f 0)

local attribute [instance] epi_comp

/- Auxiliary construction for `lift`. -/
def lift_f_one {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  P.complex.X 1 ⟶ Q.complex.X 1 :=
exact.lift (P.complex.d 1 0 ≫ lift_f_zero f P Q) (Q.complex.d 1 0) (Q.π.f 0) (by simp [lift_f_zero])

/- Auxiliary lemma for `lift`. -/
@[simp] lemma lift_f_one_zero_comm
  {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  lift_f_one f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ lift_f_zero f P Q :=
begin
  dsimp [lift_f_zero, lift_f_one],
  simp,
end

/- Auxiliary construction for `lift`. -/
def lift_f_succ {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z)
  (n : ℕ) (g : P.complex.X n ⟶ Q.complex.X n) (g' : P.complex.X (n+1) ⟶ Q.complex.X (n+1))
  (w : g' ≫ Q.complex.d (n+1) n = P.complex.d (n+1) n ≫ g) :
  Σ' g'' : P.complex.X (n+2) ⟶ Q.complex.X (n+2),
    g'' ≫ Q.complex.d (n+2) (n+1) = P.complex.d (n+2) (n+1) ≫ g' :=
⟨exact.lift
  (P.complex.d (n+2) (n+1) ≫ g') ((Q.complex.d (n+2) (n+1))) (Q.complex.d (n+1) n) (by simp [w]),
  (by simp)⟩

/-- A morphism in `C` lifts to a chain map between projective resolutions. -/
def lift {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  P.complex ⟶ Q.complex :=
begin
  fapply homological_complex.hom.mk_inductive,
  apply lift_f_zero f,
  apply lift_f_one f,
  apply lift_f_one_zero_comm f,
  rintro n ⟨g, g', w⟩,
  exact lift_f_succ f P Q n g g' w,
end

/-- The resolution maps interwine the lift of a morphism and that morphism. -/
@[simp, reassoc]
lemma lift_commutes
  {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  lift f P Q ≫ Q.π = P.π ≫ (homological_complex.single C _ 0).map f :=
begin
  ext n,
  rcases n with (_|_|n),
  { dsimp [lift, lift_f_zero], simp, },
  { dsimp [lift, lift_f_one], simp, },
  { dsimp, simp, },
end

-- Now that we've checked this property of the lift,
-- we can seal away the actual definition.
attribute [irreducible] lift

end ProjectiveResolution

end

namespace ProjectiveResolution

variables [preadditive C] [has_equalizers C] [has_images C] [has_image_maps C]
  [has_zero_object C] [has_cokernels C]

/-- An auxiliary definition for `lift_homotopy_zero`. -/
def lift_homotopy_zero_zero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  (f : P.complex ⟶ Q.complex)
  (comm : f ≫ Q.π = 0) : P.complex.X 0 ⟶ Q.complex.X 1 :=
exact.lift (f.f 0) (Q.complex.d 1 0) (Q.π.f 0)
  (congr_fun (congr_arg homological_complex.hom.f comm) 0)

/-- An auxiliary definition for `lift_homotopy_zero`. -/
def lift_homotopy_zero_one {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  (f : P.complex ⟶ Q.complex)
  (comm : f ≫ Q.π = 0) : P.complex.X 1 ⟶ Q.complex.X 2 :=
exact.lift
  (f.f 1 - P.complex.d 1 0 ≫ lift_homotopy_zero_zero f comm) (Q.complex.d 2 1) (Q.complex.d 1 0)
  (by simp [lift_homotopy_zero_zero])

/-- An auxiliary definition for `lift_homotopy_zero`. -/
def lift_homotopy_zero_succ {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  (f : P.complex ⟶ Q.complex)
  (comm : f ≫ Q.π = 0) (n : ℕ)
  (g : P.complex.X n ⟶ Q.complex.X (n + 1)) (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
  (w : f.f (n + 1) = g' ≫ Q.complex.d (n + 2) (n + 1) + P.complex.d (n + 1) n ≫ g) :
  P.complex.X (n + 2) ⟶ Q.complex.X (n + 3) :=
exact.lift
  (f.f (n+2) - P.complex.d (n+2) (n+1) ≫ g') (Q.complex.d (n+3) (n+2)) (Q.complex.d (n+2) (n+1))
  (by simp [w])

/-- Any lift of the zero morphism is homotopic to zero. -/
def lift_homotopy_zero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  (f : P.complex ⟶ Q.complex)
  (comm : f ≫ Q.π = 0) :
  homotopy f 0 :=
begin
  fapply homotopy.mk_inductive,
  { exact lift_homotopy_zero_zero f comm, },
  { simp [lift_homotopy_zero_zero], },
  { exact lift_homotopy_zero_one f comm, },
  { simp [lift_homotopy_zero_one], },
  { rintro n ⟨g, g', w⟩,
    fsplit,
    { exact lift_homotopy_zero_succ f comm n g g' w, },
    { simp [lift_homotopy_zero_succ, w], }, }
end

/-- Two lifts of the same morphism are homotopic. -/
def lift_homotopy {Y Z : C} (f : Y ⟶ Z) {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  (g h : P.complex ⟶ Q.complex)
  (g_comm : g ≫ Q.π = P.π ≫ (homological_complex.single C _ 0).map f)
  (h_comm : h ≫ Q.π = P.π ≫ (homological_complex.single C _ 0).map f) :
  homotopy g h :=
begin
  apply homotopy.equiv_sub_zero.inv_fun,
  apply lift_homotopy_zero,
  simp [g_comm, h_comm],
end

/-- The lift of the identity morphism is homotopic to the identity chain map. -/
def lift_id_homotopy (X : C) (P : ProjectiveResolution X) :
  homotopy (lift (𝟙 X) P P) (𝟙 P.complex) :=
by { apply lift_homotopy (𝟙 X); simp, }

/-- The lift of a composition is homotopic to the composition of the lifts. -/
def lift_comp_homotopy {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
  (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) (R : ProjectiveResolution Z) :
  homotopy (lift (f ≫ g) P R) (lift f P Q ≫ lift g Q R) :=
by { apply lift_homotopy (f ≫ g); simp, }

/-- Any two projective resolutions are homotopy equivalent. -/
def homotopy_equiv {X : C} (P Q : ProjectiveResolution X) :
  homotopy_equiv P.complex Q.complex :=
{ hom := lift (𝟙 X) P Q,
  inv := lift (𝟙 X) Q P,
  homotopy_hom_inv_id := begin
    refine (lift_comp_homotopy (𝟙 X) (𝟙 X) P Q P).symm.trans _,
    simp [category.id_comp],
    apply lift_id_homotopy,
  end,
  homotopy_inv_hom_id := begin
    refine (lift_comp_homotopy (𝟙 X) (𝟙 X) Q P Q).symm.trans _,
    simp [category.id_comp],
    apply lift_id_homotopy,
  end, }

end ProjectiveResolution

section

variables [has_zero_morphisms C] [has_zero_object C] [has_equalizers C] [has_cokernels C]
  [has_images C] [has_image_maps C]

/-- An arbitrarily chosen projective resolution of an object. -/
abbreviation projective_resolution (Z : C) [has_projective_resolution Z] : chain_complex C ℕ :=
(has_projective_resolution.out Z).some.complex

/-- The chain map from the arbitrarily chosen projective resolution `projective_resolution Z`
back to the chain complex consisting of `Z` supported in degree `0`. -/
abbreviation projective_resolution.π (Z : C) [has_projective_resolution Z] :
  projective_resolution Z ⟶ (homological_complex.single C _ 0).obj Z :=
(has_projective_resolution.out Z).some.π

/-- The lift of a morphism to a chain map between the arbitrarily chosen projective resolutions. -/
abbreviation projective_resolution.lift {X Y : C} (f : X ⟶ Y)
  [has_projective_resolution X] [has_projective_resolution Y] :
  projective_resolution X ⟶ projective_resolution Y :=
ProjectiveResolution.lift f _ _

end

variables (C) [preadditive C] [has_zero_object C] [has_equalizers C] [has_cokernels C]
  [has_images C] [has_image_maps C] [has_projective_resolutions C]

/--
Taking projective resolutions is functorial,
if considered with target the homotopy category
(`ℕ`-indexed chain complexes and chain maps up to homotopy).
-/
def projective_resolutions : C ⥤ homotopy_category C (complex_shape.down ℕ) :=
{ obj := λ X, (homotopy_category.quotient _ _).obj (projective_resolution X),
  map := λ X Y f, (homotopy_category.quotient _ _).map (projective_resolution.lift f),
  map_id' := λ X, begin
    rw ←(homotopy_category.quotient _ _).map_id,
    apply homotopy_category.eq_of_homotopy,
    apply ProjectiveResolution.lift_id_homotopy,
  end,
  map_comp' := λ X Y Z f g, begin
    rw ←(homotopy_category.quotient _ _).map_comp,
    apply homotopy_category.eq_of_homotopy,
    apply ProjectiveResolution.lift_comp_homotopy,
  end, }

variables {C} {D : Type*} [category D] [preadditive D] [has_zero_object D]
  [has_equalizers D] [has_images D] [has_image_maps D] [has_cokernels D]

/-- The left derived functors of an additive functor. -/
def functor.left_derived (n : ℕ) (F : C ⥤ D) [F.additive] : C ⥤ D :=
projective_resolutions C ⋙ F.map_homotopy_category _ ⋙ homotopy_category.homology_functor D _ n

/-- We can compute a left derived functor using a chosen projective resolution. -/
def functor.left_derived_obj_iso (n : ℕ) (F : C ⥤ D) [F.additive] (X : C) (P : ProjectiveResolution X) :
  (F.left_derived n).obj X ≅
    (homology_functor D _ n).obj ((F.map_homological_complex _).obj P.complex) :=
(homotopy_category.homology_functor D _ n).map_iso
  (homotopy_category.iso_of_homotopy_equiv
    (F.map_homotopy_equiv (ProjectiveResolution.homotopy_equiv _ P)))
  ≪≫ (homotopy_category.homology_factors D _ n).app _

/--
We can compute a left derived functor on a morphism using a lift of that morphism
to a chain map between chosen projective resolutions.
-/
lemma functor.left_derived_map_eq (n : ℕ) (F : C ⥤ D) [F.additive] {X Y : C} (f : X ⟶ Y)
  (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) (g : P.complex ⟶ Q.complex)
  (w : g ≫ Q.π = P.π ≫ (homological_complex.single C _ 0).map f) :
  (F.left_derived n).map f =
  (F.left_derived_obj_iso n X P).hom ≫
    (homology_functor D _ n).map ((F.map_homological_complex _).map g) ≫
    (F.left_derived_obj_iso n Y Q).inv :=
begin
  dsimp only [functor.left_derived, functor.left_derived_obj_iso],
  dsimp, simp,
  sorry,
end

/-- The natural transformation between left-derived functors induced by a natural transformation. -/
def nat_trans.left_derived (n : ℕ) {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G) :
  F.left_derived n ⟶ G.left_derived n :=
whisker_left (projective_resolutions C)
  (whisker_right (nat_trans.map_homotopy_category α _)
    (homotopy_category.homology_functor D _ n))

/--
A component of the natural transformation between left-derived functors can be computed
using a chosen projective resolution.
-/
lemma nat_trans.left_derived_eq (n : ℕ) {F G : C ⥤ D} [F.additive] [G.additive] (α : F ⟶ G)
  (X : C) (P : ProjectiveResolution X) :
  (nat_trans.left_derived n α).app X =
    (F.left_derived_obj_iso n X P).hom ≫
      (homology_functor D _ n).map ((nat_trans.map_homological_complex α _).app P.complex) ≫
        (G.left_derived_obj_iso n X P).inv :=
begin
  dsimp [nat_trans.left_derived, functor.left_derived_obj_iso],
  simp only [category.comp_id, category.id_comp],
  rw homotopy_category.homology_functor_map_factors,
  simp only [←functor.map_comp],
  congr' 1,
  apply homotopy_category.eq_of_homotopy,
end


-- TODO calculate on projective objects
-- TODO left-derived functors of the identity functor
-- PROJECT left-derived functors of a composition (Grothendieck sequence)

end category_theory
