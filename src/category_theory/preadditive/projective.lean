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

def complex {Z : C} (P : ProjectiveResolution Z) : chain_complex C ℕ :=
chain_complex.truncate.obj P.exact_sequence

instance exact' {Z : C} (P : ProjectiveResolution Z) (n : ℕ) :
  category_theory.exact (P.complex.d (n+2) (n+1)) (P.complex.d (n+1) n) :=
begin
  dsimp [complex, exact_sequence],
  rw [if_pos rfl, if_pos rfl],
  rw [category.id_comp, category.id_comp],
  exact P.exact (n+1),
end

instance projective' {Z : C} (P : ProjectiveResolution Z) (n : ℕ) :
  category_theory.projective (P.complex.X n) :=
P.projective n

def π {Z : C} (P : ProjectiveResolution Z) :
  P.complex ⟶ (homological_complex.single C _ 0).obj Z :=
chain_complex.truncate_to_single P.exact_sequence ≫
  (homological_complex.single C _ 0).map P.zero.hom

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
sorry

instance {Z : C} (P : ProjectiveResolution Z) (n : ℕ) : category_theory.epi (P.π.f n) := sorry

/- Auxiliary construction for `lift`. -/
def lift_f_zero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  P.complex.X 0 ⟶ Q.complex.X 0 :=
factor_thru (P.π.f 0 ≫ f) (Q.π.f 0)

local attribute [instance] epi_comp

/- Auxiliary construction for `lift`. -/
def lift_f_one {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  P.complex.X 1 ⟶ Q.complex.X 1 :=
begin
  have z : (P.complex.d 1 0 ≫ lift_f_zero f P Q) ≫ Q.π.f 0 = 0,
  { dsimp [lift_f_zero], simp, },
  let g := factor_thru_kernel_subobject (Q.π.f 0) _ z,
  -- It is tempting, but incorrect, to factor `g` through the composition in one step here!
  exact factor_thru (factor_thru g
    (image_to_kernel (Q.complex.d 1 0) (Q.π.f 0) (by simp)))
      (factor_thru_image_subobject (Q.complex.d 1 0))
end

/- Auxiliary lemma for `lift`. -/
@[simp] lemma lift_f_one_zero_comm
  {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  lift_f_one f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ lift_f_zero f P Q :=
begin
  dsimp [lift_f_zero, lift_f_one],
  conv_lhs { congr, skip, rw ← image_subobject_arrow_comp (Q.complex.d 1 0), },
  rw [←category.assoc, category_theory.projective.factor_thru_comp, ←image_to_kernel_arrow,
    ←category.assoc, category_theory.projective.factor_thru_comp,
    factor_thru_kernel_subobject_comp_arrow],
end

/- Auxiliary construction for `lift`. -/
def lift_f_succ {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) (n : ℕ)
  (p : Σ' (f : P.complex.X n ⟶ Q.complex.X n) (f' : P.complex.X (n+1) ⟶ Q.complex.X (n+1)),
    f' ≫ Q.complex.d (n+1) n = P.complex.d (n+1) n ≫ f) :
  Σ' f'' : P.complex.X (n+2) ⟶ Q.complex.X (n+2),
    f'' ≫ Q.complex.d (n+2) (n+1) = P.complex.d (n+2) (n+1) ≫ p.2.1 :=
begin
  rcases p with ⟨f, f', w⟩,
  have z : (P.complex.d (n+2) (n+1) ≫ f') ≫ Q.complex.d (n+1) n = 0,
  { rw [category.assoc, w, ←category.assoc, P.complex.d_comp_d, zero_comp], },
  let g := factor_thru_kernel_subobject (Q.complex.d (n+1) n) _ z,
  fsplit,
  -- It is tempting, but incorrect, to factor `g` through the composition in one step here!
  exact factor_thru (factor_thru g
    (image_to_kernel (Q.complex.d (n+2) (n+1)) (Q.complex.d (n+1) n) (Q.complex.d_comp_d _ _ _)))
      (factor_thru_image_subobject (Q.complex.d (n+2) (n+1))),
  dsimp [g],
  conv_lhs { congr, skip, rw ← image_subobject_arrow_comp (Q.complex.d (n+2) (n+1)), },
  rw [←category.assoc, category_theory.projective.factor_thru_comp, ←image_to_kernel_arrow,
    ←category.assoc, category_theory.projective.factor_thru_comp,
    factor_thru_kernel_subobject_comp_arrow],
end

/-- A morphism in `C` lifts to a chain map between projective resolutions. -/
def lift {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  P.complex ⟶ Q.complex :=
begin
  fapply homological_complex.hom.mk_inductive,
  apply lift_f_zero f,
  apply lift_f_one f,
  apply lift_f_one_zero_comm f,
  apply lift_f_succ f,
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

/-- Any lift of the zero morphism is homotopic to zero. -/
def lift_homotopy_zero {Y Z : C} {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  (f : P.complex ⟶ Q.complex)
  (comm : f ≫ Q.π = 0) :
  homotopy f 0 :=
sorry

/-- Two lifts of the same morphism are homotopic. -/
def lift_homotopy {Y Z : C} (f : Y ⟶ Z) {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  (g h : P.complex ⟶ Q.complex)
  (g_comm : g ≫ Q.π = P.π ≫ (homological_complex.single C _ 0).map f)
  (h_comm : h ≫ Q.π = P.π ≫ (homological_complex.single C _ 0).map f) :
  homotopy g h :=
begin
  apply homotopy.sub_zero.inv_fun,
  apply lift_homotopy_zero,
  simp [g_comm, h_comm],
end

def lift_id_homotopy (X : C) (P : ProjectiveResolution X) :
  homotopy (lift (𝟙 X) P P) (𝟙 P.complex) :=
by { apply lift_homotopy (𝟙 X); simp, }

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

abbreviation projective_resolution (Z : C) [has_projective_resolution Z] : chain_complex C ℕ :=
(has_projective_resolution.out Z).some.complex

abbreviation projective_resolution.π (Z : C) [has_projective_resolution Z] :
  projective_resolution Z ⟶ (homological_complex.single C _ 0).obj Z :=
(has_projective_resolution.out Z).some.π

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
projective_resolutions C ⋙ F.map_homotopy_category _ _ ⋙ homotopy_category.homology_functor D _ n

/-- We can compute a left derived functor using a chosen projective resolution. -/
def functor.left_derived.iso (n : ℕ) (F : C ⥤ D) [F.additive] (X : C) (P : ProjectiveResolution X) :
  (F.left_derived n).obj X ≅
    (homology_functor D _ n).obj ((F.map_homological_complex _).obj P.complex) :=
(homotopy_category.homology_functor D _ n).map_iso
  (homotopy_category.iso_of_homotopy_equiv
    (F.map_homotopy_equiv (ProjectiveResolution.homotopy_equiv _ P)))
  ≪≫ (homotopy_category.homology_factors D _ n).app _

end category_theory
