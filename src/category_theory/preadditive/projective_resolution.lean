/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.projective
import algebra.homology.single
import algebra.homology.homotopy_category

/-!
# Projective resolutions

A projective resolution `P : ProjectiveResolution Z` of an object `Z : C` consists of
a `ℕ`-indexed chain complex `P.complex` of projective objects,
along with a chain map `P.π` from `C` to the chain complex consisting just of `Z` in degree zero,
so that the augmented chain complex is exact.

When `C` is abelian, this exactness condition is equivalent to `π` being a quasi-isomorphism.
It turns out that this formulation allows us to set up the basic theory of derived functors
without even assuming `C` is abelian.

(Typically, however, to show `has_projective_resolutions C`
one will assume `enough_projectives C` and `abelian C`.
This construction appears in `category_theory.abelian.projectives`.)

We show that given `P : ProjectiveResolution X` and `Q : ProjectiveResolution Y`,
any morphism `X ⟶ Y` admits a lift to a chain map `P.complex ⟶ Q.complex`.
(It is a lift in the sense that
the projection maps `P.π` and `Q.π` intertwine the lift and the original morphism.)

Moreover, we show that any two such lifts are homotopic.

As a consequence, if every object admits a projective resolution,
we can construct a functor `projective_resolutions C : C ⥤ homotopy_category C`.
-/

noncomputable theory

open category_theory
open category_theory.limits

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

open projective

section
variables [has_zero_object C] [has_zero_morphisms C] [has_equalizers C] [has_images C]

/--
A `ProjectiveResolution Z` consists of a bundled `ℕ`-indexed chain complex of projective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.

(We don't actually ask here that the chain map is a quasi-iso, just exactness everywhere:
that `π` is a quasi-iso is a lemma when the category is abelian.
Should we just ask for it here?)

Except in situations where you want to provide a particular projective resolution
(for example to compute a derived functor),
you will not typically need to use this bundled object, and will instead use
* `projective_resolution Z`: the `ℕ`-indexed chain complex
  (equipped with `projective` and `exact` instances)
* `projective_resolution.π Z`: the chain map from `projective_resolution Z` to
  `(single C _ 0).obj Z` (all the components are equipped with `epi` instances,
  and when the category is `abelian` we will show `π` is a quasi-iso).
-/
@[nolint has_inhabited_instance]
structure ProjectiveResolution (Z : C) :=
(complex : chain_complex C ℕ)
(π : homological_complex.hom complex ((chain_complex.single₀ C).obj Z))
(projective : ∀ n, projective (complex.X n) . tactic.apply_instance)
(exact₀ : exact (complex.d 1 0) (π.f 0) . tactic.apply_instance)
(exact : ∀ n, exact (complex.d (n+2) (n+1)) (complex.d (n+1) n) . tactic.apply_instance)
(epi : epi (π.f 0) . tactic.apply_instance)

attribute [instance] ProjectiveResolution.projective ProjectiveResolution.exact₀
  ProjectiveResolution.exact ProjectiveResolution.epi

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
By itself it's enough to set up the basic theory of derived functors.
-/
class has_projective_resolutions : Prop :=
(out : ∀ Z : C, has_projective_resolution Z)

attribute [instance, priority 100] has_projective_resolutions.out

end

namespace ProjectiveResolution

@[simp] lemma π_f_succ {Z : C} (P : ProjectiveResolution Z) (n : ℕ) :
  P.π.f (n+1) = 0 :=
begin
  apply zero_of_target_iso_zero,
  dsimp, refl,
end

instance {Z : C} (P : ProjectiveResolution Z) (n : ℕ) : category_theory.epi (P.π.f n) :=
by cases n; apply_instance

/-- A projective object admits a trivial projective resolution: itself in degree 0. -/
def self (Z : C) [category_theory.projective Z] : ProjectiveResolution Z :=
{ complex := (chain_complex.single₀ C).obj Z,
  π := 𝟙 ((chain_complex.single₀ C).obj Z),
  projective := λ n, begin
    cases n,
    { dsimp, apply_instance, },
    { dsimp, apply_instance, },
  end,
  exact₀ := by { dsimp, apply_instance, },
  exact := λ n, by { dsimp, apply_instance, },
  epi := by { dsimp, apply_instance, }, }

/-- Auxiliary construction for `lift`. -/
def lift_f_zero {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  P.complex.X 0 ⟶ Q.complex.X 0 :=
factor_thru (P.π.f 0 ≫ f) (Q.π.f 0)

/-- Auxiliary construction for `lift`. -/
def lift_f_one {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  P.complex.X 1 ⟶ Q.complex.X 1 :=
exact.lift (P.complex.d 1 0 ≫ lift_f_zero f P Q) (Q.complex.d 1 0) (Q.π.f 0) (by simp [lift_f_zero])

/-- Auxiliary lemma for `lift`. -/
@[simp] lemma lift_f_one_zero_comm
  {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  lift_f_one f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ lift_f_zero f P Q :=
begin
  dsimp [lift_f_zero, lift_f_one],
  simp,
end

/-- Auxiliary construction for `lift`. -/
def lift_f_succ {Y Z : C} (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z)
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
  fapply chain_complex.mk_hom,
  apply lift_f_zero f,
  apply lift_f_one f,
  apply lift_f_one_zero_comm f,
  rintro n ⟨g, g', w⟩,
  exact lift_f_succ P Q n g g' w,
end

/-- The resolution maps interwine the lift of a morphism and that morphism. -/
@[simp, reassoc]
lemma lift_commutes
  {Y Z : C} (f : Y ⟶ Z) (P : ProjectiveResolution Y) (Q : ProjectiveResolution Z) :
  lift f P Q ≫ Q.π = P.π ≫ (chain_complex.single₀ C).map f :=
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

variables [has_zero_object C] [preadditive C] [has_equalizers C] [has_images C]

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
  (f : P.complex ⟶ Q.complex) (n : ℕ)
  (g : P.complex.X n ⟶ Q.complex.X (n + 1)) (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2))
  (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
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
    { exact lift_homotopy_zero_succ f n g g' w, },
    { simp [lift_homotopy_zero_succ, w], }, }
end

/-- Two lifts of the same morphism are homotopic. -/
def lift_homotopy {Y Z : C} (f : Y ⟶ Z) {P : ProjectiveResolution Y} {Q : ProjectiveResolution Z}
  (g h : P.complex ⟶ Q.complex)
  (g_comm : g ≫ Q.π = P.π ≫ (chain_complex.single₀ C).map f)
  (h_comm : h ≫ Q.π = P.π ≫ (chain_complex.single₀ C).map f) :
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

-- We don't care about the actual definitions of these homotopies.
attribute [irreducible] lift_homotopy_zero lift_homotopy lift_id_homotopy lift_comp_homotopy

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

@[simp, reassoc] lemma homotopy_equiv_hom_π {X : C} (P Q : ProjectiveResolution X) :
  (homotopy_equiv P Q).hom ≫ Q.π = P.π :=
by simp [homotopy_equiv]

@[simp, reassoc] lemma homotopy_equiv_inv_π {X : C} (P Q : ProjectiveResolution X) :
  (homotopy_equiv P Q).inv ≫ P.π = Q.π :=
by simp [homotopy_equiv]

end ProjectiveResolution

section

variables [has_zero_morphisms C] [has_zero_object C] [has_equalizers C] [has_images C]

/-- An arbitrarily chosen projective resolution of an object. -/
abbreviation projective_resolution (Z : C) [has_projective_resolution Z] : chain_complex C ℕ :=
(has_projective_resolution.out Z).some.complex

/-- The chain map from the arbitrarily chosen projective resolution `projective_resolution Z`
back to the chain complex consisting of `Z` supported in degree `0`. -/
abbreviation projective_resolution.π (Z : C) [has_projective_resolution Z] :
  projective_resolution Z ⟶ (chain_complex.single₀ C).obj Z :=
(has_projective_resolution.out Z).some.π

/-- The lift of a morphism to a chain map between the arbitrarily chosen projective resolutions. -/
abbreviation projective_resolution.lift {X Y : C} (f : X ⟶ Y)
  [has_projective_resolution X] [has_projective_resolution Y] :
  projective_resolution X ⟶ projective_resolution Y :=
ProjectiveResolution.lift f _ _

end

variables (C) [preadditive C] [has_zero_object C] [has_equalizers C] [has_images C]
  [has_projective_resolutions C]

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

end category_theory
