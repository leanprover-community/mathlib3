/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.exact
import algebra.homology.single
import algebra.homology.quasi_iso
import algebra.homology.homotopy

/-!
# Projective objects and categories with enough projectives

An object `P` is called projective if every morphism out of `P` factors through every epimorphism.

A category `C` has enough projectives if every object admits an epimorphism from some
projective object.

`projective.over X` picks an arbitrary such projective object,
and `projective.π X : projective.over X ⟶ X` is the corresponding epimorphism.

Given a morphism `f : X ⟶ Y`, `projective.left f` is a projective object over `kernel f`,
and `projective.d f : projective.left f ⟶ X` is the morphism `π (kernel f) ≫ kernel.ι f`.
When `C` is abelian `projective.d f` and `f` are exact.
Hence, starting from an epimorphism `P ⟶ X`, where `P` is projective,
we can apply `projective.d` repeatedly to obtain a projective resolution of `X`.
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
(projective : projective P)
(f : P ⟶ X)
(epi : epi f)

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

section
variables [abelian C]

/--
When `C` is abelian, `projective.d f` and `f` are exact.
-/
lemma exact_d_f {X Y : C} (f : X ⟶ Y) : exact (d f) f :=
(abelian.exact_iff _ _).2 $
  ⟨by simp, zero_of_epi_comp (π _) $ by rw [←category.assoc, cokernel.condition]⟩

end

section
variables [has_zero_morphisms C] [has_equalizers C] [has_images C]

/--
An auxiliary structure for working with projective resolutions:
this is the low-brow version of `resolution`,
with everything spelled out explicitly without using cochain complexes or quasi-isomorphism.
-/
@[nolint has_inhabited_instance]
structure resolution_core (Z : C) :=
(X : ℕ → C)
(d : Π n, X (n+1) ⟶ X n)
(zero : X 0 ≅ Z)
(projective : ∀ n, projective (X (n+1)))
(epi : epi (d 0))
(exact : ∀ n, exact (d (n+1)) (d n))

variables [has_zero_object C] [has_image_maps C] [has_cokernels C]

-- TODO maybe ditch this structure, and just have these as constructions.
/--
A `projective.resolution Z` consists of a `ℕ`-indexed cochain complex of projective objects,
along with a quasi-isomorphism to the complex consisting of just `Z` supported in degree `0`.
-/
structure resolution (Z : C) :=
(complex : cochain_complex C ℕ)
(projective : ∀ n, projective (complex.X n))
(map : complex ⟶ (homological_complex.single C _ 0).obj Z)
(quasi_iso : quasi_iso map)

attribute [instance] resolution.projective

instance {Z : C} (P : resolution Z) (n : ℕ) : epi (P.map.f n) := sorry

namespace resolution

def lift {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) :
  P.complex ⟶ Q.complex :=
sorry

lemma lift_commutes {Y Z : C} (f : Y ⟶ Z) (P : resolution Y) (Q : resolution Z) :
  lift f P Q ≫ Q.map = P.map ≫ (homological_complex.single C _ 0).map f :=
sorry

end resolution

end

namespace resolution

variables [preadditive C] [has_equalizers C] [has_images C] [has_image_maps C]
  [has_zero_object C] [has_cokernels C]

lemma lift_homotopy {Y Z : C} (f : Y ⟶ Z) {P : resolution Y} {Q : resolution Z}
  (g h : P.complex ⟶ Q.complex)
  (g_comm : g ≫ Q.map = P.map ≫ (homological_complex.single C _ 0).map f)
  (h_comm : h ≫ Q.map = P.map ≫ (homological_complex.single C _ 0).map f) :
  homotopy g h :=
sorry

def homotopy_equiv {Z : C} (P Q : resolution Z) : P.complex ⟶ Q.complex :=
  lift (𝟙 Z) P Q

@[simp] lemma homotopy_equiv_commutes {Z : C} (P Q : resolution Z) :
  homotopy_equiv P Q ≫ Q.map = P.map :=
sorry

-- TODO state that in the homotopy category `resolution.homotopy_equiv P Q` becomes an isomorphism
-- (and hence that it is a homotopy equivalence and a quasi-isomorphism).

-- TODO construct `resolution_functor : C ⥤ homotopy_category V ℕ`

end resolution

end enough_projectives

namespace resolution

/- We have to jump through some hoops to get `resolution.of` to typecheck! -/
section
variables (O : C → C) (π : Π X, O X ⟶ X)
variables (L : Π {X Y : C} (f : X ⟶ Y), C) (δ : Π {X Y : C} (f : X ⟶ Y), L f ⟶ X)

/-- An auxiliary construction for `resolution.of`. -/
def B' (Z : C) : ℕ → Σ (X Y : C), X ⟶ Y
| 0 := ⟨O Z, Z, π Z⟩
| (n+1) := ⟨L (B' n).2.2, (B' n).1, δ (B' n).2.2⟩

/-- An auxiliary construction for `resolution.of`. -/
def X' (Z : C) (n : ℕ) : C := (B' O π @L @δ Z n).2.1

/-- An auxiliary construction for `resolution.of`. -/
def d' (Z : C) (n : ℕ) : X' O π @L @δ Z (n+1) ⟶ X' O π @L @δ Z n :=
(B' O π @L @δ Z n).2.2

end

variables [enough_projectives C] [abelian C]

/--
In any category with enough projectives,
`projective.resolution.of Z` constructs a projection resolution of the object `Z`.
-/
def of (Z : C) : resolution_core Z :=
{ X := λ n, X' projective.over projective.π
    (λ (X Y : C) (f : X ⟶ Y), projective.left f)
    (λ (X Y : C) (f : X ⟶ Y), projective.d f)
    Z n,
  d := λ n, d' projective.over projective.π
    (λ (X Y : C) (f : X ⟶ Y), projective.left f)
    (λ (X Y : C) (f : X ⟶ Y), projective.d f)
    Z n,
  zero := iso.refl _,
  projective := λ n,
  begin
    induction n;
    { dsimp [X', B'],
      apply_instance, },
  end,
  epi := projective.π_epi _,
  exact := λ n, exact_d_f _ }

end resolution

end projective

end category_theory
