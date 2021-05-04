/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.single
import algebra.homology.exact
import tactic.linarith

/-!
# Augmentation and truncation of `ℕ`-indexed chain complexes.
-/

open category_theory
open category_theory.limits
open homological_complex

universes v u

variables {V : Type u} [category.{v} V]

namespace chain_complex

/--
The truncation of a `ℕ`-indexed chain complex,
deleting the object at `0` and shifting everything else down.
-/
@[simps]
def truncate [has_zero_morphisms V] : chain_complex V ℕ ⥤ chain_complex V ℕ :=
{ obj := λ C,
  { X := λ i, C.X (i+1),
    d := λ i j, C.d (i+1) (j+1),
    shape' := λ i j w, by { apply C.shape, dsimp at w ⊢, omega, }, },
  map := λ C D f,
  { f := λ i, f.f (i+1), }, }

/--
There is a canonical chain map from the truncation of a chain map `C` to
the "single object" chain complex consisting of the truncated object `C.X 0` in degree 0.
The components of this chain map are `C.d 1 0` in degree 0, and zero otherwise.
-/
def truncate_to [has_zero_object V] [has_zero_morphisms V] (C : chain_complex V ℕ) :
  truncate.obj C ⟶ (single_0 V).obj (C.X 0) :=
(to_single_0_equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 1 0, by tidy⟩

-- PROJECT when `V` is abelian (but not generally?)
-- `[∀ n, exact (C.d (n+2) (n+1)) (C.d (n+1) n)] [epi (C.d 1 0)]` iff `quasi_iso (C.truncate_to)`

variables [has_zero_morphisms V]

/--
We can "augment" a chain complex by inserting an arbitrary object in degree zero
(shifting everything else up), along with a suitable differential.
-/
def augment (C : chain_complex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
  chain_complex V ℕ :=
{ X := λ i, match i with
  | 0 := X
  | (i+1) := C.X i
  end,
  d := λ i j, match i, j with
  | 1, 0 := f
  | (i+1), (j+1) := C.d i j
  | _, _ := 0
  end,
  shape' := λ i j s, begin
    simp at s,
    rcases i with _|_|i; cases j; unfold_aux; try { simp },
    { simpa using s, },
    { rw [C.shape], simp, omega, },
  end,
  d_comp_d' := λ i j k, begin
    rcases i with _|_|i; rcases j with _|_|j; cases k; unfold_aux; try { simp },
    cases i,
    { exact w, },
    { rw [C.shape, zero_comp],
      simp, omega, },
  end, }

@[simp] lemma augment_X_zero (C : chain_complex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
  (augment C f w).X 0 = X := rfl

@[simp] lemma augment_X_succ (C : chain_complex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0)
  (i : ℕ) :
  (augment C f w).X (i+1) = C.X i := rfl

@[simp] lemma augment_d_one_zero
  (C : chain_complex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
  (augment C f w).d 1 0 = f := rfl

@[simp] lemma augment_d_succ_succ
  (C : chain_complex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) (i j : ℕ) :
  (augment C f w).d (i+1) (j+1) = C.d i j :=
by { dsimp [augment], rcases i with _|i, refl, refl, }

/--
Truncating an augmented chain complex is isomorphic (with components the identity)
to the original complex.
-/
def truncate_augment (C : chain_complex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) :
  truncate.obj (augment C f w) ≅ C :=
{ hom :=
  { f := λ i, 𝟙 _, },
  inv :=
  { f := λ i, by { cases i; exact 𝟙 _, },
    comm' := λ i j, by { cases i; cases j; { dsimp, simp, }, }, },
  hom_inv_id' := by { ext i, cases i; { dsimp, simp, }, },
  inv_hom_id' := by { ext i, cases i; { dsimp, simp, }, }, }.

@[simp] lemma truncate_augment_hom_f
  (C : chain_complex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) (i : ℕ) :
  (truncate_augment C f w).hom.f i = 𝟙 (C.X i) := rfl
@[simp] lemma truncate_augment_inv_f
  (C : chain_complex V ℕ) {X : V} (f : C.X 0 ⟶ X) (w : C.d 1 0 ≫ f = 0) (i : ℕ) :
  (truncate_augment C f w).inv.f i = 𝟙 ((truncate.obj (augment C f w)).X i) :=
by { cases i; refl, }

@[simp] lemma cochain_complex_d_succ_succ_zero (C : chain_complex V ℕ) (i : ℕ) :
  C.d (i+2) 0 = 0 :=
by { rw C.shape, simp, omega, }

/--
Augmenting a truncated complex with the original object and morphism is isomorphic
(with components the identity) to the original complex.
-/
def augment_truncate (C : chain_complex V ℕ) :
  augment (truncate.obj C) (C.d 1 0) (C.d_comp_d _ _ _) ≅ C :=
{ hom :=
  { f := λ i, by { cases i; exact 𝟙 _, },
    comm' := λ i j, by { rcases i with _|_|i; cases j; { dsimp, simp, }, }, },
  inv :=
  { f := λ i, by { cases i; exact 𝟙 _, },
    comm' := λ i j, by { rcases i with _|_|i; cases j; { dsimp, simp, }, }, },
  hom_inv_id' := by { ext i, cases i; { dsimp, simp, }, },
  inv_hom_id' := by { ext i, cases i; { dsimp, simp, }, }, }.

@[simp] lemma augment_truncate_hom_f_zero (C : chain_complex V ℕ) :
  (augment_truncate C).hom.f 0 = 𝟙 (C.X 0) :=
rfl
@[simp] lemma augment_truncate_hom_f_succ (C : chain_complex V ℕ) (i : ℕ) :
  (augment_truncate C).hom.f (i+1) = 𝟙 (C.X (i+1)) :=
rfl
@[simp] lemma augment_truncate_inv_f_zero (C : chain_complex V ℕ) :
  (augment_truncate C).inv.f 0 = 𝟙 (C.X 0) :=
rfl
@[simp] lemma augment_truncate_inv_f_succ (C : chain_complex V ℕ) (i : ℕ) :
  (augment_truncate C).inv.f (i+1) = 𝟙 (C.X (i+1)) :=
rfl

/--
A chain map from a chain complex to a single object chain complex in degree zero
can be reinterpreted as a chain complex.

Ths is the inverse construction of `truncate_to`.
-/
def to_single_0_as_complex
  [has_zero_object V] (C : chain_complex V ℕ) (X : V) (f : C ⟶ (single_0 V).obj X) :
  chain_complex V ℕ :=
let ⟨f, w⟩ := to_single_0_equiv C X f in augment C f w

end chain_complex
