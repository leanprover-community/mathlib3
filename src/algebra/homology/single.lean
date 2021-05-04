/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.homology
import tactic.omega

/-!
# Chain complexes supported in a single degree

We define `single V j c : V ⥤ homological_complex V c`,
which constructs complexes in `V` of shape `c`, supported in degree `j`.

Similarly `single_0 V : V ⥤ chain_complex V ℕ` is the special case for
`ℕ`-indexed chain complexes, with the object supported in degree `0`,
but with better definitional properties.

In `to_single_0_equiv` we characterize chain maps to a `ℕ`-indexed complex concentrated in degree 0;
they are equivalent to `{ f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 }`.
(This is useful translating between a projective resolution and
an augmented exact complex of projectives.)
-/

open category_theory
open category_theory.limits

universes v u

variables (V : Type u) [category.{v} V] [has_zero_morphisms V] [has_zero_object V]

namespace homological_complex
variables {ι : Type*} [decidable_eq ι] (c : complex_shape ι)

local attribute [instance] has_zero_object.has_zero

/--
The functor `V ⥤ homological_complex V c` creating a chain complex supported in a single degree.

See also `chain_complex.single_0 : V ⥤ chain_complex V ℕ`,
which has better definitional properties,
if you are working with `ℕ`-indexed complexes.
-/
@[simps]
def single (j : ι) : V ⥤ homological_complex V c :=
{ obj := λ A,
  { X := λ i, if i = j then A else 0,
    d := λ i j, 0, },
  map := λ A B f,
  { f := λ i, if h : i = j then
      eq_to_hom (by { dsimp, rw if_pos h, }) ≫ f ≫ eq_to_hom (by { dsimp, rw if_pos h, })
    else
      0, },
  map_id' := λ A, begin
    ext,
    dsimp,
    split_ifs with h,
    { subst h, simp, },
    { rw if_neg h, simp, },
  end,
  map_comp' := λ A B C f g, begin
    ext,
    dsimp,
    split_ifs with h,
    { subst h, simp, },
    { simp, },
  end, }.

@[simps]
def single_obj_X_self (j : ι) (A : V) : ((single V c j).obj A).X j ≅ A :=
eq_to_iso (by simp)

@[simp]
lemma single_map_f_self (j : ι) {A B : V} (f : A ⟶ B) :
  ((single V c j).map f).f j =
    (single_obj_X_self V c j A).hom ≫ f ≫ (single_obj_X_self V c j B).inv :=
by { simp, refl, }

end homological_complex

open homological_complex

namespace chain_complex

local attribute [instance] has_zero_object.has_zero

/--
`chain_complex.single_0 V` is the embedding of `V` into `chain_complex V ℕ`
as chain complexes supported in degree 0.

This is naturally isomorphism to `single V _ 0`, but has better definitional properties.
-/
def single_0 : V ⥤ chain_complex V ℕ :=
{ obj := λ X,
  { X := λ n, match n with
    | 0 := X
    | (n+1) := 0
    end,
    d := λ i j, 0, },
  map := λ X Y f,
  { f := λ n, match n with
    | 0 := f
    | (n+1) := 0
    end, },
  map_id' := λ X, by { ext n, cases n, refl, dsimp, unfold_aux, simp, },
  map_comp' := λ X Y Z f g, by { ext n, cases n, refl, dsimp, unfold_aux, simp, } }

@[simp] lemma single_0_obj_X_0 (X : V) : ((single_0 V).obj X).X 0 = X := rfl
@[simp] lemma single_0_obj_X_succ (X : V) (n : ℕ) : ((single_0 V).obj X).X (n+1) = 0 := rfl
@[simp] lemma single_0_obj_X_d (X : V) (i j : ℕ) : ((single_0 V).obj X).d i j = 0 := rfl
@[simp] lemma single_0_obj_X_d_to (X : V) (j : ℕ) : ((single_0 V).obj X).d_to j = 0 :=
by { rw [d_to_eq ((single_0 V).obj X) rfl], simp, }
@[simp] lemma single_0_obj_X_d_from (X : V) (i : ℕ) : ((single_0 V).obj X).d_from i = 0 :=
begin
  cases i,
  { rw [d_from_eq_zero], simp, },
  { rw [d_from_eq ((single_0 V).obj X) rfl], simp, },
end
@[simp] lemma single_0_map_f_0 {X Y : V} (f : X ⟶ Y) : ((single_0 V).map f).f 0 = f := rfl
@[simp] lemma single_0_map_f_succ {X Y : V} (f : X ⟶ Y) (n : ℕ) :
  ((single_0 V).map f).f (n+1) = 0 := rfl

section
variables [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

/--
Sending objects to chain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable
def homology_functor_0_single_0 : single_0 V ⋙ homology_functor V _ 0 ≅ (𝟭 V) :=
nat_iso.of_components (λ X, homology.congr _ _ (by simp) (by simp) ≪≫ homology_zero_zero)
  (λ X Y f, by { ext, dsimp [homology_functor], simp, })

/--
Sending objects to chain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable
def homology_functor_succ_single_0 (n : ℕ) : single_0 V ⋙ homology_functor V _ (n+1) ≅ 0 :=
nat_iso.of_components (λ X, homology.congr _ _ (by simp) (by simp) ≪≫ homology_zero_zero)
  (λ X Y f, by ext)

end

variables {V}

/--
Morphisms from a `ℕ`-indexed chain complex `C`
to a single object chain complex with `X` concentrated in degree 0
are the same as morphisms `f : C.X 0 ⟶ X` such that `C.d 1 0 ≫ f = 0`.
-/
def to_single_0_equiv (C : chain_complex V ℕ) (X : V) :
  (C ⟶ (single_0 V).obj X) ≃ { f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 } :=
{ to_fun := λ f, ⟨f.f 0, by { rw ←f.comm 1 0, simp, }⟩,
  inv_fun := λ f,
  { f := λ i, match i with
    | 0 := f.1
    | (n+1) := 0
    end,
    comm' := λ i j, begin
      rcases i with _|_|i; cases j; unfold_aux; simp only [comp_zero, zero_comp, single_0_obj_X_d],
      { rw [C.shape, zero_comp], simp, },
      { exact f.2.symm, },
      { rw [C.shape, zero_comp], simp only [complex_shape.down_rel, zero_add], omega, },
    end, },
  left_inv := λ f, begin
    ext i,
    rcases i,
    { refl, },
    { ext, },
  end,
  right_inv := by tidy, }

end chain_complex
