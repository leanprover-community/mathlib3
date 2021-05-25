/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.homology

/-!
# Chain complexes supported in a single degree

We define `single V j c : V ⥤ homological_complex V c`,
which constructs complexes in `V` of shape `c`, supported in degree `j`.

Similarly `single₀ V : V ⥤ chain_complex V ℕ` is the special case for
`ℕ`-indexed chain complexes, with the object supported in degree `0`,
but with better definitional properties.

In `to_single₀_equiv` we characterize chain maps to a `ℕ`-indexed complex concentrated in degree 0;
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

See also `chain_complex.single₀ : V ⥤ chain_complex V ℕ`,
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

/--
The object in degree `j` of `(single V c h).obj A` is just `A`.
-/
@[simps]
def single_obj_X_self (j : ι) (A : V) : ((single V c j).obj A).X j ≅ A :=
eq_to_iso (by simp)

@[simp]
lemma single_map_f_self (j : ι) {A B : V} (f : A ⟶ B) :
  ((single V c j).map f).f j =
    (single_obj_X_self V c j A).hom ≫ f ≫ (single_obj_X_self V c j B).inv :=
by { simp, refl, }

instance (j : ι) : faithful (single V c j) :=
{ map_injective' := λ X Y f g w, begin
    have := congr_hom w j,
    dsimp at this,
    simp only [dif_pos] at this,
    rw [←is_iso.inv_comp_eq, inv_eq_to_hom, eq_to_hom_trans_assoc, eq_to_hom_refl, category.id_comp,
      ←is_iso.comp_inv_eq, category.assoc, inv_eq_to_hom, eq_to_hom_trans, eq_to_hom_refl,
      category.comp_id] at this,
    exact this,
  end, }

instance (j : ι) : full (single V c j) :=
{ preimage := λ X Y f, eq_to_hom (by simp) ≫ f.f j ≫ eq_to_hom (by simp),
  witness' := λ X Y f, begin
    ext i,
    dsimp,
    split_ifs,
    { subst h, simp, },
    { symmetry,
      apply zero_of_target_iso_zero,
      dsimp,
      rw [if_neg h], },
  end }

end homological_complex

open homological_complex

namespace chain_complex

local attribute [instance] has_zero_object.has_zero

/--
`chain_complex.single₀ V` is the embedding of `V` into `chain_complex V ℕ`
as chain complexes supported in degree 0.

This is naturally isomorphic to `single V _ 0`, but has better definitional properties.
-/
def single₀ : V ⥤ chain_complex V ℕ :=
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

@[simp] lemma single₀_obj_X_0 (X : V) : ((single₀ V).obj X).X 0 = X := rfl
@[simp] lemma single₀_obj_X_succ (X : V) (n : ℕ) : ((single₀ V).obj X).X (n+1) = 0 := rfl
@[simp] lemma single₀_obj_X_d (X : V) (i j : ℕ) : ((single₀ V).obj X).d i j = 0 := rfl
@[simp] lemma single₀_obj_X_d_to (X : V) (j : ℕ) : ((single₀ V).obj X).d_to j = 0 :=
by { rw [d_to_eq ((single₀ V).obj X) rfl], simp, }
@[simp] lemma single₀_obj_X_d_from (X : V) (i : ℕ) : ((single₀ V).obj X).d_from i = 0 :=
begin
  cases i,
  { rw [d_from_eq_zero], simp, },
  { rw [d_from_eq ((single₀ V).obj X) rfl], simp, },
end
@[simp] lemma single₀_map_f_0 {X Y : V} (f : X ⟶ Y) : ((single₀ V).map f).f 0 = f := rfl
@[simp] lemma single₀_map_f_succ {X Y : V} (f : X ⟶ Y) (n : ℕ) :
  ((single₀ V).map f).f (n+1) = 0 := rfl

section
variables [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

/--
Sending objects to chain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable
def homology_functor_0_single₀ : single₀ V ⋙ homology_functor V _ 0 ≅ (𝟭 V) :=
nat_iso.of_components (λ X, homology.congr _ _ (by simp) (by simp) ≪≫ homology_zero_zero)
  (λ X Y f, by { ext, dsimp [homology_functor], simp, })

/--
Sending objects to chain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable
def homology_functor_succ_single₀ (n : ℕ) : single₀ V ⋙ homology_functor V _ (n+1) ≅ 0 :=
nat_iso.of_components (λ X, homology.congr _ _ (by simp) (by simp) ≪≫ homology_zero_zero)
  (λ X Y f, by ext)

end

variables {V}

/--
Morphisms from a `ℕ`-indexed chain complex `C`
to a single object chain complex with `X` concentrated in degree 0
are the same as morphisms `f : C.X 0 ⟶ X` such that `C.d 1 0 ≫ f = 0`.
-/
def to_single₀_equiv (C : chain_complex V ℕ) (X : V) :
  (C ⟶ (single₀ V).obj X) ≃ { f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 } :=
{ to_fun := λ f, ⟨f.f 0, by { rw ←f.comm 1 0, simp, }⟩,
  inv_fun := λ f,
  { f := λ i, match i with
    | 0 := f.1
    | (n+1) := 0
    end,
    comm' := λ i j h, begin
      rcases i with _|_|i; cases j; unfold_aux; simp only [comp_zero, zero_comp, single₀_obj_X_d],
      { rw [C.shape, zero_comp], simp, },
      { exact f.2.symm, },
      { rw [C.shape, zero_comp], simp [i.succ_succ_ne_one.symm] },
    end, },
  left_inv := λ f, begin
    ext i,
    rcases i,
    { refl, },
    { ext, },
  end,
  right_inv := by tidy, }

variables (V)

/-- `single₀` is the same as `single V _ 0`. -/
def single₀_iso_single : single₀ V ≅ single V _ 0 :=
nat_iso.of_components
  (λ X,
  { hom := { f := λ i, by { cases i; simpa using 𝟙 _, } },
    inv := { f := λ i, by { cases i; simpa using 𝟙 _, } },
    hom_inv_id' := by { ext (_|i); { dsimp, simp, }, },
    inv_hom_id' := begin
      ext (_|i),
      { apply category.id_comp, },
      { apply has_zero_object.to_zero_ext, },
    end, })
  (λ X Y f, by { ext (_|i); { dsimp, simp, }, })

instance : faithful (single₀ V) := faithful.of_iso (single₀_iso_single V).symm
instance : full (single₀ V) := full.of_iso (single₀_iso_single V).symm

end chain_complex

namespace cochain_complex

local attribute [instance] has_zero_object.has_zero

/--
`cochain_complex.single₀ V` is the embedding of `V` into `cochain_complex V ℕ`
as cochain complexes supported in degree 0.

This is naturally isomorphic to `single V _ 0`, but has better definitional properties.
-/
def single₀ : V ⥤ cochain_complex V ℕ :=
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

@[simp] lemma single₀_obj_X_0 (X : V) : ((single₀ V).obj X).X 0 = X := rfl
@[simp] lemma single₀_obj_X_succ (X : V) (n : ℕ) : ((single₀ V).obj X).X (n+1) = 0 := rfl
@[simp] lemma single₀_obj_X_d (X : V) (i j : ℕ) : ((single₀ V).obj X).d i j = 0 := rfl
@[simp] lemma single₀_obj_X_d_from (X : V) (j : ℕ) : ((single₀ V).obj X).d_from j = 0 :=
by { rw [d_from_eq ((single₀ V).obj X) rfl], simp, }
@[simp] lemma single₀_obj_X_d_to (X : V) (i : ℕ) : ((single₀ V).obj X).d_to i = 0 :=
begin
  cases i,
  { rw [d_to_eq_zero], simp, },
  { rw [d_to_eq ((single₀ V).obj X) rfl], simp, },
end
@[simp] lemma single₀_map_f_0 {X Y : V} (f : X ⟶ Y) : ((single₀ V).map f).f 0 = f := rfl
@[simp] lemma single₀_map_f_succ {X Y : V} (f : X ⟶ Y) (n : ℕ) :
  ((single₀ V).map f).f (n+1) = 0 := rfl

section
variables [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

/--
Sending objects to cochain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable
def homology_functor_0_single₀ : single₀ V ⋙ homology_functor V _ 0 ≅ (𝟭 V) :=
nat_iso.of_components (λ X, homology.congr _ _ (by simp) (by simp) ≪≫ homology_zero_zero)
  (λ X Y f, by { ext, dsimp [homology_functor], simp, })

/--
Sending objects to cochain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable
def homology_functor_succ_single₀ (n : ℕ) : single₀ V ⋙ homology_functor V _ (n+1) ≅ 0 :=
nat_iso.of_components (λ X, homology.congr _ _ (by simp) (by simp) ≪≫ homology_zero_zero)
  (λ X Y f, by ext)

end

variables {V}

/--
Morphisms from a single object cochain complex with `X` concentrated in degree 0
to a `ℕ`-indexed cochain complex `C`
are the same as morphisms `f : X ⟶ C.X 0` such that `f ≫ C.d 0 1 = 0`.
-/
def from_single₀_equiv (C : cochain_complex V ℕ) (X : V) :
  ((single₀ V).obj X ⟶ C) ≃ { f : X ⟶ C.X 0 // f ≫ C.d 0 1 = 0 } :=
{ to_fun := λ f, ⟨f.f 0, by { rw f.comm 0 1, simp, }⟩,
  inv_fun := λ f,
  { f := λ i, match i with
    | 0 := f.1
    | (n+1) := 0
    end,
    comm' := λ i j h, begin
      rcases j with _|_|j; cases i; unfold_aux; simp only [comp_zero, zero_comp, single₀_obj_X_d],
      { convert comp_zero, rw [C.shape], simp, },
      { exact f.2, },
      { convert comp_zero, rw [C.shape], simp only [complex_shape.up_rel, zero_add],
        exact (nat.one_lt_succ_succ j).ne },
    end, },
  left_inv := λ f, begin
    ext i,
    rcases i,
    { refl, },
    { ext, },
  end,
  right_inv := by tidy, }

variables (V)

/-- `single₀` is the same as `single V _ 0`. -/
def single₀_iso_single : single₀ V ≅ single V _ 0 :=
nat_iso.of_components
  (λ X,
  { hom := { f := λ i, by { cases i; simpa using 𝟙 _, } },
    inv := { f := λ i, by { cases i; simpa using 𝟙 _, } },
    hom_inv_id' := by { ext (_|i); { dsimp, simp, }, },
    inv_hom_id' := begin
      ext (_|i),
      { apply category.id_comp, },
      { apply has_zero_object.to_zero_ext, },
    end, })
  (λ X Y f, by { ext (_|i); { dsimp, simp, }, })

instance : faithful (single₀ V) := faithful.of_iso (single₀_iso_single V).symm
instance : full (single₀ V) := full.of_iso (single₀_iso_single V).symm

end cochain_complex
