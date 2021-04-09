import algebra.homology2.homology
import tactic.omega
import tactic.linarith

open category_theory
open category_theory.limits

universes v u

variables (V : Type u) [category.{v} V] [has_zero_morphisms V] [has_zero_object V]

section
variables {ι : Type*} [decidable_eq ι] (c : complex_shape ι)

local attribute [instance] has_zero_object.has_zero

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

@[simp] lemma single_obj_X_self (j : ι) (A : V) : ((single V c j).obj A).X j = A :=
by simp

@[simp] lemma single_map_f_self (j : ι) {A B : V} (f : A ⟶ B) :
  ((single V c j).map f).f j = eq_to_hom (by simp) ≫ f ≫ eq_to_hom (by simp) :=
by { simp, refl, }

end

variables {V}

/--
Morphisms from a `ℕ`-indexed chain complex `C`
to a single object chain complex with `X` concentrated in degree 0
are the same as morphisms `f : C.X 0 ⟶ X` such that `C.d 1 0 ≫ f = 0`.
-/
def to_single_equiv (C : chain_complex V ℕ) (X : V) :
  (C ⟶ (single V _ 0).obj X) ≃ { f : C.X 0 ⟶ X // C.d 1 0 ≫ f = 0 } :=
{ to_fun := λ f, ⟨f.f 0, by { rw ←f.comm 1 0, simp, }⟩,
  inv_fun := λ f,
  { f := λ i, if h : i = 0 then
      eq_to_hom (congr_arg C.X h) ≫ f.1 ≫ eq_to_hom (by { subst h, refl, })
    else
      0,
    comm' := λ i j, begin
      split_ifs with hi hj hj,
      { substs hi hj, simp, },
      { simp, },
      { subst hj,
        simp only [category.comp_id, category.id_comp, single_obj_d, eq_to_hom_refl, zero_comp],
        cases i,
        { simp, },
        { cases i,
          { exact f.2.symm, },
          { rw [C.shape, zero_comp],
            simp only [complex_shape.down_rel],
            omega, } }, },
      { simp, },
    end, },
  left_inv := λ f, begin
    ext i,
    dsimp,
    split_ifs with h,
    { subst h, simp, },
    { refine (zero_of_target_iso_zero _ _).symm,
      rw if_neg h, },
  end,
  right_inv := by tidy, }

/--
The truncation of a `ℕ`-indexed chain complex,
deleting the object at `0` and shifting everything else down.
-/
@[simps]
def truncate : chain_complex V ℕ ⥤ chain_complex V ℕ :=
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
def truncate_to_single (C : chain_complex V ℕ) : truncate.obj C ⟶ (single V _ 0).obj (C.X 0) :=
(to_single_equiv (truncate.obj C) (C.X 0)).symm ⟨C.d 1 0, by tidy⟩

-- TODO: `C` is exact iff `truncate_to_single` is a quasi-isomorphism.

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
