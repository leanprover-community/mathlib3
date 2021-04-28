/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebra.homology.complex_shape
import category_theory.subobject.limits

/-!
# Homological complexes.

A `homological_complex V c` with a "shape" controlled by `c : complex_shape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape'` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.

We provide `chain_complex V α` for
`α`-indexed chain complexes in which `d i j ≠ 0` only if `j + 1 = i`,
and similarly `cochain_complex V α`, with `i = j + 1`.

There is a category structure, where morphisms are chain maps.

For `C : homological_complex V c`, we define `C.X_next i`, which is either `C.X j` for some
arbitrarily chosen `j` such that `c.r i j`, or the zero object if there is no such `j`.
Similarly we have `C.X_prev j`.
Defined in terms of these we have `C.d_from i : C.X i ⟶ C.X_next i` and
`C.d_to j : C.X_prev j ⟶ C.X j`, which are either defined in as `C.d i j`, or zero, as needed.
-/

universes v u

open category_theory category_theory.limits

variables {ι : Type*}
variables (V : Type u) [category.{v} V] [has_zero_morphisms V]

/--
A `homological_complex V c` with a "shape" controlled by `c : complex_shape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape'` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.
-/
structure homological_complex (c : complex_shape ι) :=
(X : ι → V)
(d : Π i j, X i ⟶ X j)
(shape' : ∀ i j, ¬ c.rel i j → d i j = 0 . obviously)
(d_comp_d' : ∀ i j k, d i j ≫ d j k = 0 . obviously)

restate_axiom homological_complex.shape'
restate_axiom homological_complex.d_comp_d'

attribute [simp] homological_complex.shape
attribute [simp, reassoc] homological_complex.d_comp_d

/--
An `α`-indexed chain complex is a `homological_complex`
in which `d i j ≠ 0` only if `j + 1 = i`.
-/
abbreviation chain_complex (α : Type*) [add_right_cancel_semigroup α] [has_one α] :=
homological_complex V (complex_shape.down α)

/--
An `α`-indexed cochain complex is a `homological_complex`
in which `d i j ≠ 0` only if `i + 1 = j`.
-/
abbreviation cochain_complex (α : Type*) [add_right_cancel_semigroup α] [has_one α] :=
homological_complex V (complex_shape.up α)

namespace homological_complex
variables {V} {c : complex_shape ι} (C : homological_complex V c)

local attribute [instance] has_zero_object.has_zero

instance [has_zero_object V] : inhabited (homological_complex V c) :=
⟨{ X := λ i, 0,
  d := λ i j, 0, }⟩

/--
A morphism of homological complexes consists of maps between the chain groups,
commuting with the differentials.
-/
@[ext] structure hom (A B : homological_complex V c) :=
(f : ∀ i, A.X i ⟶ B.X i)
(comm' : ∀ i j, f i ≫ B.d i j = A.d i j ≫ f j . obviously)

restate_axiom hom.comm'
attribute [simp, reassoc, elementwise] hom.comm

instance (A B : homological_complex V c) : inhabited (hom A B) :=
⟨{ f := λ i, 0, }⟩

/-- Identity chain map. -/
def id (A : homological_complex V c) : hom A A :=
{ f := λ _, 𝟙 _ }

/-- Composition of chain maps. -/
def comp (A B C : homological_complex V c) (φ : hom A B) (ψ : hom B C) : hom A C :=
{ f := λ i, φ.f i ≫ ψ.f i }

section
local attribute [simp] id comp

instance : category (homological_complex V c) :=
{ hom := hom,
  id := id,
  comp := comp, }

end

@[simp] lemma id_f (C : homological_complex V c) (i : ι) : hom.f (𝟙 C) i = 𝟙 (C.X i) := rfl
@[simp] lemma comp_f {C₁ C₂ C₃ : homological_complex V c} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
  (f ≫ g).f i = f.f i ≫ g.f i :=
rfl

-- We'll use this later to show that `homological_complex V c` is preadditive when `V` is.
lemma hom_f_injective {C₁ C₂ : homological_complex V c} :
  function.injective (λ f : hom C₁ C₂, hom.f f) :=
by tidy

instance : has_zero_morphisms (homological_complex V c) :=
{ has_zero := λ C D, ⟨{ f := λ i, 0, }⟩ }

@[simp] lemma zero_apply (C D : homological_complex V c) (i : ι) :
  (0 : C ⟶ D).f i = 0 := rfl

lemma congr_hom {C D : homological_complex V c} {f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i :=
congr_fun (congr_arg hom.f w) i

/--
Picking out the `i`-th object, as a functor.
-/
def eval_at (i : ι) : homological_complex V c ⥤ V :=
{ obj := λ C, C.X i,
  map := λ C D f, f.f i, }

open_locale classical
noncomputable theory

/--
If `C.d i j` and `C.d i j'` are both allowed, then we must have `j = j'`,
and so the differentials only differ by an `eq_to_hom`.
-/
lemma d_comp_eq_to_hom {i j j' : ι} (rij : c.rel i j) (rij' : c.rel i j') :
  C.d i j' ≫ eq_to_hom (congr_arg C.X (c.next_eq rij' rij)) = C.d i j :=
begin
  have P : ∀ h : j' = j, C.d i j' ≫ eq_to_hom (congr_arg C.X h) = C.d i j,
  { rintro rfl, simp, },
  apply P,
end

/--
If `C.d i j` and `C.d i' j` are both allowed, then we must have `i = i'`,
and so the differentials only differ by an `eq_to_hom`.
-/
lemma eq_to_hom_comp_d {i i' j : ι} (rij : c.rel i j) (rij' : c.rel i' j) :
  eq_to_hom (congr_arg C.X (c.prev_eq rij rij')) ≫ C.d i' j = C.d i j :=
begin
  have P : ∀ h : i = i', eq_to_hom (congr_arg C.X h) ≫ C.d i' j = C.d i j,
  { rintro rfl, simp, },
  apply P,
end

lemma kernel_eq_kernel [has_kernels V] {i j j' : ι} (r : c.rel i j) (r' : c.rel i j') :
  kernel_subobject (C.d i j) = kernel_subobject (C.d i j') :=
begin
  rw ←d_comp_eq_to_hom C r r',
  apply kernel_subobject_comp_mono,
end

lemma image_eq_image [has_images V] [has_equalizers V]
  {i i' j : ι} (r : c.rel i j) (r' : c.rel i' j) :
  image_subobject (C.d i j) = image_subobject (C.d i' j) :=
begin
  rw ←eq_to_hom_comp_d C r r',
  apply image_subobject_iso_comp,
end

section

variables [has_zero_object V]
local attribute [instance] has_zero_object.has_zero

/-- Either `C.X i`, if there is some `i` with `c.rel i j`, or the zero object. -/
def X_prev (j : ι) : V :=
match c.prev j with
| none := 0
| (some ⟨i,_⟩) := C.X i
end

/-- If `c.rel i j`, then `C.X_prev j` is isomorphic to `C.X i`. -/
def X_prev_iso {i j : ι} (r : c.rel i j) :
  C.X_prev j ≅ C.X i :=
begin
  apply eq_to_iso,
  dsimp [X_prev],
  rw c.prev_eq_some r,
  refl,
end

/-- If there is no `i` so `c.rel i j`, then `C.X_prev j` is isomorphic to `0`. -/
def X_prev_iso_zero {j : ι} (h : c.prev j = none) :
  C.X_prev j ≅ 0 :=
begin
  apply eq_to_iso,
  dsimp [X_prev],
  rw h,
  refl,
end

/-- Either `C.X j`, if there is some `j` with `c.rel i j`, or the zero object. -/
def X_next (i : ι) : V :=
match c.next i with
| none := 0
| (some ⟨j,_⟩) := C.X j
end

/-- If `c.rel i j`, then `C.X_next i` is isomorphic to `C.X j`. -/
def X_next_iso {i j : ι} (r : c.rel i j) :
  C.X_next i ≅ C.X j :=
begin
  apply eq_to_iso,
  dsimp [X_next],
  rw c.next_eq_some r,
  refl,
end

/-- If there is no `j` so `c.rel i j`, then `C.X_next i` is isomorphic to `0`. -/
def X_next_iso_zero {i : ι} (h : c.next i = none) :
  C.X_next i ≅ 0 :=
begin
  apply eq_to_iso,
  dsimp [X_next],
  rw h,
  refl,
end

/--
The differential mapping into `C.X j`, or zero if there isn't one.
-/
def d_to (j : ι) : C.X_prev j ⟶ C.X j :=
match c.prev j with
| none := (0 : C.X_prev j ⟶ C.X j)
| (some ⟨i, w⟩) := (C.X_prev_iso w).hom ≫ C.d i j
end

/--
The differential mapping out of `C.X i`, or zero if there isn't one.
-/
def d_from (i : ι) : C.X i ⟶ C.X_next i :=
match c.next i with
| none := (0 : C.X i ⟶ C.X_next i)
| (some ⟨j, w⟩) := C.d i j ≫ (C.X_next_iso w).inv
end

lemma d_to_eq {i j : ι} (r : c.rel i j) :
  C.d_to j = (C.X_prev_iso r).hom ≫ C.d i j :=
begin
  dsimp [d_to, X_prev_iso],
  rw c.prev_eq_some r,
  refl,
end

@[simp]
lemma d_to_eq_zero {j : ι} (h : c.prev j = none) :
  C.d_to j = 0 :=
begin
  dsimp [d_to],
  rw h, refl,
end

lemma d_from_eq {i j : ι} (r : c.rel i j) :
  C.d_from i = C.d i j ≫ (C.X_next_iso r).inv :=
begin
  dsimp [d_from, X_next_iso],
  rw c.next_eq_some r,
  refl,
end

@[simp]
lemma d_from_eq_zero {i : ι} (h : c.next i = none) :
  C.d_from i = 0 :=
begin
  dsimp [d_from],
  rw h, refl,
end

@[simp]
lemma d_to_comp_d_from (j : ι) : C.d_to j ≫ C.d_from j = 0 :=
begin
  rcases h₁ : c.next j with _ | ⟨k,w₁⟩,
  { rw [d_from_eq_zero _ h₁], simp, },
  { rw [d_from_eq _ w₁],
    rcases h₂ : c.prev j with _ | ⟨i,w₂⟩,
    { rw [d_to_eq_zero _ h₂], simp, },
    { rw [d_to_eq _ w₂], simp, } }
end

lemma kernel_from_eq_kernel [has_kernels V] {i j : ι} (r : c.rel i j) :
  kernel_subobject (C.d_from i) = kernel_subobject (C.d i j) :=
begin
  rw C.d_from_eq r,
  apply kernel_subobject_comp_mono,
end

lemma image_to_eq_image [has_images V] [has_equalizers V]
  {i j : ι} (r : c.rel i j) :
  image_subobject (C.d_to j) = image_subobject (C.d i j) :=
begin
  rw C.d_to_eq r,
  apply image_subobject_iso_comp,
end

end

namespace hom

variables {C₁ C₂ : homological_complex V c}
variables [has_zero_object V]
local attribute [instance] has_zero_object.has_zero

/-! Lemmas relating chain maps and `d_to`/`d_from`. -/

/-- `f.f_prev j` is `f.f i` if there is some `r i j`, and zero otherwise. -/
def f_prev (f : hom C₁ C₂) (j : ι) : C₁.X_prev j ⟶ C₂.X_prev j :=
match c.prev j with
| none := 0
| some ⟨i,w⟩ := (C₁.X_prev_iso w).hom ≫ f.f i ≫ (C₂.X_prev_iso w).inv
end

lemma f_prev_eq (f : hom C₁ C₂) {i j : ι} (w : c.rel i j) :
  f.f_prev j = (C₁.X_prev_iso w).hom ≫ f.f i ≫ (C₂.X_prev_iso w).inv :=
begin
  dsimp [f_prev],
  rw c.prev_eq_some w,
  refl,
end

/-- `f.f_next i` is `f.f j` if there is some `r i j`, and zero otherwise. -/
def f_next (f : hom C₁ C₂) (i : ι) : C₁.X_next i ⟶ C₂.X_next i :=
match c.next i with
| none := 0
| some ⟨j,w⟩ := (C₁.X_next_iso w).hom ≫ f.f j ≫ (C₂.X_next_iso w).inv
end

lemma f_next_eq (f : hom C₁ C₂) {i j : ι} (w : c.rel i j) :
  f.f_next i = (C₁.X_next_iso w).hom ≫ f.f j ≫ (C₂.X_next_iso w).inv :=
begin
  dsimp [f_next],
  rw c.next_eq_some w,
  refl,
end

@[simp, reassoc, elementwise]
lemma comm_from (f : hom C₁ C₂) (i : ι) :
  f.f i ≫ C₂.d_from i = C₁.d_from i ≫ f.f_next i :=
begin
  rcases h : c.next i with _ | ⟨j,w⟩,
  { simp [h], },
  { simp [d_from_eq _ w, f_next_eq _ w], }
end

@[simp, reassoc, elementwise]
lemma comm_to (f : hom C₁ C₂) (j : ι) :
  f.f_prev j ≫ C₂.d_to j = C₁.d_to j ≫ f.f j :=
begin
  rcases h : c.prev j with _ | ⟨j,w⟩,
  { simp [h], },
  { simp [d_to_eq _ w, f_prev_eq _ w], }
end

/--
A morphism of chain complexes
induces a morphism of arrows of the differentials into each object.
-/
def sq_to (f : hom C₁ C₂) (j : ι) : arrow.mk (C₁.d_to j) ⟶ arrow.mk (C₂.d_to j) :=
arrow.hom_mk (f.comm_to j)

@[simp] lemma sq_to_right (f : hom C₁ C₂) (j : ι) : (f.sq_to j).right = f.f j := rfl

end hom

end homological_complex
