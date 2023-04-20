/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebra.homology.complex_shape
import category_theory.subobject.limits
import category_theory.graded_object

/-!
# Homological complexes.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
arbitrarily chosen `j` such that `c.r i j`, or `C.X i` if there is no such `j`.
Similarly we have `C.X_prev j`.
Defined in terms of these we have `C.d_from i : C.X i ⟶ C.X_next i` and
`C.d_to j : C.X_prev j ⟶ C.X j`, which are either defined as `C.d i j`, or zero, as needed.
-/

universes v u

open category_theory category_theory.category category_theory.limits

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
(d_comp_d' : ∀ i j k, c.rel i j → c.rel j k → d i j ≫ d j k = 0 . obviously)

namespace homological_complex

restate_axiom shape'
attribute [simp] shape

variables {V} {c : complex_shape ι}

@[simp, reassoc] lemma d_comp_d (C : homological_complex V c) (i j k : ι) :
  C.d i j ≫ C.d j k = 0 :=
begin
  by_cases hij : c.rel i j,
  { by_cases hjk : c.rel j k,
    { exact C.d_comp_d' i j k hij hjk },
    { rw [C.shape j k hjk, comp_zero] } },
  { rw [C.shape i j hij, zero_comp] }
end

lemma ext {C₁ C₂ : homological_complex V c} (h_X : C₁.X = C₂.X)
  (h_d : ∀ (i j : ι), c.rel i j → C₁.d i j ≫ eq_to_hom (congr_fun h_X j) =
    eq_to_hom (congr_fun h_X i) ≫ C₂.d i j) : C₁ = C₂ :=
begin
  cases C₁,
  cases C₂,
  dsimp at h_X,
  subst h_X,
  simp only [true_and, eq_self_iff_true, heq_iff_eq],
  ext i j,
  by_cases hij : c.rel i j,
  { simpa only [id_comp, eq_to_hom_refl, comp_id] using h_d i j hij, },
  { rw [C₁_shape' i j hij, C₂_shape' i j hij], }
end

end homological_complex

/--
An `α`-indexed chain complex is a `homological_complex`
in which `d i j ≠ 0` only if `j + 1 = i`.
-/
abbreviation chain_complex (α : Type*) [add_right_cancel_semigroup α] [has_one α] : Type* :=
homological_complex V (complex_shape.down α)

/--
An `α`-indexed cochain complex is a `homological_complex`
in which `d i j ≠ 0` only if `i + 1 = j`.
-/
abbreviation cochain_complex (α : Type*) [add_right_cancel_semigroup α] [has_one α] : Type* :=
homological_complex V (complex_shape.up α)

namespace chain_complex

@[simp] lemma prev (α : Type*) [add_right_cancel_semigroup α] [has_one α] (i : α) :
  (complex_shape.down α).prev i = i+1 :=
(complex_shape.down α).prev_eq' rfl

@[simp] lemma next (α : Type*) [add_group α] [has_one α] (i : α) :
  (complex_shape.down α).next i = i-1 :=
(complex_shape.down α).next_eq' $ sub_add_cancel _ _

@[simp] lemma next_nat_zero :
  (complex_shape.down ℕ).next 0 = 0 :=
by { classical, refine dif_neg _, push_neg, intro, apply nat.no_confusion }

@[simp] lemma next_nat_succ (i : ℕ) :
  (complex_shape.down ℕ).next (i+1) = i :=
(complex_shape.down ℕ).next_eq' rfl

end chain_complex

namespace cochain_complex

@[simp] lemma prev (α : Type*) [add_group α] [has_one α] (i : α) :
  (complex_shape.up α).prev i = i-1 :=
(complex_shape.up α).prev_eq' $ sub_add_cancel _ _

@[simp] lemma next (α : Type*) [add_right_cancel_semigroup α] [has_one α] (i : α) :
  (complex_shape.up α).next i = i+1 :=
(complex_shape.up α).next_eq' rfl

@[simp] lemma prev_nat_zero :
  (complex_shape.up ℕ).prev 0 = 0 :=
by { classical, refine dif_neg _, push_neg, intro, apply nat.no_confusion }

@[simp] lemma prev_nat_succ (i : ℕ) :
  (complex_shape.up ℕ).prev (i+1) = i :=
(complex_shape.up ℕ).prev_eq' rfl

end cochain_complex

namespace homological_complex
variables {V} {c : complex_shape ι} (C : homological_complex V c)

/--
A morphism of homological complexes consists of maps between the chain groups,
commuting with the differentials.
-/
@[ext] structure hom (A B : homological_complex V c) :=
(f : ∀ i, A.X i ⟶ B.X i)
(comm' : ∀ i j, c.rel i j → f i ≫ B.d i j = A.d i j ≫ f j . obviously)

@[simp, reassoc]
lemma hom.comm {A B : homological_complex V c} (f : A.hom B) (i j : ι) :
  f.f i ≫ B.d i j = A.d i j ≫ f.f j :=
begin
  by_cases hij : c.rel i j,
  { exact f.comm' i j hij },
  rw [A.shape i j hij, B.shape i j hij, comp_zero, zero_comp],
end

instance (A B : homological_complex V c) : inhabited (hom A B) :=
⟨{ f := λ i, 0 }⟩

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
  comp := comp }

end

@[simp] lemma id_f (C : homological_complex V c) (i : ι) : hom.f (𝟙 C) i = 𝟙 (C.X i) := rfl
@[simp] lemma comp_f {C₁ C₂ C₃ : homological_complex V c} (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
  (f ≫ g).f i = f.f i ≫ g.f i :=
rfl

@[simp]
lemma eq_to_hom_f {C₁ C₂ : homological_complex V c} (h : C₁ = C₂) (n : ι) :
  homological_complex.hom.f (eq_to_hom h) n =
  eq_to_hom (congr_fun (congr_arg homological_complex.X h) n) :=
by { subst h, refl, }

-- We'll use this later to show that `homological_complex V c` is preadditive when `V` is.
lemma hom_f_injective {C₁ C₂ : homological_complex V c} :
  function.injective (λ f : hom C₁ C₂, f.f) :=
by tidy

instance : has_zero_morphisms (homological_complex V c) :=
{ has_zero := λ C D, ⟨{ f := λ i, 0 }⟩ }

@[simp] lemma zero_apply (C D : homological_complex V c) (i : ι) :
  (0 : C ⟶ D).f i = 0 := rfl

open_locale zero_object

/-- The zero complex -/
noncomputable def zero [has_zero_object V] : homological_complex V c :=
{ X := λ i, 0, d := λ i j, 0 }

lemma is_zero_zero [has_zero_object V] : is_zero (zero : homological_complex V c) :=
by { refine ⟨λ X, ⟨⟨⟨0⟩, λ f, _⟩⟩, λ X, ⟨⟨⟨0⟩, λ f, _⟩⟩⟩; ext, }

instance [has_zero_object V] : has_zero_object (homological_complex V c) :=
⟨⟨zero, is_zero_zero⟩⟩

noncomputable
instance [has_zero_object V] : inhabited (homological_complex V c) := ⟨zero⟩

lemma congr_hom {C D : homological_complex V c} {f g : C ⟶ D} (w : f = g) (i : ι) : f.f i = g.f i :=
congr_fun (congr_arg hom.f w) i

section
variables (V c)

/-- The functor picking out the `i`-th object of a complex. -/
@[simps] def eval (i : ι) : homological_complex V c ⥤ V :=
{ obj := λ C, C.X i,
  map := λ C D f, f.f i, }

/-- The functor forgetting the differential in a complex, obtaining a graded object. -/
@[simps] def forget : homological_complex V c ⥤ graded_object ι V :=
{ obj := λ C, C.X,
  map := λ _ _ f, f.f }

/-- Forgetting the differentials than picking out the `i`-th object is the same as
just picking out the `i`-th object. -/
@[simps] def forget_eval (i : ι) : forget V c ⋙ graded_object.eval i ≅ eval V c i :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

end

open_locale classical
noncomputable theory

/--
If `C.d i j` and `C.d i j'` are both allowed, then we must have `j = j'`,
and so the differentials only differ by an `eq_to_hom`.
-/
@[simp] lemma d_comp_eq_to_hom {i j j' : ι} (rij : c.rel i j) (rij' : c.rel i j') :
  C.d i j' ≫ eq_to_hom (congr_arg C.X (c.next_eq rij' rij)) = C.d i j :=
begin
  have P : ∀ h : j' = j, C.d i j' ≫ eq_to_hom (congr_arg C.X h) = C.d i j,
  { rintro rfl, simp },
  apply P,
end

/--
If `C.d i j` and `C.d i' j` are both allowed, then we must have `i = i'`,
and so the differentials only differ by an `eq_to_hom`.
-/
@[simp] lemma eq_to_hom_comp_d {i i' j : ι} (rij : c.rel i j) (rij' : c.rel i' j) :
  eq_to_hom (congr_arg C.X (c.prev_eq rij rij')) ≫ C.d i' j = C.d i j :=
begin
  have P : ∀ h : i = i', eq_to_hom (congr_arg C.X h) ≫ C.d i' j = C.d i j,
  { rintro rfl, simp },
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

/-- Either `C.X i`, if there is some `i` with `c.rel i j`, or `C.X j`. -/
abbreviation X_prev (j : ι) : V := C.X (c.prev j)

/-- If `c.rel i j`, then `C.X_prev j` is isomorphic to `C.X i`. -/
def X_prev_iso {i j : ι} (r : c.rel i j) :
  C.X_prev j ≅ C.X i :=
eq_to_iso $ by rw ← c.prev_eq' r

/-- If there is no `i` so `c.rel i j`, then `C.X_prev j` is isomorphic to `C.X j`. -/
def X_prev_iso_self {j : ι} (h : ¬c.rel (c.prev j) j) :
  C.X_prev j ≅ C.X j :=
eq_to_iso $ congr_arg C.X begin
  dsimp [complex_shape.prev],
  rw dif_neg, push_neg, intros i hi,
  have : c.prev j = i := c.prev_eq' hi,
  rw this at h, contradiction,
end

/-- Either `C.X j`, if there is some `j` with `c.rel i j`, or `C.X i`. -/
abbreviation X_next (i : ι) : V := C.X (c.next i)

/-- If `c.rel i j`, then `C.X_next i` is isomorphic to `C.X j`. -/
def X_next_iso {i j : ι} (r : c.rel i j) :
  C.X_next i ≅ C.X j :=
eq_to_iso $ by rw ← c.next_eq' r

/-- If there is no `j` so `c.rel i j`, then `C.X_next i` is isomorphic to `C.X i`. -/
def X_next_iso_self {i : ι} (h : ¬c.rel i (c.next i)) :
  C.X_next i ≅ C.X i :=
eq_to_iso $ congr_arg C.X begin
  dsimp [complex_shape.next],
  rw dif_neg, rintro ⟨j, hj⟩,
  have : c.next i = j := c.next_eq' hj,
  rw this at h, contradiction,
end

/--
The differential mapping into `C.X j`, or zero if there isn't one.
-/
abbreviation d_to (j : ι) : C.X_prev j ⟶ C.X j := C.d (c.prev j) j

/--
The differential mapping out of `C.X i`, or zero if there isn't one.
-/
abbreviation d_from (i : ι) : C.X i ⟶ C.X_next i := C.d i (c.next i)

lemma d_to_eq {i j : ι} (r : c.rel i j) :
  C.d_to j = (C.X_prev_iso r).hom ≫ C.d i j :=
begin
  obtain rfl := c.prev_eq' r,
  exact (category.id_comp _).symm,
end

@[simp]
lemma d_to_eq_zero {j : ι} (h : ¬c.rel (c.prev j) j) :
  C.d_to j = 0 :=
C.shape _ _ h

lemma d_from_eq {i j : ι} (r : c.rel i j) :
  C.d_from i = C.d i j ≫ (C.X_next_iso r).inv :=
begin
  obtain rfl := c.next_eq' r,
  exact (category.comp_id _).symm,
end

@[simp]
lemma d_from_eq_zero {i : ι} (h : ¬c.rel i (c.next i)) :
  C.d_from i = 0 :=
C.shape _ _ h

@[simp, reassoc] lemma X_prev_iso_comp_d_to {i j : ι} (r : c.rel i j) :
  (C.X_prev_iso r).inv ≫ C.d_to j = C.d i j :=
by simp [C.d_to_eq r]

@[simp, reassoc] lemma X_prev_iso_self_comp_d_to {j : ι} (h : ¬c.rel (c.prev j) j) :
  (C.X_prev_iso_self h).inv ≫ C.d_to j = 0 :=
by simp [h]

@[simp, reassoc] lemma d_from_comp_X_next_iso {i j : ι} (r : c.rel i j) :
  C.d_from i ≫ (C.X_next_iso r).hom = C.d i j :=
by simp [C.d_from_eq r]

@[simp, reassoc] lemma d_from_comp_X_next_iso_self {i : ι} (h : ¬c.rel i (c.next i)) :
  C.d_from i ≫ (C.X_next_iso_self h).hom = 0 :=
by simp [h]

@[simp]
lemma d_to_comp_d_from (j : ι) : C.d_to j ≫ C.d_from j = 0 :=
C.d_comp_d _ _ _

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

variables {C₁ C₂ C₃ : homological_complex V c}

/-- The `i`-th component of an isomorphism of chain complexes. -/
@[simps]
def iso_app (f : C₁ ≅ C₂) (i : ι) : C₁.X i ≅ C₂.X i :=
(eval V c i).map_iso f

/-- Construct an isomorphism of chain complexes from isomorphism of the objects
which commute with the differentials. -/
@[simps]
def iso_of_components (f : Π i, C₁.X i ≅ C₂.X i)
  (hf : ∀ i j, c.rel i j → (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom) :
  C₁ ≅ C₂ :=
{ hom := { f := λ i, (f i).hom, comm' := hf },
  inv :=
  { f := λ i, (f i).inv,
    comm' := λ i j hij,
    calc (f i).inv ≫ C₁.d i j
        = (f i).inv ≫ (C₁.d i j ≫ (f j).hom) ≫ (f j).inv : by simp
    ... = (f i).inv ≫ ((f i).hom ≫ C₂.d i j) ≫ (f j).inv : by rw hf i j hij
    ... =  C₂.d i j ≫ (f j).inv : by simp },
  hom_inv_id' := by { ext i, exact (f i).hom_inv_id },
  inv_hom_id' := by { ext i, exact (f i).inv_hom_id } }

@[simp] lemma iso_of_components_app (f : Π i, C₁.X i ≅ C₂.X i)
  (hf : ∀ i j, c.rel i j → (f i).hom ≫ C₂.d i j = C₁.d i j ≫ (f j).hom) (i : ι) :
  iso_app (iso_of_components f hf) i = f i :=
by { ext, simp, }

lemma is_iso_of_components (f : C₁ ⟶ C₂) [∀ (n : ι), is_iso (f.f n)] : is_iso f :=
begin
  convert is_iso.of_iso (homological_complex.hom.iso_of_components (λ n, as_iso (f.f n))
    (by tidy)),
  ext n,
  refl,
end

/-! Lemmas relating chain maps and `d_to`/`d_from`. -/

/-- `f.prev j` is `f.f i` if there is some `r i j`, and `f.f j` otherwise. -/
abbreviation prev (f : hom C₁ C₂) (j : ι) : C₁.X_prev j ⟶ C₂.X_prev j := f.f _

lemma prev_eq (f : hom C₁ C₂) {i j : ι} (w : c.rel i j) :
  f.prev j = (C₁.X_prev_iso w).hom ≫ f.f i ≫ (C₂.X_prev_iso w).inv :=
begin
  obtain rfl := c.prev_eq' w,
  simp only [X_prev_iso, eq_to_iso_refl, iso.refl_hom, iso.refl_inv, id_comp, comp_id],
end

/-- `f.next i` is `f.f j` if there is some `r i j`, and `f.f j` otherwise. -/
abbreviation next (f : hom C₁ C₂) (i : ι) : C₁.X_next i ⟶ C₂.X_next i := f.f _

lemma next_eq (f : hom C₁ C₂) {i j : ι} (w : c.rel i j) :
  f.next i = (C₁.X_next_iso w).hom ≫ f.f j ≫ (C₂.X_next_iso w).inv :=
begin
  obtain rfl := c.next_eq' w,
  simp only [X_next_iso, eq_to_iso_refl, iso.refl_hom, iso.refl_inv, id_comp, comp_id],
end

@[simp, reassoc, elementwise]
lemma comm_from (f : hom C₁ C₂) (i : ι) :
  f.f i ≫ C₂.d_from i = C₁.d_from i ≫ f.next i :=
f.comm _ _

@[simp, reassoc, elementwise]
lemma comm_to (f : hom C₁ C₂) (j : ι) :
  f.prev j ≫ C₂.d_to j = C₁.d_to j ≫ f.f j :=
f.comm _ _

/--
A morphism of chain complexes
induces a morphism of arrows of the differentials out of each object.
-/
def sq_from (f : hom C₁ C₂) (i : ι) : arrow.mk (C₁.d_from i) ⟶ arrow.mk (C₂.d_from i) :=
arrow.hom_mk (f.comm_from i)

@[simp] lemma sq_from_left (f : hom C₁ C₂) (i : ι) : (f.sq_from i).left = f.f i := rfl
@[simp] lemma sq_from_right (f : hom C₁ C₂) (i : ι) : (f.sq_from i).right = f.next i := rfl

@[simp] lemma sq_from_id (C₁ : homological_complex V c) (i : ι) : sq_from (𝟙 C₁) i = 𝟙 _ := rfl

@[simp] lemma sq_from_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
  sq_from (f ≫ g) i = sq_from f i ≫ sq_from g i := rfl

/--
A morphism of chain complexes
induces a morphism of arrows of the differentials into each object.
-/
def sq_to (f : hom C₁ C₂) (j : ι) : arrow.mk (C₁.d_to j) ⟶ arrow.mk (C₂.d_to j) :=
arrow.hom_mk (f.comm_to j)

@[simp] lemma sq_to_left (f : hom C₁ C₂) (j : ι) : (f.sq_to j).left = f.prev j := rfl
@[simp] lemma sq_to_right (f : hom C₁ C₂) (j : ι) : (f.sq_to j).right = f.f j := rfl

end hom

end homological_complex

namespace chain_complex

section of
variables {V} {α : Type*} [add_right_cancel_semigroup α] [has_one α] [decidable_eq α]

/--
Construct an `α`-indexed chain complex from a dependently-typed differential.
-/
def of (X : α → V) (d : Π n, X (n+1) ⟶ X n) (sq : ∀ n, d (n+1) ≫ d n = 0) : chain_complex V α :=
{ X := X,
  d := λ i j, if h : i = j + 1 then
    eq_to_hom (by subst h) ≫ d j
  else
    0,
  shape' := λ i j w, by rw dif_neg (ne.symm w),
  d_comp_d' := λ i j k hij hjk,
  begin
    dsimp at hij hjk, substs hij hjk,
    simp only [category.id_comp, dif_pos rfl, eq_to_hom_refl],
    exact sq k,
  end }

variables (X : α → V) (d : Π n, X (n+1) ⟶ X n) (sq : ∀ n, d (n+1) ≫ d n = 0)

@[simp] lemma of_X (n : α) : (of X d sq).X n = X n := rfl
@[simp] lemma of_d (j : α) : (of X d sq).d (j+1) j = d j :=
by { dsimp [of], rw [if_pos rfl, category.id_comp] }
lemma of_d_ne {i j : α} (h : i ≠ j + 1) : (of X d sq).d i j = 0 :=
by { dsimp [of], rw [dif_neg h], }

end of

section of_hom

variables {V} {α : Type*} [add_right_cancel_semigroup α] [has_one α] [decidable_eq α]

variables (X : α → V) (d_X : Π n, X (n+1) ⟶ X n) (sq_X : ∀ n, d_X (n+1) ≫ d_X n = 0)
  (Y : α → V) (d_Y : Π n, Y (n+1) ⟶ Y n) (sq_Y : ∀ n, d_Y (n+1) ≫ d_Y n = 0)

/--
A constructor for chain maps between `α`-indexed chain complexes built using `chain_complex.of`,
from a dependently typed collection of morphisms.
-/
@[simps] def of_hom (f : Π i : α, X i ⟶ Y i) (comm : ∀ i : α, f (i+1) ≫ d_Y i = d_X i ≫ f i) :
  of X d_X sq_X ⟶ of Y d_Y sq_Y :=
{ f := f,
  comm' := λ n m,
  begin
    by_cases h : n = m + 1,
    { subst h,
      simpa using comm m, },
    { rw [of_d_ne X _ _ h, of_d_ne Y _ _ h], simp }
  end }

end of_hom

section mk

/--
Auxiliary structure for setting up the recursion in `mk`.
This is purely an implementation detail: for some reason just using the dependent 6-tuple directly
results in `mk_aux` taking much longer (well over the `-T100000` limit) to elaborate.
-/
@[nolint has_nonempty_instance]
structure mk_struct :=
(X₀ X₁ X₂ : V)
(d₀ : X₁ ⟶ X₀)
(d₁ : X₂ ⟶ X₁)
(s : d₁ ≫ d₀ = 0)

variables {V}

/-- Flatten to a tuple. -/
def mk_struct.flat (t : mk_struct V) :
  Σ' (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁), d₁ ≫ d₀ = 0 :=
⟨t.X₀, t.X₁, t.X₂, t.d₀, t.d₁, t.s⟩

variables (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁) (s : d₁ ≫ d₀ = 0)
  (succ : Π (t : Σ' (X₀ X₁ X₂ : V) (d₀ : X₁ ⟶ X₀) (d₁ : X₂ ⟶ X₁), d₁ ≫ d₀ = 0),
    Σ' (X₃ : V) (d₂ : X₃ ⟶ t.2.2.1), d₂ ≫ t.2.2.2.2.1 = 0)

/-- Auxiliary definition for `mk`. -/
def mk_aux :
  Π n : ℕ, mk_struct V
| 0 := ⟨X₀, X₁, X₂, d₀, d₁, s⟩
| (n+1) :=
  let p := mk_aux n in
  ⟨p.X₁, p.X₂, (succ p.flat).1, p.d₁, (succ p.flat).2.1, (succ p.flat).2.2⟩

/--
A inductive constructor for `ℕ`-indexed chain complexes.

You provide explicitly the first two differentials,
then a function which takes two differentials and the fact they compose to zero,
and returns the next object, its differential, and the fact it composes appropiately to zero.

See also `mk'`, which only sees the previous differential in the inductive step.
-/
def mk : chain_complex V ℕ :=
of (λ n, (mk_aux X₀ X₁ X₂ d₀ d₁ s succ n).X₀) (λ n, (mk_aux X₀ X₁ X₂ d₀ d₁ s succ n).d₀)
  (λ n, (mk_aux X₀ X₁ X₂ d₀ d₁ s succ n).s)

@[simp] lemma mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀ := rfl
@[simp] lemma mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁ := rfl
@[simp] lemma mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂ := rfl
@[simp] lemma mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 0 = d₀ :=
by { change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀, rw [if_pos rfl, category.id_comp] }
@[simp] lemma mk_d_2_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 2 1 = d₁ :=
by { change ite (2 = 1 + 1) (𝟙 X₂ ≫ d₁) 0 = d₁, rw [if_pos rfl, category.id_comp] }
-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.

/--
A simpler inductive constructor for `ℕ`-indexed chain complexes.

You provide explicitly the first differential,
then a function which takes a differential,
and returns the next object, its differential, and the fact it composes appropriately to zero.
-/
def mk' (X₀ X₁ : V) (d : X₁ ⟶ X₀)
  (succ' : Π (t : Σ (X₀ X₁ : V), X₁ ⟶ X₀), Σ' (X₂ : V) (d : X₂ ⟶ t.2.1), d ≫ t.2.2 = 0) :
  chain_complex V ℕ :=
mk X₀ X₁ (succ' ⟨X₀, X₁, d⟩).1 d (succ' ⟨X₀, X₁, d⟩).2.1 (succ' ⟨X₀, X₁, d⟩).2.2
  (λ t, succ' ⟨t.2.1, t.2.2.1, t.2.2.2.2.1⟩)

variables (succ' : Π (t : Σ (X₀ X₁ : V), X₁ ⟶ X₀), Σ' (X₂ : V) (d : X₂ ⟶ t.2.1), d ≫ t.2.2 = 0)

@[simp] lemma mk'_X_0 : (mk' X₀ X₁ d₀ succ').X 0 = X₀ := rfl
@[simp] lemma mk'_X_1 : (mk' X₀ X₁ d₀ succ').X 1 = X₁ := rfl
@[simp] lemma mk'_d_1_0 : (mk' X₀ X₁ d₀ succ').d 1 0 = d₀ :=
by { change ite (1 = 0 + 1) (𝟙 X₁ ≫ d₀) 0 = d₀, rw [if_pos rfl, category.id_comp] }
-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.

end mk

section mk_hom

variables {V} (P Q : chain_complex V ℕ)
  (zero : P.X 0 ⟶ Q.X 0)
  (one : P.X 1 ⟶ Q.X 1)
  (one_zero_comm : one ≫ Q.d 1 0 = P.d 1 0 ≫ zero)
  (succ : ∀ (n : ℕ)
    (p : Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n+1) ⟶ Q.X (n+1)), f' ≫ Q.d (n+1) n = P.d (n+1) n ≫ f),
    Σ' f'' : P.X (n+2) ⟶ Q.X (n+2), f'' ≫ Q.d (n+2) (n+1) = P.d (n+2) (n+1) ≫ p.2.1)

/--
An auxiliary construction for `mk_hom`.

Here we build by induction a family of commutative squares,
but don't require at the type level that these successive commutative squares actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a chain map)
in `mk_hom`.
-/
def mk_hom_aux :
  Π n, Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n+1) ⟶ Q.X (n+1)), f' ≫ Q.d (n+1) n = P.d (n+1) n ≫ f
| 0 := ⟨zero, one, one_zero_comm⟩
| (n+1) := ⟨(mk_hom_aux n).2.1,
    (succ n (mk_hom_aux n)).1, (succ n (mk_hom_aux n)).2⟩

/--
A constructor for chain maps between `ℕ`-indexed chain complexes,
working by induction on commutative squares.

You need to provide the components of the chain map in degrees 0 and 1,
show that these form a commutative square,
and then give a construction of each component,
and the fact that it forms a commutative square with the previous component,
using as an inductive hypothesis the data (and commutativity) of the previous two components.
-/
def mk_hom : P ⟶ Q :=
{ f := λ n, (mk_hom_aux P Q zero one one_zero_comm succ n).1,
  comm' := λ n m,
  begin
    rintro (rfl : m + 1 = n),
    exact (mk_hom_aux P Q zero one one_zero_comm succ m).2.2,
  end }

@[simp] lemma mk_hom_f_0 : (mk_hom P Q zero one one_zero_comm succ).f 0 = zero := rfl
@[simp] lemma mk_hom_f_1 : (mk_hom P Q zero one one_zero_comm succ).f 1 = one := rfl
@[simp] lemma mk_hom_f_succ_succ (n : ℕ) :
  (mk_hom P Q zero one one_zero_comm succ).f (n+2) =
    (succ n ⟨(mk_hom P Q zero one one_zero_comm succ).f n,
      (mk_hom P Q zero one one_zero_comm succ).f (n+1),
        (mk_hom P Q zero one one_zero_comm succ).comm (n+1) n⟩).1 :=
begin
  dsimp [mk_hom, mk_hom_aux],
  induction n; congr,
end

end mk_hom

end chain_complex

namespace cochain_complex

section of
variables {V} {α : Type*} [add_right_cancel_semigroup α] [has_one α] [decidable_eq α]

/--
Construct an `α`-indexed cochain complex from a dependently-typed differential.
-/
def of (X : α → V) (d : Π n, X n ⟶ X (n+1)) (sq : ∀ n, d n ≫ d (n+1) = 0) : cochain_complex V α :=
{ X := X,
  d := λ i j, if h : i + 1 = j then
    d _ ≫ eq_to_hom (by subst h)
  else
    0,
  shape' := λ i j w, by {rw dif_neg, exact w},
  d_comp_d' := λ i j k,
  begin
    split_ifs with h h' h',
    { substs h h',
      simp [sq] },
    all_goals { simp },
  end }

variables (X : α → V) (d : Π n, X n ⟶ X (n+1)) (sq : ∀ n, d n ≫ d (n+1) = 0)

@[simp] lemma of_X (n : α) : (of X d sq).X n = X n := rfl
@[simp] lemma of_d (j : α) : (of X d sq).d j (j+1) = d j :=
by { dsimp [of], rw [if_pos rfl, category.comp_id] }
lemma of_d_ne {i j : α} (h : i + 1 ≠ j) : (of X d sq).d i j = 0 :=
by { dsimp [of], rw [dif_neg h] }

end of

section of_hom

variables {V} {α : Type*} [add_right_cancel_semigroup α] [has_one α] [decidable_eq α]

variables (X : α → V) (d_X : Π n, X n ⟶ X (n+1)) (sq_X : ∀ n, d_X n ≫ d_X (n+1) = 0)
  (Y : α → V) (d_Y : Π n, Y n ⟶ Y (n+1)) (sq_Y : ∀ n, d_Y n ≫ d_Y (n+1) = 0)

/--
A constructor for chain maps between `α`-indexed cochain complexes built using `cochain_complex.of`,
from a dependently typed collection of morphisms.
-/
@[simps] def of_hom (f : Π i : α, X i ⟶ Y i) (comm : ∀ i : α, f i ≫ d_Y i = d_X i ≫ f (i+1)) :
  of X d_X sq_X ⟶ of Y d_Y sq_Y :=
{ f := f,
  comm' := λ n m,
  begin
    by_cases h : n + 1 = m,
    { subst h,
      simpa using comm n },
    { rw [of_d_ne X _ _ h, of_d_ne Y _ _ h], simp }
  end }

end of_hom

section mk

/--
Auxiliary structure for setting up the recursion in `mk`.
This is purely an implementation detail: for some reason just using the dependent 6-tuple directly
results in `mk_aux` taking much longer (well over the `-T100000` limit) to elaborate.
-/
@[nolint has_nonempty_instance]
structure mk_struct :=
(X₀ X₁ X₂ : V)
(d₀ : X₀ ⟶ X₁)
(d₁ : X₁ ⟶ X₂)
(s : d₀ ≫ d₁ = 0)

variables {V}

/-- Flatten to a tuple. -/
def mk_struct.flat (t : mk_struct V) :
  Σ' (X₀ X₁ X₂ : V) (d₀ : X₀ ⟶ X₁) (d₁ : X₁ ⟶ X₂), d₀ ≫ d₁ = 0 :=
⟨t.X₀, t.X₁, t.X₂, t.d₀, t.d₁, t.s⟩

variables (X₀ X₁ X₂ : V) (d₀ : X₀ ⟶ X₁) (d₁ : X₁ ⟶ X₂) (s : d₀ ≫ d₁ = 0)
  (succ : Π (t : Σ' (X₀ X₁ X₂ : V) (d₀ : X₀ ⟶ X₁) (d₁ : X₁ ⟶ X₂), d₀ ≫ d₁ = 0),
    Σ' (X₃ : V) (d₂ : t.2.2.1 ⟶ X₃), t.2.2.2.2.1 ≫ d₂ = 0)

/-- Auxiliary definition for `mk`. -/
def mk_aux :
  Π n : ℕ, mk_struct V
| 0 := ⟨X₀, X₁, X₂, d₀, d₁, s⟩
| (n+1) :=
  let p := mk_aux n in
  ⟨p.X₁, p.X₂, (succ p.flat).1, p.d₁, (succ p.flat).2.1, (succ p.flat).2.2⟩

/--
A inductive constructor for `ℕ`-indexed cochain complexes.

You provide explicitly the first two differentials,
then a function which takes two differentials and the fact they compose to zero,
and returns the next object, its differential, and the fact it composes appropiately to zero.

See also `mk'`, which only sees the previous differential in the inductive step.
-/
def mk : cochain_complex V ℕ :=
of (λ n, (mk_aux X₀ X₁ X₂ d₀ d₁ s succ n).X₀) (λ n, (mk_aux X₀ X₁ X₂ d₀ d₁ s succ n).d₀)
  (λ n, (mk_aux X₀ X₁ X₂ d₀ d₁ s succ n).s)

@[simp] lemma mk_X_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 0 = X₀ := rfl
@[simp] lemma mk_X_1 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 1 = X₁ := rfl
@[simp] lemma mk_X_2 : (mk X₀ X₁ X₂ d₀ d₁ s succ).X 2 = X₂ := rfl
@[simp] lemma mk_d_1_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 0 1 = d₀ :=
by { change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀, rw [if_pos rfl, category.comp_id] }
@[simp] lemma mk_d_2_0 : (mk X₀ X₁ X₂ d₀ d₁ s succ).d 1 2 = d₁ :=
by { change ite (2 = 1 + 1) (d₁ ≫ 𝟙 X₂) 0 = d₁, rw [if_pos rfl, category.comp_id] }
-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.

/--
A simpler inductive constructor for `ℕ`-indexed cochain complexes.

You provide explicitly the first differential,
then a function which takes a differential,
and returns the next object, its differential, and the fact it composes appropriately to zero.
-/
def mk' (X₀ X₁ : V) (d : X₀ ⟶ X₁)
  (succ' : Π (t : Σ (X₀ X₁ : V), X₀ ⟶ X₁), Σ' (X₂ : V) (d : t.2.1 ⟶ X₂), t.2.2 ≫ d = 0) :
  cochain_complex V ℕ :=
mk X₀ X₁ (succ' ⟨X₀, X₁, d⟩).1 d (succ' ⟨X₀, X₁, d⟩).2.1 (succ' ⟨X₀, X₁, d⟩).2.2
  (λ t, succ' ⟨t.2.1, t.2.2.1, t.2.2.2.2.1⟩)

variables (succ' : Π (t : Σ (X₀ X₁ : V), X₀ ⟶ X₁), Σ' (X₂ : V) (d : t.2.1 ⟶ X₂), t.2.2 ≫ d = 0)

@[simp] lemma mk'_X_0 : (mk' X₀ X₁ d₀ succ').X 0 = X₀ := rfl
@[simp] lemma mk'_X_1 : (mk' X₀ X₁ d₀ succ').X 1 = X₁ := rfl
@[simp] lemma mk'_d_1_0 : (mk' X₀ X₁ d₀ succ').d 0 1 = d₀ :=
by { change ite (1 = 0 + 1) (d₀ ≫ 𝟙 X₁) 0 = d₀, rw [if_pos rfl, category.comp_id] }
-- TODO simp lemmas for the inductive steps? It's not entirely clear that they are needed.

end mk

section mk_hom

variables {V} (P Q : cochain_complex V ℕ)
  (zero : P.X 0 ⟶ Q.X 0)
  (one : P.X 1 ⟶ Q.X 1)
  (one_zero_comm : zero ≫ Q.d 0 1 = P.d 0 1 ≫ one)
  (succ : ∀ (n : ℕ)
    (p : Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n+1) ⟶ Q.X (n+1)), f ≫ Q.d n (n+1) = P.d n (n+1) ≫ f'),
    Σ' f'' : P.X (n+2) ⟶ Q.X (n+2), p.2.1 ≫ Q.d (n+1) (n+2) = P.d (n+1) (n+2) ≫ f'')

/--
An auxiliary construction for `mk_hom`.

Here we build by induction a family of commutative squares,
but don't require at the type level that these successive commutative squares actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a chain map)
in `mk_hom`.
-/
def mk_hom_aux :
  Π n, Σ' (f : P.X n ⟶ Q.X n) (f' : P.X (n+1) ⟶ Q.X (n+1)), f ≫ Q.d n (n+1) = P.d n (n+1) ≫ f'
| 0 := ⟨zero, one, one_zero_comm⟩
| (n+1) := ⟨(mk_hom_aux n).2.1,
    (succ n (mk_hom_aux n)).1, (succ n (mk_hom_aux n)).2⟩

/--
A constructor for chain maps between `ℕ`-indexed cochain complexes,
working by induction on commutative squares.

You need to provide the components of the chain map in degrees 0 and 1,
show that these form a commutative square,
and then give a construction of each component,
and the fact that it forms a commutative square with the previous component,
using as an inductive hypothesis the data (and commutativity) of the previous two components.
-/
def mk_hom : P ⟶ Q :=
{ f := λ n, (mk_hom_aux P Q zero one one_zero_comm succ n).1,
  comm' := λ n m,
  begin
    rintro (rfl : n + 1 = m),
    exact (mk_hom_aux P Q zero one one_zero_comm succ n).2.2,
  end }

@[simp] lemma mk_hom_f_0 : (mk_hom P Q zero one one_zero_comm succ).f 0 = zero := rfl
@[simp] lemma mk_hom_f_1 : (mk_hom P Q zero one one_zero_comm succ).f 1 = one := rfl
@[simp] lemma mk_hom_f_succ_succ (n : ℕ) :
  (mk_hom P Q zero one one_zero_comm succ).f (n+2) =
    (succ n ⟨(mk_hom P Q zero one one_zero_comm succ).f n,
      (mk_hom P Q zero one one_zero_comm succ).f (n+1),
        (mk_hom P Q zero one one_zero_comm succ).comm n (n+1)⟩).1 :=
begin
  dsimp [mk_hom, mk_hom_aux],
  induction n; congr,
end

end mk_hom

end cochain_complex
