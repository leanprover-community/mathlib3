import algebra.homology2.complex_shape
import category_theory.limits.shapes.zero
import category_theory.subobject.lattice
import category_theory.subobject.factor_thru

universes v u

open category_theory category_theory.limits

variables {ι : Type*}
variables (V : Type u) [category.{v} V] [has_zero_morphisms V]

structure homological_complex (c : complex_shape ι) :=
(X : ι → V)
(d : Π i j, X i ⟶ X j)
(shape' : ∀ i j, ¬ c.rel i j → d i j = 0 . obviously)
(d_comp_d' : ∀ i j k, d i j ≫ d j k = 0 . obviously)

restate_axiom homological_complex.shape'
restate_axiom homological_complex.d_comp_d'

attribute [simp] homological_complex.shape
attribute [simp, reassoc] homological_complex.d_comp_d

namespace homological_complex
variables {V} {c : complex_shape ι} (C : homological_complex V c)

@[ext] structure hom (A B : homological_complex V c) :=
(f : ∀ i, A.X i ⟶ B.X i)
(comm' : ∀ i j, f i ≫ B.d i j = A.d i j ≫ f j . obviously)

restate_axiom hom.comm'
attribute [simp, reassoc, elementwise] hom.comm

def id (A : homological_complex V c) : hom A A :=
{ f := λ _, 𝟙 _ }

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

lemma hom_f_injective {C₁ C₂ : homological_complex V c} :
  function.injective (λ f : hom C₁ C₂, hom.f f) :=
by tidy

open_locale classical
noncomputable theory

variables [has_zero_object V]
local attribute [instance] has_zero_object.has_zero

lemma d_comp_eq_to_hom {i j j' : ι} (rij : c.rel i j) (rij' : c.rel i j') :
  C.d i j' ≫ eq_to_hom (congr_arg C.X (c.next_eq rij' rij)) = C.d i j :=
begin
  have P : ∀ h : j' = j, C.d i j' ≫ eq_to_hom (congr_arg C.X h) = C.d i j,
  { rintro rfl, simp, },
  apply P,
end

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

lemma image_eq_image [has_images V] [has_equalizers V] [has_zero_object V]
  {i i' j : ι} (r : c.rel i j) (r' : c.rel i' j) :
  image_subobject (C.d i j) = image_subobject (C.d i' j) :=
begin
  rw ←eq_to_hom_comp_d C r r',
  apply image_subobject_iso_comp,
end

def X_pred (j : ι) : V :=
match c.prev j with
| none := 0
| (some ⟨i,_⟩) := C.X i
end

def X_pred_iso {i j : ι} (r : c.rel i j) :
  C.X_pred j ≅ C.X i :=
begin
  dsimp [X_pred],
  apply eq_to_iso,
  rw c.prev_eq_some r,
  refl,
end

def X_pred_iso_zero {j : ι} (h : c.prev j = none) :
  C.X_pred j ≅ 0 :=
begin
  dsimp [X_pred],
  apply eq_to_iso,
  rw h,
  refl,
end

def X_succ (i : ι) : V :=
match c.next i with
| none := 0
| (some ⟨j,_⟩) := C.X j
end

def X_succ_iso {i j : ι} (r : c.rel i j) :
  C.X_succ i ≅ C.X j :=
begin
  dsimp [X_succ],
  apply eq_to_iso,
  rw c.next_eq_some r,
  refl,
end

def X_succ_iso_zero {i : ι} (h : c.next i = none) :
  C.X_succ i ≅ 0 :=
begin
  dsimp [X_succ],
  apply eq_to_iso,
  rw h,
  refl,
end

/--
The differential mapping into `C.X j`, or zero if there isn't one.
-/
def d_to (j : ι) : C.X_pred j ⟶ C.X j :=
match c.prev j with
| none := (0 : C.X_pred j ⟶ C.X j)
| (some ⟨i, w⟩) := (C.X_pred_iso w).hom ≫ C.d i j
end

/--
The differential mapping out of `C.X i`, or zero if there isn't one.
-/
def d_from (i : ι) : C.X i ⟶ C.X_succ i :=
match c.next i with
| none := (0 : C.X i ⟶ C.X_succ i)
| (some ⟨j, w⟩) := C.d i j ≫ (C.X_succ_iso w).inv
end

lemma d_to_eq {i j : ι} (r : c.rel i j) :
  C.d_to j = (C.X_pred_iso r).hom ≫ C.d i j :=
begin
  dsimp [d_to, X_pred_iso],
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
  C.d_from i = C.d i j ≫ (C.X_succ_iso r).inv :=
begin
  dsimp [d_from, X_succ_iso],
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

lemma image_to_eq_image [has_images V] [has_equalizers V] [has_zero_object V]
  {i j : ι} (r : c.rel i j) :
  image_subobject (C.d_to j) = image_subobject (C.d i j) :=
begin
  rw C.d_to_eq r,
  apply image_subobject_iso_comp,
end

namespace hom

variables {C₁ C₂ : homological_complex V c}

/-- The commutative square
```
C₁.X i ---d---> C₁.X j
  |               |
f.f i           f.f j
  |               |
  v               v
C₂.X i ---d---> C₂.X j
```
-/
def sq (f : hom C₁ C₂) (i j : ι) : arrow.mk (C₁.d i j) ⟶ arrow.mk (C₂.d i j) :=
arrow.hom_mk (f.comm i j)

@[simp] lemma sq_left (f : hom C₁ C₂) (i j : ι) : (f.sq i j).left = f.f i := rfl
@[simp] lemma sq_right (f : hom C₁ C₂) (i j : ι) : (f.sq i j).right = f.f j := rfl

/--
The map induced on boundaries by a chain map.
-/
def image_map [has_images V] [has_image_maps V] (f : hom C₁ C₂) (i j : ι) :
  image (C₁.d i j) ⟶ image (C₂.d i j) :=
image.map (f.sq i j)

/-! Lemmas relating chain maps and `d_to`/`d_from`. -/

/-- `f.f_pred j` is `f.f i` if there is some `r i j`, and zero otherwise. -/
def f_pred (f : hom C₁ C₂) (j : ι) : C₁.X_pred j ⟶ C₂.X_pred j :=
match c.prev j with
| none := 0
| some ⟨i,w⟩ := (C₁.X_pred_iso w).hom ≫ f.f i ≫ (C₂.X_pred_iso w).inv
end

lemma f_pred_eq (f : hom C₁ C₂) {i j : ι} (w : c.rel i j) :
  f.f_pred j = (C₁.X_pred_iso w).hom ≫ f.f i ≫ (C₂.X_pred_iso w).inv :=
begin
  dsimp [f_pred],
  rw c.prev_eq_some w,
  refl,
end

/-- `f.f_succ i` is `f.f j` if there is some `r i j`, and zero otherwise. -/
def f_succ (f : hom C₁ C₂) (i : ι) : C₁.X_succ i ⟶ C₂.X_succ i :=
match c.next i with
| none := 0
| some ⟨j,w⟩ := (C₁.X_succ_iso w).hom ≫ f.f j ≫ (C₂.X_succ_iso w).inv
end

lemma f_succ_eq (f : hom C₁ C₂) {i j : ι} (w : c.rel i j) :
  f.f_succ i = (C₁.X_succ_iso w).hom ≫ f.f j ≫ (C₂.X_succ_iso w).inv :=
begin
  dsimp [f_succ],
  rw c.next_eq_some w,
  refl,
end

@[simp, reassoc, elementwise]
lemma comm_from (f : hom C₁ C₂) (i : ι) :
  f.f i ≫ C₂.d_from i = C₁.d_from i ≫ f.f_succ i :=
begin
  rcases h : c.next i with _ | ⟨j,w⟩,
  { simp [h], },
  { simp [d_from_eq _ w, f_succ_eq _ w], }
end

@[simp, reassoc, elementwise]
lemma comm_to (f : hom C₁ C₂) (j : ι) :
  f.f_pred j ≫ C₂.d_to j = C₁.d_to j ≫ f.f j :=
begin
  rcases h : c.prev j with _ | ⟨j,w⟩,
  { simp [h], },
  { simp [d_to_eq _ w, f_pred_eq _ w], }
end

def sq_to (f : hom C₁ C₂) (j : ι) : arrow.mk (C₁.d_to j) ⟶ arrow.mk (C₂.d_to j) :=
arrow.hom_mk (f.comm_to j)

@[simp] lemma sq_to_right (f : hom C₁ C₂) (j : ι) : (f.sq_to j).right = f.f j := rfl

def image_map_to [has_images V] [has_image_maps V] (f : hom C₁ C₂) (j : ι) :
  image (C₁.d_to j) ⟶ image (C₂.d_to j) :=
image.map (f.sq_to j)

end hom

end homological_complex
