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
(shape' : ∀ i j, ¬ c.r i j → d i j = 0 . obviously)
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
attribute [simp, reassoc] hom.comm

@[simps] def id (A : homological_complex V c) : hom A A :=
{ f := λ _, 𝟙 _ }

@[simps] def comp (A B C : homological_complex V c) (φ : hom A B) (ψ : hom B C) : hom A C :=
{ f := λ i, φ.f i ≫ ψ.f i }

instance : category (homological_complex V c) :=
{ hom := hom,
  id := id,
  comp := comp, }

open_locale classical
noncomputable theory

variables [has_zero_object V]
local attribute [instance] has_zero_object.has_zero

lemma d_comp_eq_to_hom {i j j' : ι} (rij : c.r i j) (rij' : c.r i j') :
  C.d i j' ≫ eq_to_hom (congr_arg C.X (c.succ_eq rij' rij)) = C.d i j :=
begin
  have P : ∀ h : j' = j, C.d i j' ≫ eq_to_hom (congr_arg C.X h) = C.d i j,
  { rintro rfl, simp, },
  apply P,
end

lemma eq_to_hom_comp_d {i i' j : ι} (rij : c.r i j) (rij' : c.r i' j) :
  eq_to_hom (congr_arg C.X (c.pred_eq rij rij')) ≫ C.d i' j = C.d i j :=
begin
  have P : ∀ h : i = i', eq_to_hom (congr_arg C.X h) ≫ C.d i' j = C.d i j,
  { rintro rfl, simp, },
  apply P,
end

lemma kernel_eq_kernel [has_kernels V] {i j j' : ι} (r : c.r i j) (r' : c.r i j') :
  kernel_subobject (C.d i j) = kernel_subobject (C.d i j') :=
begin
  rw ←d_comp_eq_to_hom C r r',
  apply kernel_subobject_comp_iso,
end

lemma image_eq_image [has_images V] [has_equalizers V] [has_zero_object V]
  {i i' j : ι} (r : c.r i j) (r' : c.r i' j) :
  image_subobject (C.d i j) = image_subobject (C.d i' j) :=
begin
  rw ←eq_to_hom_comp_d C r r',
  apply image_subobject_iso_comp,
end

/--
The differential mapping into `C.X j`, or zero if there isn't one.

We represent this as an object over `C.X j`,
in order to avoid explicitly picking a predecessor of `j`,
and because the source might be `0`, rather than some `C.X i`.
-/
def d_to (j : ι) : over (C.X j) :=
if h : nonempty (c.pred j) then
  over.mk (C.d h.some.1 j)
else
  over.mk (0 : 0 ⟶ C.X j)

/--
The differential mapping out of `C.X i`, or zero if there isn't one.

We represent this as an object under `C.X i`,
in order to avoid explicitly picking a successor of `i`,
and because the target might be `0`, rather than some `C.X j`.
-/
def d_from (i : ι) : under (C.X i) :=
if h : nonempty (c.succ i) then
  under.mk (C.d i h.some.1)
else
  under.mk (0 : C.X i ⟶ 0)

lemma over.hom_congr {X : V} {A B : over X} (h : A = B) : A.hom = eq_to_hom (by subst h) ≫ B.hom :=
by { subst h, simp }

def d_to_left {i j : ι} (r : c.r i j) :
  (C.d_to j).left ≅ C.X i :=
begin
  dsimp [d_to],
  apply eq_to_iso,
  rw [dif_pos (c.nonempty_pred r)],
  exact congr_arg C.X (c.nonempty_pred_some r),
end

lemma d_to_hom {i j : ι} (r : c.r i j) :
  (C.d_to j).hom = (C.d_to_left r).hom ≫ C.d i j :=
begin
  dsimp [d_to, d_to_left],
  convert over.hom_congr (dif_pos (c.nonempty_pred r)),
  repeat { apply (c.nonempty_pred_some r).symm, },
  repeat { assumption, },
end

lemma d_to_hom_eq_zero {j : ι} (h : c.pred j → false) :
  (C.d_to j).hom = 0 :=
begin
  dsimp [d_to],
  rw [dif_neg],
  { refl, },
  { rintro ⟨a⟩, exact h a, }
end

lemma under.hom_congr {X : V} {A B : under X} (h : A = B) : A.hom = B.hom ≫ eq_to_hom (by subst h) :=
by { subst h, simp }

def d_from_right {i j : ι} (r : c.r i j) :
  (C.d_from i).right ≅ C.X j :=
begin
  dsimp [d_from],
  apply eq_to_iso,
  rw [dif_pos (c.nonempty_succ r)],
  exact congr_arg C.X (c.nonempty_succ_some r),
end

lemma d_from_hom {i j : ι} (r : c.r i j) :
  (C.d_from i).hom = C.d i j ≫ (C.d_from_right r).inv :=
begin
  dsimp [d_from, d_from_right],
  convert under.hom_congr (dif_pos (c.nonempty_succ r)),
  repeat { apply (c.nonempty_succ_some r).symm, },
  repeat { assumption, },
end

lemma d_from_hom_eq_zero {i : ι} (h : c.succ i → false) :
  (C.d_from i).hom = 0 :=
begin
  dsimp [d_from],
  rw [dif_neg],
  { refl, },
  { rintro ⟨a⟩, exact h a, }
end

@[simp]
lemma d_to_comp_d_from (j : ι) : (C.d_to j).hom ≫ (C.d_from j).hom = 0 :=
begin
  by_cases h : nonempty (c.pred j),
  { obtain ⟨⟨i, rij⟩⟩ := h,
    by_cases h' : nonempty (c.succ j),
    { obtain ⟨⟨k, rjk⟩⟩ := h',
      rw [C.d_to_hom rij, C.d_from_hom rjk],
      simp, },
    { rw [C.d_from_hom_eq_zero (not_nonempty_iff_imp_false.mp h')],
      simp, }, },
  { rw [C.d_to_hom_eq_zero (not_nonempty_iff_imp_false.mp h)],
    simp, },
end

lemma kernel_from_eq_kernel [has_kernels V] {i j : ι} (r : c.r i j) :
  kernel_subobject (C.d_from i).hom = kernel_subobject (C.d i j) :=
begin
  rw C.d_from_hom r,
  apply kernel_subobject_comp_iso,
end

lemma image_to_eq_image [has_images V] [has_equalizers V] [has_zero_object V]
  {i j : ι} (r : c.r i j) :
  image_subobject (C.d_to j).hom = image_subobject (C.d i j) :=
begin
  rw C.d_to_hom r,
  apply image_subobject_iso_comp,
end

end homological_complex
