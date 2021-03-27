import category_theory.limits.shapes.zero
import category_theory.subobject.lattice
import category_theory.subobject.factor_thru

structure complex_shape (ι : Type*) :=
(r : ι → ι → Prop)
(succ_eq : ∀ {i j k}, r i j → r i k → j = k)
(pred_eq : ∀ {i j k}, r i k → r j k → i = j)

namespace complex_shape
variables {ι : Type*}

def succ (c : complex_shape ι) (i : ι) := { j // c.r i j }
def pred (c : complex_shape ι) (j : ι) := { i // c.r i j }

instance (c : complex_shape ι) (i : ι) : subsingleton (c.succ i) :=
begin
  fsplit,
  rintros ⟨j, rij⟩ ⟨k, rik⟩,
  congr,
  exact c.succ_eq rij rik,
end

instance (c : complex_shape ι) (k : ι) : subsingleton (c.pred k) :=
begin
  fsplit,
  rintros ⟨i, rik⟩ ⟨j, rjk⟩,
  congr,
  exact c.pred_eq rik rjk,
end

end complex_shape

universes v u

open category_theory category_theory.limits

variables {ι : Type*}
variables (V : Type u) [category.{v} V] [has_zero_morphisms V]

structure pre_complex (c : complex_shape ι) :=
(X : ι → V)
(d : Π i j, X i ⟶ X j)
(shape : ∀ i j, ¬ c.r i j → d i j = 0)
(d_comp_d : ∀ i j k, d i j ≫ d j k = 0)

namespace pre_complex
variables {V} {c : complex_shape ι} (C : pre_complex V c)

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


open_locale classical
noncomputable theory

section cycles
variables [has_kernels V]

lemma kernel_eq_kernel {i j j' : ι} (r : c.r i j) (r' : c.r i j') :
  kernel_subobject (C.d i j) = kernel_subobject (C.d i j') :=
begin
  rw ←d_comp_eq_to_hom C r r',
  apply kernel_subobject_comp_iso,
end

def cycles (i : ι) : subobject (C.X i) :=
if h : nonempty (c.succ i) then
  kernel_subobject (C.d i (nonempty.some h).1)
else
  ⊤

lemma cycles_eq_kernel_subobject {i j : ι} (r : c.r i j) :
  C.cycles i = kernel_subobject (C.d i j) :=
begin
  let n : nonempty (c.succ i) := ⟨⟨j, r⟩⟩,
  dsimp [cycles],
  rw [dif_pos n],
  apply kernel_eq_kernel C n.some.2 r,
end

lemma cycles_eq_top {i} (h : c.succ i → false) : C.cycles i = ⊤ :=
begin
  dsimp [cycles],
  rw [dif_neg],
  rintro ⟨a⟩,
  exact h a,
end

end cycles

section boundaries
variables [has_images V] [has_equalizers V] [has_zero_object V]

lemma image_eq_image {i i' j : ι} (r : c.r i j) (r' : c.r i' j) :
  image_subobject (C.d i j) = image_subobject (C.d i' j) :=
begin
  rw ←eq_to_hom_comp_d C r r',
  apply image_subobject_iso_comp,
end

def boundaries (C : pre_complex V c) (j : ι) : subobject (C.X j) :=
if h : nonempty (c.pred j) then
  image_subobject (C.d (nonempty.some h).1 j)
else
  ⊥

lemma boundaries_eq_image_subobject {i j : ι} (r : c.r i j) :
  C.boundaries j = image_subobject (C.d i j) :=
begin
  let n : nonempty (c.pred j) := ⟨⟨i, r⟩⟩,
  dsimp [boundaries],
  rw [dif_pos n],
  apply image_eq_image C n.some.2 r,
end

lemma boundaries_eq_bot {j} (h : c.pred j → false) : C.boundaries j = ⊥ :=
begin
  dsimp [boundaries],
  rw [dif_neg],
  rintro ⟨a⟩,
  exact h a,
end

end boundaries

section
variables [has_kernels V] [has_images V] [has_equalizers V] [has_zero_object V]

lemma boundaries_le_cycles [has_kernels V] [has_images V] (C : pre_complex V c) (i : ι) :
  C.boundaries i ≤ C.cycles i :=
begin
  dsimp [cycles, boundaries],
  split_ifs with h h',
  { exact image_subobject_le_mk _ (C.d _ i)
      (kernel.lift _ _ (C.d_comp_d _ i _)) (by simp), },
  { exact le_top, },
  { exact bot_le, },
  { exact le_top, },
end

end



end pre_complex
