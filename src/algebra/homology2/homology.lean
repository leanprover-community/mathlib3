import algebra.homology2.pre_complex

universes v u

open category_theory category_theory.limits

variables {ι : Type*}
variables (V : Type u) [category.{v} V] [has_zero_morphisms V]

open_locale classical
noncomputable theory

namespace homological_complex

variables {V} {c : complex_shape ι} (C : homological_complex V c)

section cycles
variables [has_kernels V]

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

def boundaries (C : homological_complex V c) (j : ι) : subobject (C.X j) :=
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

lemma boundaries_le_cycles (C : homological_complex V c) (i : ι) :
  C.boundaries i ≤ C.cycles i :=
begin
  dsimp [cycles, boundaries],
  split_ifs with h h',
  { exact image_subobject_le_mk _ (C.d _ i) (kernel.lift _ _ (C.d_comp_d _ i _)) (by simp), },
  { exact le_top, },
  { exact bot_le, },
  { exact le_top, },
end

end

end homological_complex
