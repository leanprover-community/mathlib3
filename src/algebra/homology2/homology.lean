import algebra.homology2.homological_complex

universes v u

open category_theory category_theory.limits

variables {ι : Type*}
variables (V : Type u) [category.{v} V] [has_zero_object V] [has_zero_morphisms V]

open_locale classical
noncomputable theory

namespace homological_complex

variables {V} {c : complex_shape ι} (C : homological_complex V c)

section cycles
variables [has_kernels V]

def cycles (i : ι) : subobject (C.X i) :=
kernel_subobject (C.d_from i)

@[simp, reassoc]
lemma cycles_arrow_d_from (i : ι) : (C.cycles i).arrow ≫ C.d_from i = 0 :=
by { dsimp [cycles], simp, }

lemma cycles_eq_kernel_subobject {i j : ι} (r : c.r i j) :
  C.cycles i = kernel_subobject (C.d i j) :=
C.kernel_from_eq_kernel r

def cycles_iso_kernel {i j : ι} (r : c.r i j) :
  (C.cycles i : V) ≅ kernel (C.d i j) :=
subobject.underlying.map_iso (eq_to_iso (C.cycles_eq_kernel_subobject r)) ≪≫
  kernel_subobject_iso (C.d i j)

lemma cycles_eq_top {i} (h : c.succ i → false) : C.cycles i = ⊤ :=
begin
  rw eq_top_iff,
  apply le_kernel_subobject,
  rw [C.d_from_eq_zero h, comp_zero],
end

end cycles

section boundaries
variables [has_images V] [has_equalizers V]

def boundaries (C : homological_complex V c) (j : ι) : subobject (C.X j) :=
image_subobject (C.d_to j)

lemma boundaries_eq_image_subobject {i j : ι} (r : c.r i j) :
  C.boundaries j = image_subobject (C.d i j) :=
C.image_to_eq_image r

def boundaries_iso_image {i j : ι} (r : c.r i j) :
  (C.boundaries j : V) ≅ image (C.d i j) :=
subobject.underlying.map_iso (eq_to_iso (C.boundaries_eq_image_subobject r)) ≪≫
  image_subobject_iso (C.d i j)

lemma boundaries_eq_bot {j} (h : c.pred j → false) : C.boundaries j = ⊥ :=
begin
  rw eq_bot_iff,
  refine image_subobject_le _ 0 _,
  rw [C.d_to_eq_zero h, zero_comp],
end

end boundaries

section
variables [has_kernels V] [has_images V] [has_equalizers V] [has_zero_object V]

lemma boundaries_le_cycles (C : homological_complex V c) (i : ι) :
  C.boundaries i ≤ C.cycles i :=
image_subobject_le_mk _ _ (kernel.lift _ _ (C.d_to_comp_d_from i)) (by simp)

variables [has_cokernels V]

def homology (C : homological_complex V c) (i : ι) : V :=
cokernel (subobject.underlying.map (hom_of_le (C.boundaries_le_cycles i)))

end

/-! Computing the cycles is functorial. -/
section
variables [has_kernels V]
variables {C₁ C₂ C₃ : homological_complex V c} (f : C₁ ⟶ C₂)

def cycles_map (f : C₁ ⟶ C₂) (i : ι) : (C₁.cycles i : V) ⟶ (C₂.cycles i : V) :=
subobject.factor_thru _ ((C₁.cycles i).arrow ≫ f.f i) (kernel_subobject_factors _ _ (by simp))

@[simp] lemma cycles_map_id (i : ι) : cycles_map (𝟙 C₁) i = 𝟙 _ :=
by { simp [cycles_map], }

@[simp] lemma cycles_map_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
  cycles_map (f ≫ g) i = cycles_map f i ≫ cycles_map g i :=
by { simp [cycles_map], }

@[simps]
def cycles_functor (i : ι) : homological_complex V c ⥤ V :=
{ obj := λ C, C.cycles i,
  map := λ C₁ C₂ f, cycles_map f i, }

end

/-! Computing the boundaries is functorial. -/
section
variables [has_images V] [has_image_maps V] [has_equalizers V]
variables {C₁ C₂ C₃ : homological_complex V c} (f : C₁ ⟶ C₂)

def boundaries_map (f : C₁ ⟶ C₂) (i : ι) : (C₁.boundaries i : V) ⟶ (C₂.boundaries i : V) :=
image_subobject_map (f.sq_to i)

@[simp] lemma boundaries_map_id (i : ι) : boundaries_map (𝟙 C₁) i = 𝟙 _ :=
begin
  simp [boundaries_map],
  ext,
  simp,
  erw [category.id_comp],  --- hrm.
end

@[simp] lemma boundaries_map_comp (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) (i : ι) :
  boundaries_map (f ≫ g) i = boundaries_map f i ≫ boundaries_map g i :=
begin
  simp [boundaries_map],
  ext,
  simp,
end

@[simps]
def boundaries_functor (i : ι) : homological_complex V c ⥤ V :=
{ obj := λ C, C.boundaries i,
  map := λ C₁ C₂ f, boundaries_map f i, }

end

end homological_complex
