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
(shape : ∀ i j, ¬ c.r i j → d i j = 0)
(d_comp_d : ∀ i j k, d i j ≫ d j k = 0)

namespace homological_complex
variables {V} {c : complex_shape ι} (C : homological_complex V c)

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

end homological_complex
