import algebra.homology2.additive

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_object V] [preadditive V]

variables {c : complex_shape ι} {C D E : homological_complex V c}
variables (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

@[ext]
structure ihom (k : ℤ) (C D : homological_complex V c) :=
(h : Π i j, C.X i ⟶ D.X j)
(zero' : ∀ i j, ¬ c.r' k i j → h i j = 0 . obviously)

def ihom.to_pred {k : ℤ} (f : ihom k C D) (i j : ι) : C.X i ⟶ D.X_pred j := sorry
def ihom.from_succ {k : ℤ} (f : ihom k C D) (i j : ι) : C.X_succ i ⟶ D.X j := sorry

structure homotopy (f g : C ⟶ D) extends ihom (-1) C D :=
(comm' : ∀ i, to_ihom.to_pred i i ≫ D.d_to i + C.d_from i ≫ to_ihom.from_succ i i + g.f i = f.f i)

variables [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

theorem homology_map_eq_of_homotopy (h : homotopy f g) (i : ι) :
  (homology_functor V c i).map f = (homology_functor V c i).map g :=
begin
  dsimp [homology_functor, cycles_map],
  ext,
  dsimp,
  simp [←h.comm' i],
  apply eq_of_sub_eq_zero,
  rw [←preadditive.sub_comp],

  suffices h : ((D.cycles i).factor_thru ((C.cycles i).arrow ≫ h.to_ihom.to_pred i i ≫ D.d_to i) _) ≫ cokernel.π (D.boundaries_to_cycles i) = 0,
  sorry, -- interaction of factor_thru and preadditive
  dsimp [cycles],
  erw [subobject.factor_thru_le _ (D.boundaries_le_cycles i)],
  dsimp [boundaries_to_cycles],
  simp,
  dsimp [boundaries],
  rw [←category.assoc],
  apply image_subobject_factors',
end
