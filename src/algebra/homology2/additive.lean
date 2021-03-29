import algebra.homology2.homology
import category_theory.abelian.additive_functor

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_object V] [preadditive V]

variables {c : complex_shape ι} {C D E : homological_complex V c}
variables (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

namespace homological_complex

instance : has_zero (C ⟶ D) := ⟨{ f := λ i, 0 }⟩
instance : has_add (C ⟶ D) := ⟨λ f g, { f := λ i, f.f i + g.f i, }⟩
instance : has_neg (C ⟶ D) := ⟨λ f, { f := λ i, -(f.f i), }⟩

@[simp] lemma zero_f_apply (i : ι) : (0 : C ⟶ D).f i = 0 := rfl
@[simp] lemma add_f_apply (f g : C ⟶ D) (i : ι) : (f + g).f i = f.f i + g.f i := rfl
@[simp] lemma neg_f_apply (f : C ⟶ D) (i : ι) : (-f).f i = -(f.f i) := rfl

instance : add_comm_group (C ⟶ D) :=
function.injective.add_comm_group hom.f
  homological_complex.hom_f_injective (by tidy) (by tidy) (by tidy)

instance : preadditive (homological_complex V c) := {}

end homological_complex

variables [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

instance : functor.additive (cycles_functor V c i) :=
{ map_zero' := λ C D, by { dsimp [cycles_functor, cycles_map], ext, simp, },
  map_add' := λ C D f g, by { dsimp [cycles_functor, cycles_map], ext, simp, }, }

instance : functor.additive (boundaries_functor V c i) :=
{ map_zero' := λ C D, by { dsimp [boundaries_functor, boundaries_map], ext, simp, },
  map_add' := λ C D f g, by { dsimp [boundaries_functor, boundaries_map], ext, simp, }, }

instance : functor.additive (homology_functor V c i) :=
{ map_zero' := λ C D, begin
    dsimp [homology_functor, boundaries_to_cycles, cycles_map],
    ext,
    simp,
  end,
  map_add' := λ C D f g, begin
    dsimp [homology_functor, boundaries_to_cycles, cycles_map],
    ext,
    simp only [limits.cokernel.π_desc, preadditive.comp_add,
      limits.coequalizer_as_cokernel, ←preadditive.add_comp],
    congr,
    ext,
    simp,
  end }
