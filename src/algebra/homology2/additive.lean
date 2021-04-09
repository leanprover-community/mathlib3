/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology2.homology
import category_theory.preadditive.additive_functor

/-!
# Homology is an additive functor

When `V` is preadditive, `homological_complex V c` is also preadditive,
and `homology_functor` is additive.
-/

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
instance : has_sub (C ⟶ D) := ⟨λ f g, { f := λ i, f.f i - g.f i, }⟩

@[simp] lemma zero_f_apply (i : ι) : (0 : C ⟶ D).f i = 0 := rfl
@[simp] lemma add_f_apply (f g : C ⟶ D) (i : ι) : (f + g).f i = f.f i + g.f i := rfl
@[simp] lemma neg_f_apply (f : C ⟶ D) (i : ι) : (-f).f i = -(f.f i) := rfl
@[simp] lemma sub_f_apply (f g : C ⟶ D) (i : ι) : (f - g).f i = f.f i - g.f i := rfl

instance : add_comm_group (C ⟶ D) :=
function.injective.add_comm_group hom.f
  homological_complex.hom_f_injective (by tidy) (by tidy) (by tidy) (by tidy)

instance : preadditive (homological_complex V c) := {}

end homological_complex

namespace homological_complex

variables [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

instance cycles_additive : functor.additive (cycles_functor V c i) :=
{ map_zero' := λ C D, by { dsimp [cycles_functor], ext, simp, },
  map_add' := λ C D f g, by { dsimp [cycles_functor], ext, simp, }, }

instance boundaries_additive : functor.additive (boundaries_functor V c i) :=
{ map_zero' := λ C D, by { dsimp [boundaries_functor], ext, simp, },
  map_add' := λ C D f g, by { dsimp [boundaries_functor], ext, simp, }, }

instance homology_additive : functor.additive (homology_functor V c i) :=
{ map_zero' := λ C D, begin
    dsimp [homology_functor],
    ext,
    simp only [limits.cokernel.π_desc, limits.comp_zero],
    convert zero_comp,
    ext,
    simp,
  end,
  map_add' := λ C D f g, begin
    dsimp [homology_functor],
    ext,
    simp only [limits.cokernel.π_desc, preadditive.comp_add,
      limits.coequalizer_as_cokernel, ←preadditive.add_comp],
    congr,
    ext,
    simp,
  end }

end homological_complex
