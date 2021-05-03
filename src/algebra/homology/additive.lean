/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.homology
import category_theory.preadditive.additive_functor

/-!
# Homology is an additive functor

When `V` is preadditive, `homological_complex V c` is also preadditive,
and `homology_functor` is additive.

TODO: similarly for `R`-linear.
-/

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [preadditive V]

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

variables [has_zero_object V]

instance cycles_additive [has_equalizers V] : (cycles_functor V c i).additive :=
{ map_zero' := λ C D, by { dsimp [cycles_functor], ext, simp, },
  map_add' := λ C D f g, by { dsimp [cycles_functor], ext, simp, }, }

variables [has_images V] [has_image_maps V]

instance boundaries_additive : (boundaries_functor V c i).additive :=
{ map_zero' := λ C D, by { dsimp [boundaries_functor], ext, simp, },
  map_add' := λ C D f g, by { dsimp [boundaries_functor], ext, simp, }, }

variables [has_equalizers V] [has_cokernels V]

instance homology_additive : (homology_functor V c i).additive :=
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

namespace category_theory

variables {W : Type*} [category W] [preadditive W]

/--
An additive functor induces a functor between homological complexes.
This is sometimes called the "prolongation".
-/
@[simps]
def functor.map_homological_complex (F : V ⥤ W) [F.additive] (c : complex_shape ι) :
  homological_complex V c ⥤ homological_complex W c :=
{ obj := λ C,
  { X := λ i, F.obj (C.X i),
    d := λ i j, F.map (C.d i j),
    shape' := λ i j w, by rw [C.shape _ _ w, F.map_zero],
    d_comp_d' := λ i j k, by rw [←F.map_comp, C.d_comp_d, F.map_zero], },
  map := λ C D f,
  { f := λ i, F.map (f.f i),
    comm' := λ i j, by { dsimp,  rw [←F.map_comp, ←F.map_comp, f.comm], }, }, }.

instance functor.map_homogical_complex_additive
  (F : V ⥤ W) [F.additive] (c : complex_shape ι) : (F.map_homological_complex c).additive := {}

@[simps]
def nat_trans.map_homological_complex {F G : V ⥤ W} [F.additive] [G.additive]
  (α : F ⟶ G) (c : complex_shape ι) : F.map_homological_complex c ⟶ G.map_homological_complex c :=
{ app := λ C, { f := λ i, α.app _, }, }

@[simp] lemma nat_trans.map_homological_complex_id (c : complex_shape ι) (F : V ⥤ W) [F.additive] :
  nat_trans.map_homological_complex (𝟙 F) c = 𝟙 (F.map_homological_complex c) :=
by tidy

@[simp] lemma nat_trans.map_homological_complex_comp (c : complex_shape ι)
  {F G H : V ⥤ W} [F.additive] [G.additive] [H.additive]
  (α : F ⟶ G) (β : G ⟶ H):
  nat_trans.map_homological_complex (α ≫ β) c =
    nat_trans.map_homological_complex α c ≫ nat_trans.map_homological_complex β c :=
by tidy

@[simp, reassoc] lemma nat_trans.map_homological_complex_naturality {c : complex_shape ι}
  {F G : V ⥤ W} [F.additive] [G.additive] (α : F ⟶ G) {C D : homological_complex V c} (f : C ⟶ D) :
  (F.map_homological_complex c).map f ≫ (nat_trans.map_homological_complex α c).app D =
    (nat_trans.map_homological_complex α c).app C ≫ (G.map_homological_complex c).map f :=
by tidy

end category_theory
