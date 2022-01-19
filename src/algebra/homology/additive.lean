/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.homology
import algebra.homology.single
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

/- TODO(jmc/Scott): the instance below doesn't have the correct defeq for `nsmul` and `zsmul`.
We should generalize `function.injective.add_comm_group` and friends.
For the `R`-linear version, it will be very convenient to have
a good definition of `nsmul` and `zsmul` that matches `smul`. -/

instance : add_comm_group (C ⟶ D) :=
function.injective.add_comm_group hom.f
  homological_complex.hom_f_injective (by tidy) (by tidy) (by tidy) (by tidy)

instance : preadditive (homological_complex V c) := {}

/-- The `i`-th component of a chain map, as an additive map from chain maps to morphisms. -/
@[simps]
def hom.f_add_monoid_hom {C₁ C₂ : homological_complex V c} (i : ι) :
  (C₁ ⟶ C₂) →+ (C₁.X i ⟶ C₂.X i) :=
add_monoid_hom.mk' (λ f, hom.f f i) (λ _ _, rfl)

end homological_complex

namespace homological_complex

instance eval_additive (i : ι) : (eval V c i).additive := {}

variables [has_zero_object V]

instance cycles_additive [has_equalizers V] : (cycles_functor V c i).additive := {}

variables [has_images V] [has_image_maps V]

instance boundaries_additive : (boundaries_functor V c i).additive := {}

variables [has_equalizers V] [has_cokernels V]

instance homology_additive : (homology_functor V c i).additive :=
{ map_zero' := λ C D, begin
    dsimp [homology_functor],
    ext,
    simp only [limits.cokernel.π_desc, limits.comp_zero, homology.π_map],
    convert zero_comp,
    ext,
    simp,
  end,
  map_add' := λ C D f g, begin
    dsimp [homology_functor],
    ext,
    simp only [homology.π_map, preadditive.comp_add, ←preadditive.add_comp],
    congr,
    ext, simp,
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
    d_comp_d' := λ i j k _ _, by rw [←F.map_comp, C.d_comp_d, F.map_zero], },
  map := λ C D f,
  { f := λ i, F.map (f.f i),
    comm' := λ i j h, by { dsimp,  rw [←F.map_comp, ←F.map_comp, f.comm], }, }, }.

instance functor.map_homogical_complex_additive
  (F : V ⥤ W) [F.additive] (c : complex_shape ι) : (F.map_homological_complex c).additive := {}

/--
A natural transformation between functors induces a natural transformation
between those functors applied to homological complexes.
-/
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

variables [has_zero_object V] {W : Type*} [category W] [preadditive W] [has_zero_object W]

namespace homological_complex

/--
Turning an object into a complex supported at `j` then applying a functor is
the same as applying the functor then forming the complex.
-/
def single_map_homological_complex (F : V ⥤ W) [F.additive] (c : complex_shape ι) (j : ι):
  single V c j ⋙ F.map_homological_complex _ ≅ F ⋙ single W c j :=
nat_iso.of_components (λ X,
{ hom := { f := λ i, if h : i = j then
    eq_to_hom (by simp [h])
  else
    0, },
  inv := { f := λ i, if h : i = j then
    eq_to_hom (by simp [h])
  else
    0, },
  hom_inv_id' := begin
    ext i,
    dsimp,
    split_ifs with h,
    { simp [h] },
    { rw [zero_comp, if_neg h],
      exact (zero_of_source_iso_zero _ F.map_zero_object).symm, },
  end,
  inv_hom_id' := begin
    ext i,
    dsimp,
    split_ifs with h,
    { simp [h] },
    { rw [zero_comp, if_neg h],
      simp, },
  end, })
  (λ X Y f, begin
    ext i,
    dsimp,
    split_ifs with h; simp [h],
  end).

variables (F : V ⥤ W) [functor.additive F] (c)

@[simp] lemma single_map_homological_complex_hom_app_self (j : ι) (X : V) :
  ((single_map_homological_complex F c j).hom.app X).f j = eq_to_hom (by simp) :=
by simp [single_map_homological_complex]
@[simp] lemma single_map_homological_complex_hom_app_ne
  {i j : ι} (h : i ≠ j) (X : V) :
  ((single_map_homological_complex F c j).hom.app X).f i = 0 :=
by simp [single_map_homological_complex, h]
@[simp] lemma single_map_homological_complex_inv_app_self (j : ι) (X : V) :
  ((single_map_homological_complex F c j).inv.app X).f j = eq_to_hom (by simp) :=
by simp [single_map_homological_complex]
@[simp] lemma single_map_homological_complex_inv_app_ne
  {i j : ι} (h : i ≠ j) (X : V):
  ((single_map_homological_complex F c j).inv.app X).f i = 0 :=
by simp [single_map_homological_complex, h]

end homological_complex

namespace chain_complex

-- TODO: dualize to cochain complexes

/--
Turning an object into a chain complex supported at zero then applying a functor is
the same as applying the functor then forming the complex.
-/
def single₀_map_homological_complex (F : V ⥤ W) [F.additive] :
  single₀ V ⋙ F.map_homological_complex _ ≅ F ⋙ single₀ W :=
nat_iso.of_components (λ X,
{ hom := { f := λ i, match i with
    | 0 := 𝟙 _
    | (i+1) := F.map_zero_object.hom
    end, },
  inv := { f := λ i, match i with
    | 0 := 𝟙 _
    | (i+1) := F.map_zero_object.inv
    end, },
  hom_inv_id' := begin
    ext (_|i),
    { unfold_aux, simp, },
    { unfold_aux,
      dsimp,
      simp only [comp_f, id_f, zero_comp],
      exact (zero_of_source_iso_zero _ F.map_zero_object).symm, }
  end,
  inv_hom_id' := by { ext (_|i); { unfold_aux, dsimp, simp, }, }, })
  (λ X Y f, by { ext (_|i); { unfold_aux, dsimp, simp, }, }).

@[simp] lemma single₀_map_homological_complex_hom_app_zero (F : V ⥤ W) [F.additive] (X : V) :
  ((single₀_map_homological_complex F).hom.app X).f 0 = 𝟙 _ := rfl
@[simp] lemma single₀_map_homological_complex_hom_app_succ
  (F : V ⥤ W) [F.additive] (X : V) (n : ℕ) :
  ((single₀_map_homological_complex F).hom.app X).f (n+1) = 0 := rfl
@[simp] lemma single₀_map_homological_complex_inv_app_zero (F : V ⥤ W) [F.additive] (X : V) :
  ((single₀_map_homological_complex F).inv.app X).f 0 = 𝟙 _ := rfl
@[simp] lemma single₀_map_homological_complex_inv_app_succ
  (F : V ⥤ W) [F.additive] (X : V) (n : ℕ) :
  ((single₀_map_homological_complex F).inv.app X).f (n+1) = 0 := rfl

end chain_complex
