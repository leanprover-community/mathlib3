/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive.default
import category_theory.preadditive.single_obj
import category_theory.abelian.additive_functor
import category_theory.limits.shapes.biproducts
import algebra.big_operators.basic
import data.matrix.notation

/-!
# Matrices over a category.

When `C` is a preadditive category, `Mat_ C` is the preadditive categoriy
whose objects are finite tuples of objects in `C`, and
whose morphisms are matrices of morphisms from `C`.

-/

open category_theory category_theory.preadditive
open_locale big_operators
noncomputable theory

universes w v₁ v₂ u₁ u₂
variables (C : Type u₁) [category.{v₁} C] [preadditive C]

/--
An object in `Mat_ C` is a finite tuple of objects in `C`.
-/
structure Mat_ : Type (max (v₁+1) u₁) :=
(ι : Type v₁)
[F : fintype ι]
[D : decidable_eq ι]
(X : ι → C)

attribute [instance] Mat_.F Mat_.D

namespace Mat_

variables {C}

/-- A morphism in `Mat_ C` is a dependently typed matrix of morphisms. -/
def hom (M N : Mat_ C) : Type v₁ := dmatrix M.ι N.ι (λ i j, M.X i ⟶ N.X j)

namespace hom

/-- The identity matrix consists of identity morphisms on the diagonal, and zeros elsewhere. -/
def id (M : Mat_ C) : hom M M := λ i j, if h : i = j then eq_to_hom (congr_arg M.X h) else 0

/-- Composition of matrices using matrix multiplication. -/
def comp {M N K : Mat_ C} (f : hom M N) (g : hom N K) : hom M K :=
λ i k, ∑ j : N.ι, f i j ≫ g j k

end hom

section
local attribute [simp] hom.id hom.comp

instance : category.{v₁} (Mat_ C) :=
{ hom := hom,
  id := hom.id,
  comp := λ M N K f g, f.comp g,
  id_comp' := λ M N f, by simp [dite_comp],
  comp_id' := λ M N f, by simp [comp_dite],
  assoc' := λ M N K L f g h, begin
    ext i k,
    simp_rw [hom.comp, sum_comp, comp_sum, category.assoc],
    rw finset.sum_comm,
  end, }.


lemma id_apply (M : Mat_ C) (i j : M.ι) :
  (𝟙 M : hom M M) i j = if h : i = j then eq_to_hom (congr_arg M.X h) else 0 :=
rfl

@[simp] lemma id_apply_self (M : Mat_ C) (i : M.ι) :
  (𝟙 M : hom M M) i i = 𝟙 _ :=
by simp [id_apply]

@[simp] lemma id_apply_of_ne (M : Mat_ C) (i j : M.ι) (h : i ≠ j) :
  (𝟙 M : hom M M) i j = 0 :=
by simp [id_apply, h]

@[simp] lemma comp_apply {M N K : Mat_ C} (f : M ⟶ N) (g : N ⟶ K) (i k) :
  (f ≫ g) i k = ∑ j : N.ι, f i j ≫ g j k := rfl

end

instance : preadditive (Mat_ C) :=
{ hom_group := λ M N, by { change add_comm_group (dmatrix M.ι N.ι _), apply_instance, },
  add_comp' := λ M N K f f' g, by { ext, simp [finset.sum_add_distrib], },
  comp_add' := λ M N K f g g', by { ext, simp [finset.sum_add_distrib], }, }

@[simp] lemma add_apply {M N : Mat_ C} (f g : M ⟶ N) (i j) : (f + g) i j = f i j + g i j := rfl

open category_theory.limits

/--
We now prove that `Mat_ C` has finite biproducts.

Be warned, however, that `Mat_ C` is not necessarily Krull-Schmidt,
and so the internal indexing of biproduct may have nothing to do with the external indexing!
-/
instance has_finite_biproducts : has_finite_biproducts (Mat_ C) :=
{ has_biproducts_of_shape := λ J 𝒟 ℱ, by exactI
  { has_biproduct := λ f,
    has_biproduct_of_total
    { X := ⟨Σ j : J, (f j).ι, λ p, (f p.1).X p.2⟩,
      π := λ j x y,
      begin
        dsimp at x ⊢,
        refine if h : x.1 = j then _ else 0,
        refine if h' : (@eq.rec J x.1 (λ j, (f j).ι) x.2 _ h) = y then _ else 0,
        apply eq_to_hom,
        substs h h', -- Notice we were careful not to use `subst` until we had a goal in `Prop`.
      end,
      ι := λ j x y,
      begin
        dsimp at y ⊢,
        refine if h : y.1 = j then _ else 0,
        refine if h' : (@eq.rec J y.1 (λ j, (f j).ι) y.2 _ h) = x then _ else 0,
        apply eq_to_hom,
        substs h h',
      end,
      ι_π := λ j j',
      begin
        ext x y,
        dsimp,
        simp_rw [dite_comp, comp_dite],
        simp only [if_t_t, dite_eq_ite, dif_ctx_congr, limits.comp_zero, limits.zero_comp,
          eq_to_hom_trans, finset.sum_congr],
        erw finset.sum_sigma,
        dsimp,
        simp only [if_congr, if_true, dif_ctx_congr, finset.sum_dite_irrel, finset.mem_univ,
          finset.sum_const_zero, finset.sum_congr, finset.sum_dite_eq'],
        split_ifs with h h',
        { substs h h', simp, },
        { subst h, simp at h', simp [h'], },
        { refl, },
      end, }
    begin
      funext i₁,
      dsimp at i₁ ⊢,
      rcases i₁ with ⟨j₁, i₁⟩,
      -- I'm not sure why we can't just `simp` by `finset.sum_apply`: something doesn't quite match
      convert finset.sum_apply _ _ _,
      { refl, },
      { apply heq_of_eq,
        symmetry,
        funext i₂,
        rcases i₂ with ⟨j₂, i₂⟩,
        simp only [comp_apply, dite_comp, comp_dite,
          if_t_t, dite_eq_ite, if_congr, if_true, dif_ctx_congr,
          finset.sum_dite_irrel, finset.sum_dite_eq, finset.mem_univ, finset.sum_const_zero,
          finset.sum_congr, finset.sum_dite_eq, finset.sum_apply,
          limits.comp_zero, limits.zero_comp, eq_to_hom_trans, Mat_.id_apply],
        by_cases h : j₁ = j₂,
        { subst h, simp, },
        { simp [h], }, },
    end }}.

end Mat_

def Mat.of (R : Type*) [ring R] (n : ℕ) : Mat_ (single_obj R) :=
⟨fin n, λ _, punit.star⟩

@[derive [category, preadditive]]
def Mat (R : Type*) [ring R] := induced_category (Mat_ (single_obj R)) (Mat.of R)

example : matrix (fin 3) (fin 3) ℤ := 𝟙 (Mat.of ℤ 3)
example : Mat.of ℤ 2 ⟶ Mat.of ℤ 3 := ![![(37 : ℤ), 42, 0], ![0, 37, 42]]


namespace Mat_

variables (C)

@[simps]
def embedding : C ⥤ Mat_ C :=
{ obj := λ X, ⟨punit, λ _, X⟩,
  map := λ X Y f, λ _ _, f,
  map_id' := λ X, by { ext ⟨⟩ ⟨⟩, simp, },
  map_comp' := λ X Y Z f g, by { ext ⟨⟩ ⟨⟩, simp, }, }

namespace embedding

instance : faithful (embedding C) :=
{ map_injective' := λ X Y f g h, congr_fun (congr_fun h punit.star) punit.star, }

instance : full (embedding C) :=
{ preimage := λ X Y f, f punit.star punit.star, }

end embedding

open category_theory.limits

/--
Every object in `Mat_ C` is isomorphic to the biproduct of its summands.
-/
def iso_biproduct_embedding (M : Mat_ C) : M ≅ ⨁ (λ i, (embedding C).obj (M.X i)) :=
{ hom := biproduct.lift (λ i j k, if h : j = i then eq_to_hom (congr_arg M.X h) else 0),
  inv := biproduct.desc (λ i j k, if h : i = k then eq_to_hom (congr_arg M.X h) else 0),
  hom_inv_id' :=
  begin
    simp only [biproduct.lift_desc],
    funext i,
    dsimp,
    convert finset.sum_apply _ _ _,
    { dsimp, refl, },
    { apply heq_of_eq,
      symmetry,
      funext j,
      simp only [finset.sum_apply],
      dsimp,
      simp [dite_comp, comp_dite, Mat_.id_apply], }
  end,
  inv_hom_id' :=
  begin
    apply biproduct.hom_ext,
    intro i,
    apply biproduct.hom_ext',
    intro j,
    simp only [category.id_comp, category.assoc,
      biproduct.lift_π, biproduct.ι_desc_assoc, biproduct.ι_π],
    ext ⟨⟩ ⟨⟩,
    simp [dite_comp, comp_dite],
    split_ifs,
    { subst h, simp, },
    { simp [h], },
  end, }.

variables {C} {D : Type u₁} [category.{v₁} D] [preadditive D] [has_finite_biproducts D]

/-- Any additive functor `C ⥤ D` to a category `D` with finite biproducts extends to
a functor `Mat_ C ⥤ D`. -/
@[simps]
def lift (F : C ⥤ D) [functor.additive F] : Mat_ C ⥤ D :=
{ obj := λ X, ⨁ (λ i, F.obj (X.X i)),
  map := λ X Y f, biproduct.matrix (λ i j, F.map (f i j)),
  map_id' := λ X, begin
    ext i j,
    by_cases h : i = j,
    { subst h, simp, },
    { simp [h, Mat_.id_apply], },
  end,
  map_comp' := λ X Y Z f g, by { ext i j, simp, }, }.

instance lift_additive (F : C ⥤ D) [functor.additive F] : functor.additive (lift F) :=
{}

/-- An additive functor `C ⥤ D` factors through its lift to `Mat_ C ⥤ D`. -/
@[simps]
def embedding_lift_iso (F : C ⥤ D) [functor.additive F] : embedding C ⋙ lift F ≅ F :=
nat_iso.of_components (λ X,
  { hom := biproduct.desc (λ P, 𝟙 (F.obj X)),
    inv := biproduct.lift (λ P, 𝟙 (F.obj X)), })
  (by sorry).

/-- this is just `additive.map_biproduct`, which doesn't yet exist -/
def additive_obj_iso_biproduct (F : Mat_ C ⥤ D) [functor.additive F] (M : Mat_ C) :
  F.obj M ≅ ⨁ (λ i, F.obj ((embedding C).obj (M.X i))) :=
sorry

def lift_unique (F : C ⥤ D) [functor.additive F] (L : Mat_ C ⥤ D) [functor.additive L]
  (α : embedding C ⋙ L ≅ F) :
  L ≅ lift F :=
nat_iso.of_components
  (λ M, begin end)
  sorry

end Mat_
