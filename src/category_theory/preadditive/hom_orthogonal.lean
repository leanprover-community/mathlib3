/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.linear.basic
import category_theory.preadditive.biproducts
import linear_algebra.matrix.invariant_basis_number

/-!
# Hom orthogonal families.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A family of objects in a category with zero morphisms is "hom orthogonal" if the only
morphism between distinct objects is the zero morphism.

We show that in any category with zero morphisms and finite biproducts,
a morphism between biproducts drawn from a hom orthogonal family `s : ι → C`
can be decomposed into a block diagonal matrix with entries in the endomorphism rings of the `s i`.

When the category is preadditive, this decomposition is an additive equivalence,
and intertwines composition and matrix multiplication.
When the category is `R`-linear, the decomposition is an `R`-linear equivalence.

If every object in the hom orthogonal family has an endomorphism ring with invariant basis number
(e.g. if each object in the family is simple, so its endomorphism ring is a division ring,
or otherwise if each endomorphism ring is commutative),
then decompositions of an object as a biproduct of the family have uniquely defined multiplicities.
We state this as:
```
lemma hom_orthogonal.equiv_of_iso (o : hom_orthogonal s) {f : α → ι} {g : β → ι}
  (i : ⨁ (λ a, s (f a)) ≅ ⨁ (λ b, s (g b))) : ∃ e : α ≃ β, ∀ a, g (e a) = f a
```

This is preliminary to defining semisimple categories.
-/

open_locale classical matrix

open category_theory.limits

universes v u

namespace category_theory

variables {C : Type u} [category.{v} C]

/-- A family of objects is "hom orthogonal" if
there is at most one morphism between distinct objects.

(In a category with zero morphisms, that must be the zero morphism.) -/
def hom_orthogonal {ι : Type*} (s : ι → C) : Prop :=
∀ i j, i ≠ j → subsingleton (s i ⟶ s j)

namespace hom_orthogonal

variables {ι : Type*} {s : ι → C}

lemma eq_zero [has_zero_morphisms C] (o : hom_orthogonal s)
  {i j : ι} (w : i ≠ j) (f : s i ⟶ s j) : f = 0 :=
by { haveI := o i j w, apply subsingleton.elim, }

section
variables [has_zero_morphisms C] [has_finite_biproducts C]

/-- Morphisms between two direct sums over a hom orthogonal family `s : ι → C`
are equivalent to block diagonal matrices,
with blocks indexed by `ι`,
and matrix entries in `i`-th block living in the endomorphisms of `s i`. -/
@[simps] noncomputable
def matrix_decomposition
  (o : hom_orthogonal s) {α β : Type} [fintype α] [fintype β] {f : α → ι} {g : β → ι} :
  (⨁ (λ a, s (f a)) ⟶ ⨁ (λ b, s (g b))) ≃
    Π (i : ι), matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
{ to_fun := λ z i j k,
    eq_to_hom (by { rcases k with ⟨k, ⟨⟩⟩, simp, }) ≫
      biproduct.components z k j ≫ eq_to_hom (by { rcases j with ⟨j, ⟨⟩⟩, simp, }),
  inv_fun := λ z, biproduct.matrix (λ j k, if h : f j = g k then
      z (f j) ⟨k, by simp [h]⟩ ⟨j, by simp⟩ ≫ eq_to_hom (by simp [h])
    else
      0),
  left_inv := λ z, begin
    ext j k,
    simp only [category.assoc, biproduct.lift_π, biproduct.ι_matrix],
    split_ifs,
    { simp, refl, },
    { symmetry, apply o.eq_zero h, },
  end,
  right_inv := λ z, begin
    ext i ⟨j, w⟩ ⟨k, ⟨⟩⟩,
    simp only [set.mem_preimage, set.mem_singleton_iff],
    simp [w.symm], refl,
  end, }

end

section
variables [preadditive C] [has_finite_biproducts C]

/-- `hom_orthogonal.matrix_decomposition` as an additive equivalence. -/
@[simps] noncomputable
def matrix_decomposition_add_equiv
  (o : hom_orthogonal s) {α β : Type} [fintype α] [fintype β] {f : α → ι} {g : β → ι} :
  (⨁ (λ a, s (f a)) ⟶ ⨁ (λ b, s (g b))) ≃+
    Π (i : ι), matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
{ map_add' := λ w z, by { ext, dsimp [biproduct.components], simp, },
  ..o.matrix_decomposition, }.

@[simp]
lemma matrix_decomposition_id
  (o : hom_orthogonal s) {α : Type} [fintype α] {f : α → ι} (i : ι) :
  o.matrix_decomposition (𝟙 (⨁ (λ a, s (f a)))) i = 1 :=
begin
  ext ⟨b, ⟨⟩⟩ ⟨a⟩,
  simp only [set.mem_preimage, set.mem_singleton_iff] at j_property,
  simp only [category.comp_id, category.id_comp, category.assoc, End.one_def, eq_to_hom_refl,
    matrix.one_apply, hom_orthogonal.matrix_decomposition_apply, biproduct.components],
  split_ifs with h,
  { cases h, simp, },
  { convert comp_zero,
    simpa using biproduct.ι_π_ne _ (ne.symm h), },
end

lemma matrix_decomposition_comp
  (o : hom_orthogonal s)
  {α β γ : Type} [fintype α] [fintype β] [fintype γ] {f : α → ι} {g : β → ι} {h : γ → ι}
  (z : (⨁ (λ a, s (f a)) ⟶ ⨁ (λ b, s (g b)))) (w : (⨁ (λ b, s (g b)) ⟶ ⨁ (λ c, s (h c))))
  (i : ι) :
  o.matrix_decomposition (z ≫ w) i = o.matrix_decomposition w i ⬝ o.matrix_decomposition z i :=
begin
  ext ⟨c, ⟨⟩⟩ ⟨a⟩,
  simp only [set.mem_preimage, set.mem_singleton_iff] at j_property,
  simp only [matrix.mul_apply, limits.biproduct.components,
    hom_orthogonal.matrix_decomposition_apply,
    category.comp_id, category.id_comp, category.assoc, End.mul_def,
    eq_to_hom_refl, eq_to_hom_trans_assoc, finset.sum_congr],
  conv_lhs { rw [←category.id_comp w, ←biproduct.total], },
  simp only [preadditive.sum_comp, preadditive.comp_sum],
  apply finset.sum_congr_set,
  { intros, simp, refl, },
  { intros b nm,
    simp only [set.mem_preimage, set.mem_singleton_iff] at nm,
    simp only [category.assoc],
    convert comp_zero,
    convert comp_zero,
    convert comp_zero,
    convert comp_zero,
    apply o.eq_zero nm, },
end

section
variables {R : Type*} [semiring R] [linear R C]

/-- `hom_orthogonal.matrix_decomposition` as an `R`-linear equivalence. -/
@[simps] noncomputable
def matrix_decomposition_linear_equiv
(o : hom_orthogonal s)
  {α β : Type} [fintype α] [fintype β] {f : α → ι} {g : β → ι} :
  (⨁ (λ a, s (f a)) ⟶ ⨁ (λ b, s (g b))) ≃ₗ[R]
    Π (i : ι), matrix (g ⁻¹' {i}) (f ⁻¹' {i}) (End (s i)) :=
{ map_smul' := λ w z, by { ext, dsimp [biproduct.components], simp, },
  ..o.matrix_decomposition_add_equiv, }

end

/-!
The hypothesis that `End (s i)` has invariant basis number is automatically satisfied
if `s i` is simple (as then `End (s i)` is a division ring).
-/
variables [∀ i, invariant_basis_number (End (s i))]

/--
Given a hom orthogonal family `s : ι → C`
for which each `End (s i)` is a ring with invariant basis number (e.g. if each `s i` is simple),
if two direct sums over `s` are isomorphic, then they have the same multiplicities.
-/
lemma equiv_of_iso (o : hom_orthogonal s)
  {α β : Type} [fintype α] [fintype β] {f : α → ι} {g : β → ι}
  (i : ⨁ (λ a, s (f a)) ≅ ⨁ (λ b, s (g b))) :
  ∃ e : α ≃ β, ∀ a, g (e a) = f a :=
begin
  refine ⟨equiv.of_preimage_equiv _, λ a, equiv.of_preimage_equiv_map _ _⟩,
  intro c,
  apply nonempty.some,
  apply cardinal.eq.1,
  simp only [cardinal.mk_fintype, nat.cast_inj],
  exact matrix.square_of_invertible
    (o.matrix_decomposition i.inv c) (o.matrix_decomposition i.hom c)
    (by { rw ←o.matrix_decomposition_comp, simp, })
    (by { rw ←o.matrix_decomposition_comp, simp, })
end

end

end hom_orthogonal

end category_theory
