import category_theory.preadditive
import category_theory.limits.shapes.biproducts
import data.matrix.basic

open_locale classical

open category_theory
open category_theory.limits

universes v u

variables {C : Type u} [category.{v} C]

def hom_orthogonal {ι : Type*} (s : ι → C) : Prop :=
∀ i j, i ≠ j → subsingleton (s i ⟶ s j)

variables {ι : Type*} {s : ι → C}

def hom_orthogonal.eq_zero [has_zero_morphisms C] (o : hom_orthogonal s) {i j : ι} (w : i ≠ j) (f : s i ⟶ s j) :
  f = 0 :=
by { haveI := o i j w, apply subsingleton.elim, }

variables [has_zero_morphisms C] [has_finite_biproducts C]

noncomputable
def hom_orthogonal.matrix_decomposition {α β : Type*} [fintype α] [fintype β] (f : α → ι) (g : β → ι)
  (o : hom_orthogonal s) :
  (⨁ (s ∘ f) ⟶ ⨁ (s ∘ g)) ≃ Π (i : ι), matrix (f ⁻¹' {i}) (g ⁻¹' {i}) (End (s i)) :=
{ to_fun := λ z i j k,
    eq_to_hom (by { rcases j with ⟨j, ⟨⟩⟩, simp, }) ≫
      biproduct.components z j k ≫ eq_to_hom (by { rcases k with ⟨k, ⟨⟩⟩, simp, }),
  inv_fun := λ z, biproduct.matrix (λ j k, if h : f j = g k then
      z (f j) ⟨j, by simp⟩ ⟨k, by simp [h]⟩ ≫ eq_to_hom (by simp [h])
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
    ext i ⟨j, ⟨⟩⟩ ⟨k, w⟩,
    simp only [set.mem_preimage, set.mem_singleton_iff],
    simp [w.symm], refl,
  end, }

-- TODO additive version? linear version?

def brick (X : C) : Prop :=
∀ f : X ⟶ X, f ≠ 0 → is_iso f

structure semibrick {ι : Type*} (s : ι → C) :=
(brick : ∀ i, brick (s i))
(orthogonal : hom_orthogonal s)
