/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.additive

/-!
# Chain homotopies

We define chain homotopies, and prove that homotopic chain maps induce the same map on homology.
-/

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

section

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_object V] [preadditive V]

variables {c : complex_shape ι} {C D E : homological_complex V c}
variables (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

/-- Auxiliary definition for `homotopy`. Use `homotopy.from_next` instead. -/
def from_next' (f : Π i j, C.X i ⟶ D.X j) (i j : ι) : C.X_next i ⟶ D.X j :=
match c.next i with
| none := 0
| some ⟨i',w⟩ := (C.X_next_iso w).hom ≫ f i' j
end

/-- Auxiliary definition for `homotopy`. Use `homotopy.to_prev` instead. -/
def to_prev' (f : Π i j, C.X i ⟶ D.X j) (i j : ι) : C.X i ⟶ D.X_prev j :=
match c.prev j with
| none := 0
| some ⟨j',w⟩ := f i j' ≫ (D.X_prev_iso w).inv
end

/--
A homotopy `h` between chain maps `f` and `g` consists of components `h i j : C.X i ⟶ D.X i`
which are zero unless `c.rel j i`,
satisfying the homotopy condition.
-/
structure homotopy (f g : C ⟶ D) :=
(hom : Π i j, C.X i ⟶ D.X j)
(zero' : ∀ i j, ¬ c.rel j i → hom i j = 0 . obviously)
(comm' : ∀ i,
  f.f i = to_prev' hom i i ≫ D.d_to i + C.d_from i ≫ from_next' hom i i + g.f i . obviously')

variables {f g}
namespace homotopy

restate_axiom homotopy.zero'

/--
The component of a homotopy from `next i` to `j`.
-/
def from_next (h : homotopy f g) (i j : ι) : C.X_next i ⟶ D.X j :=
from_next' h.hom i j

/--
The component of a homotopy from `i` to `prev j`.
-/
def to_prev (h : homotopy f g) (i j : ι) : C.X i ⟶ D.X_prev j :=
to_prev' h.hom i j

lemma comm (h : homotopy f g) (i : ι) :
  f.f i = h.to_prev i i ≫ D.d_to i + C.d_from i ≫ h.from_next i i + g.f i :=
h.comm' i

end homotopy

variables [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

/--
Homotopic maps induced the same map on homology.
-/
theorem homology_map_eq_of_homotopy (h : homotopy f g) (i : ι) :
  (homology_functor V c i).map f = (homology_functor V c i).map g :=
begin
  dsimp [homology_functor],
  apply eq_of_sub_eq_zero,
  ext,
  dunfold cycles_map,
  simp only [comp_zero, preadditive.comp_sub, cokernel.π_desc],
  simp_rw [h.comm i],
  simp only [add_zero, zero_comp, cycles_arrow_d_from_assoc, preadditive.comp_add],
  rw [←preadditive.sub_comp],
  simp only [category_theory.subobject.factor_thru_add_sub_factor_thru_right],
  dsimp [cycles],
  erw [subobject.factor_thru_of_le (D.boundaries_le_cycles i)],
  { simp, },
  { rw [←category.assoc],
    apply image_subobject_factors_comp_self, },
end

end
