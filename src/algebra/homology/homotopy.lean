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

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [has_zero_object V] [preadditive V]

variables {c : complex_shape ι} {C D E : homological_complex V c}
variables (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

section

/-- Auxiliary definition for `homotopy`. Use `homotopy.from_next` instead. -/
def from_next' (f : Π i j, C.X i ⟶ D.X j) (i j : ι) : C.X_next i ⟶ D.X j :=
match c.next i with
| none := 0
| some ⟨i',w⟩ := (C.X_next_iso w).hom ≫ f i' j
end

@[simp] lemma from_next'_zero (i j : ι) : from_next' (λ i j, (0 : C.X i ⟶ D.X j)) i j = 0 :=
begin
  dsimp [from_next'],
  rcases c.next i with ⟨⟩|⟨⟨i', w⟩⟩;
  { dsimp [from_next'._match_1], simp, },
end

/-- Auxiliary definition for `homotopy`. Use `homotopy.to_prev` instead. -/
def to_prev' (f : Π i j, C.X i ⟶ D.X j) (i j : ι) : C.X i ⟶ D.X_prev j :=
match c.prev j with
| none := 0
| some ⟨j',w⟩ := f i j' ≫ (D.X_prev_iso w).inv
end

@[simp] lemma to_prev'_zero (i j : ι) : to_prev' (λ i j, (0 : C.X i ⟶ D.X j)) i j = 0 :=
begin
  dsimp [to_prev'],
  rcases c.prev j with ⟨⟩|⟨⟨j', w⟩⟩;
  { dsimp [to_prev'._match_1], simp, },
end

/--
A homotopy `h` between chain maps `f` and `g` consists of components `h i j : C.X i ⟶ D.X i`
which are zero unless `c.rel j i`,
satisfying the homotopy condition.
-/
@[nolint has_inhabited_instance]
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

@[refl]
def refl (f : C ⟶ D) : homotopy f f :=
{ hom := λ i j, 0,
  zero' := λ i j w, rfl,
  comm' := λ i, by simp, }

@[symm]
def symm {f g : C ⟶ D} (h : homotopy f g) : homotopy g f :=
{ hom := λ i j, -h.hom i j,
  zero' := λ i j w, by rw [h.zero i j w, neg_zero],
  comm' := λ i, begin
    sorry,
  end, }

@[trans]
def trans {e f g : C ⟶ D} (h : homotopy e f) (k : homotopy f g) : homotopy e g :=
{ hom := λ i j, h.hom i j + k.hom i j,
  zero' := λ i j w, by rw [h.zero i j w, k.zero i j w, zero_add],
  comm' := λ i, begin
    sorry,
  end, }

def comp_right {e f : C ⟶ D} (g : D ⟶ E) (h : homotopy e f) : homotopy (e ≫ g) (f ≫ g) :=
sorry

def comp_left (e : C ⟶ D) {f g : D ⟶ E} (h : homotopy f g) : homotopy (e ≫ f) (e ≫ g) :=
sorry

end homotopy

structure homotopy_equiv (C D : homological_complex V c) :=
(hom : C ⟶ D)
(inv : D ⟶ C)
(homotopy_hom_inv_id : homotopy (hom ≫ inv) (𝟙 C))
(homotopy_inv_hom_id : homotopy (inv ≫ hom) (𝟙 D))

variables [has_equalizers V] [has_cokernels V] [has_images V] [has_image_maps V]

/--
Homotopic maps induce the same map on homology.
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

/-- Homotopy equivalent complexes have isomorphic homologies. -/
def homology_obj_iso_of_homotopy_equiv (f : homotopy_equiv C D) (i : ι) :
  (homology_functor V c i).obj C ≅ (homology_functor V c i).obj D :=
{ hom := (homology_functor V c i).map f.hom,
  inv := (homology_functor V c i).map f.inv,
  hom_inv_id' := begin
    rw [←functor.map_comp, homology_map_eq_of_homotopy f.homotopy_hom_inv_id,
      category_theory.functor.map_id],
  end,
  inv_hom_id' := begin
    rw [←functor.map_comp, homology_map_eq_of_homotopy f.homotopy_inv_hom_id,
      category_theory.functor.map_id],
  end, }

end

namespace category_theory

variables {W : Type*} [category W] [preadditive W] [has_zero_object W]

/-- An additive functor induces a functor between homological complexes. -/
@[simps]
def functor.map_homotopy (F : V ⥤ W) [F.additive] {f g : C ⟶ D} (h : homotopy f g) :
  homotopy ((F.map_homological_complex c).map f) ((F.map_homological_complex c).map g) :=
{ hom := λ i j, F.map (h.hom i j),
  zero' := λ i j w, by { rw [h.zero i j w, F.map_zero], },
  comm' := λ i, begin dsimp, sorry, end, }

/-- An additive functor preserves homotopy equivalences. -/
def functor.map_homotopy_equiv (F : V ⥤ W) [F.additive] (h : homotopy_equiv C D) :
  homotopy_equiv ((F.map_homological_complex c).obj C) ((F.map_homological_complex c).obj D) :=
{ hom := (F.map_homological_complex c).map h.hom,
  inv := (F.map_homological_complex c).map h.inv,
  homotopy_hom_inv_id := begin
    rw [←(F.map_homological_complex c).map_comp, ←(F.map_homological_complex c).map_id],
    exact F.map_homotopy h.homotopy_hom_inv_id,
  end,
  homotopy_inv_hom_id := begin
    rw [←(F.map_homological_complex c).map_comp, ←(F.map_homological_complex c).map_id],
    exact F.map_homotopy h.homotopy_inv_hom_id,
  end }

end category_theory
