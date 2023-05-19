/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebra.homology.additive
import tactic.abel

/-!
# Chain homotopies

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define chain homotopies, and prove that homotopic chain maps induce the same map on homology.
-/

universes v u

open_locale classical
noncomputable theory

open category_theory category_theory.limits homological_complex

variables {ι : Type*}
variables {V : Type u} [category.{v} V] [preadditive V]

variables {c : complex_shape ι} {C D E : homological_complex V c}
variables (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

section

/-- The composition of `C.d i i' ≫ f i' i` if there is some `i'` coming after `i`,
and `0` otherwise. -/
def d_next (i : ι) : (Π i j, C.X i ⟶ D.X j) →+ (C.X i ⟶ D.X i) :=
add_monoid_hom.mk' (λ f, C.d i (c.next i) ≫ f (c.next i) i) $
λ f g, preadditive.comp_add _ _ _ _ _ _

/-- `f i' i` if `i'` comes after `i`, and 0 if there's no such `i'`.
Hopefully there won't be much need for this, except in `d_next_eq_d_from_from_next`
to see that `d_next` factors through `C.d_from i`. -/
def from_next (i : ι) : (Π i j, C.X i ⟶ D.X j) →+ (C.X_next i ⟶ D.X i) :=
add_monoid_hom.mk' (λ f, f (c.next i) i) $ λ f g, rfl

@[simp]
lemma d_next_eq_d_from_from_next (f : Π i j, C.X i ⟶ D.X j) (i : ι) :
  d_next i f = C.d_from i ≫ from_next i f := rfl

lemma d_next_eq (f : Π i j, C.X i ⟶ D.X j) {i i' : ι} (w : c.rel i i') :
  d_next i f = C.d i i' ≫ f i' i :=
by { obtain rfl := c.next_eq' w, refl }

@[simp] lemma d_next_comp_left (f : C ⟶ D) (g : Π i j, D.X i ⟶ E.X j) (i : ι) :
  d_next i (λ i j, f.f i ≫ g i j) = f.f i ≫ d_next i g :=
(f.comm_assoc _ _ _).symm

@[simp] lemma d_next_comp_right (f : Π i j, C.X i ⟶ D.X j) (g : D ⟶ E) (i : ι) :
  d_next i (λ i j, f i j ≫ g.f j) = d_next i f ≫ g.f i :=
(category.assoc _ _ _).symm

/-- The composition of `f j j' ≫ D.d j' j` if there is some `j'` coming before `j`,
and `0` otherwise. -/
def prev_d (j : ι) : (Π i j, C.X i ⟶ D.X j) →+ (C.X j ⟶ D.X j) :=
add_monoid_hom.mk' (λ f, f j (c.prev j) ≫ D.d (c.prev j) j) $
λ f g, preadditive.add_comp _ _ _ _ _ _

/-- `f j j'` if `j'` comes after `j`, and 0 if there's no such `j'`.
Hopefully there won't be much need for this, except in `d_next_eq_d_from_from_next`
to see that `d_next` factors through `C.d_from i`. -/
def to_prev (j : ι) : (Π i j, C.X i ⟶ D.X j) →+ (C.X j ⟶ D.X_prev j) :=
add_monoid_hom.mk' (λ f, f j (c.prev j)) $ λ f g, rfl

@[simp]
lemma prev_d_eq_to_prev_d_to (f : Π i j, C.X i ⟶ D.X j) (j : ι) :
  prev_d j f = to_prev j f ≫ D.d_to j := rfl

lemma prev_d_eq (f : Π i j, C.X i ⟶ D.X j) {j j' : ι} (w : c.rel j' j) :
  prev_d j f = f j j' ≫ D.d j' j :=
by { obtain rfl := c.prev_eq' w, refl }

@[simp] lemma prev_d_comp_left (f : C ⟶ D) (g : Π i j, D.X i ⟶ E.X j) (j : ι) :
  prev_d j (λ i j, f.f i ≫ g i j) = f.f j ≫ prev_d j g :=
category.assoc _ _ _

@[simp] lemma prev_d_comp_right (f : Π i j, C.X i ⟶ D.X j) (g : D ⟶ E) (j : ι) :
  prev_d j (λ i j, f i j ≫ g.f j) = prev_d j f ≫ g.f j :=
by { dsimp [prev_d], simp only [category.assoc, g.comm] }

lemma d_next_nat (C D : chain_complex V ℕ) (i : ℕ) (f : Π i j, C.X i ⟶ D.X j) :
  d_next i f = C.d i (i-1) ≫ f (i-1) i :=
begin
  dsimp [d_next],
  cases i,
  { simp only [shape, chain_complex.next_nat_zero, complex_shape.down_rel,
      nat.one_ne_zero, not_false_iff, zero_comp], },
  { dsimp only [nat.succ_eq_add_one],
    have : (complex_shape.down ℕ).next (i + 1) = i + 1 - 1,
    { rw chain_complex.next_nat_succ, refl },
    congr' 2, }
end

lemma prev_d_nat (C D : cochain_complex V ℕ) (i : ℕ) (f : Π i j, C.X i ⟶ D.X j) :
  prev_d i f = f i (i-1) ≫ D.d (i-1) i :=
begin
  dsimp [prev_d],
  cases i,
  { simp only [shape, cochain_complex.prev_nat_zero, complex_shape.up_rel,
      nat.one_ne_zero, not_false_iff, comp_zero]},
  { dsimp only [nat.succ_eq_add_one],
    have : (complex_shape.up ℕ).prev (i + 1) = i + 1 - 1,
    { rw cochain_complex.prev_nat_succ, refl },
    congr' 2, },
end

/--
A homotopy `h` between chain maps `f` and `g` consists of components `h i j : C.X i ⟶ D.X j`
which are zero unless `c.rel j i`, satisfying the homotopy condition.
-/
@[ext, nolint has_nonempty_instance]
structure homotopy (f g : C ⟶ D) :=
(hom : Π i j, C.X i ⟶ D.X j)
(zero' : ∀ i j, ¬ c.rel j i → hom i j = 0 . obviously)
(comm : ∀ i, f.f i = d_next i hom + prev_d i hom + g.f i . obviously')

variables {f g}
namespace homotopy

restate_axiom homotopy.zero'

/--
`f` is homotopic to `g` iff `f - g` is homotopic to `0`.
-/
def equiv_sub_zero : homotopy f g ≃ homotopy (f - g) 0 :=
{ to_fun := λ h,
  { hom := λ i j, h.hom i j,
    zero' := λ i j w, h.zero _ _ w,
    comm := λ i, by simp [h.comm] },
  inv_fun := λ h,
  { hom := λ i j, h.hom i j,
    zero' := λ i j w, h.zero _ _ w,
    comm := λ i, by simpa [sub_eq_iff_eq_add] using h.comm i },
  left_inv := by tidy,
  right_inv := by tidy, }

/-- Equal chain maps are homotopic. -/
@[simps]
def of_eq (h : f = g) : homotopy f g :=
{ hom := 0,
  zero' := λ _ _ _, rfl,
  comm := λ _, by simp only [add_monoid_hom.map_zero, zero_add, h] }

/-- Every chain map is homotopic to itself. -/
@[simps, refl]
def refl (f : C ⟶ D) : homotopy f f :=
of_eq (rfl : f = f)

/-- `f` is homotopic to `g` iff `g` is homotopic to `f`. -/
@[simps, symm]
def symm {f g : C ⟶ D} (h : homotopy f g) : homotopy g f :=
{ hom := -h.hom,
  zero' := λ i j w, by rw [pi.neg_apply, pi.neg_apply, h.zero i j w, neg_zero],
  comm := λ i, by rw [add_monoid_hom.map_neg, add_monoid_hom.map_neg, h.comm, ← neg_add,
      ← add_assoc, neg_add_self, zero_add] }

/-- homotopy is a transitive relation. -/
@[simps, trans]
def trans {e f g : C ⟶ D} (h : homotopy e f) (k : homotopy f g) : homotopy e g :=
{ hom := h.hom + k.hom,
  zero' := λ i j w, by rw [pi.add_apply, pi.add_apply, h.zero i j w, k.zero i j w, zero_add],
  comm := λ i, by { rw [add_monoid_hom.map_add, add_monoid_hom.map_add, h.comm, k.comm], abel }, }

/-- the sum of two homotopies is a homotopy between the sum of the respective morphisms. -/
@[simps]
def add {f₁ g₁ f₂ g₂ : C ⟶ D}
  (h₁ : homotopy f₁ g₁) (h₂ : homotopy f₂ g₂) : homotopy (f₁+f₂) (g₁+g₂) :=
{ hom := h₁.hom + h₂.hom,
  zero' := λ i j hij, by
    rw [pi.add_apply, pi.add_apply, h₁.zero' i j hij, h₂.zero' i j hij, add_zero],
  comm := λ i, by
    { simp only [homological_complex.add_f_apply, h₁.comm, h₂.comm,
        add_monoid_hom.map_add],
      abel, }, }

/-- homotopy is closed under composition (on the right) -/
@[simps]
def comp_right {e f : C ⟶ D} (h : homotopy e f) (g : D ⟶ E) : homotopy (e ≫ g) (f ≫ g) :=
{ hom := λ i j, h.hom i j ≫ g.f j,
  zero' := λ i j w, by rw [h.zero i j w, zero_comp],
  comm := λ i, by simp only [h.comm i, d_next_comp_right, preadditive.add_comp,
    prev_d_comp_right, comp_f], }

/-- homotopy is closed under composition (on the left) -/
@[simps]
def comp_left {f g : D ⟶ E} (h : homotopy f g) (e : C ⟶ D) : homotopy (e ≫ f) (e ≫ g) :=
{ hom := λ i j, e.f i ≫ h.hom i j,
  zero' := λ i j w, by rw [h.zero i j w, comp_zero],
  comm := λ i, by simp only [h.comm i, d_next_comp_left, preadditive.comp_add,
    prev_d_comp_left, comp_f], }

/-- homotopy is closed under composition -/
@[simps]
def comp {C₁ C₂ C₃ : homological_complex V c} {f₁ g₁ : C₁ ⟶ C₂} {f₂ g₂ : C₂ ⟶ C₃}
  (h₁ : homotopy f₁ g₁) (h₂ : homotopy f₂ g₂) : homotopy (f₁ ≫ f₂) (g₁ ≫ g₂) :=
(h₁.comp_right _).trans (h₂.comp_left _)

/-- a variant of `homotopy.comp_right` useful for dealing with homotopy equivalences. -/
@[simps]
def comp_right_id {f : C ⟶ C} (h : homotopy f (𝟙 C)) (g : C ⟶ D) : homotopy (f ≫ g) g :=
(h.comp_right g).trans (of_eq $ category.id_comp _)

/-- a variant of `homotopy.comp_left` useful for dealing with homotopy equivalences. -/
@[simps]
def comp_left_id {f : D ⟶ D} (h : homotopy f (𝟙 D)) (g : C ⟶ D) : homotopy (g ≫ f) g :=
(h.comp_left g).trans (of_eq $ category.comp_id _)

/-!
Null homotopic maps can be constructed using the formula `hd+dh`. We show that
these morphisms are homotopic to `0` and provide some convenient simplification
lemmas that give a degreewise description of `hd+dh`, depending on whether we have
two differentials going to and from a certain degree, only one, or none.
-/

/-- The null homotopic map associated to a family `hom` of morphisms `C_i ⟶ D_j`.
This is the same datum as for the field `hom` in the structure `homotopy`. For
this definition, we do not need the field `zero` of that structure
as this definition uses only the maps `C_i ⟶ C_j` when `c.rel j i`. -/
def null_homotopic_map (hom : Π i j, C.X i ⟶ D.X j) : C ⟶ D :=
{ f      := λ i, d_next i hom + prev_d i hom,
  comm'  := λ i j hij,
  begin
    have eq1 : prev_d i hom ≫ D.d i j = 0,
    { simp only [prev_d, add_monoid_hom.mk'_apply, category.assoc, d_comp_d, comp_zero], },
    have eq2 : C.d i j ≫ d_next j hom = 0,
    { simp only [d_next, add_monoid_hom.mk'_apply, d_comp_d_assoc, zero_comp], },
    rw [d_next_eq hom hij, prev_d_eq hom hij, preadditive.comp_add, preadditive.add_comp,
      eq1, eq2, add_zero, zero_add, category.assoc],
  end }

/-- Variant of `null_homotopic_map` where the input consists only of the
relevant maps `C_i ⟶ D_j` such that `c.rel j i`. -/
def null_homotopic_map' (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) : C ⟶ D :=
null_homotopic_map (λ i j, dite (c.rel j i) (h i j) (λ _, 0))

/-- Compatibility of `null_homotopic_map` with the postcomposition by a morphism
of complexes. -/
lemma null_homotopic_map_comp (hom : Π i j, C.X i ⟶ D.X j) (g : D ⟶ E) :
null_homotopic_map hom ≫ g = null_homotopic_map (λ i j, hom i j ≫ g.f j) :=
begin
  ext n,
  dsimp [null_homotopic_map, from_next, to_prev, add_monoid_hom.mk'_apply],
  simp only [preadditive.add_comp, category.assoc, g.comm],
end

/-- Compatibility of `null_homotopic_map'` with the postcomposition by a morphism
of complexes. -/
lemma null_homotopic_map'_comp (hom : Π i j, c.rel j i → (C.X i ⟶ D.X j)) (g : D ⟶ E) :
null_homotopic_map' hom ≫ g = null_homotopic_map' (λ i j hij, hom i j hij ≫ g.f j) :=
begin
  ext n,
  erw null_homotopic_map_comp,
  congr',
  ext i j,
  split_ifs,
  { refl, },
  { rw zero_comp, },
end

/-- Compatibility of `null_homotopic_map` with the precomposition by a morphism
of complexes. -/
lemma comp_null_homotopic_map (f : C ⟶ D) (hom : Π i j, D.X i ⟶ E.X j) :
f ≫ null_homotopic_map hom = null_homotopic_map (λ i j, f.f i ≫ hom i j) :=
begin
  ext n,
  dsimp [null_homotopic_map, from_next, to_prev, add_monoid_hom.mk'_apply],
  simp only [preadditive.comp_add, category.assoc, f.comm_assoc],
end

/-- Compatibility of `null_homotopic_map'` with the precomposition by a morphism
of complexes. -/
lemma comp_null_homotopic_map' (f : C ⟶ D) (hom : Π i j, c.rel j i → (D.X i ⟶ E.X j)) :
f ≫ null_homotopic_map' hom = null_homotopic_map' (λ i j hij, f.f i ≫ hom i j hij) :=
begin
  ext n,
  erw comp_null_homotopic_map,
  congr',
  ext i j,
  split_ifs,
  { refl, },
  { rw comp_zero, },
end

/-- Compatibility of `null_homotopic_map` with the application of additive functors -/
lemma map_null_homotopic_map {W : Type*} [category W] [preadditive W]
  (G : V ⥤ W) [G.additive] (hom : Π i j, C.X i ⟶ D.X j) :
  (G.map_homological_complex c).map (null_homotopic_map hom) =
  null_homotopic_map (λ i j, G.map (hom i j)) :=
begin
  ext i,
  dsimp [null_homotopic_map, d_next, prev_d],
  simp only [G.map_comp, functor.map_add],
end

/-- Compatibility of `null_homotopic_map'` with the application of additive functors -/
lemma map_null_homotopic_map' {W : Type*} [category W] [preadditive W]
  (G : V ⥤ W) [G.additive] (hom : Π i j, c.rel j i → (C.X i ⟶ D.X j)) :
  (G.map_homological_complex c).map (null_homotopic_map' hom) =
  null_homotopic_map' (λ i j hij, G.map (hom i j hij)) :=
begin
  ext n,
  erw map_null_homotopic_map,
  congr',
  ext i j,
  split_ifs,
  { refl, },
  { rw G.map_zero, }
end

/-- Tautological construction of the `homotopy` to zero for maps constructed by
`null_homotopic_map`, at least when we have the `zero'` condition. -/
@[simps]
def null_homotopy (hom : Π i j, C.X i ⟶ D.X j) (zero' : ∀ i j, ¬ c.rel j i → hom i j = 0) :
  homotopy (null_homotopic_map hom) 0 :=
{ hom := hom,
  zero' := zero',
  comm := by { intro i, rw [homological_complex.zero_f_apply, add_zero], refl, }, }

/-- Homotopy to zero for maps constructed with `null_homotopic_map'` -/
@[simps]
def null_homotopy' (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) :
  homotopy (null_homotopic_map' h) 0 :=
begin
  apply null_homotopy (λ i j, dite (c.rel j i) (h i j) (λ _, 0)),
  intros i j hij,
  dsimp,
  rw [dite_eq_right_iff],
  intro hij',
  exfalso,
  exact hij hij',
end

/-! This lemma and the following ones can be used in order to compute
the degreewise morphisms induced by the null homotopic maps constructed
with `null_homotopic_map` or `null_homotopic_map'` -/
@[simp]
lemma null_homotopic_map_f {k₂ k₁ k₀ : ι} (r₂₁ : c.rel k₂ k₁) (r₁₀ : c.rel k₁ k₀)
  (hom : Π i j, C.X i ⟶ D.X j) :
  (null_homotopic_map hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁ + hom k₁ k₂ ≫ D.d k₂ k₁ :=
by { dsimp only [null_homotopic_map], rw [d_next_eq hom r₁₀, prev_d_eq hom r₂₁], }

@[simp]
lemma null_homotopic_map'_f {k₂ k₁ k₀  : ι} (r₂₁ : c.rel k₂ k₁) (r₁₀ : c.rel k₁ k₀)
  (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) :
  (null_homotopic_map' h).f k₁ = C.d k₁ k₀ ≫ h k₀ k₁ r₁₀ + h k₁ k₂ r₂₁ ≫ D.d k₂ k₁ :=
begin
  simp only [← null_homotopic_map'],
  rw null_homotopic_map_f r₂₁ r₁₀ (λ i j, dite (c.rel j i) (h i j) (λ _, 0)),
  dsimp,
  split_ifs,
  refl,
end

@[simp]
lemma null_homotopic_map_f_of_not_rel_left {k₁ k₀ : ι} (r₁₀ : c.rel k₁ k₀)
  (hk₀ : ∀ l : ι, ¬c.rel k₀ l)
  (hom : Π i j, C.X i ⟶ D.X j) :
  (null_homotopic_map hom).f k₀ = hom k₀ k₁ ≫ D.d k₁ k₀ :=
begin
  dsimp only [null_homotopic_map],
  rw [prev_d_eq hom r₁₀, d_next, add_monoid_hom.mk'_apply, C.shape, zero_comp, zero_add],
  exact hk₀ _
end

@[simp]
lemma null_homotopic_map'_f_of_not_rel_left {k₁ k₀ : ι} (r₁₀ : c.rel k₁ k₀)
  (hk₀ : ∀ l : ι, ¬c.rel k₀ l)
  (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) :
  (null_homotopic_map' h).f k₀ = h k₀ k₁ r₁₀ ≫ D.d k₁ k₀ :=
begin
  simp only [← null_homotopic_map'],
  rw null_homotopic_map_f_of_not_rel_left r₁₀ hk₀ (λ i j, dite (c.rel j i) (h i j) (λ _, 0)),
  dsimp,
  split_ifs,
  refl,
end

@[simp]
lemma null_homotopic_map_f_of_not_rel_right {k₁ k₀ : ι} (r₁₀ : c.rel k₁ k₀)
  (hk₁ : ∀ l : ι, ¬c.rel l k₁)
  (hom : Π i j, C.X i ⟶ D.X j) :
  (null_homotopic_map hom).f k₁ = C.d k₁ k₀ ≫ hom k₀ k₁ :=
begin
  dsimp only [null_homotopic_map],
  rw [d_next_eq hom r₁₀, prev_d, add_monoid_hom.mk'_apply, D.shape, comp_zero, add_zero],
  exact hk₁ _,
end

@[simp]
lemma null_homotopic_map'_f_of_not_rel_right {k₁ k₀ : ι} (r₁₀ : c.rel k₁ k₀)
  (hk₁ : ∀ l : ι, ¬c.rel l k₁)
  (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) :
  (null_homotopic_map' h).f k₁ = C.d k₁ k₀ ≫ h k₀ k₁ r₁₀ :=
begin
  simp only [← null_homotopic_map'],
  rw null_homotopic_map_f_of_not_rel_right r₁₀ hk₁ (λ i j, dite (c.rel j i) (h i j) (λ _, 0)),
  dsimp,
  split_ifs,
  refl,
end

@[simp]
lemma null_homotopic_map_f_eq_zero {k₀ : ι}
  (hk₀ : ∀ l : ι, ¬c.rel k₀ l) (hk₀' : ∀ l : ι, ¬c.rel l k₀)
  (hom : Π i j, C.X i ⟶ D.X j) :
  (null_homotopic_map hom).f k₀ = 0 :=
begin
  dsimp [null_homotopic_map, d_next, prev_d],
  rw [C.shape, D.shape, zero_comp, comp_zero, add_zero]; apply_assumption,
end

@[simp]
lemma null_homotopic_map'_f_eq_zero {k₀ : ι}
  (hk₀ : ∀ l : ι, ¬c.rel k₀ l) (hk₀' : ∀ l : ι, ¬c.rel l k₀)
  (h : Π i j, c.rel j i → (C.X i ⟶ D.X j)) :
  (null_homotopic_map' h).f k₀ = 0 :=
begin
  simp only [← null_homotopic_map'],
  exact null_homotopic_map_f_eq_zero hk₀ hk₀'
    (λ i j, dite (c.rel j i) (h i j) (λ _, 0)),
end

/-!
`homotopy.mk_inductive` allows us to build a homotopy of chain complexes inductively,
so that as we construct each component, we have available the previous two components,
and the fact that they satisfy the homotopy condition.

To simplify the situation, we only construct homotopies of the form `homotopy e 0`.
`homotopy.equiv_sub_zero` can provide the general case.

Notice however, that this construction does not have particularly good definitional properties:
we have to insert `eq_to_hom` in several places.
Hopefully this is okay in most applications, where we only need to have the existence of some
homotopy.
-/
section mk_inductive

variables {P Q : chain_complex V ℕ}

@[simp] lemma prev_d_chain_complex (f : Π i j, P.X i ⟶ Q.X j) (j : ℕ) :
  prev_d j f = f j (j+1) ≫ Q.d _ _ :=
begin
  dsimp [prev_d],
  have : (complex_shape.down ℕ).prev j = j + 1 := chain_complex.prev ℕ j,
  congr' 2,
end

@[simp] lemma d_next_succ_chain_complex (f : Π i j, P.X i ⟶ Q.X j) (i : ℕ) :
  d_next (i+1) f = P.d _ _ ≫ f i (i+1) :=
begin
  dsimp [d_next],
  have : (complex_shape.down ℕ).next (i + 1) = i := chain_complex.next_nat_succ _,
  congr' 2,
end

@[simp] lemma d_next_zero_chain_complex (f : Π i j, P.X i ⟶ Q.X j) :
  d_next 0 f = 0 :=
begin
  dsimp [d_next],
  rw [P.shape, zero_comp],
  rw chain_complex.next_nat_zero, dsimp, dec_trivial,
end

variables (e : P ⟶ Q)
  (zero : P.X 0 ⟶ Q.X 1)
  (comm_zero : e.f 0 = zero ≫ Q.d 1 0)
  (one : P.X 1 ⟶ Q.X 2)
  (comm_one : e.f 1 = P.d 1 0 ≫ zero + one ≫ Q.d 2 1)
  (succ : ∀ (n : ℕ)
    (p : Σ' (f : P.X n ⟶ Q.X (n+1)) (f' : P.X (n+1) ⟶ Q.X (n+2)),
      e.f (n+1) = P.d (n+1) n ≫ f + f' ≫ Q.d (n+2) (n+1)),
    Σ' f'' : P.X (n+2) ⟶ Q.X (n+3), e.f (n+2) = P.d (n+2) (n+1) ≫ p.2.1 + f'' ≫ Q.d (n+3) (n+2))

include comm_one comm_zero

/--
An auxiliary construction for `mk_inductive`.

Here we build by induction a family of diagrams,
but don't require at the type level that these successive diagrams actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a homotopy)
in `mk_inductive`.

At this stage, we don't check the homotopy condition in degree 0,
because it "falls off the end", and is easier to treat using `X_next` and `X_prev`,
which we do in `mk_inductive_aux₂`.
-/
@[simp, nolint unused_arguments]
def mk_inductive_aux₁ :
  Π n, Σ' (f : P.X n ⟶ Q.X (n+1)) (f' : P.X (n+1) ⟶ Q.X (n+2)),
    e.f (n+1) = P.d (n+1) n ≫ f + f' ≫ Q.d (n+2) (n+1)
| 0 := ⟨zero, one, comm_one⟩
| 1 := ⟨one, (succ 0 ⟨zero, one, comm_one⟩).1, (succ 0 ⟨zero, one, comm_one⟩).2⟩
| (n+2) :=
  ⟨(mk_inductive_aux₁ (n+1)).2.1,
    (succ (n+1) (mk_inductive_aux₁ (n+1))).1,
    (succ (n+1) (mk_inductive_aux₁ (n+1))).2⟩

section

/--
An auxiliary construction for `mk_inductive`.
-/
@[simp]
def mk_inductive_aux₂ :
  Π n, Σ' (f : P.X_next n ⟶ Q.X n) (f' : P.X n ⟶ Q.X_prev n), e.f n = P.d_from n ≫ f + f' ≫ Q.d_to n
| 0 := ⟨0, zero ≫ (Q.X_prev_iso rfl).inv, by simpa using comm_zero⟩
| (n+1) := let I := mk_inductive_aux₁ e zero comm_zero one comm_one succ n in
  ⟨(P.X_next_iso rfl).hom ≫ I.1, I.2.1 ≫ (Q.X_prev_iso rfl).inv, by simpa using I.2.2⟩

lemma mk_inductive_aux₃ (i j : ℕ) (h : i+1 = j) :
  (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.X_prev_iso h).hom
    = (P.X_next_iso h).inv ≫ (mk_inductive_aux₂ e zero comm_zero one comm_one succ j).1 :=
by subst j; rcases i with (_|_|i); { dsimp, simp, }

/--
A constructor for a `homotopy e 0`, for `e` a chain map between `ℕ`-indexed chain complexes,
working by induction.

You need to provide the components of the homotopy in degrees 0 and 1,
show that these satisfy the homotopy condition,
and then give a construction of each component,
and the fact that it satisfies the homotopy condition,
using as an inductive hypothesis the data and homotopy condition for the previous two components.
-/
def mk_inductive : homotopy e 0 :=
{ hom := λ i j, if h : i + 1 = j then
    (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.1 ≫ (Q.X_prev_iso h).hom
  else
    0,
  zero' := λ i j w, by rwa dif_neg,
  comm := λ i, begin
    dsimp, simp only [add_zero],
    convert (mk_inductive_aux₂ e zero comm_zero one comm_one succ i).2.2,
    { cases i,
      { dsimp [from_next], rw dif_neg,
        simp only [chain_complex.next_nat_zero, nat.one_ne_zero, not_false_iff], },
      { dsimp [from_next], rw dif_pos, swap, { simp only [chain_complex.next_nat_succ] },
        have aux : (complex_shape.down ℕ).next i.succ = i := chain_complex.next_nat_succ i,
        rw mk_inductive_aux₃ e zero comm_zero one comm_one succ
          ((complex_shape.down ℕ).next i.succ) (i+1) (by rw aux),
        dsimp [X_next_iso], erw category.id_comp, } },
    { dsimp [to_prev], rw dif_pos, swap, { simp only [chain_complex.prev] },
      dsimp [X_prev_iso], erw category.comp_id, },
  end, }

end

end mk_inductive

/-!
`homotopy.mk_coinductive` allows us to build a homotopy of cochain complexes inductively,
so that as we construct each component, we have available the previous two components,
and the fact that they satisfy the homotopy condition.
-/
section mk_coinductive

variables {P Q : cochain_complex V ℕ}

@[simp] lemma d_next_cochain_complex (f : Π i j, P.X i ⟶ Q.X j) (j : ℕ) :
  d_next j f = P.d _ _ ≫ f (j+1) j :=
begin
  dsimp [d_next],
  have : (complex_shape.up ℕ).next j = j + 1 := cochain_complex.next ℕ j,
  congr' 2,
end

@[simp] lemma prev_d_succ_cochain_complex (f : Π i j, P.X i ⟶ Q.X j) (i : ℕ) :
  prev_d (i+1) f = f (i+1) _ ≫ Q.d i (i+1) :=
begin
  dsimp [prev_d],
  have : (complex_shape.up ℕ).prev (i+1) = i := cochain_complex.prev_nat_succ i,
  congr' 2,
end

@[simp] lemma prev_d_zero_cochain_complex (f : Π i j, P.X i ⟶ Q.X j) :
  prev_d 0 f = 0 :=
begin
  dsimp [prev_d],
  rw [Q.shape, comp_zero],
  rw [cochain_complex.prev_nat_zero], dsimp, dec_trivial,
end

variables (e : P ⟶ Q)
  (zero : P.X 1 ⟶ Q.X 0)
  (comm_zero : e.f 0 = P.d 0 1 ≫ zero)
  (one : P.X 2 ⟶ Q.X 1)
  (comm_one : e.f 1 = zero ≫ Q.d 0 1 + P.d 1 2 ≫ one)
  (succ : ∀ (n : ℕ)
    (p : Σ' (f : P.X (n+1) ⟶ Q.X n) (f' : P.X (n+2) ⟶ Q.X (n+1)),
      e.f (n+1) = f ≫ Q.d n (n+1) + P.d (n+1) (n+2) ≫ f'),
    Σ' f'' : P.X (n+3) ⟶ Q.X (n+2), e.f (n+2) = p.2.1 ≫ Q.d (n+1) (n+2) + P.d (n+2) (n+3) ≫ f'')

include comm_one comm_zero succ

/--
An auxiliary construction for `mk_coinductive`.

Here we build by induction a family of diagrams,
but don't require at the type level that these successive diagrams actually agree.
They do in fact agree, and we then capture that at the type level (i.e. by constructing a homotopy)
in `mk_coinductive`.

At this stage, we don't check the homotopy condition in degree 0,
because it "falls off the end", and is easier to treat using `X_next` and `X_prev`,
which we do in `mk_inductive_aux₂`.
-/
@[simp, nolint unused_arguments]
def mk_coinductive_aux₁ :
  Π n, Σ' (f : P.X (n+1) ⟶ Q.X n) (f' : P.X (n+2) ⟶ Q.X (n+1)),
    e.f (n+1) = f ≫ Q.d n (n+1) + P.d (n+1) (n+2) ≫ f'
| 0 := ⟨zero, one, comm_one⟩
| 1 := ⟨one, (succ 0 ⟨zero, one, comm_one⟩).1, (succ 0 ⟨zero, one, comm_one⟩).2⟩
| (n+2) :=
  ⟨(mk_coinductive_aux₁ (n+1)).2.1,
    (succ (n+1) (mk_coinductive_aux₁ (n+1))).1,
    (succ (n+1) (mk_coinductive_aux₁ (n+1))).2⟩

section

/--
An auxiliary construction for `mk_inductive`.
-/
@[simp]
def mk_coinductive_aux₂ :
  Π n, Σ' (f : P.X n ⟶ Q.X_prev n) (f' : P.X_next n ⟶ Q.X n),
    e.f n = f ≫ Q.d_to n + P.d_from n ≫ f'
| 0 := ⟨0, (P.X_next_iso rfl).hom ≫ zero, by simpa using comm_zero⟩
| (n+1) := let I := mk_coinductive_aux₁ e zero comm_zero one comm_one succ n in
  ⟨I.1 ≫ (Q.X_prev_iso rfl).inv, (P.X_next_iso rfl).hom ≫ I.2.1, by simpa using I.2.2⟩

lemma mk_coinductive_aux₃ (i j : ℕ) (h : i + 1 = j) :
  (P.X_next_iso h).inv ≫ (mk_coinductive_aux₂ e zero comm_zero one comm_one succ i).2.1
    = (mk_coinductive_aux₂ e zero comm_zero one comm_one succ j).1 ≫ (Q.X_prev_iso h).hom :=
by subst j; rcases i with (_|_|i); { dsimp, simp, }

/--
A constructor for a `homotopy e 0`, for `e` a chain map between `ℕ`-indexed cochain complexes,
working by induction.

You need to provide the components of the homotopy in degrees 0 and 1,
show that these satisfy the homotopy condition,
and then give a construction of each component,
and the fact that it satisfies the homotopy condition,
using as an inductive hypothesis the data and homotopy condition for the previous two components.
-/
def mk_coinductive : homotopy e 0 :=
{ hom := λ i j, if h : j + 1 = i then
    (P.X_next_iso h).inv ≫ (mk_coinductive_aux₂ e zero comm_zero one comm_one succ j).2.1
  else
    0,
  zero' := λ i j w, by rwa dif_neg,
  comm := λ i, begin
    dsimp,
    rw [add_zero, add_comm],
    convert (mk_coinductive_aux₂ e zero comm_zero one comm_one succ i).2.2 using 2,
    { cases i,
      { dsimp [to_prev], rw dif_neg,
        simp only [cochain_complex.prev_nat_zero, nat.one_ne_zero, not_false_iff], },
      { dsimp [to_prev], rw dif_pos, swap, { simp only [cochain_complex.prev_nat_succ] },
        have aux : (complex_shape.up ℕ).prev i.succ = i := cochain_complex.prev_nat_succ i,
        rw mk_coinductive_aux₃ e zero comm_zero one comm_one succ
          ((complex_shape.up ℕ).prev i.succ) (i+1) (by rw aux),
        dsimp [X_prev_iso], erw category.comp_id, } },
    { dsimp [from_next], rw dif_pos, swap, { simp only [cochain_complex.next] },
      dsimp [X_next_iso], erw category.id_comp, },
  end }

end

end mk_coinductive

end homotopy

/--
A homotopy equivalence between two chain complexes consists of a chain map each way,
and homotopies from the compositions to the identity chain maps.

Note that this contains data;
arguably it might be more useful for many applications if we truncated it to a Prop.
-/
structure homotopy_equiv (C D : homological_complex V c) :=
(hom : C ⟶ D)
(inv : D ⟶ C)
(homotopy_hom_inv_id : homotopy (hom ≫ inv) (𝟙 C))
(homotopy_inv_hom_id : homotopy (inv ≫ hom) (𝟙 D))

namespace homotopy_equiv

/-- Any complex is homotopy equivalent to itself. -/
@[refl] def refl (C : homological_complex V c) : homotopy_equiv C C :=
{ hom := 𝟙 C,
  inv := 𝟙 C,
  homotopy_hom_inv_id := by simp,
  homotopy_inv_hom_id := by simp, }

instance : inhabited (homotopy_equiv C C) := ⟨refl C⟩

/-- Being homotopy equivalent is a symmetric relation. -/
@[symm] def symm
  {C D : homological_complex V c} (f : homotopy_equiv C D) :
  homotopy_equiv D C :=
{ hom := f.inv,
  inv := f.hom,
  homotopy_hom_inv_id := f.homotopy_inv_hom_id,
  homotopy_inv_hom_id := f.homotopy_hom_inv_id, }

/-- Homotopy equivalence is a transitive relation. -/
@[trans] def trans
  {C D E : homological_complex V c} (f : homotopy_equiv C D) (g : homotopy_equiv D E) :
  homotopy_equiv C E :=
{ hom := f.hom ≫ g.hom,
  inv := g.inv ≫ f.inv,
  homotopy_hom_inv_id := by simpa using
    ((g.homotopy_hom_inv_id.comp_right_id f.inv).comp_left f.hom).trans f.homotopy_hom_inv_id,
  homotopy_inv_hom_id := by simpa using
    ((f.homotopy_inv_hom_id.comp_right_id g.hom).comp_left g.inv).trans g.homotopy_inv_hom_id, }

/-- An isomorphism of complexes induces a homotopy equivalence. -/
def of_iso {ι : Type*} {V : Type u} [category.{v} V] [preadditive V]
  {c : complex_shape ι} {C D : homological_complex V c} (f : C ≅ D) :
  homotopy_equiv C D :=
⟨f.hom, f.inv, homotopy.of_eq f.3, homotopy.of_eq f.4⟩

end homotopy_equiv

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
  simp only [homology.π_map, comp_zero, preadditive.comp_sub],
  dsimp [kernel_subobject_map],
  simp_rw [h.comm i],
  simp only [zero_add, zero_comp, d_next_eq_d_from_from_next, kernel_subobject_arrow_comp_assoc,
    preadditive.comp_add],
  rw [←preadditive.sub_comp],
  simp only [category_theory.subobject.factor_thru_add_sub_factor_thru_right],
  erw [subobject.factor_thru_of_le (D.boundaries_le_cycles i)],
  { simp, },
  { rw [prev_d_eq_to_prev_d_to, ←category.assoc],
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

variables {W : Type*} [category W] [preadditive W]

/-- An additive functor takes homotopies to homotopies. -/
@[simps]
def functor.map_homotopy (F : V ⥤ W) [F.additive] {f g : C ⟶ D} (h : homotopy f g) :
  homotopy ((F.map_homological_complex c).map f) ((F.map_homological_complex c).map g) :=
{ hom := λ i j, F.map (h.hom i j),
  zero' := λ i j w, by { rw [h.zero i j w, F.map_zero], },
  comm := λ i, begin
    dsimp [d_next, prev_d] at *,
    rw h.comm i,
    simp only [F.map_add, ← F.map_comp],
    refl
  end, }

/-- An additive functor preserves homotopy equivalences. -/
@[simps]
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
