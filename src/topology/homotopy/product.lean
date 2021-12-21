/-
Copyright (c) 2021 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import topology.homotopy.basic
import topology.constructions

/-!
# Product of homotopies

In this file, we introduce definitions for the product of
homotopies and projection of homotopies. We show that the product
and projection of relative homotopies are still relative homotopies.

## Definitions
- `product_homotopy f g S homotopies`: Let f and g be a family of functions
  indexed on I, such that for each i ∈ I, fᵢ and gᵢ are maps from A to Xᵢ.
  Let `homotopies` be a family of homotopies from fᵢ to gᵢ for each i.
  Then `product_homotopy f g S homotopies` is the canonical homotopy
  from ∏ f to ∏ g, where ∏ f is the product map from A to Πi, Xᵢ.
  All homotopies are done relative to the set S ⊆ A.

- `proj_homotopy i f g s`: The inverse of `product_homotopy`. Given
  maps `f` and `g` from `A` to `Πi, Xᵢ`, returns a homotopy from
  the projection of `f` onto `Xᵢ` to the projection of `g` onto `Xᵢ`
-/

noncomputable theory

namespace continuous_map
section
parameters {I : Type*} {X : I → Type*}
           [∀i, topological_space (X i)]
           {A : Type*}
           [topological_space A]

/-- Abbreviation for product of continuous maps, which is continuous -/
def product (f : Π i, C(A, X i)) : C(A, Π i, X i) :=
{ to_fun := λ (a : A) (i : I), f i a,
  continuous_to_fun := by continuity, }

@[simp]
lemma product_eval (f : Π i, C(A, X i)) (a : A)  :
  (product f) a  = λ i : I, (f i) a := rfl

/-- Abbreviation for composition with projection -/
def projection (i : I) (f : C(A, Π i, X i)) : C(A, X i) :=
{ to_fun := λ (a : A), f a i,
  continuous_to_fun := by
  { apply continuous_proj, exact f.continuous_to_fun, }, }

@[simp]
lemma projection_eval (i : I) (f : C(A, Π i, X i)) (a : A) :
  (projection i f) a = f a i := rfl


namespace homotopy
/-- The product homotopy of `homotopies` between functions `f`
      and `g` -/
def product_homotopy
  (f g : Π i, C(A, X i)) (S : set A)
  (homotopies : Π i : I, continuous_map.homotopy_rel (f i) (g i) S) :
  continuous_map.homotopy_rel (product f) (product g) S :=
{ to_fun := λ t i, (homotopies i).to_fun t,
  continuous_to_fun := by continuity,
  to_fun_zero := by {
    intro t, ext i, simpa only [(homotopies i).to_fun_zero], },
  to_fun_one := by {
    intro t, ext i, simpa only [(homotopies i).to_fun_one], },

  prop' :=
  begin
    intros t x hx,
    have := λ i, (homotopies i).prop' t x hx,
    -- finish, -- this works, but it's slow
    change (λ (i : I), (homotopies i) (t, x)) = (λ i, f i x) ∧
          (λ (i : I), (homotopies i) (t, x)) = (λ i, g i x),
    change ∀ i, (homotopies i) (t, x) = (f i) x ∧ (homotopies i) (t, x) = (g i) x at this,
    split;
      ext i;
      have := this i;
      tauto,
  end, }

/-- The projection homotopy of `homotopy` between `f` and `g`
     onto index `i`-/
def proj_homotopy
  (i : I) (f g : C(A, Π i, X i))
  (S : set A)
  (homotopy : continuous_map.homotopy_rel f g S) :
  continuous_map.homotopy_rel (projection i f) (projection i g) S
  :=
{ to_fun := λ ts, (homotopy ts i),
  continuous_to_fun := by { apply continuous_proj, exact homotopy.continuous_to_fun, },
  to_fun_zero := λ s, function.funext_iff.mp (homotopy.to_fun_zero s) i,
  to_fun_one := λ s, function.funext_iff.mp (homotopy.to_fun_one s) i,
  prop' :=
  begin
    intros t s x,
    change homotopy (t, s) i = f s i ∧ homotopy (t, s) i = g s i,
    have := homotopy.prop' t s x,
    change homotopy (t, s) = f s ∧ homotopy (t, s) = g s at this,
    tauto,
  end }
end homotopy


end
end continuous_map
