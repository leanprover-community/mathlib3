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
homotopies. We show that the product of relative homotopies
are still relative homotopies.

## Definitions
- `homotopy.pi f g S homotopies`: Let f and g be a family of functions
  indexed on I, such that for each i ∈ I, fᵢ and gᵢ are maps from A to Xᵢ.
  Let `homotopies` be a family of homotopies from fᵢ to gᵢ for each i.
  Then `product_homotopy f g S homotopies` is the canonical homotopy
  from ∏ f to ∏ g, where ∏ f is the product map from A to Πi, Xᵢ.
  All homotopies are done relative to the set S ⊆ A.
-/

noncomputable theory

namespace continuous_map
variables {I : Type*} {X : I → Type*}
           [∀i, topological_space (X i)]
           {A : Type*}
           [topological_space A]

/-- Abbreviation for product of continuous maps, which is continuous -/
def pi (f : Π i, C(A, X i)) : C(A, Π i, X i) :=
{ to_fun := λ (a : A) (i : I), f i a,
  continuous_to_fun := by continuity, }

@[simp]
lemma pi_eval (f : Π i, C(A, X i)) (a : A)  :
  (pi f) a  = λ i : I, (f i) a := rfl

namespace homotopy
/-- The product homotopy of `homotopies` between functions `f`
      and `g` -/
def pi
  (f g : Π i, C(A, X i)) (S : set A)
  (homotopies : Π i : I, continuous_map.homotopy_rel (f i) (g i) S) :
  continuous_map.homotopy_rel (pi f) (pi g) S :=
{ to_fun := λ t i, (homotopies i).to_fun t,
  continuous_to_fun := by continuity,
  to_fun_zero :=
  by { intro t, ext i, simpa only [(homotopies i).to_fun_zero], },
  to_fun_one :=
  by { intro t, ext i, simpa only [(homotopies i).to_fun_one], },

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

end homotopy
end continuous_map
