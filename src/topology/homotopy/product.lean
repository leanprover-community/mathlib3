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

- `homotopy.prod f f' g g' S h₁ h₂` is the product of homotopies h₁ and h₂,
   where h₁ is a homotopy between f and f', h₂ is a homotopy between g and g',
   and the result h₁ × h₂ is a homotopy between (f × g) and (f' × g').
   Again, all homotopies are done relative to S.
-/

noncomputable theory

namespace continuous_map.homotopy
open continuous_map

section pi

variables {I : Type*} {X : I → Type*}
           [∀i, topological_space (X i)]
           {A : Type*}
           [topological_space A]


/-- The product homotopy of `homotopies` between functions `f`
      and `g` -/
def pi
  (f g : Π i, C(A, X i)) (S : set A)
  (homotopies : Π i : I, homotopy_rel (f i) (g i) S) :
  homotopy_rel (pi f) (pi g) S :=
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

end pi

section prod
variables {α β : Type*} [topological_space α] [topological_space β]
           {A : Type*} [topological_space A]

/-- The product of homotopies `homotopy₁` and `homotopy₂`,
  - where `homotopy₁` takes `f` to `f'`
  - and `homotopy₂` takes `g` to `g'`
  -/
def prod
  (f f' : C(A, α)) (g g' : C(A, β)) (S : set A)
  (homotopy₁ : homotopy_rel f f' S)
  (homotopy₂ : homotopy_rel g g' S) :
  homotopy_rel (prod_mk f g) (prod_mk f' g') S :=
{ to_fun := λ t, (homotopy₁ t, homotopy₂ t),
  continuous_to_fun := by continuity,
  to_fun_zero := by { intro, simp [homotopy_with.apply_zero], },
  to_fun_one := by { intro, simp [homotopy_with.apply_one], },
  prop' :=
  begin
    intros t x hx,
    have t₁ := homotopy₁.prop' t x hx,
    have t₂ := homotopy₂.prop' t x hx,
    dsimp only [prod_eval],
    rw [← t₁.1, ← t₁.2, ← t₂.1, ← t₂.2],
    split; refl,
  end }

end prod
end continuous_map.homotopy
