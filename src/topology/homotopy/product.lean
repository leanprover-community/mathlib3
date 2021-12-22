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
- `homotopy.pi homotopies`: Let f and g be a family of functions
  indexed on I, such that for each i ∈ I, fᵢ and gᵢ are maps from A to Xᵢ.
  Let `homotopies` be a family of homotopies from fᵢ to gᵢ for each i.
  Then `homotopy.pi homotopies` is the canonical homotopy
  from ∏ f to ∏ g, where ∏ f is the product map from A to Πi, Xᵢ,
  and similarly for ∏ g. All homotopies are done relative to some set S ⊆ A.

- `homotopy.prod F G` is the product of homotopies F and G,
   where F is a homotopy between f₀ and f₁, G is a homotopy between g₀ and g₁.
   The result F × G is a homotopy between (f₀ × g₀) and (f₁ × g₁).
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
           {f g : Π i, C(A, X i)} {S : set A}


/-- The product homotopy of `homotopies` between functions `f`
      and `g` -/
def pi (homotopies : Π i : I, homotopy_rel (f i) (g i) S) :
  homotopy_rel (pi f) (pi g) S :=
{ to_fun := λ t i, (homotopies i).to_fun t,
  continuous_to_fun := by continuity,
  to_fun_zero :=
  by { intro t, ext i, simp [(homotopies i).to_fun_zero], },
  to_fun_one :=
  by { intro t, ext i, simp [(homotopies i).to_fun_one], },
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
          {f₀ f₁ : C(A, α)} {g₀ g₁ : C(A, β)} {S : set A}

/-- The product of homotopies `F` and `G`,
    where `F` takes `f₀` to `f₁`
    and `G` takes `g₀` to `g₁`
  -/
def prod (F : homotopy_rel f₀ f₁ S) (G : homotopy_rel g₀ g₁ S) :
  homotopy_rel (prod_mk f₀ g₀) (prod_mk f₁ g₁) S :=
{ to_fun := λ t, (F t, G t),
  continuous_to_fun := by continuity,
  to_fun_zero := by { intro, simp [homotopy_with.apply_zero], },
  to_fun_one := by { intro, simp [homotopy_with.apply_one], },
  prop' :=
  begin
    intros t x hx,
    have t₁ := F.prop' t x hx,
    have t₂ := G.prop' t x hx,
    dsimp only [prod_eval],
    rw [← t₁.1, ← t₁.2, ← t₂.1, ← t₂.2],
    split; refl,
  end }

end prod
end continuous_map.homotopy
