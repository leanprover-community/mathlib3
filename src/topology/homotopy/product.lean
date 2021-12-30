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
homotopies. We show that the products of relative homotopies
are still relative homotopies.

## Definitions
- `continuous_map.homotopy.pi homotopies`: Let f and g be a family of functions
  indexed on I, such that for each i ∈ I, fᵢ and gᵢ are maps from A to Xᵢ.
  Let `homotopies` be a family of homotopies from fᵢ to gᵢ for each i.
  Then `homotopy.pi homotopies` is the canonical homotopy
  from ∏ f to ∏ g, where ∏ f is the product map from A to Πi, Xᵢ,
  and similarly for ∏ g.

- `continuous_map.homotopy_rel.pi homotopies`: Same as `continuous_map.homotopy.pi`, but
  all homotopies are done relative to some set S ⊆ A.

- `continuous_map.homotopy.prod F G` is the product of homotopies F and G,
   where F is a homotopy between f₀ and f₁, G is a homotopy between g₀ and g₁.
   The result F × G is a homotopy between (f₀ × g₀) and (f₁ × g₁).
   Again, all homotopies are done relative to S.

- `continuous_map.homotopy_rel.prod F G`: Same as `continuous_map.homotopy.prod`, but
  all homotopies are done relative to some set S ⊆ A.
-/

noncomputable theory

namespace continuous_map
open continuous_map

section pi

variables {I : Type*} {X : I → Type*} [∀i, topological_space (X i)]
  {A : Type*} [topological_space A]
  {f g : Π i, C(A, X i)} {S : set A}

/-- The product homotopy of `homotopies` between functions `f` and `g` -/
@[simps]
def homotopy.pi (homotopies : Π i, homotopy (f i) (g i)) :
        homotopy (pi f) (pi g) :=
{ to_fun := λ t i, homotopies i t,
  to_fun_zero := by { intro t, ext i, simp only [pi_eval, homotopy.apply_zero], },
  to_fun_one := by { intro t, ext i, simp only [pi_eval, homotopy.apply_one], } }

/-- The relative product homotopy of `homotopies` between functions `f` and `g` -/
@[simps]
def homotopy_rel.pi (homotopies : Π i : I, homotopy_rel (f i) (g i) S) :
  homotopy_rel (pi f) (pi g) S :=
{ prop' :=
  begin
    intros t x hx,
    dsimp only [coe_mk, pi_eval, to_fun_eq_coe, homotopy_with.coe_to_continuous_map],
    simp only [function.funext_iff, ← forall_and_distrib],
    intro i,
    exact (homotopies i).prop' t x hx,
  end,
  ..(homotopy.pi (λ i, (homotopies i).to_homotopy)), }

end pi

section prod

variables {α β : Type*} [topological_space α] [topological_space β]
  {A : Type*} [topological_space A]
  {f₀ f₁ : C(A, α)} {g₀ g₁ : C(A, β)} {S : set A}

/-- The product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁`  and `G` takes `g₀` to `g₁` -/
@[simps]
def homotopy.prod (F : homotopy f₀ f₁) (G : homotopy g₀ g₁) :
  homotopy (prod_mk f₀ g₀) (prod_mk f₁ g₁) :=
{ to_fun := λ t, (F t, G t),
  to_fun_zero := by { intro, simp only [prod_eval, homotopy.apply_zero], },
  to_fun_one := by { intro, simp only [prod_eval, homotopy.apply_one], } }

/-- The relative product of homotopies `F` and `G`,
  where `F` takes `f₀` to `f₁`  and `G` takes `g₀` to `g₁` -/
@[simps]
def homotopy_rel.prod (F : homotopy_rel f₀ f₁ S) (G : homotopy_rel g₀ g₁ S) :
  homotopy_rel (prod_mk f₀ g₀) (prod_mk f₁ g₁) S :=
{ prop' :=
  begin
    intros t x hx,
    have hF := F.prop' t x hx,
    have hG := G.prop' t x hx,
    simp only [coe_mk, prod_eval, prod.mk.inj_iff, homotopy.prod] at hF hG ⊢,
    exact ⟨⟨hF.1, hG.1⟩, ⟨hF.2, hG.2⟩⟩,
  end,
  ..(homotopy.prod F.to_homotopy G.to_homotopy) }

end prod
end continuous_map
