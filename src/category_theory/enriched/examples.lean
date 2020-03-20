/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.enriched.enriched_over
import algebra.category.Module.monoidal

universes v u

open category_theory

namespace Module

-- PROJECT
-- These next two lemmas are true in any concrete category whose forgetful functor creates limits.
-- Perhaps when we do algebraic theories this should be generalised.
@[simp]
lemma fst_tensor_hom_apply {α β γ δ : Type u} (f : α ⟶ β) (g : γ ⟶ δ) (x : α ⊗ γ) :
  (limits.prod.fst : β ⊗ δ ⟶ β) (((f ⊗ g) : α ⊗ γ ⟶ β ⊗ δ) x) = (f ((limits.prod.fst : α ⊗ γ ⟶ α) x)) :=
rfl
@[simp]
lemma snd_tensor_hom_apply {α β γ δ : Type u} (f : α ⟶ β) (g : γ ⟶ δ) (x : α ⊗ γ) :
  (limits.prod.snd : β ⊗ δ ⟶ δ) (((f ⊗ g) : α ⊗ γ ⟶ β ⊗ δ) x) = (g ((limits.prod.snd : α ⊗ γ ⟶ γ) x)) :=
rfl

local notation G`♭`:100 := ((forget (Module ℤ)).obj G)

instance : concrete_monoidal_category (Module ℤ) :=
{ lax_monoidal :=
  { ε := λ x, (1 : ℤ),
    μ := λ G H p,
    ((limits.prod.fst : G♭ ⨯ H♭ ⟶ G♭) p) ⊗ₜ ((limits.prod.snd : G♭ ⨯ H♭ ⟶ H♭) p),
    μ_natural' := λ X Y X' Y' f g, rfl,
    associativity' := λ X Y Z, rfl,
    left_unitality' := λ X,
    begin
      ext, dsimp,
      erw Module.monoidal_category.left_unitor_hom,
      simp [one_smul],
    end,
    right_unitality' := λ X,
    begin
      ext, dsimp,
      erw Module.monoidal_category.right_unitor_hom,
      simp [one_smul],
    end, }}.

section
variables (C : Type 1) [𝒞 : large_category C]
include 𝒞

instance [enriched_over (Module ℤ) C] (X Y : C) : add_comm_group (X ⟶ Y) :=
begin
  have : add_comm_group ((X ⟶[Module ℤ] Y) : Module ℤ),
  apply_instance,
  convert this,
end

instance [enriched_over (Module ℤ) C] (X Y : C) : module ℤ (X ⟶ Y) :=
begin
  change module ℤ (X ⟶[Module ℤ] Y),
  apply_instance,
end

-- How do we want to express the linearity of morphisms?
end

@[simp]
lemma as_term_eq {M : Module ℤ} (f : 𝟙_ (Module ℤ) ⟶ M) : as_term f = f (1 : ℤ) := rfl

@[simp]
lemma forget.μ_eq {M N : Module ℤ} (m : (forget (Module ℤ)).obj M) (n : (forget (Module ℤ)).obj N) :
  forget.μ m n = m ⊗ₜ n :=
rfl

-- TODO this would be easier if we noticed that the forgetful functor is representable
def enriched_id (X : Module ℤ) : 𝟙_ (Module ℤ) ⟶ of ℤ (X ⟶ X) :=
begin
  fsplit,
  intro i,
  fsplit,
  intro x, exact i • x,
  { exact smul_add i, },
  { exact smul_comm i, },
  { intros i j, ext, dsimp, exact add_smul i j x, },
  { intros i y, ext, dsimp, exact mul_smul i y x, }
end

@[simp]
lemma enriched_id_apply {X : Module ℤ} (i : ℤ) (x : X) : ((enriched_id X) i).to_fun x = i • x :=
rfl

def enriched_comp (X Y Z : Module ℤ) :
  of ℤ (X ⟶ Y) ⊗ of ℤ (Y ⟶ Z) ⟶ of ℤ (X ⟶ Z) :=
begin
  -- We build an R-linear map out of the tensor product, using the universal property,
  apply tensor_product.lift,
  -- requiring us to build an R-linear map from `X ⟶ Y` to the R-linear maps `Y ⟶ Z` to `X ⟶ Z`.
  fsplit,
  { intro f,
    fsplit,
    { intro g,
      -- The underlying function is just composition of morphisms.
      exact f ≫ g, },
    -- And now we just follow our noses,
    -- looking up the names of lemmas about R-modules and R-linear maps using `library_search`!
    { intros g₁ g₂, ext, refl, },
    { intros i g, ext, refl, }, },
  { intros f₁ f₂, ext g x, dsimp, exact g.add (f₁.to_fun x) (f₂.to_fun x), },
  { intros i f, ext g x, dsimp, exact g.smul i (f.to_fun x), },
end.

@[simp]
lemma enriched_comp_apply_pure {M N K : Module ℤ} (f : M ⟶ N) (g : N ⟶ K) :
  (enriched_comp M N K) (f ⊗ₜ g) = f ≫ g :=
begin
  dsimp [enriched_comp],
  simp,
  refl,
end

instance : enriched_over (Module ℤ) (Module ℤ) :=
{ e_hom := λ X Y, Module.of ℤ (X ⟶ Y),
  e_id := λ X, enriched_id X,
  e_comp := λ X Y Z, enriched_comp X Y Z,
  e_hom_forget := λ X Y, equiv.refl (X ⟶ Y),
  e_id_forget' := λ X,
  begin
    ext x, dsimp,
    -- FIXME this is farcical. We should just be able to call simp, and have `enriched_id_apply` work.
    have := enriched_id_apply 1 x,
    conv at this { to_rhs, simp, },
    conv { to_rhs, rw ←this, },
    refl,
  end,
  e_comp_forget' := λ M N K f g,
  begin
    ext m, dsimp,
    -- FIXME why can't we call `simp`?
    rw [enriched_comp_apply_pure f g],
    refl,
  end, }

-- TODO modules over a ring are enriched over themselves
-- TODO deduce from this that they are enriched over AddCommGroup

end Module
