/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.list.chain
import category_theory.punit
import category_theory.is_connected
import category_theory.sigma.basic
import category_theory.full_subcategory

/-!
# Connected components of a category

-/

universes v₁ v₂ v₃ u₁ u₂

noncomputable theory

open category_theory.category

namespace category_theory

attribute [instance, priority 100] is_connected.is_nonempty

variables {J : Type u₁} [category.{v₁} J]
variables {C : Type u₂} [category.{u₁} C]

/-- This type indexes the connected components of the category `J`. -/
def connected_components (J : Type u₁) [category.{v₁} J] : Type u₁ := quotient (zigzag.setoid J)

/-- Given an index for a connected component, produce the actual component as a full subcategory. -/
@[derive category]
def component (j : connected_components J) : Type u₁ := {k : J // quotient.mk' k = j}

/-- The obvious inclusion functor from a connected component to the whole category. -/
@[derive [full, faithful]]
def include_component (j) : component j ⥤ J :=
full_subcategory_inclusion _

/-- Each connected component of the category is nonempty. -/
instance (j : connected_components J) : nonempty (component j) :=
begin
  apply quotient.induction_on' j,
  intro k,
  refine ⟨⟨k, rfl⟩⟩,
end

/-- Each connected component of the category is connected. -/
instance (j : connected_components J) : is_connected (component j) :=
begin
  apply zigzag_is_connected,
  rintro ⟨j₁, hj₁⟩ ⟨j₂, rfl⟩,
  have h₁₂ : zigzag j₁ j₂ := quotient.exact' hj₁,
  rcases list.exists_chain_of_relation_refl_trans_gen h₁₂ with ⟨l, hl₁, hl₂⟩,
  let f : Π x, zigzag x j₂ → component (quotient.mk' j₂) := λ x h, subtype.mk x (quotient.sound' h),
  have hf : ∀ (a : J), a ∈ l → zigzag a j₂,
  { intros i hi,
    apply list.chain.induction (λ t, zigzag t j₂) _ hl₁ hl₂ _ _ _ (or.inr hi),
    { intros j k,
      apply relation.refl_trans_gen.head },
    { apply relation.refl_trans_gen.refl } },
  let l' : list (component (quotient.mk' j₂)) := l.pmap f hf,
  have : list.chain zigzag (⟨j₁, hj₁⟩ : component _) l',
  { induction l generalizing hl₁ hl₂ j₁ hf,
    { apply list.chain.nil },
    { have hl₃ := list.chain_cons.1 hl₁,
      apply list.chain.cons,
      { apply relation.refl_trans_gen.single,
        refine zag_of_zag_obj (include_component _) _,
        apply hl₃.1 },
      { refine l_ih _ _ _ hl₃.2 _ _,
        { apply relation.refl_trans_gen.head (zag_symmetric hl₃.1) h₁₂ },
        { rwa list.last_cons_cons at hl₂ } } } },
  apply list.chain.induction_head (λ t, zigzag t (⟨j₂, rfl⟩ : component _)) _ this _ _ _,
  { refine ⟨_, rfl⟩ },
  { have h : ∀ (a : J), a ∈ j₁ :: l → zigzag a j₂,
    { simpa [h₁₂] using hf },
    change (list.pmap f (j₁ :: l) h).last _ = _,
    erw list.last_pmap _ _ _ _ (list.cons_ne_nil _ _),
    apply subtype.ext,
    apply hl₂ },
  { intros _ _,
    apply relation.refl_trans_gen.trans },
  { apply relation.refl_trans_gen.refl },
end

/--
The disjoint union of `J`s connected components, written explicitly as a sigma-type with the
category structure.
This category is equivalent to `J`.
-/
@[derive category]
def decomposed (J : Type u₁) [category.{v₁} J] := Σ (j : connected_components J), component j

def inclusion (j : connected_components J) : component j ⥤ decomposed J :=
sigma.incl _

/-- The forward direction of the equivalence between the decomposed category and the original. -/
def forward (J : Type u₁) [category.{v₁} J] : decomposed J ⥤ J :=
sigma.desc include_component

instance : full (forward J) :=
{ preimage :=
  begin
    rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f,
    dsimp [forward] at f,
    have : j' = k',
      rw [← hX, ← hY, quotient.eq'],
      exact relation.refl_trans_gen.single (or.inl ⟨f⟩),
    subst this,
    refine sigma.sigma_hom.mk f,
  end,
  witness' :=
  begin
    rintro ⟨j', X, hX⟩ ⟨_, Y, rfl⟩ f,
    have : quotient.mk' Y = j',
    { rw [← hX, quotient.eq'],
      exact relation.refl_trans_gen.single (or.inr ⟨f⟩) },
    subst this,
    refl,
  end }

instance : faithful (forward J) :=
{ map_injective' :=
  begin
    rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨_, _, _, f⟩ ⟨_, _, _, g⟩ e,
    change f = g at e,
    subst e,
  end }

instance : ess_surj (forward J) :=
{ obj_preimage := λ j, ⟨_, j, rfl⟩,
  iso' := λ j, iso.refl _ }

/-- This gives that any category is equivalent to a disjoint union of connected categories. -/
instance : is_equivalence (forward J) := equivalence.equivalence_of_fully_faithfully_ess_surj _

@[simps]
def thingy (H F : decomposed J ⥤ C) :
  (H ⟶ F) ≅ Π j, (sigma.incl j ⋙ H ⟶ sigma.incl j ⋙ F) :=
{ hom := λ α j, whisker_left _ α,
  inv := sigma.nat_trans }

lemma thingy_natural {H H' F F' : decomposed J ⥤ C} (α : H' ⟶ H) (β : F ⟶ F') (γ : H ⟶ F) :
  (thingy H' F').hom (α ≫ γ ≫ β) = (λ j, whisker_left _ α ≫ (thingy H F).hom γ j ≫ whisker_left _ β) :=
begin
  ext j X,
  refl,
end

end category_theory
