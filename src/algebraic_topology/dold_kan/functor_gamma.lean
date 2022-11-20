/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.split_simplicial_object

/-!

# Construction of the inverse functor of the Dold-Kan equivalence

@TODO @joelriou: construct the functor `Γ₀ : chain_complex C ℕ ⥤ simplicial_object C`
which shall be the inverse functor of the Dold-Kan equivalence in the case of abelian categories,
and more generally pseudoabelian categories. Extend this functor `Γ₀` as a functor
`Γ₂ : karoubi (chain_complex C ℕ) ⥤ karoubi (simplicial_object C)` on the idempotent
completion, show that this functor shall be an equivalence of categories when `C` is any additive
category.

Currently, this file contains the definition of `Γ₀.obj.obj₂ K Δ` for
`K : chain_complex C ℕ` and `Δ : simplex_categoryᵒᵖ`. By definition, `Γ₀.obj.obj₂ K Δ`
is a certain coproduct indexed by the set `splitting.index_set Δ` whose elements
consists of epimorphisms `e : Δ.unop ⟶ Δ'.unop` (with `Δ' : simplex_categoryᵒᵖ`).
Some morphisms between the summands of these coproducts are also studied.
When the simplicial operations are defined using the epi-mono factorisations in
`simplex_category`, the simplicial object `Γ₀.obj K` we get will be a split simplicial object.

-/

noncomputable theory

open category_theory category_theory.category category_theory.limits
  simplex_category simplicial_object
open_locale simplicial

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C] (K K' : chain_complex C ℕ) (f : K ⟶ K')
  {Δ'' Δ' Δ : simplex_category} (i' : Δ'' ⟶ Δ') [mono i'] (i : Δ' ⟶ Δ) [mono i]

/-- `is_δ₀ i` is a simple condition used to check whether a monomorphism `i` in
`simplex_category` identifies to the coface map `δ 0`. -/
@[nolint unused_arguments]
def is_δ₀ {Δ Δ' : simplex_category} (i : Δ' ⟶ Δ) [mono i] : Prop :=
(Δ.len = Δ'.len+1) ∧ (i.to_order_hom 0 ≠ 0)

namespace is_δ₀

lemma iff {j : ℕ} {i : fin (j+2)} : is_δ₀ (simplex_category.δ i) ↔ i = 0 :=
begin
  split,
  { rintro ⟨h₁, h₂⟩,
    by_contradiction,
    exact h₂ (fin.succ_above_ne_zero_zero h), },
  { rintro rfl,
    exact ⟨rfl, fin.succ_ne_zero _⟩, },
end

lemma eq_δ₀ {n : ℕ} {i : [n] ⟶ [n+1]} [mono i] (hi : is_δ₀ i) :
  i = simplex_category.δ 0 :=
begin
  unfreezingI { obtain ⟨j, rfl⟩ := simplex_category.eq_δ_of_mono i, },
  rw iff at hi,
  rw hi,
end

end is_δ₀

namespace Γ₀

namespace obj

/-- In the definition of `(Γ₀.obj K).obj Δ` as a direct sum indexed by `A : splitting.index_set Δ`,
the summand `summand K Δ A` is `K.X A.1.len`. -/
def summand (Δ : simplex_categoryᵒᵖ) (A : splitting.index_set Δ) : C := K.X A.1.unop.len

/-- The functor `Γ₀` sends a chain complex `K` to the simplicial object which
sends `Δ` to the direct sum of the objects `summand K Δ A` for all `A : splitting.index_set Δ` -/
def obj₂ (K : chain_complex C ℕ) (Δ : simplex_categoryᵒᵖ) [has_finite_coproducts C] : C :=
∐ (λ (A : splitting.index_set Δ), summand K Δ A)

namespace termwise

/-- A monomorphism `i : Δ' ⟶ Δ` induces a morphism `K.X Δ.len ⟶ K.X Δ'.len` which
is the identity if `Δ = Δ'`, the differential on the complex `K` if `i = δ 0`, and
zero otherwise. -/
def map_mono (K : chain_complex C ℕ) {Δ' Δ : simplex_category} (i : Δ' ⟶ Δ) [mono i] :
  K.X Δ.len ⟶ K.X Δ'.len :=
begin
  by_cases Δ = Δ',
  { exact eq_to_hom (by congr'), },
  { by_cases is_δ₀ i,
    { exact K.d Δ.len Δ'.len, },
    { exact 0, }, },
end

variable (Δ)

lemma map_mono_id : map_mono K (𝟙 Δ) = 𝟙 _ :=
by { unfold map_mono, simp only [eq_self_iff_true, eq_to_hom_refl, dite_eq_ite, if_true], }

variable {Δ}

lemma map_mono_δ₀' (hi : is_δ₀ i) : map_mono K i = K.d Δ.len Δ'.len :=
begin
  unfold map_mono,
  classical,
  rw [dif_neg, dif_pos hi],
  unfreezingI { rintro rfl, },
  simpa only [self_eq_add_right, nat.one_ne_zero] using hi.1,
end

@[simp]
lemma map_mono_δ₀ {n : ℕ} : map_mono K (δ (0 : fin (n+2))) = K.d (n+1) n :=
map_mono_δ₀' K _ (by rw is_δ₀.iff)

lemma map_mono_eq_zero (h₁ : Δ ≠ Δ') (h₂ : ¬is_δ₀ i) : map_mono K i = 0 :=
by { unfold map_mono, rw ne.def at h₁, split_ifs, refl, }

variables {K K'}

@[simp, reassoc]
lemma map_mono_naturality : map_mono K i ≫ f.f Δ'.len = f.f Δ.len ≫ map_mono K' i :=
begin
  unfold map_mono,
  split_ifs,
  { unfreezingI { subst h, },
    simp only [id_comp, eq_to_hom_refl, comp_id], },
  { rw homological_complex.hom.comm, },
  { rw [zero_comp, comp_zero], }
end

variable (K)

@[simp, reassoc]
lemma map_mono_comp : map_mono K i ≫ map_mono K i' = map_mono K (i' ≫ i) :=
begin
  /- case where i : Δ' ⟶ Δ is the identity -/
  by_cases h₁ : Δ = Δ',
  { unfreezingI { subst h₁, },
    simp only [simplex_category.eq_id_of_mono i,
      comp_id, id_comp, map_mono_id K, eq_to_hom_refl], },
  /- case where i' : Δ'' ⟶ Δ' is the identity -/
  by_cases h₂ : Δ' = Δ'',
  { unfreezingI { subst h₂, },
    simp only [simplex_category.eq_id_of_mono i',
      comp_id, id_comp, map_mono_id K, eq_to_hom_refl], },
  /- then the RHS is always zero -/
  obtain ⟨k, hk⟩ := nat.exists_eq_add_of_lt (len_lt_of_mono i h₁),
  obtain ⟨k', hk'⟩ := nat.exists_eq_add_of_lt (len_lt_of_mono i' h₂),
  have eq : Δ.len = Δ''.len + (k+k'+2) := by linarith,
  rw map_mono_eq_zero K (i' ≫ i) _ _, rotate,
  { by_contradiction,
    simpa only [self_eq_add_right, h] using eq, },
  { by_contradiction,
    simp only [h.1, add_right_inj] at eq,
    linarith, },
  /- in all cases, the LHS is also zero, either by definition, or because d ≫ d = 0 -/
  by_cases h₃ : is_δ₀ i,
  { by_cases h₄ : is_δ₀ i',
    { rw [map_mono_δ₀' K i h₃, map_mono_δ₀' K i' h₄,
        homological_complex.d_comp_d], },
    { simp only [map_mono_eq_zero K i' h₂ h₄, comp_zero], }, },
  { simp only [map_mono_eq_zero K i h₁ h₃, zero_comp], },
end

end termwise

end obj

end Γ₀

end dold_kan

end algebraic_topology
