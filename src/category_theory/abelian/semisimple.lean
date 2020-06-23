/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.constructions.products
import category_theory.limits.shapes.constructions.binary_products
import category_theory.abelian.basic
import category_theory.abelian.additive
import category_theory.simple
import category_theory.schur

open category_theory.limits

namespace category_theory

universes v u
variables {C : Type u} [category.{v} C]

section
variables [has_zero_morphisms.{v} C] [has_finite_biproducts.{v} C]

structure decomposition_over {ι : Type v} (Z : ι → C) (X : C) :=
(κ : Type v)
[fintype : fintype κ]
[decidable_eq : decidable_eq κ]
(summand : κ → ι)
(iso : X ≅ ⨁ (λ k, Z (summand k)))

structure simple_decomposition (X : C) :=
(ι : Type v)
[fintype : fintype ι]
[decidable_eq : decidable_eq ι]
(summand : ι → C)
[is_simple : Π i, simple.{v} (summand i)]
(iso : X ≅ ⨁ summand)

attribute [instance] simple_decomposition.fintype simple_decomposition.decidable_eq
attribute [instance] simple_decomposition.is_simple

def simple_decomposition.multiplicity
  [decidable_rel (λ X Y : C, nonempty (X ≅ Y))] -- This will presumably be provided by classical logic.
  {X : C} (D : simple_decomposition.{v} X) (Y : C) [simple.{v} Y] : ℕ :=
fintype.card { i // nonempty (D.summand i ≅ Y) }

end

def equiv_punit_sum_of_term {α : Type v} [decidable_eq α] [fintype α] (a : α) :
  Σ' (β : Type v) [decidable_eq β] [fintype β] (e : α ≃ punit.{v+1} ⊕ β),
     e.symm (sum.inl punit.star) = a ∧ (by exactI fintype.card β = fintype.card α - 1) :=
⟨{a' // a' ≠ a},
by apply_instance,
by apply_instance,
{ to_fun := λ a', if h : a' = a then sum.inl punit.star else sum.inr ⟨a', h⟩,
  inv_fun := λ p, match p with | sum.inl _ := a | sum.inr v := v.1 end,
  left_inv := λ a',
  begin
    dsimp, split_ifs,
    { subst h, unfold_aux, simp, },
    { unfold_aux, simp, }
  end,
  right_inv := λ p,
  begin
    rcases p with ⟨⟨p⟩⟩|⟨a',ne⟩,
    { unfold_aux, simp, },
    { unfold_aux, simp [ne], },
  end, },
rfl,
sorry⟩

section
variables [has_zero_morphisms.{v} C]

lemma foo {I J : Type v} [fintype I] [decidable_eq I] [fintype J] [decidable_eq J] (f : I ⊕ J → C)
  [has_finite_biproducts.{v} C] [has_binary_biproducts.{v} C] :
  product_over_sum_iso f = coproduct_over_sum_iso f :=
begin
  ext1, ext1; ext1 p; cases p; ext1 x,
  { by_cases h : p = x; { simp [biproduct.ι_π, h], }, },
  { simp, },
  { simp, },
  { by_cases h : p = x; { simp [biproduct.ι_π, h], }, },
end

def biproduct_iso_of_equiv_punit_sum {I J : Type v} [fintype I] [decidable_eq I] [fintype J] [decidable_eq J] (f : I → C) (e : I ≃ punit.{v+1} ⊕ J)
  [has_finite_biproducts.{v} C] [has_binary_biproducts.{v} C] :
  ⨁ f ≅ f (e.symm (sum.inl punit.star)) ⊞ ⨁ (λ j, f (e.symm (sum.inr j))) :=
calc ⨁ f ≅ ⨁ (λ p, f (e.symm p))
           : product_iso_of_equiv f e
     ... ≅ (⨁ (λ j, f (e.symm (sum.inl j)))) ⊞ (⨁ (λ j, f (e.symm (sum.inr j))))
           : product_over_sum_iso _
     ... ≅ f (e.symm (sum.inl punit.star)) ⊞ ⨁ (λ j, f (e.symm (sum.inr j)))
           : biprod.map_iso (product_over_unique_iso (λ j, f (e.symm (sum.inl j)))) (iso.refl _)

@[simp,reassoc]
lemma srt {I J : Type v} [fintype I] [decidable_eq I] [fintype J] [decidable_eq J] (f : I → C) (e : I ≃ punit.{v+1} ⊕ J)
  [has_finite_biproducts.{v} C] [has_binary_biproducts.{v} C] :
(biproduct_iso_of_equiv_punit_sum f e).hom ≫ biprod.fst = biproduct.π f (e.symm (sum.inl punit.star)) :=
begin
  simp [biproduct_iso_of_equiv_punit_sum], refl,
end

@[simp,reassoc]
lemma quux {I J : Type v} [fintype I] [decidable_eq I] [fintype J] [decidable_eq J] (f : I → C) (e : I ≃ punit.{v+1} ⊕ J)
  [has_finite_biproducts.{v} C] [has_binary_biproducts.{v} C] :
  biprod.inl ≫ (biproduct_iso_of_equiv_punit_sum f e).inv = biproduct.ι f (e.symm (sum.inl punit.star)) :=
begin
  simp only [biproduct_iso_of_equiv_punit_sum],
  rw foo,
  simp,
  refl,
end

end

section

variables [preadditive.{v} C] [has_finite_biproducts.{v} C] -- TODO these should add up to `additive`?
variables [has_kernels.{v} C] -- We need this for Schur's lemma.
variables [∀ X Y : C, decidable_eq (X ⟶ Y)]


def equiv_of_simple_decompositions' (n : ℕ) {X : C}
  (D E : simple_decomposition.{v} X) (w : fintype.card D.ι = n) :
  trunc Σ e : D.ι ≃ E.ι, Π i, E.summand (e i) ≅ D.summand i :=
begin
  induction n with n ih generalizing X,
  { sorry, },
  have s : trunc D.ι := trunc_of_card_pos (by { rw w, exact nat.succ_pos n, }),
  trunc_cases s,
  obtain ⟨ιD, dD, fD, eD, hD, cD⟩ := equiv_punit_sum_of_term s,
  set f : ⨁ D.summand ≅ ⨁ E.summand := D.iso.symm.trans E.iso,
  have column_nonzero :=
    biproduct.column_nonzero_of_iso s (id_nonzero _) f.hom,
  trunc_cases column_nonzero,
  rcases column_nonzero with ⟨t, nz⟩,
  obtain ⟨ιE, dE, fE, eE, hE, cE⟩ := equiv_punit_sum_of_term t,
  resetI,
  set X' : C := ⨁ (λ i, D.summand (eD.symm (sum.inr i))),

  -- We only use these internally, so it doesn't matter if they're not your favorites!
  haveI := has_binary_biproducts_of_finite_biproducts C,

  set h₁ : ⨁ D.summand ≅ (D.summand s) ⊞ (⨁ (λ i, D.summand (eD.symm (sum.inr i)))) :=
    (biproduct_iso_of_equiv_punit_sum D.summand eD).trans
      (biprod.map_iso (congr_eq_to_iso _ hD) (iso.refl _)),
  set h₂ : ⨁ E.summand ≅ (E.summand t) ⊞ (⨁ (λ i, E.summand (eE.symm (sum.inr i)))) :=
    (biproduct_iso_of_equiv_punit_sum E.summand eE).trans
      (biprod.map_iso (congr_eq_to_iso _ hE) (iso.refl _)),
  have h : ⨁ (λ i, D.summand (eD.symm (sum.inr i))) ≅ ⨁ (λ i, E.summand (eE.symm (sum.inr i))),
  { set h' := ((h₁.symm.trans f).trans h₂),
    have t : biprod.inl ≫ h'.hom ≫ biprod.fst =
      biproduct.ι D.summand s ≫ f.hom ≫ biproduct.π E.summand t,
    { simp only [h', h₁, h₂], simp, },
    haveI : is_iso (biprod.inl ≫ h'.hom ≫ biprod.fst) := by { rw t, exact is_iso_of_hom_simple nz, },
    exact biprod.iso_elim h', },
  sorry,
  -- set D' : simple_decomposition X' :=
  -- { ι := ιD,
  --   summand := λ i, D.summand (eD.symm (sum.inr i)),
  --   iso := iso.refl _, },
  -- set E' : simple_decomposition X' :=
  -- { ι := ιE,
  --   summand := λ i, E.summand (eE.symm (sum.inr i)),
  --   iso := h, },
  -- have e₂ := ih D' E' (by { rw w at cD, exact cD, }),
  -- trunc_cases e₂ with e₂,
  -- rcases e₂ with ⟨e₂, π'⟩,
  -- set e := (eD.trans (equiv.sum_congr (equiv.refl _) e₂)).trans eE.symm,
  -- have π : Π (i : D.ι), E.summand (e i) ≅ D.summand i,
  -- { intro i,
  --   by_cases i = s,
  --   { subst h,
  --     simp only [e],
  --     replace hD : eD i = sum.inl punit.star, { rw ←hD, simp, },
  --     simp [hD, hE],
  --     exact (as_iso (biproduct.ι D.summand i ≫ f.hom ≫ biproduct.π E.summand t)).symm, },
  --   { have p : Σ' i' : ιD, (eD.symm) (sum.inr i') = i,
  --     { rcases w : eD i with ⟨⟨⟩⟩|i',
  --       { rw ←w at hD, simp only [equiv.symm_apply_apply] at hD, exfalso, exact h hD, },
  --       { use i', rw ←w, simp, }, },
  --     obtain ⟨i', w⟩ := p,
  --     calc E.summand (e i) ≅ E'.summand (e₂ i') : _
  --     ... ≅ D'.summand i' : π' i'
  --     ... ≅ D.summand i : _,
  --     { dsimp [E', e], rw ←w, simp, },
  --     { dsimp [D'], rw w, }, }, },
  -- exact trunc.mk ⟨e, π⟩,
end

def equiv_of_simple_decompositions {X : C} (D E : simple_decomposition.{v} X) :
  trunc Σ e : D.ι ≃ E.ι, Π i, E.summand (e i) ≅ D.summand i :=
equiv_of_simple_decompositions' (fintype.card D.ι) D E rfl

open_locale classical

lemma multiplicity_constant {X : C} (D E : simple_decomposition.{v} X) (Y : C) [simple.{v} Y] :
  D.multiplicity Y = E.multiplicity Y :=
begin
  obtain ⟨e, f⟩ := equiv_of_simple_decompositions D E,
  dsimp [simple_decomposition.multiplicity],
  apply fintype.card_congr,
  refine equiv.subtype_congr e _,
  intro i,
  refine equiv.nonempty_iff_nonempty _,
  exact
  { to_fun := λ e', (f i).trans e',
    inv_fun := λ e', (f i).symm.trans e',
    left_inv := by { intro i, simp, },
    right_inv := by { intro i, simp, }, }
end

end

variables (C) [preadditive.{v} C] [has_finite_biproducts.{v} C]
class semisimple :=
(simple_decomposition : Π X : C, trunc (simple_decomposition.{v} X))

variables {C} [semisimple.{v} C] [has_kernels.{v} C]
variables [decidable_rel (λ X Y : C, nonempty (X ≅ Y))]
variables [∀ X Y : C, decidable_eq (X ⟶ Y)]

def multiplicity (Y : C) [simple.{v} Y] (X : C) : ℕ :=
begin
  have D := semisimple.simple_decomposition.{v} X,
  trunc_cases D,
  { exact D.multiplicity Y, },
  { convert multiplicity_constant a b Y, },
end

end category_theory
