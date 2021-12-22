/-
Copyright (c) 2021 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebra.homology.homological_complex
import algebraic_topology.simplicial_object
import algebraic_topology.Moore_complex
import category_theory.abelian.basic
import algebra.big_operators.basic
import tactic.ring_exp
import data.fintype.card

/-!

# The alternating face map complex of a simplicial object in a preadditive category

We construct the alternating face map complex, as a
functor `alternating_face_map_complex : simplicial_object C ⥤ chain_complex C ℕ`
for any preadditive category `C`. For any simplicial object `X` in `C`,
this is the homological complex `... → X_2 → X_1 → X_0`
where the differentials are alternating sums of faces.

We also construct the natural transformation
`inclusion_of_Moore_complex : normalized_Moore_complex A ⟶ alternating_face_map_complex A`
when `A` is an abelian category.

## References
* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex

-/

open category_theory category_theory.limits category_theory.subobject
open opposite

open_locale big_operators
open_locale simplicial

noncomputable theory

namespace algebraic_topology

namespace alternating_face_map_complex

/-!
## Construction of the alternating face map complex
-/

/-- In degree n, the alternating face map complex is given by
the nth-object of the simplicial object -/
@[simp]
def obj_X {C : Type*} [category C] (X : simplicial_object C) (n : ℕ) :=
X.obj (op [n])

variables {C : Type*} [category C] [preadditive C]
variables (X : simplicial_object C)
variables (Y : simplicial_object C)

/-- The differential on the alternating face map complex is the alternate
sum of the face maps -/
@[simp]
def obj_d (n : ℕ) : obj_X X (n+1) ⟶ obj_X X n :=
∑ (i : fin (n+2)), (-1 : ℤ)^(i : ℕ) • X.δ i

/--
## The chain complex relation `d ≫ d`
-/
lemma d_squared (n : ℕ) : obj_d X (n+1) ≫ obj_d X n = 0 :=
begin
  /- we start by expanding d ≫ d as a double sum -/
  repeat { rw obj_d },
  rw preadditive.comp_sum,
  let d_l := λ (j : fin (n+3)), (-1 : ℤ)^(j : ℕ) • X.δ j,
  let d_r := λ (i : fin (n+2)), (-1 : ℤ)^(i : ℕ) • X.δ i,
  rw [show (λ i , (∑ j : fin (n+3), d_l j) ≫ d_r i) =
    (λ i, ∑ j : fin (n+3), (d_l j ≫ d_r i)), by { ext i, rw preadditive.sum_comp, }],
  rw ← finset.sum_product',
  /- then, we decompose the index set P into a subet S and its complement Sᶜ -/ 
  let P := fin (n+2) × fin (n+3),
  let S := finset.univ.filter (λ (ij : P), (ij.2 : ℕ) ≤ (ij.1 : ℕ)),
  let term := λ (ij : P), d_l ij.2 ≫ d_r ij.1,
  erw [show ∑ (ij : P), term ij =
    (∑ ij in S, term ij) + (∑ ij in Sᶜ, term ij), by rw finset.sum_add_sum_compl],
  rw [← eq_neg_iff_add_eq_zero, ← finset.sum_neg_distrib],
  /- we are reduced to showing that two sums are equal, and this is obtained
  by constructing a bijection φ : S -> Sᶜ, which maps (i,j) to (j,i+1),
  and by comparing the terms -/ 
  let φ : Π (ij : P), ij ∈ S → P := λ ij hij,
    (fin.cast_lt ij.2
      (lt_of_le_of_lt (finset.mem_filter.mp hij).right (fin.is_lt ij.1)), ij.1.succ),
  apply finset.sum_bij φ,
  { -- φ(S) is contained in Sᶜ
    intros ij hij,
    simp only [finset.mem_univ, finset.compl_filter, finset.mem_filter, true_and,
      fin.coe_succ, fin.coe_cast_lt] at hij ⊢,
    linarith, },
  { /- identification of corresponding terms in both sums -/
    rintro ⟨i, j⟩ hij,
    let jj : fin (n+2) := (φ (i,j) hij).1,
    simp only [finset.mem_filter, finset.mem_univ, true_and] at hij,
    simp only [term, d_l, d_r, φ],
    simp only,
    clear term d_l d_r,
    repeat { rw [category_theory.preadditive.comp_zsmul,
      category_theory.preadditive.zsmul_comp], },
    rw [← neg_smul, ← mul_smul, ← mul_smul],
    rw [← show (-1 : ℤ)^(i : ℕ) * (-1 : ℤ)^(j : ℕ) =
        - (-1 : ℤ)^(jj : ℕ) * (-1 : ℤ)^(i.succ : ℕ), by
      { simp only [fin.coe_succ, fin.coe_cast_lt], ring_exp, }],
    apply congr_arg,
    have ineq : jj ≤ i, { rw ← fin.coe_fin_le, exact hij, },
    rw category_theory.simplicial_object.δ_comp_δ X ineq,
    simp only [fin.cast_succ_cast_lt], },
  { -- φ : S → Sᶜ is injective
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij hij' h,
    rw [prod.mk.inj_iff],
    split,
    { have h1 := congr_arg prod.snd h,
      simp only [fin.succ_inj] at h1,
      exact congr_arg _ h1 },
    { have h1 := congr_arg fin.cast_succ (congr_arg prod.fst h),
      simp only [fin.cast_succ_cast_lt] at h1,
      exact h1, }, },
  { -- φ : S → Sᶜ is surjective
    clear term d_l d_r,
    rintro ⟨i', j'⟩ hij',
    simp only [true_and, finset.mem_univ, finset.compl_filter, not_le,
      finset.mem_filter] at hij',
    refine ⟨(j'.pred _,fin.cast_succ i'),_,_⟩,
    { intro H,
      rw [H] at hij',
      simp only [nat.not_lt_zero, fin.coe_zero] at hij',
      exact hij', },
    { simp only [true_and, finset.mem_univ, fin.coe_cast_succ, fin.coe_pred,
        finset.mem_filter],
      exact nat.le_pred_of_lt hij', },
    { simp only [prod.mk.inj_iff, fin.succ_pred, fin.cast_lt_cast_succ],
      split; refl, }, },
end

/-!
## Construction of the alternating face map complex functor
-/

/-- The alternating face map complex, on objects -/
def obj : chain_complex C ℕ := chain_complex.of (obj_X X) (obj_d X) (d_squared X)

variables {X} {Y}

/-- The alternating face map complex, on morphisms -/
@[simp]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
chain_complex.of_hom _ _ _ _ _ _
  (λ n, f.app (op [n]))
  (λ n,
    begin
      repeat { rw obj_d },
      rw [preadditive.comp_sum, preadditive.sum_comp],
      apply congr_arg,
      ext,
      rw category_theory.preadditive.comp_zsmul,
      rw category_theory.preadditive.zsmul_comp,
      apply congr_arg,
      erw f.naturality,
      refl,
    end)

end alternating_face_map_complex

variables (C : Type*) [category C] [preadditive C]

/-- The alternating face map complex, as a functor -/
@[simps]
def alternating_face_map_complex : simplicial_object C ⥤ chain_complex C ℕ :=
{ obj := alternating_face_map_complex.obj,
  map := λ X Y f, alternating_face_map_complex.map f }

/-!
## Construction of the natural inclusion of the normalized Moore complex
-/

variables {A : Type*} [category A] [abelian A]

/-- The inclusion map of the Moore complex in the alternating face map complex -/
def inclusion_of_Moore_complex_map (X : simplicial_object A) :
  (normalized_Moore_complex A).obj X ⟶ (alternating_face_map_complex A).obj X :=
chain_complex.of_hom _ _ _ _ _ _
  (λ n, (normalized_Moore_complex.obj_X X n).arrow)
  (λ n,
    begin
      /- we have to show the compatibility of the differentials on the alternating
         face map complex with those defined on the normalized Moore complex:
         we first get rid of the terms of the alternating sum that are obviously
         zero on the normalized_Moore_complex -/
      simp only [alternating_face_map_complex.obj_d],
      rw preadditive.comp_sum,
      let t := λ (j : fin (n+2)), (normalized_Moore_complex.obj_X X (n+1)).arrow ≫
        ((-1 : ℤ)^(j : ℕ) • X.δ j),
      have def_t : (∀ j : fin (n+2), t j = (normalized_Moore_complex.obj_X X (n+1)).arrow ≫
        ((-1 : ℤ)^(j : ℕ) • X.δ j)) := by { intro j, refl, },
      rw [fin.sum_univ_succ t],
      have null : ∀ j : fin (n+1), t j.succ = 0,
      { intro j,
        rw def_t,
        rw preadditive.comp_zsmul,
        rw ← zsmul_zero ((-1 : ℤ)^(j.succ : ℕ)),
        apply congr_arg,
        rw normalized_Moore_complex.obj_X,
        rw ← factor_thru_arrow _ _
          (finset_inf_arrow_factors finset.univ _ j (by simp only [finset.mem_univ])),
        slice_lhs 2 3 { erw kernel_subobject_arrow_comp (X.δ j.succ), },
        simp only [comp_zero], },
      rw [fintype.sum_eq_zero _ null],
      simp only [add_zero],
      /- finally, we study the remaining term which is induced by X.δ 0 -/
      let eq := def_t 0,
      rw [show (-1 : ℤ)^((0 : fin (n+2)) : ℕ) = 1, by ring] at eq,
      rw one_smul at eq,
      rw eq,
      clear eq null def_t t,
      cases n; dsimp; simp,
    end)

@[simp]
lemma inclusion_of_Moore_complex_map_f (X : simplicial_object A) (n : ℕ) :
  (inclusion_of_Moore_complex_map X).f n = (normalized_Moore_complex.obj_X X n).arrow :=
chain_complex.of_hom_f _ _ _ _ _ _ _ _ n

variables (A)

/-- The inclusion map of the Moore complex in the alternating face map complex,
as a natural transformation -/
@[simps]
def inclusion_of_Moore_complex :
  nat_trans (normalized_Moore_complex A) (alternating_face_map_complex A) :=
{ app := inclusion_of_Moore_complex_map, }

end algebraic_topology

