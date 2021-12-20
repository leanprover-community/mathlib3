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

/-!

# The alternating face map complex of a simplicial object in a preadditive category

We construct the alternating face map complex, as a 
functor `alternating_face_map_complex : simplicial_object C ⥤ chain_complex C ℕ`
for any preadditive category `C`. For any simplicial object `X` in `C`,
this is the homological complex `... → X_2 → X_1 → X_0`
where the differentials are alternate sums of faces.

We also construct the natural transformation `inclusion_of_Moore_complex :
nat_trans (normalized_Moore_complex A) (alternating_face_map_complex A)` 
when `A` is an abelian category

## References
* https://stacks.math.columbia.edu/tag/0194
* https://ncatlab.org/nlab/show/Moore+complex

-/

open category_theory category_theory.limits category_theory.subobject
open opposite
open_locale big_operators

noncomputable theory

namespace algebraic_topology

namespace alternating_face_map_complex

@[simp]
def obj_X {C : Type*} [category C] (X : simplicial_object C) (n : ℕ) :=
X.obj(op(simplex_category.mk n))

variables {C : Type*} [category C] [preadditive C]
variables (X : simplicial_object C)
variables (Y : simplicial_object C)

@[simp]
def obj_d (n : ℕ) : (obj_X X (n+1)) ⟶ (obj_X X n) :=
∑ i in finset.range(n+2), ((-1 : ℤ)^i • X.δ i)

/-!
## Proof of the chain complex relation `d ≫ d` 

The expansion of `d ≫ d` involves a double sum, or a sum of terms
indexed by a set of the form {0,...,n} × {0,...,n+1}. We shall show
a general cancellation lemma `antisymmetric_sum_cancels` of such sums when
the terms f_{i,j} satisfy an "antisymmetry" relation f_{i,j+1} = -f_{j,i}
for i≤j, The cancellation lemma follows from the study of a certain
involution `τ` on `ℕ × ℕ`.

### Definition of an involution `τ : ℕ × ℕ → ℕ × ℕ`

-/

/--
We split elements `ℕ × ℕ` into two cases. "Case 1" is the situation of
tuples `(i,j)` such that `i<j`, and "Case 2" is the other situation. These
two subsets are exchanged by τ
-/
def τ (x : ℕ × ℕ ) : ℕ × ℕ :=
if x.1 < x.2
  then (x.2-1,x.1)
  else (x.2,x.1+1)

lemma τ_case1 (x : ℕ × ℕ) (hx : (x.1<x.2)) : τ x = (x.2-1,x.1) :=
by { rw τ, split_ifs, refl }

lemma τ_case2 (x : ℕ × ℕ) (hx : ¬x.1<x.2) : τ x = (x.2,x.1+1) :=
by { rw τ, split_ifs, refl }

lemma τ_of_case2_is_case1 (x : ℕ × ℕ) (hx : ¬x.1<x.2) : (τ x).1<(τ x).2 :=
by { rw τ_case2 x hx, linarith, }

lemma τ_of_case1_is_case2 (x : ℕ × ℕ) (hx : x.1<x.2) : ¬(τ x).1<(τ x).2 :=
begin
  rw τ_case1 x hx,
  cases x.2,
  { exfalso, linarith, },
  { intro htx,
    rw nat.succ_sub_one at htx,
    have h1 := nat.le_of_lt_succ hx,
    linarith, },
end

lemma τ_inv (x : ℕ × ℕ) : τ (τ x) = x :=
begin
  by_cases x.1<x.2,
  { rw τ_case2 (τ x) (τ_of_case1_is_case2 x h),
    rw τ_case1 x h,
    ext; simp only,
      cases x.2 with m,
      { linarith, },
      { exact nat.succ_sub_one m.succ, }, },
  { rw τ_case1 (τ x) (τ_of_case2_is_case1 x h),
    rw τ_case2 x h,
    simp only [nat.add_succ_sub_one, add_zero, prod.mk.eta], },
end

/-- τ has no fixed point -/
lemma τ_ne' (x : ℕ × ℕ) : τ x ≠ x :=
begin
  have case1 : ∀ (y : ℕ × ℕ), y.1<y.2 → τ y ≠ y,
  { intros y hy h1,
    rw τ_case1 y hy at h1,
    have h2 := congr_arg prod.snd h1, 
    simp only at h2,
    linarith, },
  have case2 : ∀ (y : ℕ × ℕ), ¬y.1<y.2 → τ y ≠ y,
  { intros y hy h1,
    exact case1 (τ y) (τ_of_case2_is_case1 y hy) (congr_arg τ h1), },
  by_cases x.1<x.2,
  { exact case1 x h, },
  { exact case2 x h, },
end

/-!
### Verification that τ induces an involution τ' on {0,...,n} × {0,...,n+1}

`indices n` denotes `{0,...,n} × {0,...,n+1}` as a finite subset of `ℕ × ℕ`
-/

def indices (n : ℕ) : finset (ℕ × ℕ) := 
finset.product (finset.range(n+1)) (finset.range(n+2))

/-- τ stabilises {0,...,n} × {0,...,n+1} -/
lemma τ'_mem' {n : ℕ} (x : ℕ × ℕ) (hx : x ∈ indices n) : τ x ∈ indices n :=
begin
  simp only [indices, finset.mem_product, finset.mem_range] at hx,
  cases hx with hx1 hx2,
  by_cases x.1<x.2,
  { rw τ_case1 x h,
    simp only [indices, finset.mem_product, finset.mem_range],
    split,
      { exact nat.pred_lt_pred (show x.2 ≠ 0, by linarith) hx2, },
      { linarith, }, },
  { rw τ_case2 x h,
    simp only [indices, finset.mem_product, finset.mem_range],
    split; linarith, }
end

/-!
### Cancellation of "antisymmetric" sums indexed by {0,...,n} × {0,...,n+1}
-/

variables {α : Type*}

/-- The proof uses finset.sum_involution. Then, from the assumption, we need
to show that for all x in {0,...,n} × {0,...,n+1}, we have `f x + f (τ x) = 0`.
-/
lemma antisymmetric_sum_cancels [add_comm_group α] {n : ℕ} (f : ℕ × ℕ → α)
  (antisymmetry_f : ∀ (i j : ℕ), i≤j → j≤n → f (i,j+1) = - f (j,i)) :
  ∑ x in (indices n), f x = 0 :=
begin
  have hf_case2 : ∀ (x : ℕ × ℕ) (h2x : ¬x.1<x.2) 
    (hx : x ∈ indices n), f x + f (τ x) = 0,
  { intros x h2x hx,
    rw τ_case2 x h2x,
    simp only [indices, finset.mem_product, finset.mem_range] at hx,
    rw antisymmetry_f x.2 x.1 (by linarith) (by linarith),
    simp only [prod.mk.eta, add_right_neg], },
  have hf_case1 : ∀ (x : ℕ × ℕ) (h1x : x.1<x.2) 
    (hx : x ∈ indices n), f x + f (τ x) = 0,
  { intros x h1x hx,
    rw add_comm,
    have eq := hf_case2 (τ x) (τ_of_case1_is_case2 x h1x) (τ'_mem' x hx),
    rw τ_inv x at eq,
    exact eq, },
  let τ' : ∀ (x : ℕ × ℕ), x ∈ indices n → ℕ × ℕ := λ x hx, τ x,
  have τ'_eq_τ : ∀ (x : ℕ × ℕ) (hx : x ∈ indices n), τ' x hx = τ x := by { intros x hx, refl, },
  have hf : ∀ (x : ℕ × ℕ) (hx : x ∈ indices n), f x + f (τ' x hx) = 0,
  { intros x hx,
    rw τ'_eq_τ x hx,
    by_cases x.1<x.2,
    { exact hf_case1 x h hx, },
    { exact hf_case2 x h hx, }, },
  exact finset.sum_involution τ' hf (λ x _ _, τ_ne' x)
    τ'_mem' (λ x _, τ_inv x),
end


/-!
### Antisymmetry property for the terms that appear in the expansion of `d ≫ d`
-/

def di_dj (n : ℕ) (x : ℕ × ℕ) : (obj_X X (n+2)) ⟶ (obj_X X n) :=
((-1 : ℤ)^x.2 • X.δ x.2) ≫ ((-1 : ℤ)^x.1 • X.δ x.1)

lemma di_dj_antisymm (n i j : ℕ) (hij : i≤j) (hjn : j≤n+1) :
  (di_dj X n (i,j+1)) = - di_dj X n (j,i) :=
begin
  repeat { rw di_dj },
  simp only,
  repeat { rw category_theory.preadditive.comp_zsmul },
  repeat { rw category_theory.preadditive.zsmul_comp },
  repeat { rw ← mul_smul },
  have eq : -((-1)^i * (-1)^j : ℤ) = (-1)^i * (-1)^(j+1) := by ring_exp,
  rw [← eq, mul_comm, ← neg_smul],
  apply congr_arg,
  /- the equality shall follow from simplicial identities -/
  have ineq : (i : fin(n+2)) ≤ j,
  { rw ← fin.coe_fin_le,
    rw fin.coe_coe_of_lt (show i<n+2, by linarith),
    rw fin.coe_coe_of_lt (show j<n+2, by linarith),
    exact hij, },
  have hi : fin.cast_succ (i : fin(n+2)) = (i : fin(n+3)),
  { ext,
    rw fin.coe_cast_succ,
    rw fin.coe_coe_of_lt (show i<n+2, by linarith),
    rw fin.coe_coe_of_lt (show i<n+3, by linarith), },
  have hj : (j : fin(n+2)).succ = ((j+1) : ℕ),
  { ext,
    rw fin.coe_succ,
    rw fin.coe_coe_of_lt (show j+1<n+3, by linarith),
    rw fin.coe_coe_of_lt (show j<n+2, by linarith), },
  have seq := category_theory.simplicial_object.δ_comp_δ X ineq,
  rw [hi, hj] at seq,
  exact seq,
end

/-!
### End of the proof of `d ≫ d = 0`
-/
lemma d_squared (n : ℕ) : obj_d X (n+1) ≫ obj_d X n = 0 :=
begin
  repeat { rw obj_d },
  rw preadditive.comp_sum,
  let d_l := (λ (j:ℕ), (-1 : ℤ)^j • X.δ (j : fin(n+3))),
  let d_r := (λ (i:ℕ), (-1 : ℤ)^i • X.δ (i : fin(n+2))),
  rw [show (λ i, (∑ j in finset.range(n+3), d_l j) ≫ d_r i) =
    (λ i, ∑ j in finset.range(n+3), di_dj X n (i,j)),
    by { ext, rw preadditive.sum_comp, refl }],
  rw ← finset.sum_product',
  clear d_l d_r,
  exact antisymmetric_sum_cancels (di_dj X n) (di_dj_antisymm X n),
end

/-!
## Construction of the alternating face map complex functor
-/

def obj : chain_complex C ℕ := chain_complex.of (obj_X X) (obj_d X) (d_squared X)

variables {X} {Y}

@[simp]
def map (f : X ⟶ Y) : obj X ⟶ obj Y :=
chain_complex.of_hom _ _ _ _ _ _
  (λ n, f.app(op(simplex_category.mk n)))
  (λ n,
    begin
      repeat { rw obj_d },
      rw [preadditive.comp_sum, preadditive.sum_comp],
      apply congr_arg (finset.range(n+2)).sum,
      ext,
      rw category_theory.preadditive.comp_zsmul,
      rw category_theory.preadditive.zsmul_comp,
      apply congr_arg,
      erw f.naturality,
      refl,
    end)

end alternating_face_map_complex

variables (C : Type*) [category C] [preadditive C]

@[simps]
def alternating_face_map_complex : simplicial_object C ⥤ chain_complex C ℕ :=
{ obj := alternating_face_map_complex.obj,
  map := λ X Y f, alternating_face_map_complex.map f }

/-!
## Construction of the natural inclusion of the normalized Moore complex
-/

variables {A : Type*} [category A] [abelian A]
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
      let t := λ (j : ℕ), (normalized_Moore_complex.obj_X X (n+1)).arrow ≫
        ((-1 : ℤ)^j • X.δ j),
      have def_t : (∀ j, t j = (normalized_Moore_complex.obj_X X (n+1)).arrow ≫
        ((-1 : ℤ)^j • X.δ j)) := by { intro j, refl, },
      have h := finset.sum_range_add t 1 (n+1),
      rw finset.sum_range_one at h,
      have null : (∀ j, j ∈ finset.range(n+1) → t (1+j) = 0),
      { intros j hj,
        simp only [finset.mem_range] at hj,
        rw def_t,
        rw preadditive.comp_zsmul,
        rw ← zsmul_zero ((-1 : ℤ)^(1+j)),
        apply congr_arg,
        rw normalized_Moore_complex.obj_X,
        rw [show ((1+j : ℕ) : (fin(n+2))) = (j : fin(n+1)).succ, by
          { ext,
            rw fin.coe_succ,
            rw fin.coe_coe_of_lt (show j<n+1, by linarith),
            rw fin.coe_coe_of_lt (show 1+j<n+2, by linarith),
            rw add_comm, }],
        rw ← factor_thru_arrow _ _
          (finset_inf_arrow_factors finset.univ _ (j : fin(n+1)) (by simp)),
        slice_lhs 2 3 { erw kernel_subobject_arrow_comp (X.δ (j:fin(n+1)).succ), },
        simp, },
      rw finset.sum_eq_zero null at h,
      rw [show 1+(n+1)=n+2, by linarith] at h,
      rw h,
      simp only [add_zero],

      /- finally, we study the remaining term which is induced by X.δ 0 -/
      let eq := def_t 0,
      rw [show (-1 : ℤ)^0 = 1, by ring] at eq,
      rw one_smul at eq,
      rw eq,
      clear eq null def_t h t,
      cases n; dsimp; simp,
    end)

@[simp]
lemma inclusion_of_Moore_complex_map_f (X : simplicial_object A) (n : ℕ) :
  (inclusion_of_Moore_complex_map X).f n = (normalized_Moore_complex.obj_X X n).arrow :=
chain_complex.of_hom_f _ _ _ _ _ _ _ _ n

variables (A)

@[simps]
def inclusion_of_Moore_complex :
  nat_trans (normalized_Moore_complex A) (alternating_face_map_complex A) :=
{ app := inclusion_of_Moore_complex_map, }

end algebraic_topology

