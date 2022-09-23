/-
Copyright (c) 2022 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Matthias Uschold.
-/
import data.int.basic 
import data.int.range
import order.locally_finite
import algebra.group.basic 
import order.filter.basic

import topology.instances.real


import .Folner_amenable


/-!
# Example of a Folner amenable group

We construct an explicit Folner sequence for the additive group ℤ  (which 
we have to convert to a multiplicative group first), thus showing that
ℤ is amenable. 


## Main Definitions

- `Folner_sequence_Z`  : a Folner sequence for ℤ 

## Main Statements

- `Z_amenable`         : The group ℤ is amenable 

## References 
* [C. Löh, *Geometric Group Theory*, Example 9.2.2][loeh17]


## Tags
integers, Folner amenable, amenable,
-/

open classical 

open filter

notation `mulZ` := (multiplicative ℤ) -- the integers as a group (not an add_group)

section example_Folner

/-!
### Construction of a Folner sequence

As sets, we take the (integral) interval [-n,n]. 
We then just verify the desired properties. 

-/

/--Definition of the sets-/
def sets' : ℕ → finset ℤ
 := (λ n, finset.Icc (-(n:ℤ)) n)

/--The sets are nonempty -/
lemma sets_nonempty : ∀ n, sets' n ≠ ∅
:= begin 
  assume n,
  dsimp[sets'],
  by norm_num,
end


/--Cardinality of these sets-/
@[simp]
lemma sets_card : ∀ n, (sets' n).card = 2*n+1 
:= begin 
  assume n,
  unfold sets',
  rw int.card_Icc,
  simp,
  ring_nf,
end 





/-- The additive version of left_translate_set-/
def left_add_set 
  {G:Type*} [add_group G]
  (g : G)
  (A : finset G)
  : finset G 
:= finset.map (function.embedding.mk (λ x, g+x) (add_right_injective g)) A 

lemma translate_vs_add 
  {G:Type*} [add_group G]
  {g : G}
  {A : finset G}
  : left_add_set g A = @left_translate_set (multiplicative G) _ g A  
:= begin 
  dsimp[left_add_set, left_translate_set],
  congr,
end 

/-- Translation of an interval -/
@[simp]
lemma interval_translate
  {n : ℕ}
  {g : ℤ}
  : @left_translate_set mulZ _ g (sets' n) 
  = @finset.Icc ℤ _ _ (-(n:ℤ)+g) (n+g)
:= begin 
  rw ← translate_vs_add,
  dsimp[left_add_set],
  ext x,
  dsimp[sets'],
  simp,
  split,
  {
    assume exa,
    rcases exa with ⟨a, ⟨⟨ha₁, ha₂⟩, ha₃⟩⟩,
    split; linarith,
  },
  {
    assume h,
    use x-g,
    simp,
    split;linarith,
  },
end 

lemma interval_diff 
  {n : ℕ}
  {g : ℤ}
  (g_nonneg: g ≥ 0)
  (n_ge_g : (n:ℤ) ≥ g)
  : symm_diff (sets' n) (@left_translate_set mulZ  _ g (sets' n))
    ⊆ (finset.Ico (-(n:ℤ)) (-n+g)) ∪ (finset.Ioc (n:ℤ) (n+g))
:= begin 
  simp,
  dsimp [symm_diff],
  assume x xin,
  simp at xin,
  simp,
  unfold sets' at xin,
  cases xin,
  {
    left,
    simp at xin,
    split,  
      exact xin.left.left,
    by_contradiction,
    simp at h,
    have : (n:ℤ)+g < x := xin.right h,
    linarith,
  },
  right,
  simp at xin,
  split,
    apply xin.right,
    linarith,
  exact xin.left.right,
end 

lemma interval_diff' 
  {n : ℕ}
  {g : ℤ}
  (g_neg: g < 0)
  (n_ge_g : (n:ℤ) ≥ -g)
  : symm_diff (sets' n) (@left_translate_set mulZ _ g (sets' n))
   ⊆ (finset.Ico (-n+g) (-(n:ℤ)) ) ∪ (finset.Ioc (n+g) (n:ℤ) )
:= begin 
  simp,
  dsimp [symm_diff],
  assume x xin,
  simp at xin,
  simp,
  unfold sets' at xin,
  cases xin,
  {
    right,
    simp at xin,
    split,
      apply xin.right,
      linarith,
    exact xin.left.right,
  },
  left,
  simp at xin,
  apply and.intro xin.left.left,
  by_contradiction,
  simp at h,
  have : (n:ℤ) < x := xin.right h,
  by linarith,
end 

lemma symm_diff_card 
  {n : ℕ}
  {g : ℤ}
  (n_ge_g : (n:ℤ) ≥ abs g)
  : (symm_diff (sets' n) (@left_translate_set mulZ _ g (sets' n))).card ≤ 2 * (abs g).to_nat
:= begin 
  by_cases g_pos : g ≥ 0,
  {
    have n_ge_g : (n:ℤ) ≥ g,
    {
      rw ← abs_of_nonneg g_pos,
      exact n_ge_g,
    },
    calc  (symm_diff (sets' n) (@left_translate_set mulZ _ g (sets' n))).card 
        ≤ ((finset.Ico (-(n:ℤ)) (-(n:ℤ)+g) ) ∪ (finset.Ioc (n:ℤ) (n+g)  )).card 
          : by exact finset.card_le_of_subset (interval_diff g_pos n_ge_g) 
    ... ≤ (finset.Ico (-(n:ℤ)) (-(n:ℤ)+g) ).card  + (finset.Ioc (n:ℤ) (n+g)  ).card 
          : by exact finset.card_union_le _ _
    ... = g.to_nat + g.to_nat 
          : by simp 
    ... = 2 * g.to_nat
          : by ring 
    ... = 2 * (abs g).to_nat
          : by rw abs_of_nonneg g_pos,
  },
 {
    simp at g_pos,
    have n_ge_g : (n:ℤ) ≥ -g,
    {
      rw ← abs_of_neg g_pos,
      exact n_ge_g,
    },
    calc  (symm_diff (sets' n) (@left_translate_set mulZ _ g (sets' n))).card 
        ≤ ((finset.Ico(-(n:ℤ)+g) (-(n:ℤ))  ) ∪ (finset.Ioc ((n:ℤ)+g) (n:ℤ)   )).card 
          : by exact finset.card_le_of_subset (interval_diff' g_pos n_ge_g) 
    ... ≤ (finset.Ico (-(n:ℤ)+g)  (-(n:ℤ)) ).card  + (finset.Ioc ((n:ℤ)+g) (n:ℤ)  ).card 
          : by exact finset.card_union_le _ _
    ... = (-g).to_nat + (-g).to_nat 
          : by simp 
    ... = 2 * (-g).to_nat
          : by ring 
    ... = 2 * (abs g).to_nat
          : by rw abs_of_neg g_pos,
  },
end 


lemma eq_self_of_int_to_nat  
 : ∀ {x:ℤ}, x ≥ 0 → (x.to_nat:ℤ) = x  
:= begin 
  assume x,
  induction (x:ℤ),
  intro,
  simp,
  assume h,
  exfalso,
  finish,
end 

lemma eq_self_abs 
  {x:ℤ}
  : |x| = |x|.to_nat
:= begin 
  rw eq_self_of_int_to_nat,
  exact abs_nonneg x,
end 


/--proof that the Folner condition is satisfied -/
lemma Folner_cond : ∀ g : ℤ , 
        filter.tendsto (@Folner_quotients mulZ _ _ g sets')  filter.at_top (nhds 0)
:= begin 
  assume g,
  rw metric.tendsto_at_top,
  assume ε εpos,
  have : ∃ (N:ℕ), (N:ℝ) > (2 * (abs g) ) / ε 
    := exists_nat_gt (2 * |g| / ε),
  rcases this with ⟨N', hN'⟩,
  use max N' (abs g).to_nat,
  assume n nge,
  have n_ge_g: (n:ℤ) ≥ abs g,
    {
      simp at nge,
      exact nge.right,
    },
  unfold Folner_quotients,
  simp,
  have : (((@translate_symm_diff mulZ _ _ g (sets' n)).card):ℝ) < abs (2*n+1) * ε,
  {
    unfold translate_symm_diff,
    calc  ((symm_diff (sets' n) (@left_translate_set mulZ _ g (sets' n))).card :ℝ) 
        ≤    (((2:ℕ) * ((abs g).to_nat)) :ℝ ) 
          : by  {
              rw ← nat.cast_mul,
              exact nat.cast_le.mpr (symm_diff_card n_ge_g),
          }
    ... < N' * ε
          : by {
            simp at hN',
            rw (div_lt_iff εpos) at hN',
            simp at hN',
            have : |(g:ℝ)| = |g|.to_nat,
            {
              rw ← int.cast_abs,
              have : |g| = |g|.to_nat
                := eq_self_abs,
              rw this,
              generalize : |g| = z,
              simp,
            },
            rw ← this,
            finish,
          }
    ... < abs (2*n+1) *ε
          : by {
            have : n ≥ N' 
              := le_of_max_le_left nge,
            rw mul_lt_mul_right εpos,
            calc  (N':ℝ) 
                ≤ n 
                  : by {
                    simp,
                    exact this,
                  }
            ... < 2*n+1 
                  : by {
                       have : (n:ℝ) ≥ 0 := nat.cast_nonneg n,
                       by linarith,
                  }
            ... ≤ |2 * (n:ℝ) + 1|
                  : le_abs_self _,
          },
  },
  rw div_lt_iff,
    rw mul_comm at this,
    exact this,
  simp,
  have : 2*(n:ℝ) +1 ≥ 1 := by simp [nat.cast_nonneg n],
  by linarith,
end 


/--A Folner sequence for ℤ-/
def Folner_sequence_Z  
  : Folner_sequence mulZ 
:= Folner_sequence.mk sets' sets_nonempty Folner_cond 

/--Z (as a multiplicative group) is amenable-/
theorem Z_amenable  
  : amenable (multiplicative ℤ)
:= amenable_of_Folner_sequence Folner_sequence_Z


end example_Folner