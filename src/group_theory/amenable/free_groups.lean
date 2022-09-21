/-
Copyright (c) 2022 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold.
-/

import .def_amenable
import .aux_lemmas_bounded
import .quotient
import group_theory.free_group


/-!
# Nonamenability of Free groups

We prove that free groups (of rank at least two) are not amenable.

## Main Statements

- `F2_not_amenable`      : The free group on two generators is not amenable
- `not_amenable_of_free` : Free groups on at least two generators are not amenable


## References
* [C. Löh, *Geometric Group Theory*, Proposition 9.1.5][loeh17]
* <https://en.wikipedia.org/wiki/Amenable_group>
* [A.L.T. Paterson, *Amenability*, Example 0.6][Paterson1988]

## Tags
free groups, amenable, amenability

-/

open classical





/--a type with two elements-/
inductive ab
| a
| b

open ab


noncomputable instance ab_dec
  : decidable_eq ab
:= dec_eq ab



local notation `F2` := free_group ab




namespace F2_not_amenable_calc
/--Define a map giving the first letter of an element

We obtain the first letter by first taking the reduced word of the element,
then applying list.head' to this list

Note: This returns `none` on the neutral element -/
noncomputable def first_letter
  : F2 → option (ab × bool)
:= (λ w : F2, list.head' (free_group.to_word w))




/-! ### Characteristic Functions
-/
section indicator

noncomputable def indicator_bcont (p: F2 → Prop)
  : bounded_continuous_function F2 ℝ
:= bounded_continuous_function.mk
        (continuous_map.mk
          (set.indicator {w : F2 | p w} (λ x,1))
          continuous_of_discrete_topology)
        (begin
          rw function_bounded_classical,
          use 1,
          assume x : F2,
          simp,
          by_cases h : p x; finish,
        end)


lemma indicator_bcont_apply
  {p: F2 → Prop}
  {w : F2}
  : indicator_bcont p w = set.indicator {w : F2 | p w} (λ x,1) w
:= by refl


/-! Evaluating indicator functions -/
@[simp]
lemma indicator_bcont_apply1
  {p: F2 → Prop}
  {w : F2}
  (pw: p w)
  : indicator_bcont p w = 1
:= by simp [indicator_bcont_apply]; finish

@[simp]
lemma indicator_bcont_apply0
  {p: F2 → Prop}
  {w : F2}
  (npw: ¬ p w)
  : indicator_bcont p w = 0
:= by simp [indicator_bcont_apply]; finish

/--The sum of indicator functions belonging to disjoint predicates-/
lemma indicator_sum
  {p q: F2 → Prop}
  (pq_disjoint: ∀ (w:F2), p w → q w → false)
  : indicator_bcont p + indicator_bcont q = indicator_bcont (λ w, p w ∨ q w)
:= begin
  ext (x: F2),
  by_cases hp : p x,
  {
    simp,
    rw indicator_bcont_apply1 hp,
    have not_q : ¬ q x:= pq_disjoint x hp,
    rw indicator_bcont_apply0 not_q,
    rw indicator_bcont_apply1,
      linarith,
    left,
    assumption,
  },
  by_cases hq : q x,
  {
    simp,
    rw indicator_bcont_apply0 hp,
    rw indicator_bcont_apply1 hq,
    rw indicator_bcont_apply1,
      by linarith,
    right,
    assumption,
  },
  simp,
  rw indicator_bcont_apply0 hp,
  rw indicator_bcont_apply0 hq,
  rw indicator_bcont_apply0,
    by linarith,
  by tauto,
end

/--Indicator functions are nonnegative -/
lemma indicator_pos
  {p: F2 → Prop}
  : ∀ w : F2, indicator_bcont p w ≥ 0
:= begin
  assume w : F2,
  by_cases p w,
    rw indicator_bcont_apply1,
    linarith,
    assumption,
  rw indicator_bcont_apply0,
  linarith,
  assumption,
end

/--Indicator functions are ≤ 1 -/
lemma indicator_le1
  {p: F2 → Prop}
  : ∀ w : F2, indicator_bcont p w ≤ 1
:= begin
  assume w : F2,
   by_cases p w,
    rw indicator_bcont_apply1 h,
  rw indicator_bcont_apply0 h,
  by linarith,
end

/--Left translate of Indicator functions-/
lemma lefttransl_of_indicator
  {p: F2 → Prop}
  {g : F2}
  : left_translate g (indicator_bcont p) = indicator_bcont (λ x, p (g⁻¹*x))
:= begin
  ext (x:F2),
  rw left_translate_eval,
  tauto,
end

lemma mean_indicator_pos
  {p: F2 → Prop}
  {m: mean F2}
  : m (indicator_bcont p) ≥ 0
:= m.positivity indicator_pos

end indicator



/-!
  ### Main Idea
  The main idea is the following: We partition F2 into five subsets
  (depending on which letter a word starts with).

  We establish how these sets / indicator functions translate into one
  another and conclude that no left invariant mean can exist.
-/


@[simp]
noncomputable def ind_a
  : bounded_continuous_function F2 ℝ
:= indicator_bcont (λ w, first_letter w = some (a,tt))

@[simp]
noncomputable def ind_ainv
  : bounded_continuous_function F2 ℝ
:= indicator_bcont (λ w, first_letter w = some (a,ff))

@[simp]
noncomputable def ind_b
  : bounded_continuous_function F2 ℝ
:= indicator_bcont (λ w, first_letter w = some (b,tt))

@[simp]
noncomputable def ind_binv
  : bounded_continuous_function F2 ℝ
:= indicator_bcont (λ w, first_letter w = some (b,ff))




section aw_starts

/-!
Some technical lemmas establishing which letter
the word a*w starts with
-/

@[simp]
lemma mk_to_word
  {L: list (ab × bool)}
  : (free_group.mk L).to_word = free_group.reduce L
:= by simp [free_group.to_word]


/--A technical lemma -/
lemma reduce_step_reduced
  {x y : ab × bool}
  {L : list (ab × bool)}
  (Lred: free_group.reduce (y :: L) = y :: L)
  : free_group.reduce (x :: y :: L) =
          ite (x.fst = y.fst ∧ x.snd = !y.snd)
            L
            (x :: y :: L)
:= begin
  rw free_group.reduce.cons,
  rw Lred,
end

/-- If L is a reduced list and does not start with a⁻¹,
then a :: L starts with a -/
lemma aw_start_a_lists_reduced
  {a' : ab} -- think of as 'a' when proving but can also be b
  {L : list (ab × bool)}
  (hL: L.head' ≠ some (a', ff))
  (Lred: free_group.reduce L = L)
  : (free_group.reduce ((a', tt) :: L)).head' = some (a',tt)
:= begin
  cases L,
    simp [free_group.reduce],
  simp at hL,
  have : free_group.reduce ((a', tt) :: L_hd :: L_tl)
        = (a', tt) :: L_hd :: L_tl,
  {
    have : ¬((a',tt).fst = L_hd.fst ∧ (a',tt).snd = !L_hd.snd), -- should be easy
    {
      simp,
      assume L_hd_first_a',
      cases L_hd,
      simp,
      simp at L_hd_first_a',
      simp at hL,
      have : L_hd_snd = tt
          := hL L_hd_first_a'.symm,
      rw this,
    },


    calc free_group.reduce ((a',tt) :: L_hd :: L_tl)
      = ite ((a',tt).fst = L_hd.fst ∧ (a',tt).snd = !L_hd.snd) L_tl ((a',tt) :: L_hd :: L_tl)
        : by exact reduce_step_reduced Lred
    ... = (a',tt) :: L_hd :: L_tl
        : by simp [this],
  },
  by simp [this]; dsimp[head']; simp,
end


/-- The same lemma as above for lists-/
lemma aw_start_a_lists
  {a' : ab} -- think of as 'a' when proving but can also be b
  {L : list (ab × bool)}
  (hL: (free_group.reduce L).head' ≠ some (a', ff))
  : (free_group.reduce ((a', tt) :: L)).head' = some (a',tt)
:= begin
  have two_red : free_group.reduce ((a', tt) :: L)
              = free_group.reduce ((a', tt) :: free_group.reduce L),
  {
    have : free_group.red L (free_group.reduce L)
          := free_group.reduce.red,
    have append_red:
           free_group.red ((a', tt) :: L) ((a', tt) :: free_group.reduce L)
          := free_group.red.cons_cons this,
    exact free_group.reduce.eq_of_red append_red,
  },
  have Lred : free_group.reduce (free_group.reduce L) = free_group.reduce L
      := free_group.reduce.idem,
  calc  (free_group.reduce ((a', tt) :: L)).head'
      = (free_group.reduce ((a', tt) :: free_group.reduce L)).head'
        : by rw two_red
  ... = some (a', tt)
        : by exact aw_start_a_lists_reduced hL Lred,
end

/-- The main lemma that will be used : If w is an element of F2
whose reduced word does not start with a⁻¹,
then a*w starts with a (as there will be no cancellation)-/
lemma aw_start_a
  {a' : ab} -- think of as 'a' when proving but can also be b
  {w : F2}
  :  ( first_letter w ≠ some (a', ff))
    → first_letter ((free_group.of a')*w) = some (a',tt)
:= begin
  apply quot.induction_on w,
  assume (L : list (ab × bool)),
  assume first_letter_neq_ainv,
  dsimp[first_letter],
  dsimp[first_letter] at first_letter_neq_ainv,
  --simp only [mk_to_word] at first_letter_neq_ainv,
  simp only[free_group.of, free_group.mul_mk],
  rw mk_to_word,
  show (free_group.reduce ([(a', tt)] ++ L)).head' = some (a', tt),
  by exact aw_start_a_lists first_letter_neq_ainv,
end


end aw_starts


/-- The sum of the following indicator functions is at least 1
  (any word starts with a, or a* this word does)-/
lemma sum_transl_ind_a_ainv
  (a' : ab)
  :  left_translate (free_group.of a')⁻¹ (indicator_bcont (λ w, first_letter w = some (a',tt)))
    + indicator_bcont (λ w, first_letter w = some (a',ff))
    ≥ 1
:= begin
  assume (w:F2),
  by_cases hw : first_letter w = some (a',ff),
    simp,
    have : indicator_bcont (λ w, first_letter w = some (a',ff)) w = 1
      := indicator_bcont_apply1 hw,
    rw this,
    simp,
    exact indicator_pos _,
  rw lefttransl_of_indicator,
  simp,
  have : first_letter (free_group.of a' * w) = some (a', tt)
      := aw_start_a hw,
  have : ⇑(indicator_bcont (λ (x : F2), first_letter (free_group.of a' * x) = some (a', tt))) w
          = 1
      := indicator_bcont_apply1 this,
  rw this,
  simp,
  exact indicator_pos _,
end



/--Lemma that is used in ind_sum -/
lemma ind_sum_lemma
 : ∀ (w : F2), first_letter w = some (a, tt) → first_letter w = some (a, ff) → false
:= begin
  assume w firstw₁ firstw₂,
  by finish,
end

/--Lemma that is used in ind_sum no. 2 -/
lemma ind_sum_lemma'
  : ∀ (w : F2),
    first_letter w = some (a, tt) ∨ first_letter w = some (a, ff)
  → first_letter w = some (b, tt)
  → false
:= begin
   assume w firstw,
    cases firstw,
    {
      by finish,
    },
    {
      by finish,
    },
end


/--The sum of these indicator functions is at most one
(their predicates are disjoint)-/
lemma ind_sum
  : ind_a + ind_ainv + ind_b + ind_binv
   ≤  bounded_continuous_function.const F2 (1:ℝ)
:= begin
  dsimp [ind_a, ind_ainv, ind_b, ind_binv],
  repeat {rw indicator_sum},
    exact indicator_le1,
  --left to prove 'trivial' nonequality statements
  {
    assume w firstw,
    cases firstw,
      cases firstw,
        by finish,
      by finish,
    by finish,
  },
  exact ind_sum_lemma',
  exact ind_sum_lemma,
end

-- this is somehow necessary
lemma invmean_add
  {G: Type*} [group G]
  {m : left_invariant_mean G}
  {f g: bounded_continuous_function G ℝ}
  : m (f+g) = m f + m g
:= m.to_mean.lin_map.map_add' f g

end F2_not_amenable_calc

open mean
open F2_not_amenable_calc

lemma mean_add_four
  {a b c d : bounded_continuous_function F2 ℝ}
  {m : left_invariant_mean F2}
  : m a + m b + m c +  m d = m (a+b) + m (c+d)
:= begin
  rw invmean_add,
  rw invmean_add,
  by ring,
end

/--The free group on two generators is not amenable-/
theorem F2_not_amenable
  : ¬ amenable (free_group ab)
:= begin
  assume h : amenable F2,
  let m : left_invariant_mean F2 := invmean_of_amenable h,

  have sum_le_1 : m ind_a + m ind_ainv + m ind_b + m ind_binv ≤ 1,
  {
    calc  m ind_a + m ind_ainv + m ind_b + m ind_binv
        = m (ind_a +  ind_ainv +  ind_b +  ind_binv)
          : by repeat {rw invmean_add}
    ... ≤ m (bounded_continuous_function.const F2 (1:ℝ))
          : by exact mean_monotone F2 ind_sum
    ... = 1
          : by exact m.normality,
  },

  have sum_ge_2 : m ind_a + m ind_ainv + m ind_b + m ind_binv ≥ 2,
  {
    have inv_ind_a : m (left_translate (free_group.of a)⁻¹ ind_a) = m ind_a
          := m.left_invariance _ _,
    have inv_ind_b : m (left_translate (free_group.of b)⁻¹ ind_b) = m ind_b
          := m.left_invariance _ _,

    calc   m ind_a + m ind_ainv + m ind_b + m ind_binv
         = m (left_translate (free_group.of a)⁻¹ ind_a) + m ind_ainv
         + m (left_translate (free_group.of b)⁻¹ ind_b) + m ind_binv
          : by rw ← inv_ind_a; rw ← inv_ind_b
    ...  = m (left_translate (free_group.of a)⁻¹ ind_a +  ind_ainv)
         + m (left_translate (free_group.of b)⁻¹ ind_b +  ind_binv)
          : by exact mean_add_four
    ...  ≥ m (bounded_continuous_function.const F2 (1:ℝ))
         + m (bounded_continuous_function.const F2 (1:ℝ))
          : by {
            have : m (left_translate (free_group.of a)⁻¹ ind_a +  ind_ainv)
                ≥ m (bounded_continuous_function.const F2 (1:ℝ))
                := mean_monotone F2 (sum_transl_ind_a_ainv a),
            have : m (left_translate (free_group.of b)⁻¹ ind_b +  ind_binv)
                ≥ m (bounded_continuous_function.const F2 (1:ℝ))
                := mean_monotone F2 (sum_transl_ind_a_ainv b),
            by linarith,
          }
    ...  = 2
          : by {
            have : m (bounded_continuous_function.const F2 (1:ℝ)) = 1
                    := m.normality,
            by linarith,
          },
  },

  by linarith only [sum_ge_2, sum_le_1],
end





open function

/-!
We establish that free groups (on at least two generators)
are not amenable because they have F2 as a quotient.
-/

/--Corollary: Free groups are not amenable-/
theorem not_amenable_of_free
  {X : Type*}
  {a' b' : X}
  (hab : a' ≠ b')
  : ¬ amenable (free_group X)
:= begin
  -- Assume that the free group were amenable
  -- and show that then F2 would be amenable
  assume is_amenable : amenable (free_group X),
  classical,
  -- define maps in both directions
  -- to see that F2 is a quotient of free_group X
  let p' : X → ab
    := (λ x, ite (x=a') a b),
  let p : (free_group X) →* (free_group ab)
      := free_group.map p',
  let s' : ab → X
      := (λ x, ab.rec_on x a' b'),
  let s : (free_group ab) →* (free_group X)
      := free_group.map s',
  -- s is a split of p
  have : p ∘ s = id,
  {
    dsimp[p,s],
    ext (w: free_group ab),
    simp,
    rw free_group.map.comp,
    have : p' ∘ s' = id,
    {
      ext (a' : ab),
      dsimp[p',s'],
      cases a',
        by simp,
      simp,
      exact (λ eq', hab eq'.symm),
    },
    rw this,
    exact free_group.map.id _,
  },

  have p_surj : surjective p,
  {
    have : left_inverse p s
      := left_inverse_iff_comp.mpr this,
    exact left_inverse.surjective this,
  },
  have F2_am : amenable (free_group ab)
    := amenable_of_quotient' p p_surj is_amenable,
  exact F2_not_amenable F2_am,
end
