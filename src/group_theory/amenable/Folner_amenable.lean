/-
Copyright (c) 2022 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold.
-/

import tactic
import algebra.group.basic
import topology.basic
import topology.algebra.polynomial
import topology.separation
import data.real.basic
import data.finset.basic
import .def_amenable


import topology.continuous_function.bounded

import algebra.big_operators.basic
import algebra.big_operators.order

import .nonprincipal_ultrafilter
import .aux_lemmas_sums
import .aux_lemmas_bounded

/-!

# Amenability via Følner sets

We define Følner amenability (i.e. amenability via the existence of
a Folner set). Because of restrictions with finset, this requires
decidable equality on the group (at least for the moment).

This characterisation is useful, in particular because it allows to explicitely
exhibit that some groups are amenable (e.g. ℤ, which is done in `Folner_example.lean`).


## Main Definitions

- `Folner_sequence`             : Structure of a Folner sequence
- `Folner_amenable`             : Folner amenability (i.e. there exists a Folner sequence)
- `inv_mean_of_Folner_seq`      : Construction of an invariant mean out of a Folner sequence

## Main Statements

- `amenable_of_Folner_sequence` : If a group admits a Folner-sequence, it is amenable
- `amenable_of_Folner_amenable` : Folner amenability implies amenability

## References
* [C. Löh, *Geometric Group Theory*, Section 9.2.1, Theorem 9.2.6][loeh17]


## Tags

Folner sequence, Følner sequence, Folner amenable,
Følner amenable

-/
open classical
open real
open finset





variables
{G: Type*}
[group G]



/--left-translating a finite set of elements-/
def left_translate_set
  (g : G)
  (A : finset G)
  : finset G
:= finset.map (function.embedding.mk (λ x, g*x) (mul_right_injective g)) A

open_locale big_operators -- to enable ∑ notation


variable  [decidable_eq G]

/--summing over left-translates can be expressed via the left-translation
of the function -/
lemma left_translate_summation
  (g:G)
  (A : finset G)
  (f : bounded_continuous_function G ℝ)
  : ∑ x in left_translate_set g⁻¹ A,  f x = ∑ x in A, (left_translate g f) x
:= begin
  dsimp [left_translate_set],
  simp,
end


def translate_symm_diff
  (g: G)
  (A : finset G)
  : finset G
:= symm_diff A (left_translate_set g A)


/--The sequence appearing in the Folner condition -/
noncomputable def Folner_quotients
  (g: G)
  (sets: ℕ → finset G)
  : ℕ → ℝ
:= (λ n:ℕ, ((translate_symm_diff g (sets n)).card : ℝ)
                / (sets n).card)

/--Structure for a Folner sequence,
  most important: The Folner condition -/
structure Folner_sequence
  (G: Type*)
  [group G]
  [decidable_eq G]
:= mk ::
  (sets: ℕ → finset G)
  (sets_nonempty: ∀ n, sets n ≠ ∅)
  (Folner_cond : ∀ g : G,
        filter.tendsto (Folner_quotients g sets)  filter.at_top (nhds 0))

/--often, we speak of the sets when talking about the Folner seq-/
instance : has_coe (Folner_sequence G) (ℕ → finset G)
      := {coe := Folner_sequence.sets}

/--A group is called Folner amenable if there exists a Folner sequence-/
def Folner_amenable
  (G: Type*)
  [group G]
  [decidable_eq G]
  : Prop
:= nonempty (Folner_sequence G)

/- have to get rid of decidable
equality-/

lemma nonzero_card_of_Folner_sequence
  (F : Folner_sequence G)
  : ∀{n:ℕ}, ((F.sets n).card :ℝ) ≠ 0
:= begin
  assume n,
  simp,
  exact F.sets_nonempty n,
end

/--If a group is Folner amenable, we can pick a Folner sequence-/
noncomputable def Folner_sequence_of_Folner_amenable
  (h : Folner_amenable G)
  : Folner_sequence G
:= classical.some (classical.exists_true_of_nonempty h)




namespace Folner_amenable_to_amenable

/-!

  ### Folner amenability implies amenability

  We have to construct a left invariant mean from a Folner sequence.
  The main idea is to average over the Folner sets, then take the
  limit with respect to a nonprincipal ultrafilter (which always exists
  if the sequence is bounded). The left-invariance will then follow from
  the Folner condition
-/


open bounded_continuous_function
open_locale big_operators -- to enable ∑ notation

/--The sequence of averages-/
@[simp]
noncomputable def avg_seq
  (sets: ℕ → finset G)
  (f : bounded_continuous_function G ℝ)
  : ℕ → ℝ
:= (λ n, (1:ℝ)/(sets n).card *  ∑ x in sets n, f x)



lemma nonneg_one_over_card
  {A : Type*}
  {S : finset A}
  : (1:ℝ) / S.card ≥ 0
:= begin
  apply div_nonneg,
  by simp,
  simp,
end

@[simp]
lemma abs_one_over_card
  {A : Type*}
  {S : finset A}
  : |(1:ℝ) / S.card | = (1:ℝ) / S.card
:= abs_of_nonneg nonneg_one_over_card

lemma avg_seq_add
  {sets: ℕ → finset G}
  {f g : bounded_continuous_function G ℝ}
  : avg_seq sets (f+g) = avg_seq sets f + avg_seq sets g
:= begin
  ext n,
  calc  avg_seq sets (f + g) n
      = (1:ℝ)/(sets n).card *  ∑ x in sets n, (f+g) x
        : by simp
  ... = (1:ℝ)/(sets n).card *  ∑ x in sets n, (f x + g x)
        : by tauto
  ... = (1:ℝ)/(sets n).card *  (∑ x in sets n, f x + ∑ x in sets n, g x)
        : by {congr' 1, simp [finset.sum_add_distrib],}
  ... = (1:ℝ)/(sets n).card *  ∑ x in sets n, f x
        + (1:ℝ)/(sets n).card *  ∑ x in sets n, g x
        : by ring
  ... = avg_seq sets f n + avg_seq sets g n
        : by simp,
end

lemma avg_seq_smul
  {sets: ℕ → finset G}
  {a:ℝ}
  {f : bounded_continuous_function G ℝ}
  : avg_seq sets (a•f) = a•avg_seq sets f
:= begin
  ext n,
  calc  avg_seq sets (a • f) n
      = (1:ℝ)/(sets n).card *  ∑ x in sets n, (a•f) x
        : by simp
  ... = (1:ℝ)/(sets n).card *  ∑ x in sets n, a*(f x)
        : by tauto
  ... = (1:ℝ)/(sets n).card * (a* ∑ x in sets n, (f x))
        : by {congr' 1, exact sum_scalar a,}
  ... = a * ((1:ℝ)/(sets n).card *  ∑ x in sets n, f x)
        : by ring
  ... = (a • avg_seq sets f) n
        : by simp,
end


open filter

/--The sequence of averages converges to a real number
(wrt a fixed nonprincipal ultrafilter)-/
lemma avg_seq_conv
  (F: Folner_sequence G)
  (f : bounded_continuous_function G ℝ)
  : ∃ x:ℝ, filter.tendsto (avg_seq F.sets f) (hyperfilter ℕ) (nhds x)
:=
begin
  -- We apply the ultrafilter convergence theorem :
  -- It therefore suffices to show that the sequence is bounded
  apply ultrafilter_convergence_R,

  -- The same bound as for f works
  have f_bound : ∃ (C:ℝ), ∀ (g:G), abs (f g) ≤ C
      := function_bounded_classical' f,
  rcases f_bound with ⟨C, f_bound⟩,
  use C,
  assume n:ℕ,
  calc  |avg_seq F.sets f n|
      = |(1:ℝ)/(F.sets n).card *  ∑ x in F.sets n, f x|
        : by simp[avg_seq]
  ... = |(1:ℝ)/(F.sets n).card| *  |∑ x in F.sets n, f x|
        : abs_mul (1 / ↑((F.sets n).card)) (∑ (x : G) in F.sets n, f x)
  ... ≤ |(1:ℝ)/(F.sets n).card| *  ∑ x in F.sets n, |f x|
        : by {
          apply mul_le_mul_of_nonneg_left,
            exact is_absolute_value.abv_sum abs (λ (i : G), f i) (F.sets n),
          exact abs_nonneg _,
        }
  ... ≤ |(1:ℝ)/(F.sets n).card| *  ∑ x in F.sets n, C
        : by {
          apply mul_le_mul_of_nonneg_left,
            apply finset.sum_le_sum,
            intros x xin,
            exact f_bound x,
          exact abs_nonneg _,
        }
  ... = |(1:ℝ)/(F.sets n).card| * ((F.sets n).card *C )
        : by {congr' 1, simp,}
  ... = (|(1:ℝ)/(F.sets n).card| * (F.sets n).card) *C
        : by ring
  ... = ((1:ℝ)/(F.sets n).card * (F.sets n).card) *C
        : by rw abs_one_over_card
  ... = (1:ℝ) * C
        : by {congr' 1,
              exact (eq_div_iff (nonzero_card_of_Folner_sequence F)).mp rfl,}
  ... = C
        : by simp,
end

/-- The sequence is nonnegative if f is nonnegative-/
lemma avg_seq_pos
  (F: Folner_sequence G)
  {f : bounded_continuous_function G ℝ}
  (fpos : ∀ x : G, f x ≥ 0)
  : ∀ n: ℕ, avg_seq F.sets f n ≥ 0
:= begin
  assume n:ℕ,
  calc  avg_seq F.sets f n
      = (1:ℝ)/(F.sets n).card *  ∑ x in F.sets n, f x
        : by simp
  ... ≥ (1:ℝ)/(F.sets n).card * ∑ x in F.sets n, 0
        : by {
          apply mul_le_mul_of_nonneg_left,
            apply finset.sum_le_sum,
            assume x xin,
            exact fpos x,
          exact nonneg_one_over_card,
        }
  ... = 0
        : by simp,
end


/-- We pick (the) limit as mean function-/
noncomputable def mean_fct_of_Folner_seq
  (F: Folner_sequence G)
  : (bounded_continuous_function G ℝ) → ℝ
:= (λ f, classical.some (avg_seq_conv F f))



lemma mean_fct_of_Folner_seq_spec
  (F: Folner_sequence G)
  (f: bounded_continuous_function G ℝ)
  : filter.tendsto (avg_seq F.sets f) (hyperfilter ℕ)
        (nhds (mean_fct_of_Folner_seq F f))
:= classical.some_spec (avg_seq_conv F f)

/--The limit is unique-/
lemma mean_fct_of_Folner_unique
  (F: Folner_sequence G)
  (f: bounded_continuous_function G ℝ)
  {x:ℝ}
  (avg_tendsto_x : filter.tendsto (avg_seq F.sets f) (hyperfilter ℕ)
                    (nhds x))
  : mean_fct_of_Folner_seq F f = x
:= begin
  symmetry,
  apply tendsto_nhds_unique avg_tendsto_x,
  exact mean_fct_of_Folner_seq_spec F f,
end


lemma mean_lin_fct_of_Folner_seq_add
  (F: Folner_sequence G)
  : ∀ f g, (mean_fct_of_Folner_seq F) (f+g) =
            (mean_fct_of_Folner_seq F) f + (mean_fct_of_Folner_seq F) g
:= begin
  assume f g : bounded_continuous_function G ℝ,
  apply mean_fct_of_Folner_unique,
  rw avg_seq_add,
  apply filter.tendsto.add,
  exact mean_fct_of_Folner_seq_spec F f,
  exact mean_fct_of_Folner_seq_spec F g,
end

lemma mean_lin_fct_of_Folner_seq_smul
  (F: Folner_sequence G)
  : ∀a:ℝ, ∀ f, (mean_fct_of_Folner_seq F) (a•f) =
            a•mean_fct_of_Folner_seq F f
:= begin
  assume a: ℝ,
  assume f: bounded_continuous_function G ℝ,
  apply mean_fct_of_Folner_unique,
  have : a • mean_fct_of_Folner_seq F f = a * mean_fct_of_Folner_seq F f
      := by simp,
  rw this,
  rw avg_seq_smul,
  exact filter.tendsto.const_mul a (mean_fct_of_Folner_seq_spec F f),
end

/--The mean function is linear-/
noncomputable def mean_lin_fct_of_Folner_seq
  (F: Folner_sequence G)
  : (bounded_continuous_function G ℝ) →ₗ[ℝ] ℝ
:= linear_map.mk (mean_fct_of_Folner_seq F)
      (mean_lin_fct_of_Folner_seq_add F)
      (mean_lin_fct_of_Folner_seq_smul F)

@[simp]
lemma mean_lin_fct_of_Folner_seq_apply
  (F: Folner_sequence G)
  (f: bounded_continuous_function G ℝ)
  : mean_lin_fct_of_Folner_seq F f = mean_fct_of_Folner_seq F f
:= by refl

lemma avg_seq_const
  (F: Folner_sequence G)
  : ∀ n:ℕ, avg_seq F.sets (bounded_continuous_function.const G (1:ℝ)) n = 1
:= begin
  assume n,
  dsimp[avg_seq],
  simp,
  have : ((F.sets n).card:ℝ) ≠ 0,
  {
    simp,
    exact F.sets_nonempty n,
  },
  exact inv_mul_cancel this,
end

lemma mean_lin_fct_of_Folner_seq_normality
   (F: Folner_sequence G)
  : (mean_lin_fct_of_Folner_seq F) (bounded_continuous_function.const G (1:ℝ)) = 1
:= begin
  simp,
  apply mean_fct_of_Folner_unique,
  have avg_seq_is_one : avg_seq F.sets (const G 1) = (λ n, (1:ℝ)),
  {
    ext n,
    calc  avg_seq F.sets (const G 1) n
        = (1:ℝ)/(F.sets n).card *  ∑ x in F.sets n, (const G 1) x
          : by simp
    ... = (1:ℝ)/(F.sets n).card *  ∑ x in F.sets n, 1
          : by simp
    ... = (1:ℝ)/(F.sets n).card * (F.sets n).card
          : by simp
    ... = (1:ℝ)
          : by exact (eq_div_iff (nonzero_card_of_Folner_sequence F)).mp rfl,
  },
  rw avg_seq_is_one,
  exact tendsto_const_nhds,
end


lemma mean_lin_fct_of_Folner_seq_positivity
   (F: Folner_sequence G)
  : ∀ {f : bounded_continuous_function G ℝ},
                          (∀ (x:G), f x ≥ 0) → (mean_lin_fct_of_Folner_seq F) f ≥ 0
:= begin
  assume f,
  assume fpos,
  have avg_pos : ∀ n, avg_seq F.sets f n ≥ 0
        := avg_seq_pos F fpos,
  exact limit_positive_of_positive_ultrafilter
        (mean_fct_of_Folner_seq_spec F f)
        avg_pos,
end

/--We obtain a mean from avg_seq-/
noncomputable def mean_of_Folner_seq
  (F: Folner_sequence G)
  : mean G
:= mean.mk (mean_lin_fct_of_Folner_seq F)
           (mean_lin_fct_of_Folner_seq_normality F)
           (@mean_lin_fct_of_Folner_seq_positivity G _ _ F)

@[simp]
lemma mean_of_Folner_seq_simp
  (F: Folner_sequence G)
  (f : bounded_continuous_function G ℝ)
  : mean_of_Folner_seq F f =  mean_fct_of_Folner_seq  F f
:= by refl


/--additional lemma on the absolute value of differences-/
lemma abs_le_symm_diff_of_diff_sum
  {α : Type*} [decidable_eq α]
  {S T:finset α}
  {f: α → ℝ}
  : |∑ x in S, f x - ∑ x in T, f x|
  ≤ ∑ x in symm_diff S T, |f x|
:= begin
  calc  |∑ x in S, f x - ∑ x in T, f x|
      = |∑ x in S \ T, f x - ∑ x in T \ S, f x|
        : by rw  finset.sum_sdiff_sub_sum_sdiff
  ... ≤ |∑ x in S \ T, f x| + |∑ x in T \ S, f x|
        : abs_sub _ _
  ... ≤ ∑ x in S \ T, |f x| + ∑ x in T \ S, |f x|
        : by {
          apply add_le_add; exact finset.abs_sum_le_sum_abs _ _,
        }
  ... = ∑ x in symm_diff S T, |f x|
        : by {
          dsimp[symm_diff],
          exact eq.symm (finset.sum_union (begin
            unfold disjoint,
            assume x xininters,
            finish,
          end)),
        },
end



/--This mean is left-invariant
  (this basically is a long technical calculation, the
  main reason is that the Folner condition holds)-/
lemma mean_of_Folner_seq_inv
  (F: Folner_sequence G)
  : ∀(g:G), ∀(f: bounded_continuous_function G ℝ),
      (mean_of_Folner_seq F) (left_translate g f)
    = (mean_of_Folner_seq F)  f
:= begin
  assume g f,
  simp,
  -- choose a constant that bounds f
  have f_bound : ∃ (C:ℝ), ∀ (g:G), abs (f g) ≤ C
      := function_bounded_classical' f,
  rcases f_bound with ⟨C, f_bound⟩,

  -- difference in avg_seq is given by
  -- symmetric difference
  have avg_diff : ∀ n:ℕ,
    |avg_seq F.sets f n - avg_seq F.sets (left_translate g f) n|
   ≤ (1:ℝ)/(F.sets n).card * ∑ x in translate_symm_diff g⁻¹ (F.sets n), |f x|,
  {
    assume n,
    calc  |avg_seq F.sets f n - avg_seq F.sets (left_translate g f) n|
        = |(1:ℝ)/(F.sets n).card *  ∑ x in F.sets n, f x
            - (1:ℝ)/(F.sets n).card *  ∑ x in F.sets n, (left_translate g f) x|
          : by refl
    ... = |(1:ℝ)/(F.sets n).card *  ∑ x in F.sets n, f x
            - (1:ℝ)/(F.sets n).card *  ∑ x in (left_translate_set g⁻¹ (F.sets n)), f x|
          : by rw left_translate_summation
    ... = |(1:ℝ)/(F.sets n).card *  (∑ x in F.sets n, f x
            -  ∑ x in (left_translate_set g⁻¹ (F.sets n)), f x)|
          : by ring_nf
    ... = |(1:ℝ)/(F.sets n).card | * |(∑ x in F.sets n, f x
            -  ∑ x in (left_translate_set g⁻¹ (F.sets n)), f x)|
          : by exact abs_mul _ _
    ... ≤  |(1:ℝ)/(F.sets n).card| * ∑ x in translate_symm_diff g⁻¹ (F.sets n), |f x|
          : by {apply mul_le_mul_of_nonneg_left,
                exact abs_le_symm_diff_of_diff_sum,
                exact abs_nonneg _,
              }
    ... = (1:ℝ)/(F.sets n).card * ∑ x in translate_symm_diff g⁻¹ (F.sets n), |f x|
          : by {congr' 1, exact abs_one_over_card},
  },

  have avg_diff_bound : ∀ n, (1:ℝ)/(F.sets n).card * ∑ x in translate_symm_diff g⁻¹ (F.sets n), |f x|
              ≤ C * Folner_quotients g⁻¹ F.sets n,
  {
    assume n:ℕ,
    calc  (1:ℝ)/(F.sets n).card * ∑ x in translate_symm_diff g⁻¹ (F.sets n), |f x|
        ≤ (1:ℝ)/(F.sets n).card * ∑ x in translate_symm_diff g⁻¹ (F.sets n), C
          : by {
            apply mul_le_mul_of_nonneg_left,
              apply finset.sum_le_sum,
              assume x xin,
              exact f_bound x,
            exact nonneg_one_over_card,
          }
    ... = (1:ℝ)/(F.sets n).card * (C* (translate_symm_diff g⁻¹ (F.sets n)).card)
          : by {
            congr' 1,
            rw finset.sum_const C,
            finish,
          }
    ... = C * (((translate_symm_diff g⁻¹ (F.sets n)).card : ℝ) / (F.sets n).card)
          : by field_simp
    ... = C * Folner_quotients g⁻¹ F.sets n
          : by tauto,
  },
  have avg_diff_bound_to_zero :
      filter.tendsto (λ n, C * Folner_quotients g⁻¹ F.sets n)
            filter.at_top
            (nhds 0),
  {
    have : filter.tendsto  (C•(Folner_quotients g⁻¹ F.sets))
            filter.at_top (nhds (C*0))
        := filter.tendsto.const_mul C (F.Folner_cond g⁻¹),
    rw mul_zero at this,
    exact this,
  },

   have avg_diff_to_zero :
      filter.tendsto (λ n, avg_seq F.sets (left_translate g f) n - avg_seq F.sets f n)
            (hyperfilter ℕ)
            (nhds 0),
  {
    apply conv_hyperfilter_of_conv,
    have ineq : ∀ n, |avg_seq F.sets (left_translate g f) n - avg_seq F.sets f n|
              ≤ C * Folner_quotients g⁻¹ F.sets n
        := begin
           assume n,
           rw abs_sub_comm,
           exact le_trans (avg_diff n) (avg_diff_bound n),
        end,
    exact limit_wedge_zero ineq avg_diff_bound_to_zero,
  },

  have avg_tendsto : filter.tendsto (avg_seq F.sets f) (hyperfilter ℕ)
                  (nhds (mean_fct_of_Folner_seq F f))
        := mean_fct_of_Folner_seq_spec F f,

  apply mean_fct_of_Folner_unique,
  change filter.tendsto (avg_seq F.sets (left_translate g f))
                (hyperfilter ℕ)
                (nhds (mean_fct_of_Folner_seq F f)),

  have conv_sum := filter.tendsto.add avg_diff_to_zero avg_tendsto,
  simp [-avg_seq] at conv_sum,
  exact conv_sum,
end


/--We obtain an invariant mean-/
noncomputable def inv_mean_of_Folner_seq
  (F: Folner_sequence G)
  : left_invariant_mean G
:= left_invariant_mean.mk (mean_of_Folner_seq F) (mean_of_Folner_seq_inv F)

end Folner_amenable_to_amenable

/--The existence of a Folner sequence implies amenability-/
theorem amenable_of_Folner_sequence
  {G: Type*}
  [group G]
  [decidable_eq G]
  (F: Folner_sequence G)
  : amenable G
:= amenable_of_invmean (Folner_amenable_to_amenable.inv_mean_of_Folner_seq F)


/--Folner amenable groups are amenable -/
theorem amenable_of_Folner_amenable
  {G: Type*}
  [group G]
  [decidable_eq G]
  (Fam: Folner_amenable G)
  : amenable G
:= amenable_of_Folner_sequence (Folner_sequence_of_Folner_amenable Fam)
