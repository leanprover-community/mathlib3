/-
Copyright (c) 2021 Henry Swanson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henry Swanson
-/
import data.fintype.basic
import data.fintype.card
import data.equiv.basic
import group_theory.group_action

import tactic.field_simp
import tactic.ring

/-!
# Freek № 88 : Derangements Formula
This file proves Theorem 88 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/),
which gives an explicit formula for the number of derangements (permutations without fixed
points) on `n` elements.

The core of the proof is an equivalence between "derangements on `n+2` elements", and
an expression involving derangements on `n` and `n+1` elements. This gives a recurrence
relation `d(n+2) = (n+1) * (d(n) + d(n+1))`, from which a sum-based formula can be derived.
-/

open equiv fintype
open_locale big_operators

section definitions

/-- A permutation is a derangement if it has no fixed points. -/
def is_derangement {α : Type*} (f : perm α) : Prop := (∀ x : α, f x ≠ x)

/-- The set of derangements on `α`. -/
def derangements (α : Type*) : set (perm α) := {f : perm α | is_derangement f}

end definitions


section derangement_lemmas

/-- If `α` is equivalent to `β`, then `derangements α` is equivalent to `derangements β`. -/
def derangement_congr {α β : Type*} (e : α ≃ β) : (derangements α ≃ derangements β) :=
begin
  refine subtype_equiv (perm_congr e) _,
  intro f,
  simp only [derangements, is_derangement, perm_congr_apply, set.mem_set_of_eq],
  rw ← not_iff_not,
  push_neg,
  split,
  { rintro ⟨x, hx_fixed⟩,
    use e x,
    simp [hx_fixed] },
  { rintro ⟨y, hy_fixed⟩,
    use e.symm y,
    apply e.injective,
    simp [hy_fixed] }
end

end derangement_lemmas


section ignore_swap

variables {α : Type*} [decidable_eq α]

/-- A predicate describing if permutation `f` swaps `a` and `b`.
    Note that `a` and `b` need not be distinct. -/
def swaps {α : Type*} (f : perm α) (a b : α) : Prop := f a = b ∧ f b = a

/-- The set of permutations that swap `a` and `b` is equivalent to permutations on all other
    elements. -/
def perm_ignore_swap (a b : α) : { f : perm α | swaps f a b } ≃ perm ({a, b}ᶜ : set α) :=
begin
  let a_and_b : set α := {a, b},

  -- TODO why can't it infer this is decidable?
  haveI : decidable_pred a_and_b := by
  { dsimp [decidable_pred, a_and_b],
    intro x,
    apply set.decidable_mem },

  let swap : perm α := equiv.swap a b,
  let swap' : perm a_and_b := perm.subtype_perm swap (by {
    intro x,

    simp,
    conv_rhs { rw apply_eq_iff_eq_symm_apply, rw apply_eq_iff_eq_symm_apply },
    simp [swap, or_comm] }),

  transitivity {f : perm α // ∀ x : a_and_b, f x = swap' x},
  { apply subtype_equiv_right,
    intro σ,
    simp [swaps] },
  { exact equiv.set.compl swap' },
end

-- TODO should this be a simp lemma?
lemma perm_ignore_two_cycle_eq (a b : α) (f : perm α) (hf : swaps f a b) (c : ({a, b}ᶜ : set α)):
  ((perm_ignore_swap a b) ⟨f, hf⟩ c : α) = f c := by simp [perm_ignore_swap, equiv.set.compl]

-- TODO this name definitely isn't up to snuff... but what would it be called?
lemma perm_ignore_two_cycle_derangement_iff (a b : α) (hab : a ≠ b) (f : perm α) (hf : swaps f a b) :
  is_derangement f ↔ is_derangement ((perm_ignore_swap a b) ⟨f, hf⟩) :=
begin
  split,

  { rintros f_derangement ⟨x, hx⟩,
    simp [perm_ignore_swap, equiv.set.compl],
    exact f_derangement x },

  { -- easier to show that fixed point in f implies a fixed point
    -- in (f without a↔b)
    contrapose!,
    simp [is_derangement],

    --intro our fixed point and show that it's neither a nor b
    intros x x_fixed,
    have x_ne_a_b : ¬(x = a ∨ x = b),
    { intro contra,
      unfold swaps at hf,
      cases contra; { rw contra at x_fixed, cc } },

    use [x, x_ne_a_b],
    rw [subtype.ext_iff, perm_ignore_swap],
    exact x_fixed }
end

end ignore_swap


section splicing

-- TODO feels like this should already exist? something something equiv_functor?
-- I tried mul_action.to_perm (perm α) (perm α), but that didn't simp easily
/-- Post-multiplying by a given `f : perm α` gives a permutation on `perm α`. -/
def equiv_compose {α : Type*} (f : perm α) : perm (perm α) :=
{ to_fun := λ g, g.trans f,
  inv_fun := λ g, g.trans f.symm,
  left_inv := λ g, by { simp [trans_assoc] },
  right_inv := λ g, by { simp [trans_assoc] } }

variables {α : Type*} [decidable_eq α]

/-- For any fixed `a b : α`, the permutations that send `a` to `b` are equivalent to permutations
    away from `a`, by omitting `a` and sending `f⁻¹ a` to `b` instead. -/
def perm_splice_out (a b : α) : { f : perm α | f a = b } ≃ perm ({a}ᶜ : set α) :=
begin
  let just_a : set α := {a},

  transitivity {f : perm α // ∀ x : just_a, f x = equiv.refl just_a x},
  { -- we want to modify each permutation by composing it with (swap a and b)
    let compose_with_swap : perm (perm α) := equiv_compose (equiv.swap a b),

    apply equiv.trans (subtype_equiv_of_subtype' compose_with_swap) _,
    apply subtype_equiv_right,
    simp [compose_with_swap, equiv_compose],
    simp [apply_eq_iff_eq_symm_apply] },
  { apply equiv.set.compl }
end

lemma perm_splice_out_eq (a b : α) (f : perm α) (fa_eq_b : f a = b) (x : α) (hx : x ≠ a) :
  ((perm_splice_out a b ⟨f, fa_eq_b⟩ ⟨x, hx⟩) : α) = (swap a b) (f x) :=
begin
  simp [perm_splice_out, equiv.set.compl,
        subtype_equiv_of_subtype', subtype_equiv_of_subtype,
        equiv_compose],
end

lemma splice_derangement (a b : α) (hab : a ≠ b) (f : perm α) (fa_eq_b : f a = b) :
  f b ≠ a ∧ is_derangement f ↔ (perm_splice_out a b) ⟨f, fa_eq_b⟩ ∈ derangements ({a}ᶜ : set α) :=
begin
  -- again, easier to show that fixed points lead to other fixed points
  rw ← not_iff_not,
  simp [derangements, is_derangement],
  rw imp_iff_not_or,
  simp,

  split,
  { -- if f has a fixed point, then so does (perm_splice_out a b) f.
    -- also, if f b = a, then b is a fixed point
    rintro (rfl|⟨x, x_fixed⟩),
    { use [b, hab.symm],
      simp [subtype.ext_iff_val, perm_splice_out_eq] },
    { have x_ne_a : x ≠ a,
      { rintro rfl,
        rw x_fixed at fa_eq_b,
        contradiction },

      have x_ne_b : x ≠ b,
      { rintro rfl,
        refine hab (f.injective _),
        rw [fa_eq_b, x_fixed] },

      use [x, x_ne_a],
      simp [subtype.ext_iff_val, perm_splice_out_eq, x_fixed,
        swap_apply_of_ne_of_ne x_ne_a x_ne_b] } },
  { -- if (perm_splice_out a b) f has a fixed point, either it came from a pre-existing
    -- one, or it's b
    rintro ⟨x, x_ne_a, x_fixed⟩,
    simp [subtype.ext_iff_val, perm_splice_out_eq] at x_fixed,
    apply_fun (swap a b) at x_fixed,
    simp at x_fixed,

    by_cases x_vs_b : x = b,
    { left,
      simp [x_vs_b] at x_fixed,
      assumption },
    { right,
      use x,
      rw swap_apply_of_ne_of_ne x_ne_a x_vs_b at x_fixed,
      assumption }
  }
end

end splicing


section recursion

-- TODO: these are just here to help the elaborator. I would like to eliminate
-- them in favor of `:` coercions, but I keep getting errors about it. :\
def everything_but {α : Type*} (a : α) : set α := {a}ᶜ
def neither_of {α : Type*} (a : α) (b : everything_but a) : set α := {a, b}ᶜ

variables {α : Type*} [decidable_eq α]

/-- For any distinct `a` and `b`, the set of derangements that swap `a` and `b` is equivalent to
    the set of derangements away from `a` and `b`. -/
def equiv_of_ignore_swaps (a : α) (b : everything_but a) :
  {f : derangements α | swaps ↑f a b} ≃ derangements (neither_of a b) :=
begin
  cases b with b hab,
  have hab : a ≠ b,
  { rintro rfl,
    simpa [everything_but] using hab },

  transitivity {f' : {f : perm α // swaps f a b} // is_derangement f'.val},
  { -- TODO what's the style guidelines here? `:=`?
    exact {
      to_fun := λ f, ⟨⟨f.1.1, f.2⟩, f.1.2⟩,
      inv_fun := λ f, ⟨⟨f.1.1, f.2⟩, f.1.2⟩,
      left_inv := by { intro f, simp },
      right_inv := by { intro f, simp } } },

  refine subtype_equiv (perm_ignore_swap a b) _,
  rintro ⟨f, hf⟩,
  exact perm_ignore_two_cycle_derangement_iff a b hab f hf,
end

/-- For any distinct `a` and `b`, the set of derangements that send `a` to `b`, but don't send
    `b` back to `a`, is equivalent to the set of derangements away from `a`. -/
def equiv_of_splice_out (a : α) (b : everything_but a):
  {f : derangements α // f a = b ∧ f b ≠ a} ≃ derangements (everything_but a) :=
begin
  cases b with b hab,
  have hab' : a ≠ b,
  { rintro rfl,
    simp [everything_but] at hab,
    exact hab },

  transitivity {f' : {f : perm α // f a = b} // f'.val b ≠ a ∧ is_derangement f'.val},
  { exact {
    to_fun := λ f, ⟨⟨f.1.1, f.2.1⟩, ⟨f.2.2, f.1.2⟩⟩,
    inv_fun := λ f, ⟨⟨f.1.1, f.2.2⟩, ⟨f.1.2, f.2.1⟩⟩,
    left_inv := by { intro f, simp },
    right_inv := by { intro f, simp }}},

  refine subtype_equiv (perm_splice_out a b) _,
  rintro ⟨f, hf⟩,
  exact splice_derangement a b hab' f hf,
end

/-- For a given `a b : α`, the set of derangements sending `a` to `b` is equivalent to
    `derangements {a,b}ᶜ ⊕ derangements {a}ᶜ`. -/
def equiv_one_fiber (a : α) (b : everything_but a) :
  {f : derangements α // f a = b} ≃
  (derangements (neither_of a b) ⊕ derangements (everything_but a)) :=
begin
  -- split the type into those that send b back to a, and those that don't
  let b_goes_back_to_a : derangements α → Prop := λ f, f b = a,

  refine equiv.trans (sum_compl (b_goes_back_to_a ∘ coe)).symm _,
  apply equiv.sum_congr,
  { exact (subtype_subtype_equiv_subtype_inter _ _).trans (equiv_of_ignore_swaps a b) },
  { calc {f : {f : derangements α // f a = b} // ¬(b_goes_back_to_a ∘ coe) f }
        ≃ {f : derangements α // f a = b ∧ ¬b_goes_back_to_a f}
            : subtype_subtype_equiv_subtype_inter _ (not ∘ b_goes_back_to_a)
    ... ≃ derangements (everything_but a)
            : equiv_of_splice_out a b }
end

/-- For any fixed `a : α`, the set of derangements of `α` is equivalent to the disjoint union of
    `derangements {a,b}ᶜ ⊕ derangements {a}ᶜ`) over all `b ≠ a`. -/
def derangements_recursion_equiv (a : α):
  derangements α ≃
  Σ b : everything_but a, (derangements (neither_of a b) ⊕ derangements (everything_but a)) :=
begin
  -- the fiber over b = a is empty
  have fact : ∀ (b : α), {f : derangements α // f a = b} → b ∈ everything_but a,
  { rintros b ⟨⟨f, f_derangement⟩, fa_eq_b⟩,
    rw ← fa_eq_b,
    exact f_derangement a },

  calc derangements α
      ≃ Σ b : α, {f : derangements α // f a = b}
          : (sigma_preimage_equiv _).symm
  ... ≃ Σ b : everything_but a, {f : derangements α // f a = b}
          : (sigma_subtype_equiv_of_subset _ _ fact).symm
  ... ≃ Σ b : everything_but a, (derangements (neither_of a b) ⊕ derangements (everything_but a))
          : sigma_congr_right (equiv_one_fiber a),
end

end recursion


section finite_instances

variables {α : Type*} [decidable_eq α] [fintype α]

instance : decidable_pred (@is_derangement α) :=
begin
  intro f,
  apply fintype.decidable_forall_fintype,
end

instance : fintype (derangements α) :=
begin
  have : fintype (perm α) := by apply_instance,
  dsimp [derangements],
  exact set_fintype (set_of is_derangement),
end

instance (a : α) : fintype (everything_but a) :=
begin
  simp [everything_but],
  apply fintype.of_finset ({a}ᶜ : finset α),
  simp,
end

instance (a : α) (b : everything_but a) : fintype (neither_of a b) :=
begin
  simp [everything_but, neither_of],
  apply fintype.of_finset ({a, b}ᶜ : finset α),
  simp,
end

end finite_instances


section counting

/-- The number of derangements on an `n`-element set. -/
def num_derangements (n : ℕ) : ℕ := card (derangements (fin n))

lemma num_derangements_invariant (α : Type*) [fintype α] [decidable_eq α] :
  card (derangements α) = num_derangements (card α) :=
begin
  unfold num_derangements,
  apply card_eq.mpr,  -- card_eq because we don't need the specific equivalence
  use derangement_congr (equiv_fin α),
end

theorem num_derangements_recursive (n : ℕ) :
  num_derangements (n+2) = (n+1) * num_derangements n + (n+1) * num_derangements (n+1) :=
begin
  let X := fin(n+2),
  let star : X := 0, -- could be any element tbh

  have card_everything_but : card (everything_but star) = (n + 1),
  { simp [everything_but, finset.card_compl] },

  have card_neither_of : ∀ m : everything_but star, card (neither_of star m) = n,
  { simp [everything_but, finset.card_compl],
    intros m hm,

    suffices : finset.card ({star, m} : finset X) = 2,
    { simp [this] },

    simp [ne.symm hm]
  },

  have card_der_1 : card (derangements (everything_but star)) = num_derangements (n+1),
  { rw [num_derangements_invariant, card_everything_but] },

  have card_der_2 : ∀ m : everything_but star, card (derangements (neither_of star m)) = num_derangements n,
  { intro m, rw [num_derangements_invariant, card_neither_of] },

  have key := card_congr (derangements_recursion_equiv star),
  rw num_derangements_invariant X at key,
  simp [card_der_1, card_der_2] at key,

  rw key,
  simpa [finset.card_univ, card_everything_but] using mul_add _ _ _,
end

-- TODO `n!` inside or outside the sum? should n!/k! be a function outputting ℕ?
theorem num_derangements_sum (n : ℕ) :
  (num_derangements n : ℚ) = n.factorial * ∑ k in finset.range (n + 1), (-1 : ℚ)^k / k.factorial :=
begin
  refine nat.strong_induction_on n _,
  clear n, -- ???

  intros n hyp,

  -- need to knock out cases n = 0, 1
  cases n,
  { simp, rw ← nat.cast_one, refl },

  cases n,
  { simp [finset.sum_range_succ], refl },

  -- now we have n ≥ 2
  rw num_derangements_recursive,
  push_cast,

  -- TODO can these proofs be inferred from some tactic? i tried linarith,
  -- but for some reason that didn't work
  rw hyp n (nat.lt_succ_of_le (nat.le_succ _)),
  rw hyp n.succ (lt_add_one _),

  -- push all the constants inside the sums, strip off some trailing terms,
  -- and compare term-wise
  repeat { rw finset.mul_sum },
  conv_lhs { congr, skip, rw finset.sum_range_succ },
  rw [← add_assoc, ← finset.sum_add_distrib],

  conv_rhs {
    rw finset.sum_range_succ,
    rw finset.sum_range_succ,
    rw add_assoc },

  congr,
  { funext,

    -- show that (n+1) n! (-1)^k / k! + (n+1) (n+1)! (-1)^k / k! = (n+2)! (-1)^k / k!
    have : (n+2).factorial = (n + 1) * (n.factorial + (n+1).factorial),
    { simp [← nat.add_one], ring },
    simp [this],
    ring },
  { -- show that (n+1) (n+1)! * (-1)^(n+1) / (n+1)! = (n+2)! (-1)^(n+1)/(n+1)! + (n+2)! (-1)^(n+2) / (n+2)!

    -- delay factorial simplification until we're done clearing
    -- denominators
    -- TODO this works, but it's kinda silly. why can't i notice that the fraction is
    -- a * b * c / b, and reduce it to a * c (given a proof that b ≠ 0)
    field_simp [nat.factorial_ne_zero, -nat.factorial_succ, -nat.factorial],
    simp [nat.factorial_succ, pow_succ],
    ring },
end

end counting
