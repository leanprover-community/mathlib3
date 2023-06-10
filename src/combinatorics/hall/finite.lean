/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
import data.fintype.basic
import data.set.finite

/-!
# Hall's Marriage Theorem for finite index types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module proves the basic form of Hall's theorem.
In constrast to the theorem described in `combinatorics.hall.basic`, this
version requires that the indexed family `t : ι → finset α` have `ι` be finite.
The `combinatorics.hall.basic` module applies a compactness argument to this version
to remove the `finite` constraint on `ι`.

The modules are split like this since the generalized statement
depends on the topology and category theory libraries, but the finite
case in this module has few dependencies.

A description of this formalization is in [Gusakov2021].

## Main statements

* `finset.all_card_le_bUnion_card_iff_exists_injective'` is Hall's theorem with
  a finite index set.  This is elsewhere generalized to
  `finset.all_card_le_bUnion_card_iff_exists_injective`.

## Tags

Hall's Marriage Theorem, indexed families
-/

open finset

universes u v

namespace hall_marriage_theorem

variables {ι : Type u} {α : Type v} [decidable_eq α] {t : ι → finset α}

section fintype
variables [fintype ι]

lemma hall_cond_of_erase {x : ι} (a : α)
  (ha : ∀ (s : finset ι), s.nonempty → s ≠ univ → s.card < (s.bUnion t).card)
  (s' : finset {x' : ι | x' ≠ x}) :
  s'.card ≤ (s'.bUnion (λ x', (t x').erase a)).card :=
begin
  haveI := classical.dec_eq ι,
  specialize ha (s'.image coe),
  rw [nonempty.image_iff, finset.card_image_of_injective s' subtype.coe_injective] at ha,
  by_cases he : s'.nonempty,
  { have ha' : s'.card < (s'.bUnion (λ x, t x)).card,
    { convert ha he (λ h, by simpa [←h] using mem_univ x) using 2,
      ext x,
      simp only [mem_image, mem_bUnion, exists_prop, set_coe.exists,
                 exists_and_distrib_right, exists_eq_right, subtype.coe_mk], },
    rw ←erase_bUnion,
    by_cases hb : a ∈ s'.bUnion (λ x, t x),
    { rw card_erase_of_mem hb,
      exact nat.le_pred_of_lt ha' },
    { rw erase_eq_of_not_mem hb,
      exact nat.le_of_lt ha' }, },
  { rw [nonempty_iff_ne_empty, not_not] at he,
    subst s',
    simp },
end

/--
First case of the inductive step: assuming that
`∀ (s : finset ι), s.nonempty → s ≠ univ → s.card < (s.bUnion t).card`
and that the statement of **Hall's Marriage Theorem** is true for all
`ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
-/
lemma hall_hard_inductive_step_A {n : ℕ} (hn : fintype.card ι = n + 1)
  (ht : ∀ (s : finset ι), s.card ≤ (s.bUnion t).card)
  (ih : ∀ {ι' : Type u} [fintype ι'] (t' : ι' → finset α),
        by exactI fintype.card ι' ≤ n →
                  (∀ (s' : finset ι'), s'.card ≤ (s'.bUnion t').card) →
                  ∃ (f : ι' → α), function.injective f ∧ ∀ x, f x ∈ t' x)
  (ha : ∀ (s : finset ι), s.nonempty → s ≠ univ → s.card < (s.bUnion t).card) :
  ∃ (f : ι → α), function.injective f ∧ ∀ x, f x ∈ t x :=
begin
  haveI : nonempty ι := fintype.card_pos_iff.mp (hn.symm ▸ nat.succ_pos _),
  haveI := classical.dec_eq ι,
  /- Choose an arbitrary element `x : ι` and `y : t x`. -/
  let x := classical.arbitrary ι,
  have tx_ne : (t x).nonempty,
  { rw ←finset.card_pos,
    calc 0 < 1 : nat.one_pos
       ... ≤ (finset.bUnion {x} t).card : ht {x}
       ... = (t x).card : by rw finset.singleton_bUnion, },
  choose y hy using tx_ne,
  /- Restrict to everything except `x` and `y`. -/
  let ι' := {x' : ι | x' ≠ x},
  let t' : ι' → finset α := λ x', (t x').erase y,
  have card_ι' : fintype.card ι' = n :=
    calc fintype.card ι' = fintype.card ι - 1 : set.card_ne_eq _
                     ... = n : by { rw [hn, nat.add_succ_sub_one, add_zero], },
  rcases ih t' card_ι'.le (hall_cond_of_erase y ha) with ⟨f', hfinj, hfr⟩,
  /- Extend the resulting function. -/
  refine ⟨λ z, if h : z = x then y else f' ⟨z, h⟩, _, _⟩,
  { rintro z₁ z₂,
    have key : ∀ {x}, y ≠ f' x,
    { intros x h,
      simpa [←h] using hfr x, },
    by_cases h₁ : z₁ = x; by_cases h₂ : z₂ = x; simp [h₁, h₂, hfinj.eq_iff, key, key.symm], },
  { intro z,
    split_ifs with hz,
    { rwa hz },
    { specialize hfr ⟨z, hz⟩,
      rw mem_erase at hfr,
      exact hfr.2, }, },
end

lemma hall_cond_of_restrict {ι : Type u} {t : ι → finset α} {s : finset ι}
  (ht : ∀ (s : finset ι), s.card ≤ (s.bUnion t).card)
  (s' : finset (s : set ι)) :
  s'.card ≤ (s'.bUnion (λ a', t a')).card :=
begin
  classical,
  rw ← card_image_of_injective s' subtype.coe_injective,
  convert ht (s'.image coe) using 1,
  apply congr_arg,
  ext y,
  simp,
end

lemma hall_cond_of_compl {ι : Type u} {t : ι → finset α} {s : finset ι}
  (hus : s.card = (s.bUnion t).card)
  (ht : ∀ (s : finset ι), s.card ≤ (s.bUnion t).card)
  (s' : finset (sᶜ : set ι)) :
  s'.card ≤ (s'.bUnion (λ x', t x' \ s.bUnion t)).card :=
begin
  haveI := classical.dec_eq ι,
  have disj : disjoint s (s'.image coe),
  { simp only [disjoint_left, not_exists, mem_image, exists_prop, set_coe.exists,
               exists_and_distrib_right, exists_eq_right, subtype.coe_mk],
    intros x hx hc h,
    exact absurd hx hc, },
  have : s'.card = (s ∪ s'.image coe).card - s.card,
  { simp [disj, card_image_of_injective _ subtype.coe_injective], },
  rw [this, hus],
  refine (tsub_le_tsub_right (ht _) _).trans _,
  rw ← card_sdiff,
  { refine (card_le_of_subset _).trans le_rfl,
    intros t,
    simp only [mem_bUnion, mem_sdiff, not_exists, mem_image, and_imp, mem_union,
               exists_and_distrib_right, exists_imp_distrib],
    rintro x (hx | ⟨x', hx', rfl⟩) rat hs,
    { exact (hs x hx rat).elim },
    { exact ⟨⟨x', hx', rat⟩, hs⟩, } },
  { apply bUnion_subset_bUnion_of_subset_left,
    apply subset_union_left }
end

/--
Second case of the inductive step: assuming that
`∃ (s : finset ι), s ≠ univ → s.card = (s.bUnion t).card`
and that the statement of **Hall's Marriage Theorem** is true for all
`ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
-/
lemma hall_hard_inductive_step_B {n : ℕ} (hn : fintype.card ι = n + 1)
  (ht : ∀ (s : finset ι), s.card ≤ (s.bUnion t).card)
  (ih : ∀ {ι' : Type u} [fintype ι'] (t' : ι' → finset α),
        by exactI fintype.card ι' ≤ n →
                  (∀ (s' : finset ι'), s'.card ≤ (s'.bUnion t').card) →
                  ∃ (f : ι' → α), function.injective f ∧ ∀ x, f x ∈ t' x)
  (s : finset ι)
  (hs : s.nonempty)
  (hns : s ≠ univ)
  (hus : s.card = (s.bUnion t).card) :
  ∃ (f : ι → α), function.injective f ∧ ∀ x, f x ∈ t x :=
begin
  haveI := classical.dec_eq ι,
  /- Restrict to `s` -/
  let t' : s → finset α := λ x', t x',
  rw nat.add_one at hn,
  have card_ι'_le : fintype.card s ≤ n,
  { apply nat.le_of_lt_succ,
    calc fintype.card s = s.card : fintype.card_coe _
                    ... < fintype.card ι : (card_lt_iff_ne_univ _).mpr hns
                    ... = n.succ : hn },
  rcases ih t' card_ι'_le (hall_cond_of_restrict ht) with ⟨f', hf', hsf'⟩,
  /- Restrict to `sᶜ` in the domain and `(s.bUnion t)ᶜ` in the codomain. -/
  set ι'' := (s : set ι)ᶜ with ι''_def,
  let t'' : ι'' → finset α := λ a'', t a'' \ s.bUnion t,
  have card_ι''_le : fintype.card ι'' ≤ n,
  { simp_rw [← nat.lt_succ_iff, ← hn, ι'', ← finset.coe_compl, coe_sort_coe],
    rwa [fintype.card_coe, card_compl_lt_iff_nonempty] },
  rcases ih t'' card_ι''_le (hall_cond_of_compl hus ht) with ⟨f'', hf'', hsf''⟩,
  /- Put them together -/
  have f'_mem_bUnion : ∀ {x'} (hx' : x' ∈ s), f' ⟨x', hx'⟩ ∈ s.bUnion t,
  { intros x' hx',
    rw mem_bUnion,
    exact ⟨x', hx', hsf' _⟩, },
  have f''_not_mem_bUnion : ∀ {x''} (hx'' : ¬ x'' ∈ s), ¬ f'' ⟨x'', hx''⟩ ∈ s.bUnion t,
  { intros x'' hx'',
    have h := hsf'' ⟨x'', hx''⟩,
    rw mem_sdiff at h,
    exact h.2, },
  have im_disj : ∀ (x' x'' : ι) (hx' : x' ∈ s) (hx'' : ¬x'' ∈ s), f' ⟨x', hx'⟩ ≠ f'' ⟨x'', hx''⟩,
  { intros _ _ hx' hx'' h,
    apply f''_not_mem_bUnion hx'',
    rw ←h,
    apply f'_mem_bUnion, },
  refine ⟨λ x, if h : x ∈ s then f' ⟨x, h⟩ else f'' ⟨x, h⟩, _, _⟩,
  { exact hf'.dite _ hf'' im_disj },
  { intro x,
    split_ifs with h,
    { exact hsf' ⟨x, h⟩ },
    { exact sdiff_subset _ _ (hsf'' ⟨x, h⟩) } }
end


end fintype

variables [finite ι]

/--
Here we combine the two inductive steps into a full strong induction proof,
completing the proof the harder direction of **Hall's Marriage Theorem**.
-/
theorem hall_hard_inductive
  (ht : ∀ (s : finset ι), s.card ≤ (s.bUnion t).card) :
  ∃ (f : ι → α), function.injective f ∧ ∀ x, f x ∈ t x :=
begin
  casesI nonempty_fintype ι,
  unfreezingI
  { induction hn : fintype.card ι using nat.strong_induction_on with n ih generalizing ι },
  rcases n with _|_,
  { rw fintype.card_eq_zero_iff at hn,
    exactI ⟨is_empty_elim, is_empty_elim, is_empty_elim⟩, },
  { have ih' : ∀ (ι' : Type u) [fintype ι'] (t' : ι' → finset α),
                 by exactI fintype.card ι' ≤ n →
                    (∀ (s' : finset ι'), s'.card ≤ (s'.bUnion t').card) →
                    ∃ (f : ι' → α), function.injective f ∧ ∀ x, f x ∈ t' x,
    { introsI ι' _ _ hι' ht',
      exact ih _ (nat.lt_succ_of_le hι') ht' _ rfl },
    by_cases h : ∀ (s : finset ι), s.nonempty → s ≠ univ → s.card < (s.bUnion t).card,
    { exact hall_hard_inductive_step_A hn ht ih' h, },
    { push_neg at h,
      rcases h with ⟨s, sne, snu, sle⟩,
      exact hall_hard_inductive_step_B hn ht ih' s sne snu (nat.le_antisymm (ht _) sle), } },
end

end hall_marriage_theorem

/--
This is the version of **Hall's Marriage Theorem** in terms of indexed
families of finite sets `t : ι → finset α` with `ι` finite.
It states that there is a set of distinct representatives if and only
if every union of `k` of the sets has at least `k` elements.

See `finset.all_card_le_bUnion_card_iff_exists_injective` for a version
where the `finite ι` constraint is removed.
-/
theorem finset.all_card_le_bUnion_card_iff_exists_injective'
  {ι α : Type*} [finite ι] [decidable_eq α] (t : ι → finset α) :
  (∀ (s : finset ι), s.card ≤ (s.bUnion t).card) ↔
    (∃ (f : ι → α), function.injective f ∧ ∀ x, f x ∈ t x) :=
begin
  split,
  { exact hall_marriage_theorem.hall_hard_inductive },
  { rintro ⟨f, hf₁, hf₂⟩ s,
    rw ←card_image_of_injective s hf₁,
    apply card_le_of_subset,
    intro _,
    rw [mem_image, mem_bUnion],
    rintros ⟨x, hx, rfl⟩,
    exact ⟨x, hx, hf₂ x⟩, },
end
