/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.list.rdrop
import data.multiset.fintype
import field_theory.chevalley_warning

/-!
# The Erdős–Ginzburg–Ziv theorem

This file proves the Erdős–Ginzburg–Ziv theorem as a corollary of Chevalley-Warning. This theorem
states that among any (not necessarily distinct) `2 * n - 1` elements of `zmod n`, we can find `n`
elements of sum zero.

## Main declarations

* `zmod.exists_submultiset_eq_zero`: The Erdős–Ginzburg–Ziv theorem
-/

section
variables {α : Type*} [canonically_linear_ordered_add_monoid α] [has_sub α] [has_ordered_sub α]
  [contravariant_class α α (+) (≤)]

lemma tsub_tsub_eq_min (a b : α) : a - (a - b) = min a b :=
by rw [tsub_eq_tsub_min _ b, tsub_tsub_cancel_of_le (min_le_left a _)]

end

section
variables {α : Type*} [canonically_ordered_comm_semiring α] [has_sub α] [has_ordered_sub α]
  [is_total α (≤)] [contravariant_class α α (+) (≤)]

lemma mul_tsub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_tsub, mul_one]
lemma tsub_one_mul (a b : α) : (a - 1) * b = a * b - b := by rw [tsub_mul, one_mul]

end

namespace list
variables {α : Type*} {l l' l₀ l₁ l₂ : list α} {a b : α} {m n : ℕ}

lemma cons_sublist_cons_iff' : a :: l₁ <+ b :: l₂ ↔ a :: l₁ <+ l₂ ∨ a = b ∧ l₁ <+ l₂ :=
begin
  split,
  { rintro (_ | _),
    { exact or.inl ‹_› },
    { exact or.inr ⟨rfl, ‹_›⟩ } },
  { rintro (h | ⟨rfl, h⟩),
    { exact sublist_cons_of_sublist _ h },
    { rwa cons_sublist_cons_iff } }
end

attribute [simp] nil_subperm

lemma subperm_cons_self : l <+~ a :: l := ⟨l, perm.refl _, sublist_cons _ _⟩

@[simp] lemma subperm_nil : l <+~ [] ↔ l = [] :=
⟨λ h, length_eq_zero.1 $ le_bot_iff.1 h.length_le, by { rintro rfl, refl }⟩

lemma rtake_suffix (n : ℕ) (l : list α) : l.rtake n <:+ l := drop_suffix _ _

lemma length_rtake (n : ℕ) (l : list α) : (l.rtake n).length = min n l.length :=
(length_drop _ _).trans $ by rw [tsub_tsub_eq_min, min_comm]

@[simp] lemma take_reverse (n : ℕ) (l : list α) : l.reverse.take n = (l.rtake n).reverse :=
by rw [rtake_eq_reverse_take_reverse, reverse_reverse]

@[simp] lemma rtake_reverse (n : ℕ) (l : list α) : l.reverse.rtake n = (l.take n).reverse :=
by rw [rtake_eq_reverse_take_reverse, reverse_reverse]

@[simp] lemma rtake_rtake (n m) (l : list α) : (l.rtake m).rtake n = l.rtake (min n m) :=
by rw [rtake_eq_reverse_take_reverse, ←take_reverse, take_take, rtake_eq_reverse_take_reverse]

@[simp] lemma rdrop_append_rtake (n : ℕ) (l : list α) : l.rdrop n ++ l.rtake n = l :=
take_append_drop _ _

lemma suffix_iff_eq_rtake : l₁ <:+ l₂ ↔ l₁ = l₂.rtake (length l₁) :=
⟨λ h, append_left_cancel $
  (suffix_iff_eq_append.1 h).trans (rdrop_append_rtake _ _).symm,
 λ e, e.symm ▸ rtake_suffix _ _⟩

alias prefix_iff_eq_take ↔ is_prefix.eq_take _
alias suffix_iff_eq_rtake ↔ is_suffix.eq_rtake _

@[simp] lemma take_min : l.take (min n l.length) = l.take n := sorry
@[simp] lemma drop_min : l.drop (min n l.length) = l.drop n := sorry
@[simp] lemma rtake_min : l.rtake (min n l.length) = l.rtake n := sorry
@[simp] lemma rdrop_min : l.rdrop (min n l.length) = l.rdrop n := sorry

lemma take_prefix_take (h : m ≤ n) : l.take m <+: l.take n :=
by rw [prefix_iff_eq_take, length_take, take_take, min_right_comm, min_eq_left h, take_min]

lemma drop_suffix_drop (h : m ≤ n) : l.drop n <:+ l.drop m := sorry

lemma rtake_suffix_rtake (h : m ≤ n) : l.rtake m <:+ l.rtake n :=
drop_suffix_drop $ tsub_le_tsub_left h _

lemma rdrop_prefix_rdrop (h : m ≤ n) : l.rdrop n <+: l.rdrop m :=
take_prefix_take $ tsub_le_tsub_left h _

protected lemma is_prefix.take (hl : l <+: l') (h : l.length ≤ n) : l <+: l'.take n :=
by { rw hl.eq_take, exact take_prefix_take h }

protected lemma is_suffix.rtake (hl : l <:+ l') (h : l.length ≤ n) : l <:+ l'.rtake n :=
by { rw hl.eq_rtake, exact rtake_suffix_rtake h }

lemma exists_prefix_length_eq (hn : n ≤ l.length) : ∃ l', l' <+: l ∧ l'.length = n :=
⟨l.take n, take_prefix _ _, (length_take _ _).trans $ min_eq_left hn⟩

lemma exists_suffix_length_eq (hn : n ≤ l.length) : ∃ l', l' <:+ l ∧ l'.length = n :=
⟨l.rtake n, rtake_suffix _ _, (length_rtake _ _).trans $ min_eq_left hn⟩

lemma exists_sublist_length_eq (hn : n ≤ l.length) : ∃ l', l' <+ l ∧ l'.length = n :=
⟨l.take n, take_sublist _ _, (length_take _ _).trans $ min_eq_left hn⟩

lemma is_prefix.exists_intermediate (hl : l₀ <+: l₂) (h₀ : l₀.length ≤ n) (h₂ : n ≤ l₂.length) :
  ∃ l₁, l₀ <+: l₁ ∧ l₁ <+: l₂ ∧ l₁.length = n :=
⟨l₂.take n, hl.take h₀, take_prefix _ _, (length_take _ _).trans $ min_eq_left h₂⟩

lemma is_suffix.exists_intermediate (hl : l₀ <:+ l₂) (h₀ : l₀.length ≤ n) (h₂ : n ≤ l₂.length) :
  ∃ l₁, l₀ <:+ l₁ ∧ l₁ <:+ l₂ ∧ l₁.length = n :=
⟨l₂.rtake n, hl.rtake h₀, rtake_suffix _ _, (length_rtake _ _).trans $ min_eq_left h₂⟩

lemma sublist.exists_intermediate (hl : l₀ <+ l₂) (h₀ : l₀.length ≤ n) (h₂ : n ≤ l₂.length) :
  ∃ l₁, l₀ <+ l₁ ∧ l₁ <+ l₂ ∧ l₁.length = n :=
begin
  induction l₀ with a l₀ ih generalizing n l₂,
  { exact (exists_sublist_length_eq h₂).imp (λ l₁ h, ⟨nil_sublist _, h⟩) },
  cases n,
  { cases h₀ },
  cases l₂ with b l₂,
  { cases h₂ },
  obtain ⟨l₁, h₀₁, h₁₂, rfl⟩ := ih _ (nat.succ_le_succ_iff.1 h₀) (nat.le_of_succ_le h₂),
  rw cons_sublist_cons_iff' at hl,
  obtain hl | ⟨rfl, hl⟩ := hl,
  sorry { obtain ⟨l₁, h₀₁, h₁₂, rfl⟩ := ih _ (nat.succ_le_succ_iff.1 h₀) (nat.succ_le_succ_iff.1 h₂),
    refine ⟨l₁, hl, _⟩,
  },
  sorry,
  sorry,
end

lemma subperm.exists_intermediate (hl : l₀ <+~ l₂) (h₀ : l₀.length ≤ n) (h₂ : n ≤ l₂.length) :
  ∃ l₁, l₀ <+~ l₁ ∧ l₁ <+~ l₂ ∧ l₁.length = n :=
begin
  obtain ⟨l₀', hl₀, hl'⟩ := hl,
  obtain ⟨l₁, h₀₁, h₁₂, hn⟩ := hl'.exists_intermediate (hl₀.length_eq.trans_le h₀) h₂,
  exact ⟨l₁, ⟨_, hl₀, h₀₁⟩, h₁₂.subperm, hn⟩,
end

lemma exists_subperm_length_eq (hn : n ≤ l.length) : ∃ l', l' <+~ l ∧ l'.length = n :=
by simpa using nil_subperm.exists_intermediate bot_le hn

end list

namespace multiset
variables {α : Type*} {s t : multiset α} {n : ℕ}

lemma exists_intermediate (hst : s ≤ t) (hs : s.card ≤ n) (ht : n ≤ t.card) :
  ∃ u, s ≤ u ∧ u ≤ t ∧ u.card = n :=
begin
  induction s using quotient.induction_on with l₀,
  induction t using quotient.induction_on with l₂,
  obtain ⟨l₁, h⟩ := hst.exists_intermediate hs ht,
  exact ⟨l₁, h⟩,
end

lemma exists_le_card_eq (hn : n ≤ s.card) : ∃ t, t ≤ s ∧ t.card = n :=
by simpa using exists_intermediate (zero_le _) bot_le hn

variables [decidable_eq α]

lemma le_card_sub : s.card - t.card ≤ (s - t).card :=
tsub_le_iff_left.2 $ (card_mono le_add_tsub).trans_eq $ card_add _ _

end multiset

namespace nat

lemma prime_composite_induction {P : ℕ → Prop} (zero : P 0) (one : P 1)
  (prime : ∀ p : ℕ, p.prime → P p) (composite : ∀ a, 2 ≤ a → P a → ∀ b, 2 ≤ b → P b → P (a * b))
  (n : ℕ) : P n :=
begin
  refine induction_on_primes zero one _ _,
  rintro p (_ | _ | a) hp ha,
  { rwa mul_zero },
  { rw mul_one,
    exact prime _ hp },
  { exact composite _ hp.two_le (prime _ hp) _ a.one_lt_succ_succ ha }
end

end nat

namespace subtype
variables {α : Type*} {p : α → Prop} {a b : {a // p a}}

lemma coe_ne_coe : (a : α) ≠ b ↔ a ≠ b := coe_inj.not

end subtype

namespace multiset
variables {α : Type*} {s : multiset α}

--TODO: Rename `multiset.coe_attach` to `multiset.attach_coe`
--TODO: Rename `multiset.coe_countp` to `multiset.countp_coe`

--TODO: Maybe change `multiset.attach` to make `multiset.coe_attach` refl?

end multiset

namespace finset
variables {α β : Type*} [add_comm_monoid_with_one β]

open_locale big_operators

@[simp] lemma card_filter_attach (p : α → Prop) [decidable_pred p] (s : finset α) :
   (filter (λ a, p ↑a) s.attach).card = (filter p s).card := by simp

end finset

namespace nat
variables {a b : ℕ}

lemma eq_of_dvd_of_lt_two_mul (ha : a ≠ 0) (hdvd : b ∣ a) (hlt : a < 2 * b) : a = b :=
begin
  obtain ⟨_ | _ | c, rfl⟩ := hdvd,
  { simpa using ha },
  { exact mul_one _ },
  { cases hlt.not_le ((mul_comm _ _).trans_le $ mul_le_mul_left' (one_lt_succ_succ _) _) }
end

end nat

namespace zmod
variables {p : ℕ} [fact (nat.prime p)]

lemma pow_card_sub_one (x : zmod p) : x ^ (p - 1) = if x ≠ 0 then 1 else 0 :=
begin
  split_ifs with hx,
  { exact pow_card_sub_one_eq_one hx },
  { simp [of_not_not hx, (fact.out p.prime).one_lt] }
end

end zmod

open multiset mv_polynomial
open_locale big_operators

namespace zmod
variables {n p : ℕ} [fact p.prime] {s : multiset (zmod p)}

/-- The first multivariate polynomial used in the proof of Erdős–Ginzburg–Ziv. -/
private noncomputable def f₁ (s : multiset (zmod p)) : mv_polynomial s.to_enum_finset (zmod p) :=
∑ x in s.to_enum_finset.attach, X x ^ (p - 1)

/-- The second multivariate polynomial used in the proof of Erdős–Ginzburg–Ziv. -/
private noncomputable def f₂ (s : multiset (zmod p)) : mv_polynomial s.to_enum_finset (zmod p) :=
∑ x in s.to_enum_finset.attach, x.1.1 • X x ^ (p - 1)

lemma total_degree_f₁_add_total_degree_f₂ : (f₁ s).total_degree + (f₂ s).total_degree < 2 * p - 1 :=
begin
  refine (add_le_add (total_degree_finset_sum _ _) $
    (total_degree_finset_sum _ _).trans $ finset.sup_mono_fun _).trans_lt _,
  swap,
  exact λ a ha, total_degree_smul_le,
  simp only [total_degree_X_pow, ←two_mul],
  refine (mul_le_mul_left' finset.sup_const_le _).trans_lt _,
  rw [mul_tsub, mul_one],
  exact tsub_lt_tsub_left_of_le
    ((fact.out p.prime).two_le.trans $ le_mul_of_one_le_left' one_le_two) one_lt_two,
end

/-- The prime case of the **Erdős–Ginzburg–Ziv theorem**: Any (not necessarily distinct) `2 * p - 1`
elements of `zmod p` contain `p` elements whose sum is zero. -/
private lemma aux (hs : s.card = 2 * p - 1) : ∃ t ≤ s, t.card = p ∧ t.sum = 0 :=
begin
  haveI : ne_zero p := infer_instance,
  -- Let `N` be the number of common roots of our polynomials `f₁` and `f₂` (`f s ff` and `f s tt`).
  set N := fintype.card {x // eval x (f₁ s) = 0 ∧ eval x (f₂ s) = 0} with hN,
  -- Zero is a common root to `f₁` and `f₂`, so `N` is nonzero
  let zero_sol : {x // eval x (f₁ s) = 0 ∧ eval x (f₂ s) = 0} :=
    ⟨0, by simp [f₁, f₂, map_sum, (fact.out p.prime).one_lt]⟩,
  have hN₀ : 0 < N := @fintype.card_pos _ _ ⟨zero_sol⟩,
  have hs' : 2 * p - 1 = fintype.card s.to_enum_finset := by simp [hs],
  -- Chevalley-Warning gives us that `p ∣ n` because the total degrees of `f₁` and `f₂` are at most
  -- `p - 1`, and we have `2 * p - 1 > 2 * (p - 1)` variables.
  have hpN : p ∣ N := char_dvd_card_solutions_of_add_lt p
    (total_degree_f₁_add_total_degree_f₂.trans_eq hs'),
  -- Hence, `2 ≤ p ≤ N` and we can make a common root `x ≠ 0`.
  obtain ⟨x, hx⟩ := fintype.exists_ne_of_one_lt_card ((fact.out p.prime).one_lt.trans_le $
    nat.le_of_dvd hN₀ hpN) zero_sol,
  -- This common root gives us the required submultiset, namely the `a ∈ s` such that `x a ≠ 0`.
  -- Note that we need `multiset.to_enum_finset` to distinguish duplicated elements of `s`.
  refine ⟨(s.to_enum_finset.attach.filter $ λ a, x.1 a ≠ 0).1.map
    (prod.fst ∘ (coe : s.to_enum_finset → zmod p × ℕ)), le_iff_count.2 $ λ a, _, _, _⟩,
  { simp only [subtype.val_eq_coe, ←finset.filter_val, finset.card_val, function.comp_app,
      count_map],
    refine (finset.card_le_of_subset $ finset.filter_subset_filter _ $
      finset.filter_subset _ _).trans_eq _,
    refine (finset.card_filter_attach (λ c : zmod p × ℕ, a = c.1) _).trans _,
    simp [to_enum_finset_filter_eq] },
  -- From `f₁ x = 0`, we get that `p` divides the number of `a` such that `x a ≠ 0`.
  { simp only [card_map, ←finset.filter_val, finset.card_val, function.comp_app,
      count_map, ←finset.map_val],
    refine nat.eq_of_dvd_of_lt_two_mul (finset.card_pos.2 _).ne' _
      ((finset.card_filter_le _ _).trans_lt _),
    -- This number is nonzero because `x ≠ 0`.
    { rw [←subtype.coe_ne_coe, function.ne_iff] at hx,
      exact hx.imp (λ a ha, mem_filter.2 ⟨finset.mem_attach _ _, ha⟩) },
    { rw [←char_p.cast_eq_zero_iff (zmod p), ←finset.sum_boole],
      simpa only [f₁, map_sum, zmod.pow_card_sub_one, map_pow, eval_X] using x.2.1 },
    -- And it is at most `2 * p - 1`, so it must be `p`.
    { rw [finset.card_attach, card_to_enum_finset, hs],
     exact tsub_lt_self (mul_pos zero_lt_two (fact.out p.prime).pos) zero_lt_one } },
  -- From `f₂ x = 0`, we get that `p` divides the sum of the `a ∈ s` such that `x a ≠ 0`.
  { simpa only [f₂, map_sum, zmod.pow_card_sub_one, finset.sum_map_val, finset.sum_filter, smul_eval,
      map_pow, eval_X, mul_ite, mul_zero, mul_one] using x.2.2 }
end

--TODO: Rename `multiset.pairwise_nil` to `multiset.pairwise_zero`

/-- The **Erdős–Ginzburg–Ziv theorem**: Any (not necessarily distinct) `2 * n - 1` elements of
`zmod n` contain `n` elements whose sum is zero. -/
lemma exists_submultiset_eq_zero {s : multiset (zmod n)} (hs : 2 * n - 1 ≤ s.card) :
  ∃ t ≤ s, t.card = n ∧ t.sum = 0 :=
begin
  induction n using nat.prime_composite_induction with p hp,
  case zero { exact ⟨0, s.zero_le, card_zero, sum_zero⟩ },
  case one { obtain ⟨t, ht, hn⟩ := exists_le_card_eq hs, exact ⟨t, ht, hn, subsingleton.elim _ _⟩ },
  case prime : p hp
  { haveI := fact.mk hp,
    obtain ⟨t, hts, ht⟩ := exists_le_card_eq hs,
    obtain ⟨u, hut, hu⟩ := aux ht,
    exact ⟨u, hut.trans hts, hu⟩ },
  case composite : a ha iha b hb ihb
  { suffices : ∀ n ≤ 2 * b - 1, ∃ m : multiset (multiset $ zmod $ a * b), m.card = n ∧
      m.pairwise _root_.disjoint ∧ ∀ ⦃u : multiset $ zmod $ a * b⦄, u ∈ m →
        u.card = 2 * a + 1 ∧ u.sum ∈ add_subgroup.zmultiples (a : zmod $ a * b),
    {
      obtain ⟨m, hm⟩ := this _ le_rfl,
      sorry,
    },
    rintro n hn,
    induction n with n ih,
    { exact ⟨0, by simp⟩ },
    obtain ⟨m, hm⟩ := ih (nat.le_of_succ_le hn),
    have : 2 * a - 1 ≤ ((s - m.sum).map $ cast_hom (dvd_mul_right _ _) $ zmod a).card,
    { rw card_map,
      refine (le_tsub_of_add_le_left $ le_trans _ hs).trans le_card_sub,
      have : m.map multiset.card = repeat (2 * a - 1) n,
      {
        sorry
      },
      rw [map_multiset_sum, this, sum_repeat, ←le_tsub_iff_right, tsub_tsub_tsub_cancel_right,
        ←mul_tsub, ←mul_tsub_one],
      sorry,
      sorry,
      sorry,
    },
    sorry,
  }
end

end zmod
