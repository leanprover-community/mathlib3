/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.multiset.fintype
import field_theory.chevalley_warning

/-!
# The Erdős–Ginzburg–Ziv theorem

This file proves the Erdős–Ginzburg–Ziv theorem as a corollary of Chevalley-Warning. This theorem
states that among any (not necessarily distinct) `2 * p - 1` elements of `zmod p`, we can find `p`
elements of sum zero.

## Main declarations

* `zmod.exists_submultiset_eq_zero`: The Erdős–Ginzburg–Ziv theorem

## TODO

Derive the composite case.
-/

namespace subtype
variables {α : Type*} {p : α → Prop} {a b : {a // p a}}

lemma coe_ne_coe : (a : α) ≠ b ↔ a ≠ b := coe_inj.not

end subtype

namespace list
variables {α : Type*} {l : list α}

lemma filter_comm (p : α → Prop) [decidable_pred p] (q : α → Prop) [decidable_pred q] (l : list α) :
  filter p (filter q l) = filter q (filter p l) :=
by simp [and_comm]

@[simp] lemma countp_attach (p : α → Prop) [decidable_pred p] (l : list α) :
  l.attach.countp (λ a, p ↑a) = l.countp p :=
by rw [←countp_map, attach_map_coe]

@[simp] lemma count_attach [decidable_eq α] (a : {x // x ∈ l}) : l.attach.count a = l.count a :=
eq.trans (countp_congr $ λ _ _, subtype.ext_iff) $ countp_attach _ _

@[simp] lemma length_filter_attach (p : α → Prop) [decidable_pred p] (s : list α) :
   (filter (λ a, p ↑a) s.attach).length = (filter p s).length :=
by simp_rw [←countp_eq_length_filter, countp_attach]

end list

namespace multiset
variables {α : Type*} {s : multiset α}

attribute [simp] multiset.sup_le

lemma filter_comm (p : α → Prop) [decidable_pred p] (q : α → Prop) [decidable_pred q]
  (s : multiset α) :
  filter p (filter q s) = filter q (filter p s) :=
by simp [and_comm]

--TODO: Rename `multiset.coe_attach` to `multiset.attach_coe`
--TODO: Rename `multiset.coe_countp` to `multiset.countp_coe`

--TODO: Maybe change `multiset.attach` to make `multiset.coe_attach` refl?

-- TODO: Fix `multiset.countp_congr`
lemma countp_congr' {s s' : multiset α} (hs : s = s') {p p' : α → Prop} [decidable_pred p]
  [decidable_pred p'] (hp : ∀ x ∈ s, p x ↔ p' x) : s.countp p = s'.countp p' :=
countp_congr hs $ λ x hx, propext $ hp x hx

@[simp] lemma countp_attach (p : α → Prop) [decidable_pred p] (s : multiset α) :
  s.attach.countp (λ a, p ↑a) = s.countp p :=
quotient.induction_on s $ λ l, begin
  simp only [quot_mk_to_coe, coe_countp],
  rw [quot_mk_to_coe, coe_attach, coe_countp],
  exact list.countp_attach _ _,
end

--TODO: Fix name `multiset.attach_count_eq_count_coe `
@[simp] lemma count_attach [decidable_eq α] (a : {x // x ∈ s}) : s.attach.count a = s.count a :=
eq.trans (countp_congr' rfl $ λ _ _, subtype.ext_iff) $ countp_attach _ _

@[simp] lemma card_filter_attach (p : α → Prop) [decidable_pred p] (s : multiset α) :
   (filter (λ a, p ↑a) s.attach).card = (filter p s).card :=
by simp_rw [←countp_eq_card_filter, countp_attach]

end multiset

namespace finset
variables {α β : Type*} [comm_monoid β] (s : finset α) (f : α → β)

open_locale big_operators

@[simp, to_additive] lemma prod_map_val : (s.1.map f).prod = ∏ a in s, f a := rfl

end finset

namespace finset
variables {α β : Type*} [add_comm_monoid_with_one β]

open_locale big_operators

@[simp] lemma card_val (s : finset α) : s.1.card = s.card := rfl

lemma card_filter (p : α → Prop) [decidable_pred p] (s : finset α) :
  (filter p s).card = ∑ a in s, ite (p a) 1 0 :=
sum_boole.symm

lemma coe_card_filter (p : α → Prop) [decidable_pred p] (s : finset α) :
  ((filter p s).card : β) = ∑ a in s, ite (p a) 1 0 :=
by { rw card_filter, norm_cast }

@[simp] lemma card_filter_attach (p : α → Prop) [decidable_pred p] (s : finset α) :
   (filter (λ a, p ↑a) s.attach).card = (filter p s).card :=
multiset.card_filter_attach _ _

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

namespace mv_polynomial
variables {R S₁ σ : Type*} [semiring R] [comm_semiring S₁] [module R S₁] {a : R}
  {f : mv_polynomial σ S₁}

lemma support_smul : (a • f).support ⊆ f.support := finsupp.support_smul

lemma total_degree_smul_le : (a • f).total_degree ≤ f.total_degree := finset.sup_mono support_smul

@[simp] lemma constant_coeff_smul (a : R) (f : mv_polynomial σ S₁) :
  constant_coeff (a • f) = a • constant_coeff f := rfl

end mv_polynomial

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
variables {p : ℕ} [fact p.prime] {s : multiset (zmod p)}

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

/-- The **Erdős–Ginzburg–Ziv theorem**: Any (not necessarily distinct) `2 * p - 1` elements of
`zmod p` contain `p` elements whose sum is zero. -/
lemma exists_submultiset_eq_zero (hs : s.card = 2 * p - 1) : ∃ t ≤ s, t.card = p ∧ t.sum = 0 :=
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
    { rw [←char_p.cast_eq_zero_iff (zmod p), finset.coe_card_filter],
      simpa only [f₁, map_sum, zmod.pow_card_sub_one, map_pow, eval_X] using x.2.1 },
    -- And it is at most `2 * p - 1`, so it must be `p`.
    { rw [finset.card_attach, card_to_enum_finset, hs],
     exact tsub_lt_self (mul_pos zero_lt_two (fact.out p.prime).pos) zero_lt_one } },
  -- From `f₂ x = 0`, we get that `p` divides the sum of the `a ∈ s` such that `x a ≠ 0`.
  { simpa only [f₂, map_sum, zmod.pow_card_sub_one, finset.sum_map_val, finset.sum_filter, smul_eval,
      map_pow, eval_X, mul_ite, mul_zero, mul_one] using x.2.2 }
end

end zmod
