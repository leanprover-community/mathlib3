/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
import probability.probability_mass_function.constructions

/-!
# Probability mass functions

This file gives defines an `spmf` type to represent sub-probability mass functions,
i.e. mass functions with a total mass less than or equal to `1`, rather than equal to `1`.
We implement this as a `pmf (option α)`, where the "extra" mass is all assigned to `none`.
`spmf.to_pmf` converts back to the underlying `pmf`, and `pmf.to_spmf` converts back via `pmf.map`.

## Tags

probability mass function, discrete probability measure
-/

noncomputable theory
variables {α β γ : Type*}
open_locale classical big_operators ennreal measure_theory

/-- Rewrite a sum over `option α` as the value at `none` plus the sum over `α`. -/
lemma tsum_option_eq_extract_none {α β : Type*} [add_comm_group α] [topological_space α]
  [topological_add_group α] [t2_space α]
  (f : option β → α) (hf : summable f) : tsum f = f none + ∑' x, f (some x) :=
begin
  refine (tsum_eq_add_tsum_ite hf none).trans (congr_arg ((+) (f none)) _),
  refine tsum_eq_tsum_of_ne_zero_bij (λ x, some ↑x) (λ x y, option.some_inj.1) (λ x hx, _) _,
  { obtain ⟨y, hy⟩ := option.ne_none_iff_exists.1 (λ hx', hx (if_pos hx')),
    simpa [← hy] using hx },
  { simp only [option.some_ne_none, if_false, eq_self_iff_true, forall_true_iff] }
end

/-- Version of `tsum_option_eq_extract_none` for `add_comm_monoid` instead of `add_comm_group`. -/
lemma tsum_option_eq_extract_none' {α β : Type*} [add_comm_monoid α] [topological_space α]
  [has_continuous_add α] [t2_space α]
  (f : option β → α) (hf : summable (f.update none 0)) : tsum f = f none + ∑' x, f (some x) :=
begin
  refine (tsum_eq_add_tsum_ite' none (by convert hf)).trans (congr_arg ((+) (f none)) _),
  refine tsum_eq_tsum_of_ne_zero_bij (λ x, some ↑x) (λ x y, option.some_inj.1) (λ x hx, _) _,
  { obtain ⟨y, hy⟩ := option.ne_none_iff_exists.1 (λ hx',hx (by convert if_pos hx')),
    simpa [← hy] using hx },
  { simp only [option.some_ne_none, if_false, eq_self_iff_true, forall_true_iff] }
end






/-- A sub-probability mass function `spmf α`, is a function `α → ℝ≥0∞` such that the values
have (infinite) sum less than or equal to `1`. We implement this as a `pmf (option α)`,
where the "extra" mass is all assigned to `none`. -/
def spmf (α : Type*) : Type* := pmf (option α)

/-- View an `spmf` on `α` as the underlying `pmf` on `option α`. -/
def spmf.to_pmf (sp : spmf α) : pmf (option α) := sp

namespace spmf

instance [inhabited α] : inhabited (spmf α) := ⟨pmf.pure default⟩

/-- Applying the underlying `pmf` to `none` gives all of the "missing" mass to make the sum `1`. -/
protected lemma to_pmf_none (sp : spmf α) : sp.to_pmf none =
  1 - ∑' x, sp.to_pmf (some x) :=
begin
  have : pmf.fun_like.coe sp none + ∑' (x : α), pmf.fun_like.coe sp (some x) = 1 :=
    (tsum_option_eq_extract_none' _ ennreal.summable).symm.trans (pmf.tsum_coe sp),
  refine this ▸ (ennreal.add_sub_cancel_right (λ h, ennreal.top_ne_one _)).symm,
  rwa [h, add_top] at this,
end

/-- The probability of getting `x : α` from an `spmf α` is defined to be the chance of choosing
getting `some x` from the underlying `pmf (option α)`. -/
instance fun_like : fun_like (spmf α) α (λ x, ℝ≥0∞) :=
{ coe := λ sp x, pmf.fun_like.coe sp (some x),
  coe_injective' := λ sp sq h,
    let h' : ∀ x, sp.to_pmf (some x) = sq.to_pmf (some x) := congr_fun h in pmf.ext
      (λ x, option.rec (sp.to_pmf_none.trans (trans (by simp [h']) sq.to_pmf_none.symm)) h' x) }

protected lemma ext {sp sq : spmf α} (h : ∀ x, sp x = sq x) : sp = sq := fun_like.ext sp sq h

protected lemma ext_iff {sp sq : spmf α} : sp = sq ↔ ∀ x, sp x = sq x := fun_like.ext_iff

lemma tsum_coe_le_one (sp : spmf α) : ∑' a, sp a ≤ 1 :=
by convert le_of_le_of_eq (le_of_le_of_eq le_add_self
  (tsum_option_eq_extract_none' _ ennreal.summable).symm) (pmf.tsum_coe sp)

def support (sp : spmf α) : set α := function.support sp

@[simp] lemma mem_support_iff (sp : spmf α) (x : α) :
  x ∈ sp.support ↔ sp x ≠ 0 := function.mem_support

section pure

def pure (a : α) : spmf α := pmf.pure (some a)

variables (a a' : α)

@[simp] lemma pure_apply : pure a a' = if a' = a then 1 else 0 :=
(pmf.pure_apply _ _).trans (by simp [option.some_inj])

@[simp] lemma pure_apply_self : pure a a = 1 := by simp

lemma pure_apply_of_ne (h : a' ≠ a) : pure a a' = 0 := by simp [h]

@[simp] lemma support_pure : (pure a).support = {a} := set.ext (λ a', by simp [mem_support_iff])

lemma mem_support_pure_iff: a' ∈ (pure a).support ↔ a' = a := by simp

end pure

section bind

def bind (sp : spmf α) (sq : α → spmf β) : spmf β :=
pmf.bind sp (λ x, option.rec_on x (pmf.pure none) sq)

variables (sp : spmf α) (sq : α → spmf β) (x : α) (y : β)

@[simp] lemma bind_apply : bind sp sq y = ∑' x, sp x * sq x y :=
(pmf.bind_apply _ _ _).trans (by simpa only [tsum_option_eq_extract_none' _ ennreal.summable,
  pmf.pure_apply, if_false, mul_zero, zero_add])

@[simp] lemma support_bind : (bind sp sq).support = ⋃ x ∈ sp.support, (sq x).support :=
by simp only [set.ext_iff, mem_support_iff, bind_apply, ne.def, ennreal.tsum_eq_zero, not_forall,
  set.mem_Union, mul_eq_zero, not_or_distrib, exists_prop, iff_self, imp_true_iff]

lemma mem_support_bind_iff : y ∈ (bind sp sq).support ↔ ∃ x ∈ sp.support, y ∈ (sq x).support :=
by simp only [support_bind, set.mem_Union]

end bind

instance : monad spmf :=
{ pure := λ _, spmf.pure,
  bind := λ _ _, spmf.bind }

lemma monad_pure_eq_pure {α} (a : α) : (has_pure.pure a : spmf α) = pure a := rfl

lemma monad_bind_eq_bind {α β} (sp : spmf α) (sq : α → spmf β) :
  (has_bind.bind sp sq) = sp.bind sq := rfl

end spmf

namespace pmf

/-- View a `pmf` on `α` as an `spmf` by mapping the values with `option.some`. -/
def to_spmf (p : pmf α) : spmf α := p.map option.some

@[simp] lemma to_spmf_apply (p : pmf α) (x : α) : p.to_spmf x = p x :=
begin
  refine (pmf.map_apply option.some p (some x)).trans _,
  simp only [option.some_inj, tsum_ite_eq],
  exact trans (tsum_eq_single x (λ y hy, if_neg hy.symm)) (if_pos rfl),
end

lemma tsum_coe_to_spmf_eq_one (p : pmf α) : ∑' x, p.to_spmf x = 1 :=
(tsum_congr (p.to_spmf_apply)).trans p.tsum_coe

@[simp] lemma support_to_spmf (p : pmf α) : p.to_spmf.support = p.support := by simp [set.ext_iff]

@[simp] lemma to_spmf_pure (a : α) : (pmf.pure a).to_spmf = spmf.pure a := by simp [spmf.ext_iff]

@[simp] lemma to_spmf_bind (p : pmf α) (q : α → pmf β) :
  (p.bind q).to_spmf = p.to_spmf.bind (to_spmf ∘ q) :=
by simp [spmf.ext_iff, to_spmf_apply, spmf.bind_apply, pmf.bind_apply]

end pmf
