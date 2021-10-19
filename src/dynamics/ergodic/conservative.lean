/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import dynamics.ergodic.measure_preserving
import combinatorics.pigeonhole

/-!
# Conservative systems

In this file we define `f : α → α` to be a *conservative* system w.r.t a measure `μ` if `f` is
non-singular (`measure_theory.quasi_measure_preserving`) and for every measurable set `s` of
positive measure at least one point `x ∈ s` returns back to `s` after some number of iterations of
`f`. There are several properties that look like they are stronger than this one but actually follow
from it:

* `measure_theory.conservative.frequently_measure_inter_ne_zero`,
  `measure_theory.conservative.exists_gt_measure_inter_ne_zero`: if `μ s ≠ 0`, then for infinitely
  many `n`, the measure of `s ∩ (f^[n]) ⁻¹' s` is positive.

* `measure_theory.conservative.measure_mem_forall_ge_image_not_mem_eq_zero`,
  `measure_theory.conservative.ae_mem_imp_frequently_image_mem`: a.e. every point of `s` visits `s`
  infinitely many times (Poincaré recurrence theorem).

We also prove the topological Poincaré recurrence theorem
`measure_theory.conservative.ae_frequently_mem_of_mem_nhds`. Let `f : α → α` be a conservative
dynamical system on a topological space with second countable topology and measurable open
sets. Then almost every point `x : α` is recurrent: it visits every neighborhood `s ∈ 𝓝 x`
infinitely many times.

## Tags

conservative dynamical system, Poincare recurrence theorem
-/

noncomputable theory

open classical set filter measure_theory finset function topological_space
open_locale classical topological_space

variables {ι : Type*} {α : Type*} [measurable_space α] {f : α → α} {s : set α} {μ : measure α}

namespace measure_theory

open measure

/-- We say that a non-singular (`measure_theory.quasi_measure_preserving`) self-map is
*conservative* if for any measurable set `s` of positive measure there exists `x ∈ s` such that `x`
returns back to `s` under some iteration of `f`. -/
structure conservative (f : α → α) (μ : measure α . volume_tac)
  extends quasi_measure_preserving f μ μ : Prop :=
(exists_mem_image_mem : ∀ ⦃s⦄, measurable_set s → μ s ≠ 0 → ∃ (x ∈ s) (m ≠ 0), f^[m] x ∈ s)

/-- A self-map preserving a finite measure is conservative. -/
protected lemma measure_preserving.conservative [is_finite_measure μ]
  (h : measure_preserving f μ μ) :
  conservative f μ :=
⟨h.quasi_measure_preserving, λ s hsm h0, h.exists_mem_image_mem hsm h0⟩

namespace conservative

/-- The identity map is conservative w.r.t. any measure. -/
protected lemma id (μ : measure α) : conservative id μ :=
{ to_quasi_measure_preserving := quasi_measure_preserving.id μ,
  exists_mem_image_mem := λ s hs h0, let ⟨x, hx⟩ := nonempty_of_measure_ne_zero h0 in
    ⟨x, hx, 1, one_ne_zero, hx⟩ }

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for infinitely many values of `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
lemma frequently_measure_inter_ne_zero (hf : conservative f μ) (hs : measurable_set s)
  (h0 : μ s ≠ 0) :
  ∃ᶠ m in at_top, μ (s ∩ (f^[m]) ⁻¹' s) ≠ 0 :=
begin
  by_contra H, simp only [not_frequently, eventually_at_top, ne.def, not_not] at H,
  rcases H with ⟨N, hN⟩,
  induction N with N ihN,
  { apply h0, simpa using hN 0 le_rfl },
  rw [imp_false] at ihN, push_neg at ihN,
  rcases ihN with ⟨n, hn, hμn⟩,
  set T := s ∩ ⋃ n ≥ N + 1, (f^[n]) ⁻¹' s,
  have hT : measurable_set T,
    from hs.inter (measurable_set.bUnion (countable_encodable _)
      (λ _ _, hf.measurable.iterate _ hs)),
  have hμT : μ T = 0,
  { convert (measure_bUnion_null_iff $ countable_encodable _).2 hN,
    rw ← set.inter_bUnion, refl },
  have : μ ((s ∩ (f^[n]) ⁻¹' s) \ T) ≠ 0, by rwa [measure_diff_null hμT],
  rcases hf.exists_mem_image_mem ((hs.inter (hf.measurable.iterate n hs)).diff hT) this
    with ⟨x, ⟨⟨hxs, hxn⟩, hxT⟩, m, hm0, ⟨hxms, hxm⟩, hxx⟩,
  refine hxT ⟨hxs, mem_bUnion_iff.2 ⟨n + m, _, _⟩⟩,
  { exact add_le_add hn (nat.one_le_of_lt $ pos_iff_ne_zero.2 hm0) },
  { rwa [set.mem_preimage, ← iterate_add_apply] at hxm }
end

/-- If `f` is a conservative map and `s` is a measurable set of nonzero measure, then
for an arbitrarily large `m` a positive measure of points `x ∈ s` returns back to `s`
after `m` iterations of `f`. -/
lemma exists_gt_measure_inter_ne_zero (hf : conservative f μ) (hs : measurable_set s) (h0 : μ s ≠ 0)
  (N : ℕ) :
  ∃ m > N, μ (s ∩ (f^[m]) ⁻¹' s) ≠ 0 :=
let ⟨m, hm, hmN⟩ :=
  ((hf.frequently_measure_inter_ne_zero hs h0).and_eventually (eventually_gt_at_top N)).exists
in ⟨m, hmN, hm⟩

/-- Poincaré recurrence theorem: given a conservative map `f` and a measurable set `s`, the set
of points `x ∈ s` such that `x` does not return to `s` after `≥ n` iterations has measure zero. -/
lemma measure_mem_forall_ge_image_not_mem_eq_zero (hf : conservative f μ) (hs : measurable_set s)
  (n : ℕ) :
  μ {x ∈ s | ∀ m ≥ n, f^[m] x ∉ s} = 0 :=
begin
  by_contradiction H,
  have : measurable_set (s ∩ {x | ∀ m ≥ n, f^[m] x ∉ s}),
  { simp only [set_of_forall, ← compl_set_of],
    exact hs.inter (measurable_set.bInter (countable_encodable _)
      (λ m _, hf.measurable.iterate m hs.compl)) },
  rcases (hf.exists_gt_measure_inter_ne_zero this H) n with ⟨m, hmn, hm⟩,
  rcases nonempty_of_measure_ne_zero hm with ⟨x, ⟨hxs, hxn⟩, hxm, -⟩,
  exact hxn m hmn.lt.le hxm
end

/-- Poincaré recurrence theorem: given a conservative map `f` and a measurable set `s`,
almost every point `x ∈ s` returns back to `s` infinitely many times. -/
lemma ae_mem_imp_frequently_image_mem (hf : conservative f μ) (hs : measurable_set s) :
  ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in at_top, (f^[n] x) ∈ s :=
begin
  simp only [frequently_at_top, @forall_swap (_ ∈ s), ae_all_iff],
  intro n,
  filter_upwards [measure_zero_iff_ae_nmem.1 (hf.measure_mem_forall_ge_image_not_mem_eq_zero hs n)],
  simp
end

lemma inter_frequently_image_mem_ae_eq (hf : conservative f μ) (hs : measurable_set s) :
  (s ∩ {x | ∃ᶠ n in at_top, f^[n] x ∈ s} : set α) =ᵐ[μ] s :=
inter_eventually_eq_left.2 $ hf.ae_mem_imp_frequently_image_mem hs

lemma measure_inter_frequently_image_mem_eq (hf : conservative f μ) (hs : measurable_set s) :
  μ (s ∩ {x | ∃ᶠ n in at_top, f^[n] x ∈ s}) = μ s :=
measure_congr (hf.inter_frequently_image_mem_ae_eq hs)

/-- Poincaré recurrence theorem: if `f` is a conservative dynamical system and `s` is a measurable
set, then for `μ`-a.e. `x`, if the orbit of `x` visits `s` at least once, then it visits `s`
infinitely many times.  -/
lemma ae_forall_image_mem_imp_frequently_image_mem (hf : conservative f μ) (hs : measurable_set s) :
  ∀ᵐ x ∂μ, ∀ k, f^[k] x ∈ s → ∃ᶠ n in at_top, (f^[n] x) ∈ s :=
begin
  refine ae_all_iff.2 (λ k, _),
  refine (hf.ae_mem_imp_frequently_image_mem (hf.measurable.iterate k hs)).mono (λ x hx hk, _),
  rw [← map_add_at_top_eq_nat k, frequently_map],
  refine (hx hk).mono (λ n hn, _),
  rwa [add_comm, iterate_add_apply]
end

/-- If `f` is a conservative self-map and `s` is a measurable set of positive measure, then
`μ.ae`-frequently we have `x ∈ s` and `s` returns to `s` under infinitely many iterations of `f`. -/
lemma frequently_ae_mem_and_frequently_image_mem (hf : conservative f μ) (hs : measurable_set s)
  (h0 : μ s ≠ 0) :
  ∃ᵐ x ∂μ, x ∈ s ∧ ∃ᶠ n in at_top, (f^[n] x) ∈ s :=
((frequently_ae_mem_iff.2 h0).and_eventually (hf.ae_mem_imp_frequently_image_mem hs)).mono $ λ x hx,
  ⟨hx.1, hx.2 hx.1⟩

/-- Poincaré recurrence theorem. Let `f : α → α` be a conservative dynamical system on a topological
space with second countable topology and measurable open sets. Then almost every point `x : α`
is recurrent: it visits every neighborhood `s ∈ 𝓝 x` infinitely many times. -/
lemma ae_frequently_mem_of_mem_nhds [topological_space α] [second_countable_topology α]
  [opens_measurable_space α] {f : α → α} {μ : measure α} (h : conservative f μ) :
  ∀ᵐ x ∂μ, ∀ s ∈ 𝓝 x, ∃ᶠ n in at_top, f^[n] x ∈ s :=
begin
  have : ∀ s ∈ countable_basis α, ∀ᵐ x ∂μ, x ∈ s → ∃ᶠ n in at_top, (f^[n] x) ∈ s,
    from λ s hs, h.ae_mem_imp_frequently_image_mem
      (is_open_of_mem_countable_basis hs).measurable_set,
  refine ((ae_ball_iff $ countable_countable_basis α).2 this).mono (λ x hx s hs, _),
  rcases (is_basis_countable_basis α).mem_nhds_iff.1 hs with ⟨o, hoS, hxo, hos⟩,
  exact (hx o hoS hxo).mono (λ n hn, hos hn)
end

/-- Iteration of a conservative system is a conservative system. -/
protected lemma iterate (hf : conservative f μ) (n : ℕ) : conservative (f^[n]) μ :=
begin
  cases n, { exact conservative.id μ }, -- Discharge the trivial case `n = 0`
  refine ⟨hf.1.iterate _, λ s hs hs0, _⟩,
  rcases (hf.frequently_ae_mem_and_frequently_image_mem hs hs0).exists with ⟨x, hxs, hx⟩,
  /- We take a point `x ∈ s` such that `f^[k] x ∈ s` for infinitely many values of `k`,
  then we choose two of these values `k < l` such that `k ≡ l [MOD (n + 1)]`.
  Then `f^[k] x ∈ s` and `(f^[n + 1])^[(l - k) / (n + 1)] (f^[k] x) = f^[l] x ∈ s`. -/
  rw nat.frequently_at_top_iff_infinite at hx,
  rcases nat.exists_lt_modeq_of_infinite hx n.succ_pos with ⟨k, hk, l, hl, hkl, hn⟩,
  set m := (l - k) / (n + 1),
  have : (n + 1) * m = l - k,
  { apply nat.mul_div_cancel',
    exact (nat.modeq_iff_dvd' hkl.le).1 hn },
  refine ⟨f^[k] x, hk, m, _, _⟩,
  { intro hm,
    rw [hm, mul_zero, eq_comm, nat.sub_eq_zero_iff_le] at this,
    exact this.not_lt hkl },
  { rwa [← iterate_mul, this, ← iterate_add_apply, nat.sub_add_cancel],
    exact hkl.le }
end

end conservative

end measure_theory
