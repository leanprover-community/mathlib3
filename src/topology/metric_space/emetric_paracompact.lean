/-
Copyright (c) 202 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import topology.metric_space.emetric_space
import topology.paracompact
import set_theory.ordinal

/-!
# (Extended) metric spaces are paracompact

In this file we provide two instances:

* `emetric.paracompact_space`: a `pseudo_emetric_space` is paracompact; formalization is based
  on [MR0236876];
* `emetric.normal_of_metric`: an `emetric_space` is a normal topological space.

## Tags

metric space, paracompact space, normal space
-/

variable {α : Type*}

open_locale ennreal topological_space
open set

namespace emetric

/-- A `pseudo_emetric_space` is always a paracompact space. Formalization is based
on [MR0236876]. -/
@[priority 100] -- See note [lower instance priority]
instance [pseudo_emetric_space α] : paracompact_space α :=
begin
  classical,
  /- We start with trivial observations about `1 / 2 ^ k`. Here and below we use `1 / 2 ^ k` in
  the comments and `2⁻¹ ^ k` in the code. -/
  have pow_pos : ∀ k : ℕ, (0 : ℝ≥0∞) < 2⁻¹ ^ k,
    from λ k, ennreal.pow_pos (ennreal.inv_pos.2 ennreal.two_ne_top) _,
  have hpow_le : ∀ {m n : ℕ}, m ≤ n → (2⁻¹ : ℝ≥0∞) ^ n ≤ 2⁻¹ ^ m,
    from λ m n h, ennreal.pow_le_pow_of_le_one (ennreal.inv_le_one.2 ennreal.one_lt_two.le) h,
  have h2pow : ∀ n : ℕ, 2 * (2⁻¹ : ℝ≥0∞) ^ (n + 1) = 2⁻¹ ^ n,
    by { intro n, simp [pow_succ, ← mul_assoc, ennreal.mul_inv_cancel] },
  -- Consider an open covering `S : set (set α)`
  refine ⟨λ ι s ho hcov, _⟩,
  simp only [Union_eq_univ_iff] at hcov,
  -- choose a well founded order on `S`
  letI : linear_order ι := linear_order_of_STO' well_ordering_rel,
  have wf : well_founded ((<) : ι → ι → Prop) := @is_well_order.wf ι well_ordering_rel _,
  -- Let `ind x` be the minimal index `s : S` such that `x ∈ s`.
  set ind : α → ι := λ x, wf.min {i : ι | x ∈ s i} (hcov x),
  have mem_ind : ∀ x, x ∈ s (ind x), from λ x, wf.min_mem _ (hcov x),
  have nmem_of_lt_ind : ∀ {x i}, i < (ind x) → x ∉ s i,
    from λ x i hlt hxi, wf.not_lt_min _ (hcov x) hxi hlt,
  /- The refinement `D : ℕ → ι → set α` is defined recursively. For each `n` and `i`, `D n i`
  is the union of balls `ball x (1 / 2 ^ n)` over all points `x` such that

  * `ind x = i`;
  * `x` does not belong to any `D m j`, `m < n`;
  * `ball x (3 / 2 ^ n) ⊆ s i`;

  We define this sequence using `nat.strong_rec_on'`, then restate it as `Dn` and `memD`.
  -/
  set D : ℕ → ι → set α :=
    λ n, nat.strong_rec_on' n (λ n D' i,
      ⋃ (x : α) (hxs : ind x = i) (hb : ball x (3 * 2⁻¹ ^ n) ⊆ s i)
        (hlt : ∀ (m < n) (j : ι), x ∉ D' m ‹_› j), ball x (2⁻¹ ^ n)),
  have Dn : ∀ n i, D n i = ⋃ (x : α) (hxs : ind x = i) (hb : ball x (3 * 2⁻¹ ^ n) ⊆ s i)
    (hlt : ∀ (m < n) (j : ι), x ∉ D m j), ball x (2⁻¹ ^ n),
    from λ n s, by { simp only [D], rw nat.strong_rec_on_beta' },
  have memD : ∀ {n i y}, y ∈ D n i ↔ ∃ x (hi : ind x = i) (hb : ball x (3 * 2⁻¹ ^ n) ⊆ s i)
    (hlt : ∀ (m < n) (j : ι), x ∉ D m j), edist y x < 2⁻¹ ^ n,
  { intros n i y, rw [Dn n i], simp only [mem_Union, mem_ball] },
  -- The sets `D n i` cover the whole space. Indeed, for each `x` we can choose `n` such that
  -- `ball x (3 / 2 ^ n) ⊆ s (ind x)`, then either `x ∈ D n i`, or `x ∈ D m i` for some `m < n`.
  have Dcov : ∀ x, ∃ n i, x ∈ D n i,
  { intro x,
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ball x (3 * 2⁻¹ ^ n) ⊆ s (ind x),
    { -- This proof takes 5 lines because we can't import `specific_limits` here
      rcases is_open_iff.1 (ho $ ind x) x (mem_ind x) with ⟨ε, ε0, hε⟩,
      have : 0 < ε / 3 := ennreal.div_pos_iff.2 ⟨ε0.lt.ne', ennreal.coe_ne_top⟩,
      rcases ennreal.exists_inv_two_pow_lt this.ne' with ⟨n, hn⟩,
      refine ⟨n, subset.trans (ball_subset_ball _) hε⟩,
      simpa only [div_eq_mul_inv, mul_comm] using (ennreal.mul_lt_of_lt_div hn).le },
    by_contra h, push_neg at h,
    apply h n (ind x),
    exact memD.2 ⟨x, rfl, hn, λ _ _ _, h _ _, mem_ball_self (pow_pos _)⟩ },
  -- Each `D n i` is a union of open balls, hence it is an open set
  have Dopen : ∀ n i, is_open (D n i),
  { intros n i,
    rw Dn,
    iterate 4 { refine is_open_Union (λ _, _) },
    exact is_open_ball },
  -- the covering `D n i` is a refinement of the original covering: `D n i ⊆ s i`
  have HDS : ∀ n i, D n i ⊆ s i,
  { intros n s x,
    rw memD,
    rintro ⟨y, rfl, hsub, -, hyx⟩,
    refine hsub (lt_of_lt_of_le hyx _),
    calc 2⁻¹ ^ n = 1 * 2⁻¹ ^ n : (one_mul _).symm
    ... ≤ 3 * 2⁻¹ ^ n : ennreal.mul_le_mul _ le_rfl,
    -- TODO: use `norm_num`
    have : ((1 : ℕ) : ℝ≥0∞) ≤ (3 : ℕ), from ennreal.coe_nat_le_coe_nat.2 (by norm_num1),
    exact_mod_cast this },
  -- Let us show the rest of the properties. Since the definition expects a family indexed
  -- by a single parameter, we use `ℕ × ι` as the domain.
  refine ⟨ℕ × ι, λ ni, D ni.1 ni.2, λ _, Dopen _ _, _, _, λ ni, ⟨ni.2, HDS _ _⟩⟩,
  -- The sets `D n i` cover the whole space as we proved earlier
  { refine Union_eq_univ_iff.2 (λ x, _),
    rcases Dcov x with ⟨n, i, h⟩,
    exact ⟨⟨n, i⟩, h⟩ },
  { /- Let us prove that the covering `D n i` is locally finite. Take a point `x` and choose
    `n`, `i` so that `x ∈ D n i`. Since `D n i` is an open set, we can choose `k` so that
    `B = ball x (1 / 2 ^ (n + k + 1)) ⊆ D n i`. -/
    intro x,
    rcases Dcov x with ⟨n, i, hn⟩,
    have : D n i ∈ 𝓝 x, from is_open.mem_nhds (Dopen _ _) hn,
    rcases (nhds_basis_uniformity uniformity_basis_edist_inv_two_pow).mem_iff.1 this
      with ⟨k, -, hsub : ball x (2⁻¹ ^ k) ⊆ D n i⟩,
    set B := ball x (2⁻¹ ^ (n + k + 1)),
    refine ⟨B, ball_mem_nhds _ (pow_pos _), _⟩,
    -- The sets `D m i`, `m > n + k`, are disjoint with `B`
    have Hgt : ∀ (m ≥ n + k + 1) (i : ι), disjoint (D m i) B,
    { rintros m hm i y ⟨hym, hyx⟩,
      rcases memD.1 hym with ⟨z, rfl, hzi, H, hz⟩,
      have : z ∉ ball x (2⁻¹ ^ k), from λ hz, H n (by linarith) i (hsub hz), apply this,
      calc edist z x ≤ edist y z + edist y x : edist_triangle_left _ _ _
      ... < (2⁻¹ ^ m) + (2⁻¹ ^ (n + k + 1)) : ennreal.add_lt_add hz hyx
      ... ≤ (2⁻¹ ^ (k + 1)) + (2⁻¹ ^ (k + 1)) :
        add_le_add (hpow_le $ by linarith) (hpow_le $ by linarith)
      ... = (2⁻¹ ^ k) : by rw [← two_mul, h2pow] },
    -- For each `m ≤ n + k` there is at most one `j` such that `D m j ∩ B` is nonempty.
    have Hle : ∀ m ≤ n + k, set.subsingleton {j | (D m j ∩ B).nonempty},
    { rintros m hm j₁ ⟨y, hyD, hyB⟩ j₂ ⟨z, hzD, hzB⟩,
      by_contra h,
      wlog h : j₁ < j₂ := ne.lt_or_lt h using [j₁ j₂ y z, j₂ j₁ z y],
      rcases memD.1 hyD with ⟨y', rfl, hsuby, -, hdisty⟩,
      rcases memD.1 hzD with ⟨z', rfl, -, -, hdistz⟩,
      suffices : edist z' y' < 3 * 2⁻¹ ^ m, from nmem_of_lt_ind h (hsuby this),
      calc edist z' y' ≤ edist z' x + edist x y' : edist_triangle _ _ _
      ... ≤ (edist z z' + edist z x) + (edist y x + edist y y') :
        add_le_add (edist_triangle_left _ _ _) (edist_triangle_left _ _ _)
      ... < (2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1)) + (2⁻¹ ^ (n + k + 1) + 2⁻¹ ^ m) :
        by apply_rules [ennreal.add_lt_add]
      ... = 2 * (2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1)) : by simp only [two_mul, add_comm]
      ... ≤ 2 * (2⁻¹ ^ m + 2⁻¹ ^ (m + 1)) :
        ennreal.mul_le_mul le_rfl $ add_le_add le_rfl $ hpow_le (add_le_add hm le_rfl)
      ... = 3 * 2⁻¹ ^ m : by rw [mul_add, h2pow, bit1, add_mul, one_mul] },
    -- Finally, we glue `Hgt` and `Hle`
    have : (⋃ (m ≤ n + k) (i ∈ {i : ι | (D m i ∩ B).nonempty}), {(m, i)}).finite,
      from (finite_le_nat _).bUnion (λ i hi, (Hle i hi).finite.bUnion (λ _ _, finite_singleton _)),
    refine this.subset (λ I hI, _), simp only [mem_Union],
    refine ⟨I.1, _, I.2, hI, prod.mk.eta.symm⟩,
    exact not_lt.1 (λ hlt, Hgt I.1 hlt I.2 hI.some_spec) }
end

@[priority 100] -- see Note [lower instance priority]
instance normal_of_emetric [emetric_space α] : normal_space α := normal_of_paracompact_t2

end emetric
