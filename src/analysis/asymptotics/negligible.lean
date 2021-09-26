/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import analysis.asymptotics.asymptotics
import analysis.special_functions.polynomials
import algebra.archimedean

lemma norm_coe_nat_le_coe (R : Type*) [semi_normed_ring R] [norm_one_class R] :
  ∀ (n : ℕ), ∥(n : R)∥ ≤ (n : ℝ)
| 0 := by simp
| (n + 1) := begin
  simp only [nat.cast_add, nat.cast_one],
  refine (norm_add_le _ _).trans _,
  refine add_le_add (norm_coe_nat_le_coe n) (le_of_eq _),
  refine norm_one,
end

lemma coe_nat_is_O_coe_nat (R : Type*) [semi_normed_ring R] [norm_one_class R] :
  asymptotics.is_O (coe : ℕ → R) (coe : ℕ → ℝ) filter.at_top :=
begin
  refine asymptotics.is_O_of_le filter.at_top (λ n, _),
  refine le_trans (norm_coe_nat_le_coe R n) _,
  simp,
end

-- lemma exists_norm_coe_nat_gt (x : ℝ) : ∃ (n : ℕ), x < ∥(n : ℝ)∥ :=
-- let ⟨n, hn⟩ := exists_nat_gt x in
--   ⟨n, lt_of_lt_of_le hn (le_of_eq (real.norm_coe_nat n).symm)⟩

-- @[simp]
-- lemma norm_coe_nat_le_iff (n m : ℕ) :
--   ∥(n : ℝ)∥ ≤ ∥(m : ℝ)∥ ↔ n ≤ m :=
-- by simp only [real.norm_coe_nat, nat.cast_le]

lemma real.norm_coe_nat_eventually_ge (c : ℝ) :
  ∀ᶠ (x : ℕ) in filter.at_top, c ≤ ∥(x : ℝ)∥ :=
begin
  simp only [filter.eventually_at_top, real.norm_coe_nat, ge_iff_le],
  obtain ⟨y, hy⟩ := exists_nat_ge c,
  exact ⟨y, λ x hx, hy.trans $ nat.cast_le.mpr hx⟩,
end

lemma nat_coe_tendsto_at_top (R : Type*) [ordered_ring R] [nontrivial R] [archimedean R] :
  filter.tendsto (λ (n : ℕ), (↑n : R)) filter.at_top filter.at_top :=
begin
  refine filter.tendsto_at_top.2 (λ x, _),
  obtain ⟨m, hm⟩ := exists_nat_ge x,
  rw filter.eventually_at_top,
  refine ⟨m, λ y hy, hm.trans $ nat.cast_le.2 hy⟩,
end

namespace asymptotics

lemma fpow_is_O_fpow_of_le {α 𝕜 : Type*} [preorder α] [normed_field 𝕜]
  {f : α → 𝕜} {a b : ℤ} (hab : a ≤ b)
  (h : ∀ᶠ (x : α) in filter.at_top, 1 ≤ ∥f x∥):
  (is_O (λ n, (f n) ^ a) (λ n, (f n) ^ b) filter.at_top) :=
begin
  refine is_O.of_bound 1 (filter.sets_of_superset filter.at_top h (λ x hx, _)),
  simp only [one_mul, normed_field.norm_fpow, set.mem_set_of_eq],
  exact fpow_le_of_le hx hab,
end

/-- Definition of negligible functions over an arbitrary `normed_field`.
  Note that the second function always has type `ℕ → ℝ`, which generally gives better lemmas. -/
def negligible {𝕜 : Type*} [normed_ring 𝕜] (f : ℕ → 𝕜) :=
∀ (c : ℤ), is_O f (λ n, (n : ℝ) ^ c) filter.at_top

variables {𝕜 : Type*} [normed_field 𝕜]
variables {f g : ℕ → 𝕜}

lemma negligible_of_is_O (hg : negligible g)
  (h : is_O f g filter.at_top) : negligible f :=
λ c, h.trans $ hg c

lemma negligible_of_eventually_le (hg : negligible g)
  (h : ∀ᶠ n in filter.at_top, ∥f n∥ ≤ ∥g n∥) : negligible f :=
negligible_of_is_O hg $ is_O_iff.2 ⟨1, by simpa only [one_mul] using h⟩

/-- It suffices to check the negligiblity condition for only sufficiently small exponents -/
lemma negligible_of_eventually_is_O
  (h : ∀ᶠ (c : ℤ) in filter.at_bot, is_O f (λ n, (n : ℝ) ^ c) filter.at_top) :
  negligible f :=
begin
  obtain ⟨C, hC⟩ := filter.eventually_at_bot.mp h,
  intro c,
  by_cases hc : c ≤ C,
  { exact hC c hc },
  { exact (hC C le_rfl).trans
      (fpow_is_O_fpow_of_le (le_of_not_le hc) (real.norm_coe_nat_eventually_ge 1)) }
end

lemma negligible_of_is_O_fpow_le (C : ℤ)
  (h : ∀ c ≤ C, is_O f (λ n, (n : ℝ) ^ c) filter.at_top) :
  negligible f :=
begin
  refine negligible_of_eventually_is_O _,
  rw filter.eventually_at_bot,
  refine ⟨C, h⟩,
end

lemma negligible_of_is_O_fpow_lt (C : ℤ)
  (h : ∀ c < C, is_O f (λ n, (n : ℝ) ^ c) filter.at_top) :
  negligible f :=
begin
  refine negligible_of_is_O_fpow_le C.pred (λ c hc, _),
  refine h c _,
  refine lt_of_le_of_lt hc _,
  refine int.pred_self_lt C,
end

lemma tendsto_zero_of_negligible (hf : negligible f) :
  filter.tendsto f filter.at_top (nhds 0) :=
begin
  refine is_O.trans_tendsto (hf (-1)) _,
  have : (λ (n : ℕ), (n : ℝ) ^ (-1 : ℤ)) = (has_inv.inv : ℝ → ℝ) ∘ (coe : ℕ → ℝ),
  by simp only [gpow_one, fpow_neg],
  rw this,
  refine filter.tendsto.comp (tendsto_inv_at_top_zero) (nat_coe_tendsto_at_top ℝ),
end

lemma norm_eventually_le_of_negligible
  (hf : negligible f) (x₀ : ℝ) (hx₀ : 0 < x₀) :
  ∀ᶠ (n : ℕ) in filter.at_top, ∥f n∥ ≤ x₀ :=
begin
  specialize hf (-1),
  rw is_O_iff at hf,
  obtain ⟨c, hc⟩ := hf,
  refine filter.eventually.mp hc _,
  have : ∀ᶠ (n : ℕ) in filter.at_top, c * ∥(n : ℝ) ^ (-1 : ℤ)∥ ≤ x₀,
  {
    rw filter.eventually_at_top,
    obtain ⟨a, ha⟩ := exists_nat_ge (c * x₀⁻¹),
    rw mul_inv_le_iff hx₀ at ha,
    use (max a 1),
    intros b hb,
    have : 0 < (b : ℝ) := nat.cast_pos.2 (le_trans (le_max_right a 1) hb),
    simp,
    rw [mul_inv_le_iff this, mul_comm _ x₀],
    refine le_trans ha _,
    refine mul_le_mul le_rfl _ (nat.cast_nonneg a) (le_of_lt hx₀),
    refine nat.cast_le.2 (le_trans _ hb),
    refine le_max_left a 1,
  },
  refine filter.eventually.mono this _,
  refine (λ x hx hx', le_trans hx' hx),
end

@[simp]
lemma negligible_zero : negligible (function.const ℕ (0 : 𝕜)) :=
λ c, is_O_zero _ _

@[simp]
lemma negligable_const_iff [t1_space 𝕜] (x : 𝕜) :
  negligible (function.const ℕ x) ↔ x = 0 :=
begin
  refine ⟨λ h, not_not.1 (λ hx, _), λ h, h.symm ▸ negligible_zero⟩,
  have := tendsto_zero_of_negligible h,
  rw tendsto_nhds at this,
  specialize this {x}ᶜ (is_open_ne) (ne.symm hx),
  have h' : function.const ℕ x ⁻¹' {x}ᶜ = ∅,
  { refine set.preimage_eq_empty _,
    rw set.range_const,
    exact disjoint_compl_left },
  rw h' at this,
  exact filter.at_top.empty_not_mem this,
end

lemma negligible_add (hf : negligible f) (hg : negligible g) :
  negligible (f + g) :=
λ c, (hf c).add $ hg c

lemma negligible_mul (hf : negligible f) (hg : negligible g) :
  negligible (f * g) :=
begin
  suffices : is_O (f * g) f filter.at_top,
  from λ c, this.trans (hf c),
  refine is_O.of_bound 1 _,
  have := norm_eventually_le_of_negligible hg 1 (zero_lt_one),
  refine this.mono (λ x hx, _),
  rw [pi.mul_apply, normed_field.norm_mul, mul_comm 1 ∥f x∥],
  refine mul_le_mul le_rfl hx (norm_nonneg $ g x) (norm_nonneg $ f x),
end

lemma negligible_const_mul_iff (f : ℕ → 𝕜) {c : 𝕜} (hc : c ≠ 0) :
  negligible (λ n, c * f n) ↔ negligible f :=
forall_congr (λ x, ⟨λ h, is_O.trans (is_O_self_const_mul c hc f filter.at_top) h,
  λ h, is_O.trans (is_O_const_mul_self c f filter.at_top) h⟩)

lemma negligable_const_mul_of_negligable {f : ℕ → 𝕜} (c : 𝕜)
  (hf : negligible f) : negligible (λ n, c * f n) :=
begin
  by_cases hc : c = 0,
  { simpa only [hc, zero_mul] using negligible_zero },
  { simpa only [hc, ne.def, not_false_iff, negligible_const_mul_iff] using hf }
end

@[simp]
lemma negligible_x_mul_iff [norm_one_class 𝕜] (f : ℕ → 𝕜) :
  negligible (λ n, n • f n) ↔ negligible f :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  {
    refine negligible_of_is_O h _,
    sorry,
  },
  { refine negligible_of_is_O_fpow_lt 0 (λ c hc, _),
    specialize h (c - 1),
    have := is_O.mul (coe_nat_is_O_coe_nat 𝕜) h,
    simp at this,
    simp [nsmul_eq_mul],
    refine this.trans _,
    refine is_O_of_le _ (λ x, le_of_eq (congr_arg _ _)),
    by_cases hx : (x : ℝ) = 0,
    {
      simp [hx, this],
      refine symm (zero_fpow c (ne_of_lt hc)),
    },
    calc (x : ℝ) * ↑x ^ (c - 1) = (↑x ^ (1 : ℤ)) * (↑x ^ (c - 1)) : by rw gpow_one
      ... = ↑x ^ (1 + (c - 1)) : (fpow_add hx 1 (c - 1)).symm
      ... = ↑x ^ c : congr_arg (λ g, gpow g (x : ℝ)) (by linarith)
  }

    -- refine is_O.trans (is_O.mul _ _) _,
    -- refine (is_O.mul (is_O_refl (coe : ℕ → 𝕜) filter.at_top) (h (c - 1))).trans (_),
    -- refine is_O_of_le filter.at_top (λ x, _),
    -- simp only [one_mul, normed_field.norm_mul, normed_field.norm_fpow, set.mem_set_of_eq],
    -- by_cases hx : (x : ℝ) = 0,
    -- { by_cases hc : c = 0,
    --   { simp [hx, hc, zero_le_one] },
    --   { simp [hx, zero_fpow c hc] } },
    -- {
    --   have : ∥(x : ℝ)∥ ≠ 0,
    --   by rwa ← norm_eq_zero at hx,
    --   rw [mul_comm ∥(x : ℝ)∥, fpow_sub_one this, mul_assoc, inv_mul_cancel this, mul_one],
    --    } }
end


end asymptotics
