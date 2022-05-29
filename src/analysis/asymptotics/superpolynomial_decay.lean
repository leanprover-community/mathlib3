/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import analysis.asymptotics.asymptotics
import analysis.normed_space.ordered
import data.polynomial.eval
import topology.algebra.order.liminf_limsup

/-!
# Super-Polynomial Function Decay

This file defines a predicate `asymptotics.superpolynomial_decay f` for a function satisfying
  one of following equivalent definitions (The definition is in terms of the first condition):

* `x ^ n * f` tends to `𝓝 0` for all (or sufficiently large) naturals `n`
* `|x ^ n * f|` tends to `𝓝 0` for all naturals `n` (`superpolynomial_decay_iff_abs_tendsto_zero`)
* `|x ^ n * f|` is bounded for all naturals `n` (`superpolynomial_decay_iff_abs_is_bounded_under`)
* `f` is `o(x ^ c)` for all integers `c` (`superpolynomial_decay_iff_is_o`)
* `f` is `O(x ^ c)` for all integers `c` (`superpolynomial_decay_iff_is_O`)

These conditions are all equivalent to conditions in terms of polynomials, replacing `x ^ c` with
  `p(x)` or `p(x)⁻¹` as appropriate, since asymptotically `p(x)` behaves like `X ^ p.nat_degree`.
These further equivalences are not proven in mathlib but would be good future projects.

The definition of superpolynomial decay for `f : α → β` is relative to a parameter `k : α → β`.
Super-polynomial decay then means `f x` decays faster than `(k x) ^ c` for all integers `c`.
Equivalently `f x` decays faster than `p.eval (k x)` for all polynomials `p : polynomial β`.
The definition is also relative to a filter `l : filter α` where the decay rate is compared.

When the map `k` is given by `n ↦ ↑n : ℕ → ℝ` this defines negligible functions:
https://en.wikipedia.org/wiki/Negligible_function

When the map `k` is given by `(r₁,...,rₙ) ↦ r₁*...*rₙ : ℝⁿ → ℝ` this is equivalent
  to the definition of rapidly decreasing functions given here:
https://ncatlab.org/nlab/show/rapidly+decreasing+function

# Main Theorems

* `superpolynomial_decay.polynomial_mul` says that if `f(x)` is negligible,
    then so is `p(x) * f(x)` for any polynomial `p`.
* `superpolynomial_decay_iff_zpow_tendsto_zero` gives an equivalence between definitions in terms
    of decaying faster than `k(x) ^ n` for all naturals `n` or `k(x) ^ c` for all integer `c`.
-/

namespace asymptotics

open_locale topological_space
open filter

/-- `f` has superpolynomial decay in parameter `k` along filter `l` if
  `k ^ n * f` tends to zero at `l` for all naturals `n` -/
def superpolynomial_decay {α β : Type*} [topological_space β] [comm_semiring β]
  (l : filter α) (k : α → β) (f : α → β) :=
∀ (n : ℕ), tendsto (λ (a : α), (k a) ^ n * f a) l (𝓝 0)

variables {α β : Type*} {l : filter α} {k : α → β} {f g g' : α → β}

section comm_semiring

variables [topological_space β] [comm_semiring β]

lemma superpolynomial_decay.congr' (hf : superpolynomial_decay l k f)
  (hfg : f =ᶠ[l] g) : superpolynomial_decay l k g :=
λ z, (hf z).congr' (eventually_eq.mul (eventually_eq.refl l _) hfg)

lemma superpolynomial_decay.congr (hf : superpolynomial_decay l k f)
  (hfg : ∀ x, f x = g x) : superpolynomial_decay l k g :=
λ z, (hf z).congr (λ x, congr_arg (λ a, k x ^ z * a) $ hfg x)

@[simp]
lemma superpolynomial_decay_zero (l : filter α) (k : α → β) :
  superpolynomial_decay l k 0 :=
λ z, by simpa only [pi.zero_apply, mul_zero] using tendsto_const_nhds

lemma superpolynomial_decay.add [has_continuous_add β] (hf : superpolynomial_decay l k f)
  (hg : superpolynomial_decay l k g) : superpolynomial_decay l k (f + g) :=
λ z, by simpa only [mul_add, add_zero, pi.add_apply] using (hf z).add (hg z)

lemma superpolynomial_decay.mul [has_continuous_mul β] (hf : superpolynomial_decay l k f)
  (hg : superpolynomial_decay l k g) : superpolynomial_decay l k (f * g) :=
λ z, by simpa only [mul_assoc, one_mul, mul_zero, pow_zero] using (hf z).mul (hg 0)

lemma superpolynomial_decay.mul_const [has_continuous_mul β] (hf : superpolynomial_decay l k f)
  (c : β) : superpolynomial_decay l k (λ n, f n * c) :=
λ z, by simpa only [←mul_assoc, zero_mul] using tendsto.mul_const c (hf z)

lemma superpolynomial_decay.const_mul [has_continuous_mul β] (hf : superpolynomial_decay l k f)
  (c : β) : superpolynomial_decay l k (λ n, c * f n) :=
(hf.mul_const c).congr (λ _, mul_comm _ _)

lemma superpolynomial_decay.param_mul (hf : superpolynomial_decay l k f) :
  superpolynomial_decay l k (k * f) :=
λ z, tendsto_nhds.2 (λ s hs hs0, l.sets_of_superset ((tendsto_nhds.1 (hf $ z + 1)) s hs hs0)
  (λ x hx, by simpa only [set.mem_preimage, pi.mul_apply, ← mul_assoc, ← pow_succ'] using hx))

lemma superpolynomial_decay.mul_param (hf : superpolynomial_decay l k f) :
  superpolynomial_decay l k (f * k) :=
(hf.param_mul).congr (λ _, mul_comm _ _)

lemma superpolynomial_decay.param_pow_mul (hf : superpolynomial_decay l k f)
  (n : ℕ) : superpolynomial_decay l k (k ^ n * f) :=
begin
  induction n with n hn,
  { simpa only [one_mul, pow_zero] using hf },
  { simpa only [pow_succ, mul_assoc] using hn.param_mul }
end

lemma superpolynomial_decay.mul_param_pow (hf : superpolynomial_decay l k f)
  (n : ℕ) : superpolynomial_decay l k (f * k ^ n) :=
(hf.param_pow_mul n).congr (λ _, mul_comm _ _)

lemma superpolynomial_decay.polynomial_mul [has_continuous_add β] [has_continuous_mul β]
  (hf : superpolynomial_decay l k f) (p : polynomial β) :
  superpolynomial_decay l k (λ x, (p.eval $ k x) * f x) :=
polynomial.induction_on' p (λ p q hp hq, by simpa [add_mul] using hp.add hq)
  (λ n c, by simpa [mul_assoc] using (hf.param_pow_mul n).const_mul c)

lemma superpolynomial_decay.mul_polynomial [has_continuous_add β] [has_continuous_mul β]
  (hf : superpolynomial_decay l k f) (p : polynomial β) :
  superpolynomial_decay l k (λ x, f x * (p.eval $ k x)) :=
(hf.polynomial_mul p).congr (λ _, mul_comm _ _)

end comm_semiring

section ordered_comm_semiring

variables [topological_space β] [ordered_comm_semiring β] [order_topology β]

lemma superpolynomial_decay.trans_eventually_le (hk : 0 ≤ᶠ[l] k)
  (hg : superpolynomial_decay l k g) (hg' : superpolynomial_decay l k g')
  (hfg : g ≤ᶠ[l] f) (hfg' : f ≤ᶠ[l] g') : superpolynomial_decay l k f :=
λ z, tendsto_of_tendsto_of_tendsto_of_le_of_le' (hg z) (hg' z)
  (hfg.mp (hk.mono $ λ x hx hx', mul_le_mul_of_nonneg_left hx' (pow_nonneg hx z)))
  (hfg'.mp (hk.mono $ λ x hx hx', mul_le_mul_of_nonneg_left hx' (pow_nonneg hx z)))

end ordered_comm_semiring

section linear_ordered_comm_ring

variables [topological_space β] [linear_ordered_comm_ring β] [order_topology β]

variables (l k f)

lemma superpolynomial_decay_iff_abs_tendsto_zero :
  superpolynomial_decay l k f ↔ ∀ (n : ℕ), tendsto (λ (a : α), |(k a) ^ n * f a|) l (𝓝 0) :=
⟨λ h z, (tendsto_zero_iff_abs_tendsto_zero _).1 (h z),
  λ h z, (tendsto_zero_iff_abs_tendsto_zero _).2 (h z)⟩

lemma superpolynomial_decay_iff_superpolynomial_decay_abs :
  superpolynomial_decay l k f ↔ superpolynomial_decay l (λ a, |k a|) (λ a, |f a|) :=
(superpolynomial_decay_iff_abs_tendsto_zero l k f).trans
  (by simp_rw [superpolynomial_decay, abs_mul, abs_pow])

variables {l k f}

lemma superpolynomial_decay.trans_eventually_abs_le (hf : superpolynomial_decay l k f)
  (hfg : abs ∘ g ≤ᶠ[l] abs ∘ f) : superpolynomial_decay l k g :=
begin
  rw superpolynomial_decay_iff_abs_tendsto_zero at hf ⊢,
  refine λ z, tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_const_nhds) (hf z)
    (eventually_of_forall $ λ x, abs_nonneg _) (hfg.mono $ λ x hx, _),
  calc |k x ^ z * g x| = |k x ^ z| * |g x| : abs_mul (k x ^ z) (g x)
    ... ≤ |k x ^ z| * |f x| : mul_le_mul le_rfl hx (abs_nonneg _) (abs_nonneg _)
    ... = |k x ^ z * f x| : (abs_mul (k x ^ z) (f x)).symm,
end

lemma superpolynomial_decay.trans_abs_le (hf : superpolynomial_decay l k f)
  (hfg : ∀ x, |g x| ≤ |f x|) : superpolynomial_decay l k g :=
hf.trans_eventually_abs_le (eventually_of_forall hfg)

end linear_ordered_comm_ring

section field

variables [topological_space β] [field β] (l k f)

lemma superpolynomial_decay_mul_const_iff [has_continuous_mul β] {c : β} (hc0 : c ≠ 0) :
  superpolynomial_decay l k (λ n, f n * c) ↔ superpolynomial_decay l k f :=
⟨λ h, (h.mul_const c⁻¹).congr (λ x, by simp [mul_assoc, mul_inv_cancel hc0]), λ h, h.mul_const c⟩

lemma superpolynomial_decay_const_mul_iff [has_continuous_mul β] {c : β} (hc0 : c ≠ 0) :
  superpolynomial_decay l k (λ n, c * f n) ↔ superpolynomial_decay l k f :=
⟨λ h, (h.const_mul c⁻¹).congr (λ x, by simp [← mul_assoc, inv_mul_cancel hc0]), λ h, h.const_mul c⟩

variables {l k f}

end field

section linear_ordered_field

variables [topological_space β] [linear_ordered_field β] [order_topology β]

variable (f)

lemma superpolynomial_decay_iff_abs_is_bounded_under (hk : tendsto k l at_top) :
  superpolynomial_decay l k f ↔ ∀ (z : ℕ), is_bounded_under (≤) l (λ (a : α), |(k a) ^ z * f a|) :=
begin
  refine ⟨λ h z, tendsto.is_bounded_under_le (tendsto.abs (h z)),
    λ h, (superpolynomial_decay_iff_abs_tendsto_zero l k f).2 (λ z, _)⟩,
  obtain ⟨m, hm⟩ := h (z + 1),
  have h1 : tendsto (λ (a : α), (0 : β)) l (𝓝 0) := tendsto_const_nhds,
  have h2 : tendsto (λ (a : α), |(k a)⁻¹| * m) l (𝓝 0) := (zero_mul m) ▸ tendsto.mul_const m
    ((tendsto_zero_iff_abs_tendsto_zero _).1 hk.inv_tendsto_at_top),
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2
    (eventually_of_forall (λ x, abs_nonneg _)) ((eventually_map.1 hm).mp _),
  refine ((hk.eventually_ne_at_top 0).mono $ λ x hk0 hx, _),
  refine eq.trans_le _ (mul_le_mul_of_nonneg_left hx $ abs_nonneg (k x)⁻¹),
  rw [← abs_mul, ← mul_assoc, pow_succ, ← mul_assoc, inv_mul_cancel hk0, one_mul],
end

lemma superpolynomial_decay_iff_zpow_tendsto_zero (hk : tendsto k l at_top) :
  superpolynomial_decay l k f ↔ ∀ (z : ℤ), tendsto (λ (a : α), (k a) ^ z * f a) l (𝓝 0) :=
begin
  refine ⟨λ h z, _, λ h n, by simpa only [zpow_coe_nat] using h (n : ℤ)⟩,
  by_cases hz : 0 ≤ z,
  { lift z to ℕ using hz,
    simpa using h z },
  { have : tendsto (λ a, (k a) ^ z) l (𝓝 0) :=
      tendsto.comp (tendsto_zpow_at_top_zero (not_le.1 hz)) hk,
    have h : tendsto f l (𝓝 0) := by simpa using h 0,
    exact (zero_mul (0 : β)) ▸ this.mul h },
end

variable {f}

lemma superpolynomial_decay.param_zpow_mul (hk : tendsto k l at_top)
  (hf : superpolynomial_decay l k f) (z : ℤ) : superpolynomial_decay l k (λ a, k a ^ z * f a) :=
begin
  rw superpolynomial_decay_iff_zpow_tendsto_zero _ hk at hf ⊢,
  refine λ z', (hf $ z' + z).congr' ((hk.eventually_ne_at_top 0).mono (λ x hx, _)),
  simp [zpow_add₀ hx, mul_assoc, pi.mul_apply],
end

lemma superpolynomial_decay.mul_param_zpow (hk : tendsto k l at_top)
  (hf : superpolynomial_decay l k f) (z : ℤ) : superpolynomial_decay l k (λ a, f a * k a ^ z) :=
(hf.param_zpow_mul hk z).congr (λ _, mul_comm _ _)

lemma superpolynomial_decay.inv_param_mul (hk : tendsto k l at_top)
  (hf : superpolynomial_decay l k f) : superpolynomial_decay l k (k⁻¹ * f) :=
by simpa using (hf.param_zpow_mul hk (-1))

lemma superpolynomial_decay.param_inv_mul (hk : tendsto k l at_top)
  (hf : superpolynomial_decay l k f) : superpolynomial_decay l k (f * k⁻¹) :=
(hf.inv_param_mul hk).congr (λ _, mul_comm _ _)

variable (f)

lemma superpolynomial_decay_param_mul_iff (hk : tendsto k l at_top) :
  superpolynomial_decay l k (k * f) ↔ superpolynomial_decay l k f :=
⟨λ h, (h.inv_param_mul hk).congr' ((hk.eventually_ne_at_top 0).mono
  (λ x hx, by simp [← mul_assoc, inv_mul_cancel hx])), λ h, h.param_mul⟩

lemma superpolynomial_decay_mul_param_iff (hk : tendsto k l at_top) :
  superpolynomial_decay l k (f * k) ↔ superpolynomial_decay l k f :=
by simpa [mul_comm k] using superpolynomial_decay_param_mul_iff f hk

lemma superpolynomial_decay_param_pow_mul_iff (hk : tendsto k l at_top) (n : ℕ) :
  superpolynomial_decay l k (k ^ n * f) ↔ superpolynomial_decay l k f :=
begin
  induction n with n hn,
  { simp },
  { simpa [pow_succ, ← mul_comm k, mul_assoc,
      superpolynomial_decay_param_mul_iff (k ^ n * f) hk] using hn }
end

lemma superpolynomial_decay_mul_param_pow_iff (hk : tendsto k l at_top) (n : ℕ) :
  superpolynomial_decay l k (f * k ^ n) ↔ superpolynomial_decay l k f :=
by simpa [mul_comm f] using superpolynomial_decay_param_pow_mul_iff f hk n

variable {f}

end linear_ordered_field

section normed_linear_ordered_field

variable [normed_linear_ordered_field β]

variables (l k f)

lemma superpolynomial_decay_iff_norm_tendsto_zero :
  superpolynomial_decay l k f ↔ ∀ (n : ℕ), tendsto (λ (a : α), ∥(k a) ^ n * f a∥) l (𝓝 0) :=
⟨λ h z, tendsto_zero_iff_norm_tendsto_zero.1 (h z),
  λ h z, tendsto_zero_iff_norm_tendsto_zero.2 (h z)⟩

lemma superpolynomial_decay_iff_superpolynomial_decay_norm :
  superpolynomial_decay l k f ↔ superpolynomial_decay l (λ a, ∥k a∥) (λ a, ∥f a∥) :=
(superpolynomial_decay_iff_norm_tendsto_zero l k f).trans (by simp [superpolynomial_decay])

variables {l k}

variable [order_topology β]

lemma superpolynomial_decay_iff_is_O (hk : tendsto k l at_top) :
  superpolynomial_decay l k f ↔ ∀ (z : ℤ), is_O f (λ (a : α), (k a) ^ z) l :=
begin
  refine (superpolynomial_decay_iff_zpow_tendsto_zero f hk).trans _,
  have hk0 : ∀ᶠ x in l, k x ≠ 0 := hk.eventually_ne_at_top 0,
  refine ⟨λ h z, _, λ h z, _⟩,
  { refine is_O_of_div_tendsto_nhds (hk0.mono (λ x hx hxz, absurd (zpow_eq_zero hxz) hx)) 0 _,
    have : (λ (a : α), k a ^ z)⁻¹ = (λ (a : α), k a ^ (- z)) := funext (λ x, by simp),
    rw [div_eq_mul_inv, mul_comm f, this],
    exact h (-z) },
  { suffices : is_O (λ (a : α), k a ^ z * f a) (λ (a : α), (k a)⁻¹) l,
    from is_O.trans_tendsto this hk.inv_tendsto_at_top,
    refine ((is_O_refl (λ a, (k a) ^ z) l).mul (h (- (z + 1)))).trans
      (is_O.of_bound 1 $ hk0.mono (λ a ha0, _)),
    simp only [one_mul, neg_add z 1, zpow_add₀ ha0, ← mul_assoc, zpow_neg,
      mul_inv_cancel (zpow_ne_zero z ha0), zpow_one] }
end

lemma superpolynomial_decay_iff_is_o (hk : tendsto k l at_top) :
  superpolynomial_decay l k f ↔ ∀ (z : ℤ), is_o f (λ (a : α), (k a) ^ z) l :=
begin
  refine ⟨λ h z, _, λ h, (superpolynomial_decay_iff_is_O f hk).2 (λ z, (h z).is_O)⟩,
  have hk0 : ∀ᶠ x in l, k x ≠ 0 := hk.eventually_ne_at_top 0,
  have : is_o (λ (x : α), (1 : β)) k l := is_o_of_tendsto'
    (hk0.mono (λ x hkx hkx', absurd hkx' hkx)) (by simpa using hk.inv_tendsto_at_top),
  have : is_o f (λ (x : α), k x * k x ^ (z - 1)) l,
  by simpa using this.mul_is_O (((superpolynomial_decay_iff_is_O f hk).1 h) $ z - 1),
  refine this.trans_is_O (is_O.of_bound 1 (hk0.mono $ λ x hkx, le_of_eq _)),
  rw [one_mul, zpow_sub_one₀ hkx, mul_comm (k x), mul_assoc, inv_mul_cancel hkx, mul_one],
end

variable {f}

end normed_linear_ordered_field

end asymptotics
