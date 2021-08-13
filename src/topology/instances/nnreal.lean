/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import topology.algebra.infinite_sum
import topology.algebra.group_with_zero

/-!
# Topology on `ℝ≥0`

The natural topology on `ℝ≥0` (the one induced from `ℝ`), and a basic API.

## Main definitions

Instances for the following typeclasses are defined:

* `topological_space ℝ≥0`
* `topological_semiring ℝ≥0`
* `second_countable_topology ℝ≥0`
* `order_topology ℝ≥0`
* `has_continuous_sub ℝ≥0`
* `has_continuous_inv' ℝ≥0` (continuity of `x⁻¹` away from `0`)
* `has_continuous_smul ℝ≥0 ℝ`

Everything is inherited from the corresponding structures on the reals.

## Main statements

Various mathematically trivial lemmas are proved about the compatibility
of limits and sums in `ℝ≥0` and `ℝ`. For example

* `tendsto_coe {f : filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
  tendsto (λa, (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ tendsto m f (𝓝 x)`

says that the limit of a filter along a map to `ℝ≥0` is the same in `ℝ` and `ℝ≥0`, and

* `coe_tsum {f : α → ℝ≥0} : ((∑'a, f a) : ℝ) = (∑'a, (f a : ℝ))`

says that says that a sum of elements in `ℝ≥0` is the same in `ℝ` and `ℝ≥0`.

Similarly, some mathematically trivial lemmas about infinite sums are proved,
a few of which rely on the fact that subtraction is continuous.

-/
noncomputable theory
open set topological_space metric filter
open_locale topological_space

namespace nnreal
open_locale nnreal big_operators filter

instance : topological_space ℝ≥0 := infer_instance -- short-circuit type class inference

instance : topological_semiring ℝ≥0 :=
{ continuous_mul := continuous_subtype_mk _ $
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd),
  continuous_add := continuous_subtype_mk _ $
    (continuous_subtype_val.comp continuous_fst).add (continuous_subtype_val.comp continuous_snd) }

instance : second_countable_topology ℝ≥0 :=
topological_space.subtype.second_countable_topology _ _

instance : order_topology ℝ≥0 := @order_topology_of_ord_connected _ _ _ _ (Ici 0) _

section coe
variable {α : Type*}
open filter finset

lemma continuous_of_real : continuous real.to_nnreal :=
continuous_subtype_mk _ $ continuous_id.max continuous_const

lemma continuous_coe : continuous (coe : ℝ≥0 → ℝ) :=
continuous_subtype_val

@[simp, norm_cast] lemma tendsto_coe {f : filter α} {m : α → ℝ≥0} {x : ℝ≥0} :
  tendsto (λa, (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ tendsto m f (𝓝 x) :=
tendsto_subtype_rng.symm

lemma tendsto_coe' {f : filter α} [ne_bot f] {m : α → ℝ≥0} {x : ℝ} :
  tendsto (λ a, m a : α → ℝ) f (𝓝 x) ↔ ∃ hx : 0 ≤ x, tendsto m f (𝓝 ⟨x, hx⟩) :=
⟨λ h, ⟨ge_of_tendsto' h (λ c, (m c).2), tendsto_coe.1 h⟩, λ ⟨hx, hm⟩, tendsto_coe.2 hm⟩

@[simp] lemma map_coe_at_top : map (coe : ℝ≥0 → ℝ) at_top = at_top :=
map_coe_Ici_at_top 0

lemma comap_coe_at_top : comap (coe : ℝ≥0 → ℝ) at_top = at_top :=
(at_top_Ici_eq 0).symm

@[simp, norm_cast] lemma tendsto_coe_at_top {f : filter α} {m : α → ℝ≥0} :
  tendsto (λ a, (m a : ℝ)) f at_top ↔ tendsto m f at_top :=
tendsto_Ici_at_top.symm

lemma tendsto_of_real {f : filter α} {m : α → ℝ} {x : ℝ} (h : tendsto m f (𝓝 x)) :
  tendsto (λa, real.to_nnreal (m a)) f (𝓝 (real.to_nnreal x)) :=
(continuous_of_real.tendsto _).comp h

lemma nhds_zero : 𝓝 (0 : ℝ≥0) = ⨅a ≠ 0, 𝓟 (Iio a) :=
nhds_bot_order.trans $ by simp [bot_lt_iff_ne_bot, Iio]

lemma nhds_zero_basis : (𝓝 (0 : ℝ≥0)).has_basis (λ a : ℝ≥0, 0 < a) (λ a, Iio a) :=
nhds_bot_basis

instance : has_continuous_sub ℝ≥0 :=
⟨continuous_subtype_mk _ $
  ((continuous_coe.comp continuous_fst).sub
   (continuous_coe.comp continuous_snd)).max continuous_const⟩

instance : has_continuous_inv' ℝ≥0 :=
⟨λ x hx, tendsto_coe.1 $ (real.tendsto_inv $ nnreal.coe_ne_zero.2 hx).comp
  continuous_coe.continuous_at⟩

instance : has_continuous_smul ℝ≥0 ℝ :=
{ continuous_smul := continuous.comp real.continuous_mul $ continuous.prod_mk
    (continuous.comp continuous_subtype_val continuous_fst) continuous_snd }

@[norm_cast] lemma has_sum_coe {f : α → ℝ≥0} {r : ℝ≥0} :
  has_sum (λa, (f a : ℝ)) (r : ℝ) ↔ has_sum f r :=
by simp only [has_sum, coe_sum.symm, tendsto_coe]

lemma has_sum_of_real_of_nonneg {f : α → ℝ} (hf_nonneg : ∀ n, 0 ≤ f n) (hf : summable f) :
  has_sum (λ n, real.to_nnreal (f n)) (real.to_nnreal (∑' n, f n)) :=
begin
  have h_sum : (λ s, ∑ b in s, real.to_nnreal (f b)) = λ s, real.to_nnreal (∑ b in s, f b),
    from funext (λ _, (real.to_nnreal_sum_of_nonneg (λ n _, hf_nonneg n)).symm),
  simp_rw [has_sum, h_sum],
  exact tendsto_of_real hf.has_sum,
end

@[norm_cast] lemma summable_coe {f : α → ℝ≥0} : summable (λa, (f a : ℝ)) ↔ summable f :=
begin
  split,
  exact assume ⟨a, ha⟩, ⟨⟨a, has_sum_le (λa, (f a).2) has_sum_zero ha⟩, has_sum_coe.1 ha⟩,
  exact assume ⟨a, ha⟩, ⟨a.1, has_sum_coe.2 ha⟩
end

lemma summable_coe_of_nonneg {f : α → ℝ} (hf₁ : ∀ n, 0 ≤ f n) :
  @summable (ℝ≥0) _ _ _ (λ n, ⟨f n, hf₁ n⟩) ↔ summable f :=
begin
  lift f to α → ℝ≥0 using hf₁ with f rfl hf₁,
  simp only [summable_coe, subtype.coe_eta]
end

open_locale classical

@[norm_cast] lemma coe_tsum {f : α → ℝ≥0} : ↑∑'a, f a = ∑'a, (f a : ℝ) :=
if hf : summable f
then (eq.symm $ (has_sum_coe.2 $ hf.has_sum).tsum_eq)
else by simp [tsum, hf, mt summable_coe.1 hf]

lemma coe_tsum_of_nonneg {f : α → ℝ} (hf₁ : ∀ n, 0 ≤ f n) :
  (⟨∑' n, f n, tsum_nonneg hf₁⟩ : ℝ≥0) = (∑' n, ⟨f n, hf₁ n⟩ : ℝ≥0) :=
begin
  lift f to α → ℝ≥0 using hf₁ with f rfl hf₁,
  simp_rw [← nnreal.coe_tsum, subtype.coe_eta]
end

lemma tsum_mul_left (a : ℝ≥0) (f : α → ℝ≥0) : ∑' x, a * f x = a * ∑' x, f x :=
nnreal.eq $ by simp only [coe_tsum, nnreal.coe_mul, tsum_mul_left]

lemma tsum_mul_right (f : α → ℝ≥0) (a : ℝ≥0) : (∑' x, f x * a) = (∑' x, f x) * a :=
nnreal.eq $ by simp only [coe_tsum, nnreal.coe_mul, tsum_mul_right]

lemma summable_comp_injective {β : Type*} {f : α → ℝ≥0} (hf : summable f)
  {i : β → α} (hi : function.injective i) :
  summable (f ∘ i) :=
nnreal.summable_coe.1 $
show summable ((coe ∘ f) ∘ i), from (nnreal.summable_coe.2 hf).comp_injective hi

lemma summable_nat_add (f : ℕ → ℝ≥0) (hf : summable f) (k : ℕ) : summable (λ i, f (i + k)) :=
summable_comp_injective hf $ add_left_injective k

lemma summable_nat_add_iff {f : ℕ → ℝ≥0} (k : ℕ) : summable (λ i, f (i + k)) ↔ summable f :=
begin
  rw [← summable_coe, ← summable_coe],
  exact @summable_nat_add_iff ℝ _ _ _ (λ i, (f i : ℝ)) k,
end

lemma has_sum_nat_add_iff {f : ℕ → ℝ≥0} (k : ℕ) {a : ℝ≥0} :
  has_sum (λ n, f (n + k)) a ↔ has_sum f (a + ∑ i in range k, f i) :=
by simp [← has_sum_coe, coe_sum, nnreal.coe_add, ← has_sum_nat_add_iff k]

lemma sum_add_tsum_nat_add {f : ℕ → ℝ≥0} (k : ℕ) (hf : summable f) :
  ∑' i, f i = (∑ i in range k, f i) + ∑' i, f (i + k) :=
by rw [←nnreal.coe_eq, coe_tsum, nnreal.coe_add, coe_sum, coe_tsum,
  sum_add_tsum_nat_add k (nnreal.summable_coe.2 hf)]

lemma infi_real_pos_eq_infi_nnreal_pos [complete_lattice α] {f : ℝ → α} :
  (⨅ (n : ℝ) (h : 0 < n), f n) = (⨅ (n : ℝ≥0) (h : 0 < n), f n) :=
le_antisymm
  (infi_le_infi2 $ assume r, ⟨r, infi_le_infi $ assume hr, le_rfl⟩)
  (le_infi $ assume r, le_infi $ assume hr, infi_le_of_le ⟨r, hr.le⟩ $ infi_le _ hr)

end coe

lemma tendsto_cofinite_zero_of_summable {α} {f : α → ℝ≥0} (hf : summable f) :
  tendsto f cofinite (𝓝 0) :=
begin
  have h_f_coe : f = λ n, real.to_nnreal (f n : ℝ), from funext (λ n, real.to_nnreal_coe.symm),
  rw [h_f_coe, ← @real.to_nnreal_coe 0],
  exact tendsto_of_real ((summable_coe.mpr hf).tendsto_cofinite_zero),
end

lemma tendsto_at_top_zero_of_summable {f : ℕ → ℝ≥0} (hf : summable f) :
  tendsto f at_top (𝓝 0) :=
by { rw ←nat.cofinite_eq_at_top, exact tendsto_cofinite_zero_of_summable hf }

end nnreal
