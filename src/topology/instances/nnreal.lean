/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Nonnegative real numbers.
-/
import topology.algebra.infinite_sum
import topology.algebra.group_with_zero

noncomputable theory
open set topological_space metric
open_locale topological_space

namespace nnreal
open_locale nnreal

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

lemma continuous_of_real : continuous nnreal.of_real :=
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
map_at_top_eq_of_gc nnreal.of_real 0 nnreal.coe_mono
  (λ a b hb, (le_of_real_iff_coe_le hb).symm)
  (λ b hb, le_coe_of_real b)

lemma comap_coe_at_top : comap (coe : ℝ≥0 → ℝ) at_top = at_top :=
by rw [← map_coe_at_top, comap_map nnreal.injective_coe]

@[simp, norm_cast] lemma tendsto_coe_at_top {f : filter α} {m : α → ℝ≥0} :
  tendsto (λ a, (m a : ℝ)) f at_top ↔ tendsto m f at_top :=
by rw [← comap_coe_at_top, tendsto_comap_iff]

lemma tendsto_of_real {f : filter α} {m : α → ℝ} {x : ℝ} (h : tendsto m f (𝓝 x)) :
  tendsto (λa, nnreal.of_real (m a)) f (𝓝 (nnreal.of_real x)) :=
tendsto.comp (continuous_iff_continuous_at.1 continuous_of_real _) h

instance : has_continuous_sub ℝ≥0 :=
⟨continuous_subtype_mk _ $
  ((continuous_coe.comp continuous_fst).sub
   (continuous_coe.comp continuous_snd)).max continuous_const⟩

instance : has_continuous_inv' ℝ≥0 :=
⟨λ x hx, tendsto_coe.1 $ (real.tendsto_inv $ nnreal.coe_ne_zero.2 hx).comp
  continuous_coe.continuous_at⟩

@[norm_cast] lemma has_sum_coe {f : α → ℝ≥0} {r : ℝ≥0} :
  has_sum (λa, (f a : ℝ)) (r : ℝ) ↔ has_sum f r :=
by simp only [has_sum, coe_sum.symm, tendsto_coe]

@[norm_cast] lemma summable_coe {f : α → ℝ≥0} : summable (λa, (f a : ℝ)) ↔ summable f :=
begin
  split,
  exact assume ⟨a, ha⟩, ⟨⟨a, has_sum_le (λa, (f a).2) has_sum_zero ha⟩, has_sum_coe.1 ha⟩,
  exact assume ⟨a, ha⟩, ⟨a.1, has_sum_coe.2 ha⟩
end

open_locale classical big_operators

@[norm_cast] lemma coe_tsum {f : α → ℝ≥0} : ↑(∑'a, f a) = (∑'a, (f a : ℝ)) :=
if hf : summable f
then (eq.symm $ (has_sum_coe.2 $ hf.has_sum).tsum_eq)
else by simp [tsum, hf, mt summable_coe.1 hf]

lemma summable_comp_injective {β : Type*} {f : α → ℝ≥0} (hf : summable f)
  {i : β → α} (hi : function.injective i) :
  summable (f ∘ i) :=
nnreal.summable_coe.1 $
show summable ((coe ∘ f) ∘ i), from (nnreal.summable_coe.2 hf).comp_injective hi

lemma summable_nat_add (f : ℕ → ℝ≥0) (hf : summable f) (k : ℕ) : summable (λ i, f (i + k)) :=
summable_comp_injective hf $ add_left_injective k

lemma sum_add_tsum_nat_add {f : ℕ → ℝ≥0} (k : ℕ) (hf : summable f) :
  (∑' i, f i) = (∑ i in range k, f i) + ∑' i, f (i + k) :=
by rw [←nnreal.coe_eq, coe_tsum, nnreal.coe_add, coe_sum, coe_tsum,
  sum_add_tsum_nat_add k (nnreal.summable_coe.2 hf)]

lemma infi_real_pos_eq_infi_nnreal_pos [complete_lattice α] {f : ℝ → α} :
  (⨅ (n : ℝ) (h : 0 < n), f n) = (⨅ (n : ℝ≥0) (h : 0 < n), f n) :=
le_antisymm
  (infi_le_infi2 $ assume r, ⟨r, infi_le_infi $ assume hr, le_rfl⟩)
  (le_infi $ assume r, le_infi $ assume hr, infi_le_of_le ⟨r, hr.le⟩ $ infi_le _ hr)

end coe

end nnreal
