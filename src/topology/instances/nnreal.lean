/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Nonnegative real numbers.
-/
import topology.algebra.infinite_sum
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

instance : second_countable_topology nnreal :=
topological_space.subtype.second_countable_topology _ _

instance : order_topology ℝ≥0 :=
⟨ le_antisymm
    (le_generate_from $ assume s hs,
    match s, hs with
    | _, ⟨⟨a, ha⟩, or.inl rfl⟩ := ⟨{b : ℝ | a < b}, is_open_lt' a, rfl⟩
    | _, ⟨⟨a, ha⟩, or.inr rfl⟩ := ⟨{b : ℝ | b < a}, is_open_gt' a, set.ext $ assume b, iff.rfl⟩
    end)
    begin
      apply coinduced_le_iff_le_induced.1,
      rw @order_topology.topology_eq_generate_intervals ℝ _,
      apply le_generate_from,
      assume s hs,
      rcases hs with ⟨a, rfl | rfl⟩,
      { show topological_space.generate_open _ {b : ℝ≥0 | a < b },
        by_cases ha : 0 ≤ a,
        { exact topological_space.generate_open.basic _ ⟨⟨a, ha⟩, or.inl rfl⟩ },
        { have : a < 0, from lt_of_not_ge ha,
          have : {b : ℝ≥0 | a < b } = set.univ,
            from (set.eq_univ_iff_forall.2 $ assume b, lt_of_lt_of_le this b.2),
          rw [this],
          exact topological_space.generate_open.univ } },
      { show (topological_space.generate_from _).is_open {b : ℝ≥0 | a > b },
        by_cases ha : 0 ≤ a,
        { exact topological_space.generate_open.basic _ ⟨⟨a, ha⟩, or.inr rfl⟩ },
        { have : {b : ℝ≥0 | a > b } = ∅,
            from (set.eq_empty_iff_forall_not_mem.2 $ assume b hb, ha $
              show 0 ≤ a, from le_trans b.2 (le_of_lt hb)),
          rw [this],
          apply @is_open_empty } },
    end⟩

section coe
variable {α : Type*}
open filter

lemma continuous_of_real : continuous nnreal.of_real :=
continuous_subtype_mk _ $ continuous_id.max continuous_const

lemma continuous_coe : continuous (coe : nnreal → ℝ) :=
continuous_subtype_val

lemma tendsto_coe {f : filter α} {m : α → nnreal} :
  ∀{x : nnreal}, tendsto (λa, (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ tendsto m f (𝓝 x)
| ⟨r, hr⟩ := by rw [nhds_subtype_eq_comap, tendsto_comap_iff]; refl

lemma tendsto_of_real {f : filter α} {m : α → ℝ} {x : ℝ} (h : tendsto m f (𝓝 x)) :
  tendsto (λa, nnreal.of_real (m a)) f (𝓝 (nnreal.of_real x)) :=
tendsto.comp (continuous_iff_continuous_at.1 continuous_of_real _) h

lemma tendsto.sub {f : filter α} {m n : α → nnreal} {r p : nnreal}
  (hm : tendsto m f (𝓝 r)) (hn : tendsto n f (𝓝 p)) :
  tendsto (λa, m a - n a) f (𝓝 (r - p)) :=
tendsto_of_real $ (tendsto_coe.2 hm).sub (tendsto_coe.2 hn)

lemma continuous_sub : continuous (λp:nnreal×nnreal, p.1 - p.2) :=
continuous_subtype_mk _ $
  ((continuous.comp continuous_coe continuous_fst).sub
   (continuous.comp continuous_coe continuous_snd)).max continuous_const

lemma continuous.sub [topological_space α] {f g : α → nnreal}
  (hf : continuous f) (hg : continuous g) : continuous (λ a, f a - g a) :=
continuous_sub.comp (hf.prod_mk hg)

@[norm_cast] lemma has_sum_coe {f : α → nnreal} {r : ℝ≥0} :
  has_sum (λa, (f a : ℝ)) (r : ℝ) ↔ has_sum f r :=
by simp only [has_sum, coe_sum.symm, tendsto_coe]

@[norm_cast] lemma summable_coe {f : α → ℝ≥0} : summable (λa, (f a : ℝ)) ↔ summable f :=
begin
  split,
  exact assume ⟨a, ha⟩, ⟨⟨a, has_sum_le (λa, (f a).2) has_sum_zero ha⟩, has_sum_coe.1 ha⟩,
  exact assume ⟨a, ha⟩, ⟨a.1, has_sum_coe.2 ha⟩
end

open_locale classical

@[norm_cast] lemma coe_tsum {f : α → nnreal} : ↑(∑'a, f a) = (∑'a, (f a : ℝ)) :=
if hf : summable f
then (eq.symm $ (has_sum_coe.2 $ hf.has_sum).tsum_eq)
else by simp [tsum, hf, mt summable_coe.1 hf]

lemma summable_comp_injective {β : Type*} {f : α → nnreal} (hf : summable f)
  {i : β → α} (hi : function.injective i) :
  summable (f ∘ i) :=
nnreal.summable_coe.1 $
show summable ((coe ∘ f) ∘ i), from (nnreal.summable_coe.2 hf).comp_injective hi

end coe

end nnreal
