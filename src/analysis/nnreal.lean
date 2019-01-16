/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Nonnegative real numbers.
-/
import data.real.nnreal analysis.real analysis.topology.infinite_sum
noncomputable theory
open set topological_space metric

namespace nnreal
local notation ` ℝ≥0 ` := nnreal

instance : metric_space ℝ≥0 := by unfold nnreal; apply_instance
instance : topological_space ℝ≥0 := infer_instance

instance : topological_semiring ℝ≥0 :=
{ continuous_mul :=
   continuous_subtype_mk _
        (continuous_mul (continuous.comp continuous_fst continuous_subtype_val)
                        (continuous.comp continuous_snd continuous_subtype_val)),
  continuous_add :=
    continuous_subtype_mk _
          (continuous_add (continuous.comp continuous_fst continuous_subtype_val)
                          (continuous.comp continuous_snd continuous_subtype_val)) }

instance : orderable_topology ℝ≥0 :=
⟨ le_antisymm
    begin
      apply induced_le_iff_le_coinduced.2,
      rw [orderable_topology.topology_eq_generate_intervals ℝ],
      apply generate_from_le,
      assume s hs,
      rcases hs with ⟨a, rfl | rfl⟩,
      { show topological_space.generate_open _ {b : ℝ≥0 | a < b },
        by_cases ha : 0 ≤ a,
        { exact topological_space.generate_open.basic _ ⟨⟨a, ha⟩, or.inl rfl⟩ },
        { have : a < 0, from lt_of_not_ge ha,
          have : {b : ℝ≥0 | a < b } = set.univ,
            from (set.eq_univ_iff_forall.2 $ assume b, lt_of_lt_of_le this b.2),
          rw [this],
          exact topological_space.generate_open.univ _ } },
      { show (topological_space.generate_from _).is_open {b : ℝ≥0 | a > b },
        by_cases ha : 0 ≤ a,
        { exact topological_space.generate_open.basic _ ⟨⟨a, ha⟩, or.inr rfl⟩ },
        { have : {b : ℝ≥0 | a > b } = ∅,
            from (set.eq_empty_iff_forall_not_mem.2 $ assume b hb, ha $
              show 0 ≤ a, from le_trans b.2 (le_of_lt hb)),
          rw [this],
          apply @is_open_empty } },
    end
    (generate_from_le $ assume s hs,
    match s, hs with
    | _, ⟨⟨a, ha⟩, or.inl rfl⟩ := ⟨{b : ℝ | a < b}, is_open_lt' a, rfl⟩
    | _, ⟨⟨a, ha⟩, or.inr rfl⟩ := ⟨{b : ℝ | b < a}, is_open_gt' a, set.ext $ assume b, iff.refl _⟩
    end) ⟩

section coe
variable {α : Type*}
open filter

lemma continuous_of_real : continuous nnreal.of_real :=
continuous_subtype_mk _ $ continuous_max continuous_id continuous_const

lemma continuous_coe : continuous (coe : nnreal → ℝ) :=
continuous_subtype_val

lemma tendsto_coe {f : filter α} {m : α → nnreal} :
  ∀{x : nnreal}, tendsto (λa, (m a : ℝ)) f (nhds (x : ℝ)) ↔ tendsto m f (nhds x)
| ⟨r, hr⟩ := by rw [nhds_subtype_eq_comap, tendsto_comap_iff]; refl

lemma tendsto_of_real {f : filter α} {m : α → ℝ} {x : ℝ} (h : tendsto m f (nhds x)):
  tendsto (λa, nnreal.of_real (m a)) f (nhds (nnreal.of_real x)) :=
h.comp (continuous_iff_tendsto.1 continuous_of_real _)

lemma tendsto_sub {f : filter α} {m n : α → nnreal} {r p : nnreal}
  (hm : tendsto m f (nhds r)) (hn : tendsto n f (nhds p)) :
  tendsto (λa, m a - n a) f (nhds (r - p)) :=
tendsto_of_real $ tendsto_sub (tendsto_coe.2 hm) (tendsto_coe.2 hn)

lemma is_sum_coe {f : α → nnreal} {r : nnreal} : is_sum (λa, (f a : ℝ)) (r : ℝ) ↔ is_sum f r :=
by simp [is_sum, sum_coe.symm, tendsto_coe]

lemma has_sum_coe {f : α → nnreal} : has_sum (λa, (f a : ℝ)) ↔ has_sum f :=
begin
  simp [has_sum],
  split,
  exact assume ⟨a, ha⟩, ⟨⟨a, is_sum_le (λa, (f a).2) is_sum_zero ha⟩, is_sum_coe.1 ha⟩,
  exact assume ⟨a, ha⟩, ⟨a.1, is_sum_coe.2 ha⟩
end

lemma tsum_coe {f : α → nnreal} (hf : has_sum f) : (∑a, (f a : ℝ)) = ↑(∑a, f a) :=
tsum_eq_is_sum $ is_sum_coe.2 $ is_sum_tsum $ hf

end coe

end nnreal