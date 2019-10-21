/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Nonnegative real numbers.
-/
import data.real.nnreal topology.instances.real topology.algebra.infinite_sum
noncomputable theory
open set topological_space metric
open_locale topological_space

namespace nnreal
open_locale nnreal

instance : topological_space ℝ≥0 := infer_instance

instance : topological_semiring ℝ≥0 :=
{ continuous_mul :=
   continuous_subtype_mk _
        (continuous_mul (continuous.comp continuous_subtype_val continuous_fst)
                        (continuous.comp continuous_subtype_val continuous_snd)),
  continuous_add :=
    continuous_subtype_mk _
          (continuous_add (continuous.comp continuous_subtype_val continuous_fst)
                          (continuous.comp continuous_subtype_val continuous_snd)) }

instance : second_countable_topology nnreal :=
topological_space.subtype.second_countable_topology _ _

instance : orderable_topology ℝ≥0 :=
⟨ le_antisymm
    (le_generate_from $ assume s hs,
    match s, hs with
    | _, ⟨⟨a, ha⟩, or.inl rfl⟩ := ⟨{b : ℝ | a < b}, is_open_lt' a, rfl⟩
    | _, ⟨⟨a, ha⟩, or.inr rfl⟩ := ⟨{b : ℝ | b < a}, is_open_gt' a, set.ext $ assume b, iff.refl _⟩
    end)
    begin
      apply coinduced_le_iff_le_induced.1,
      rw [orderable_topology.topology_eq_generate_intervals ℝ],
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
          exact topological_space.generate_open.univ _ } },
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
continuous_subtype_mk _ $ continuous_max continuous_id continuous_const

lemma continuous_coe : continuous (coe : nnreal → ℝ) :=
continuous_subtype_val

lemma tendsto_coe {f : filter α} {m : α → nnreal} :
  ∀{x : nnreal}, tendsto (λa, (m a : ℝ)) f (𝓝 (x : ℝ)) ↔ tendsto m f (𝓝 x)
| ⟨r, hr⟩ := by rw [nhds_subtype_eq_comap, tendsto_comap_iff]; refl

lemma tendsto_of_real {f : filter α} {m : α → ℝ} {x : ℝ} (h : tendsto m f (𝓝 x)) :
  tendsto (λa, nnreal.of_real (m a)) f (𝓝 (nnreal.of_real x)) :=
tendsto.comp (continuous_iff_continuous_at.1 continuous_of_real _) h

lemma tendsto_sub {f : filter α} {m n : α → nnreal} {r p : nnreal}
  (hm : tendsto m f (𝓝 r)) (hn : tendsto n f (𝓝 p)) :
  tendsto (λa, m a - n a) f (𝓝 (r - p)) :=
tendsto_of_real $ tendsto_sub (tendsto_coe.2 hm) (tendsto_coe.2 hn)

lemma continuous_sub' : continuous (λp:nnreal×nnreal, p.1 - p.2) :=
  continuous_subtype_mk _ (continuous_max
    (continuous_sub (continuous.comp continuous_coe continuous_fst)
                    (continuous.comp continuous_coe continuous_snd))
                                                      continuous_const)

lemma continuous_sub [topological_space α] {f g : α → nnreal}
  (hf : continuous f) (hg : continuous g) : continuous (λ a, f a - g a) :=
continuous_sub'.comp (hf.prod_mk hg)

lemma has_sum_coe {f : α → nnreal} {r : nnreal} : has_sum (λa, (f a : ℝ)) (r : ℝ) ↔ has_sum f r :=
by simp [has_sum, sum_coe.symm, tendsto_coe]

lemma summable_coe {f : α → nnreal} : summable (λa, (f a : ℝ)) ↔ summable f :=
begin
  simp [summable],
  split,
  exact assume ⟨a, ha⟩, ⟨⟨a, has_sum_le (λa, (f a).2) has_sum_zero ha⟩, has_sum_coe.1 ha⟩,
  exact assume ⟨a, ha⟩, ⟨a.1, has_sum_coe.2 ha⟩
end

lemma tsum_coe {f : α → nnreal} (hf : summable f) : (∑a, (f a : ℝ)) = ↑(∑a, f a) :=
tsum_eq_has_sum $ has_sum_coe.2 $ has_sum_tsum $ hf

end coe

end nnreal
