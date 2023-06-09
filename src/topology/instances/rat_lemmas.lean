/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.instances.irrational
import topology.instances.rat
import topology.alexandroff

/-!
# Additional lemmas about the topology on rational numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The structure of a metric space on `ℚ` (`rat.metric_space`) is introduced elsewhere, induced from
`ℝ`. In this file we prove some properties of this topological space and its one-point
compactification.

## Main statements

- `rat.totally_disconnected_space`: `ℚ` is a totally disconnected space;

- `rat.not_countably_generated_nhds_infty_alexandroff`: the filter of neighbourhoods of infinity in
  `alexandroff ℚ` is not countably generated.

## Notation

- `ℚ∞` is used as a local notation for `alexandroff ℚ`
-/

open set metric filter topological_space
open_locale topology alexandroff
local notation `ℚ∞` := alexandroff ℚ

namespace rat

variables {p q : ℚ} {s t : set ℚ}

lemma interior_compact_eq_empty (hs : is_compact s) :
  interior s = ∅ :=
dense_embedding_coe_real.to_dense_inducing.interior_compact_eq_empty dense_irrational hs

lemma dense_compl_compact (hs : is_compact s) : dense sᶜ :=
interior_eq_empty_iff_dense_compl.1 (interior_compact_eq_empty hs)

instance cocompact_inf_nhds_ne_bot : ne_bot (cocompact ℚ ⊓ 𝓝 p) :=
begin
  refine (has_basis_cocompact.inf (nhds_basis_opens _)).ne_bot_iff.2 _,
  rintro ⟨s, o⟩ ⟨hs, hpo, ho⟩, rw inter_comm,
  exact (dense_compl_compact hs).inter_open_nonempty _ ho ⟨p, hpo⟩
end

lemma not_countably_generated_cocompact : ¬is_countably_generated (cocompact ℚ) :=
begin
  introI H,
  rcases exists_seq_tendsto (cocompact ℚ ⊓ 𝓝 0) with ⟨x, hx⟩,
  rw tendsto_inf at hx, rcases hx with ⟨hxc, hx0⟩,
  obtain ⟨n, hn⟩ : ∃ n : ℕ, x n ∉ insert (0 : ℚ) (range x),
    from (hxc.eventually hx0.is_compact_insert_range.compl_mem_cocompact).exists,
  exact hn (or.inr ⟨n, rfl⟩)
end

lemma not_countably_generated_nhds_infty_alexandroff :
  ¬is_countably_generated (𝓝 (∞ : ℚ∞)) :=
begin
  introI,
  have : is_countably_generated (comap (coe : ℚ → ℚ∞) (𝓝 ∞)), by apply_instance,
  rw [alexandroff.comap_coe_nhds_infty, coclosed_compact_eq_cocompact] at this,
  exact not_countably_generated_cocompact this
end

lemma not_first_countable_topology_alexandroff :
  ¬first_countable_topology ℚ∞ :=
by { introI, exact not_countably_generated_nhds_infty_alexandroff infer_instance }

lemma not_second_countable_topology_alexandroff :
  ¬second_countable_topology ℚ∞ :=
by { introI, exact not_first_countable_topology_alexandroff infer_instance }

instance : totally_disconnected_space ℚ :=
begin
  refine ⟨λ s hsu hs x hx y hy, _⟩, clear hsu,
  by_contra' H : x ≠ y,
  wlog hlt : x < y,
  { exact this s hs y hy x hx H.symm (H.lt_or_lt.resolve_left hlt) },
  rcases exists_irrational_btwn (rat.cast_lt.2 hlt) with ⟨z, hz, hxz, hzy⟩,
  have := hs.image coe continuous_coe_real.continuous_on,
  rw [is_preconnected_iff_ord_connected] at this,
  have : z ∈ coe '' s := this.out (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) ⟨hxz.le, hzy.le⟩,
  exact hz (image_subset_range _ _ this)
end

end rat
