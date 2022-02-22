/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.instances.irrational
import topology.alexandroff

/-!
# Topology on rational numbers

The structure of a metric space on `ℚ` is introduced in this file, induced from `ℝ`. We then
prove some properties of this topological space and its one-point compactification.

## Main statements

- `rat.totally_disconnected_space`: `ℚ` is a totally disconnected space;

- `rat.not_countably_generated_nhds_infty_alexandroff`: the filter of neighbourhoods of infinity in
  `alexandroff ℚ` is not countably generated.

## Notation

- `ℚ∞` is used as a local notation for `alexandroff ℚ`
-/

open set metric filter topological_space
open_locale topological_space alexandroff
local notation `ℚ∞` := alexandroff ℚ

namespace rat

instance : metric_space ℚ :=
metric_space.induced coe rat.cast_injective real.metric_space

theorem dist_eq (x y : ℚ) : dist x y = |x - y| := rfl

@[norm_cast, simp] lemma dist_cast (x y : ℚ) : dist (x : ℝ) y = dist x y := rfl

theorem uniform_continuous_coe_real : uniform_continuous (coe : ℚ → ℝ) :=
uniform_continuous_comap

theorem uniform_embedding_coe_real : uniform_embedding (coe : ℚ → ℝ) :=
uniform_embedding_comap rat.cast_injective

theorem dense_embedding_coe_real : dense_embedding (coe : ℚ → ℝ) :=
uniform_embedding_coe_real.dense_embedding $
λ x, mem_closure_iff_nhds.2 $ λ t ht,
let ⟨ε,ε0, hε⟩ := metric.mem_nhds_iff.1 ht in
let ⟨q, h⟩ := exists_rat_near x ε0 in
⟨_, hε (mem_ball'.2 h), q, rfl⟩

theorem embedding_coe_real : embedding (coe : ℚ → ℝ) := dense_embedding_coe_real.to_embedding

theorem continuous_coe_real : continuous (coe : ℚ → ℝ) := uniform_continuous_coe_real.continuous

end rat

@[norm_cast, simp] theorem nat.dist_cast_rat (x y : ℕ) : dist (x : ℚ) y = dist x y :=
by rw [← nat.dist_cast_real, ← rat.dist_cast]; congr' 1; norm_cast

lemma nat.uniform_embedding_coe_rat : uniform_embedding (coe : ℕ → ℚ) :=
uniform_embedding_bot_of_pairwise_le_dist zero_lt_one $ by simpa using nat.pairwise_one_le_dist

lemma nat.closed_embedding_coe_rat : closed_embedding (coe : ℕ → ℚ) :=
closed_embedding_of_pairwise_le_dist zero_lt_one $ by simpa using nat.pairwise_one_le_dist


@[norm_cast, simp] theorem int.dist_cast_rat (x y : ℤ) : dist (x : ℚ) y = dist x y :=
by rw [← int.dist_cast_real, ← rat.dist_cast]; congr' 1; norm_cast

lemma int.uniform_embedding_coe_rat : uniform_embedding (coe : ℤ → ℚ) :=
uniform_embedding_bot_of_pairwise_le_dist zero_lt_one $ by simpa using int.pairwise_one_le_dist

lemma int.closed_embedding_coe_rat : closed_embedding (coe : ℤ → ℚ) :=
closed_embedding_of_pairwise_le_dist zero_lt_one $ by simpa using int.pairwise_one_le_dist

instance : noncompact_space ℚ := int.closed_embedding_coe_rat.noncompact_space


-- TODO(Mario): Find a way to use rat_add_continuous_lemma
theorem rat.uniform_continuous_add : uniform_continuous (λp : ℚ × ℚ, p.1 + p.2) :=
rat.uniform_embedding_coe_real.to_uniform_inducing.uniform_continuous_iff.2 $
  by simp only [(∘), rat.cast_add]; exact real.uniform_continuous_add.comp
    (rat.uniform_continuous_coe_real.prod_map rat.uniform_continuous_coe_real)

theorem rat.uniform_continuous_neg : uniform_continuous (@has_neg.neg ℚ _) :=
metric.uniform_continuous_iff.2 $ λ ε ε0, ⟨_, ε0, λ a b h,
  by rw dist_comm at h; simpa [rat.dist_eq] using h⟩

instance : uniform_add_group ℚ :=
uniform_add_group.mk' rat.uniform_continuous_add rat.uniform_continuous_neg

instance : topological_add_group ℚ := by apply_instance

instance : order_topology ℚ :=
induced_order_topology _ (λ x y, rat.cast_lt) (@exists_rat_btwn _ _ _)

lemma rat.uniform_continuous_abs : uniform_continuous (abs : ℚ → ℚ) :=
metric.uniform_continuous_iff.2 $ λ ε ε0,
  ⟨ε, ε0, λ a b h, lt_of_le_of_lt
    (by simpa [rat.dist_eq] using abs_abs_sub_abs_le_abs_sub _ _) h⟩

lemma rat.continuous_mul : continuous (λp : ℚ × ℚ, p.1 * p.2) :=
rat.embedding_coe_real.continuous_iff.2 $ by simp [(∘)]; exact
real.continuous_mul.comp ((rat.continuous_coe_real.prod_map rat.continuous_coe_real))

instance : topological_ring ℚ :=
{ continuous_mul := rat.continuous_mul, ..rat.topological_add_group }

lemma rat.totally_bounded_Icc (a b : ℚ) : totally_bounded (Icc a b) :=
begin
  have := totally_bounded_preimage rat.uniform_embedding_coe_real (totally_bounded_Icc a b),
  rwa (set.ext (λ q, _) : Icc _ _ = _), simp
end

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
  wlog hlt : x < y := H.lt_or_lt using [x y, y x],
  rcases exists_irrational_btwn (rat.cast_lt.2 hlt) with ⟨z, hz, hxz, hzy⟩,
  have := hs.image coe continuous_coe_real.continuous_on,
  rw [is_preconnected_iff_ord_connected] at this,
  have : z ∈ coe '' s := this.out (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) ⟨hxz.le, hzy.le⟩,
  exact hz (image_subset_range _ _ this)
end

end rat
