import analysis.normed_space.basic
import topology.metric_space.hausdorff_distance

variables {k : Type*} [normed_field k]
variables {α : Type*} [normed_group α] [normed_space k α]

/-- Riesz's Lemma. Stated in terms of multiples of norms since in
    general the existence of an element of norm exactly 1 is not
    guaranteed. -/
lemma riesz_lemma {β : subspace k α} (hβc : is_closed β.carrier)
(hβ : ∃ a : α, a ∉ β)
{r : ℝ} (hr : r < 1) : ∃ x : α, ∀ y : β, r * ∥x∥ ≤ ∥x - y∥ :=
or.cases_on (le_or_lt r 0)
(λ hle, ⟨0, λ b, by {rw [norm_zero, mul_zero], exact norm_nonneg _}⟩)
(λ hlt,
let ⟨a, ha⟩ := hβ in
let d := metric.inf_dist a β in
have hβn : β.carrier ≠ ∅, from set.ne_empty_of_mem (submodule.zero β),
have hdp : 0 < d,
  from lt_of_le_of_ne metric.inf_dist_nonneg $ λ heq, ha
  ((metric.mem_iff_inf_dist_zero_of_closed hβc hβn).2 heq.symm),
have hdlt : d < d / r, from lt_div_of_mul_lt hlt ((mul_lt_iff_lt_one_right hdp).2 hr),
let ⟨b₀, hb₀β, hab₀⟩ := metric.exists_dist_lt_of_inf_dist_lt hdlt hβn in
⟨a - b₀, λ b,
have hb₀b : (b₀ + b) ∈ β.carrier, from β.add hb₀β b.property,
le_of_lt $ calc
∥a - b₀ - b∥ = dist a (b₀ + b) : by { rw [sub_sub, dist_eq_norm] }
...          ≥ d : metric.inf_dist_le_dist_of_mem hb₀b
...          > _ : by { rw ←dist_eq_norm, exact (lt_div_iff' hlt).1 hab₀ }⟩)

