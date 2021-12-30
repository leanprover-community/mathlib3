import analysis.normed_space.basic
import analysis.normed_space.bounded_linear_maps
import topology.algebra.module
import data.complex.is_R_or_C
.
variables {𝕜 E₁ E₂ : Type*} [nondiscrete_normed_field 𝕜] -- how much needs nondiscrete?
variables [normed_group E₁] [normed_group E₂] [normed_space 𝕜 E₁] [normed_space 𝕜 E₂]

def compact_operator (f : E₁ →ₗ[𝕜] E₂) : Prop :=
∀ s : set E₁, metric.bounded s → is_compact (closure (f '' s))

namespace compact_operator
open_locale topological_space

variable {f : E₁ →ₗ[𝕜] E₂}

lemma of_is_compact_closure_img_ball (h : ∀ r, is_compact (closure (f '' metric.closed_ball 0 r))) :
  compact_operator f :=
begin
  intros s hs,
  cases (metric.bounded_iff_subset_ball (0 : E₁)).mp hs with r hsr,
  exact compact_of_is_closed_subset (h _) is_closed_closure (closure_mono (set.image_subset f hsr))
end

variables (hf : compact_operator f)
include hf

lemma bounded : ∃ C, ∀ x : E₁, ∥f x∥ ≤ C * ∥x∥ :=
begin
  rcases metric.bounded.subset_ball_lt (hf (metric.ball 0 1) metric.bounded_ball).bounded 0 (0 : E₂)
    with ⟨r, hrl, hcl⟩,
  refine linear_map.bound_of_ball_bound zero_lt_one r _ (λ z hz, _),
  refine mem_closed_ball_zero_iff.mp (hcl _),
  refine subset_closure (set.mem_image_of_mem _ (mem_ball_zero_iff.mpr _)),
  exact mem_ball_zero_iff.mp hz
end

lemma continuous : continuous f :=
f.continuous_of_bound _ hf.bounded.some_spec

def to_continuous_linear_map : E₁ →L[𝕜] E₂ :=
{ to_linear_map := f, cont := continuous hf }

lemma subseq_conv {t : ℕ → E₁} (ht : metric.bounded (set.range t)) :
  ∃ (b : E₂) (hb : b ∈ closure (f '' set.range t)) (φ : ℕ → ℕ),
    strict_mono φ ∧ filter.tendsto ((f ∘ t) ∘ φ) filter.at_top (𝓝 b) :=
(hf (set.range t) ht).is_seq_compact $ λ n, subset_closure $
  by simp only [set.mem_range, set.mem_image, exists_exists_eq_and, exists_apply_eq_apply]



end compact_operator
