/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.measure.ae_measurable

/-!
# Measure preserving maps

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We say that `f : α → β` is a measure preserving map w.r.t. measures `μ : measure α` and
`ν : measure β` if `f` is measurable and `map f μ = ν`. In this file we define the predicate
`measure_theory.measure_preserving` and prove its basic properties.

We use the term "measure preserving" because in many applications `α = β` and `μ = ν`.

## References

Partially based on
[this](https://www.isa-afp.org/browser_info/current/AFP/Ergodic_Theory/Measure_Preserving_Transformations.html)
Isabelle formalization.

## Tags

measure preserving map, measure
-/

variables {α β γ δ : Type*} [measurable_space α] [measurable_space β] [measurable_space γ]
  [measurable_space δ]

namespace measure_theory

open measure function set

variables {μa : measure α} {μb : measure β} {μc : measure γ} {μd : measure δ}

/-- `f` is a measure preserving map w.r.t. measures `μa` and `μb` if `f` is measurable
and `map f μa = μb`. -/
@[protect_proj]
structure measure_preserving (f : α → β) (μa : measure α . volume_tac)
  (μb : measure β . volume_tac) : Prop :=
(measurable : measurable f)
(map_eq : map f μa = μb)

protected lemma _root_.measurable.measure_preserving {f : α → β}
  (h : measurable f) (μa : measure α) :
  measure_preserving f μa (map f μa) :=
⟨h, rfl⟩

namespace measure_preserving

protected lemma id (μ : measure α) : measure_preserving id μ μ :=
⟨measurable_id, map_id⟩

protected lemma ae_measurable {f : α → β} (hf : measure_preserving f μa μb) :
  ae_measurable f μa :=
hf.1.ae_measurable

lemma symm (e : α ≃ᵐ β) {μa : measure α} {μb : measure β} (h : measure_preserving e μa μb) :
  measure_preserving e.symm μb μa :=
⟨e.symm.measurable,
  by rw [← h.map_eq, map_map e.symm.measurable e.measurable, e.symm_comp_self, map_id]⟩

lemma restrict_preimage {f : α → β} (hf : measure_preserving f μa μb) {s : set β}
  (hs : measurable_set s) : measure_preserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
⟨hf.measurable, by rw [← hf.map_eq, restrict_map hf.measurable hs]⟩

lemma restrict_preimage_emb {f : α → β} (hf : measure_preserving f μa μb)
  (h₂ : measurable_embedding f) (s : set β) :
  measure_preserving f (μa.restrict (f ⁻¹' s)) (μb.restrict s) :=
⟨hf.measurable, by rw [← hf.map_eq, h₂.restrict_map]⟩

lemma restrict_image_emb {f : α → β} (hf : measure_preserving f μa μb) (h₂ : measurable_embedding f)
  (s : set α) : measure_preserving f (μa.restrict s) (μb.restrict (f '' s)) :=
by simpa only [preimage_image_eq _ h₂.injective] using hf.restrict_preimage_emb h₂ (f '' s)

lemma ae_measurable_comp_iff {f : α → β} (hf : measure_preserving f μa μb)
  (h₂ : measurable_embedding f) {g : β → γ} :
  ae_measurable (g ∘ f) μa ↔ ae_measurable g μb :=
by rw [← hf.map_eq, h₂.ae_measurable_map_iff]

protected lemma quasi_measure_preserving {f : α → β} (hf : measure_preserving f μa μb) :
  quasi_measure_preserving f μa μb :=
⟨hf.1, hf.2.absolutely_continuous⟩

protected lemma comp {g : β → γ} {f : α → β} (hg : measure_preserving g μb μc)
  (hf : measure_preserving f μa μb) :
  measure_preserving (g ∘ f) μa μc :=
⟨hg.1.comp hf.1, by rw [← map_map hg.1 hf.1, hf.2, hg.2]⟩

protected lemma comp_left_iff {g : α → β} {e : β ≃ᵐ γ} (h : measure_preserving e μb μc) :
  measure_preserving (e ∘ g) μa μc ↔ measure_preserving g μa μb :=
begin
  refine ⟨λ hg, _, λ hg, h.comp hg⟩,
  convert (measure_preserving.symm e h).comp hg,
  simp [← function.comp.assoc e.symm e g],
end

protected lemma comp_right_iff {g : α → β} {e : γ ≃ᵐ α} (h : measure_preserving e μc μa) :
  measure_preserving (g ∘ e) μc μb ↔ measure_preserving g μa μb :=
begin
  refine ⟨λ hg, _, λ hg, hg.comp h⟩,
  convert hg.comp (measure_preserving.symm e h),
  simp [function.comp.assoc g e e.symm],
end

protected lemma sigma_finite {f : α → β} (hf : measure_preserving f μa μb) [sigma_finite μb] :
  sigma_finite μa :=
sigma_finite.of_map μa hf.ae_measurable (by rwa hf.map_eq)

lemma measure_preimage {f : α → β} (hf : measure_preserving f μa μb)
  {s : set β} (hs : measurable_set s) :
  μa (f ⁻¹' s) = μb s :=
by rw [← hf.map_eq, map_apply hf.1 hs]

lemma measure_preimage_emb {f : α → β} (hf : measure_preserving f μa μb)
  (hfe : measurable_embedding f) (s : set β) :
  μa (f ⁻¹' s) = μb s :=
by rw [← hf.map_eq, hfe.map_apply]

protected lemma iterate {f : α → α} (hf : measure_preserving f μa μa) :
  ∀ n, measure_preserving (f^[n]) μa μa
| 0 := measure_preserving.id μa
| (n + 1) := (iterate n).comp hf

variables {μ : measure α} {f : α → α} {s : set α}

/-- If `μ univ < n * μ s` and `f` is a map preserving measure `μ`,
then for some `x ∈ s` and `0 < m < n`, `f^[m] x ∈ s`. -/
lemma exists_mem_image_mem_of_volume_lt_mul_volume (hf : measure_preserving f μ μ)
  (hs : measurable_set s) {n : ℕ} (hvol : μ (univ : set α) < n * μ s) :
  ∃ (x ∈ s) (m ∈ Ioo 0 n), f^[m] x ∈ s :=
begin
  have A : ∀ m, measurable_set (f^[m] ⁻¹' s) := λ m, (hf.iterate m).measurable hs,
  have B : ∀ m, μ (f^[m] ⁻¹' s) = μ s, from λ m, (hf.iterate m).measure_preimage hs,
  have : μ (univ : set α) < (finset.range n).sum (λ m, μ (f^[m] ⁻¹' s)),
    by simpa only [B, nsmul_eq_mul, finset.sum_const, finset.card_range],
  rcases exists_nonempty_inter_of_measure_univ_lt_sum_measure μ (λ m hm, A m) this
    with ⟨i, hi, j, hj, hij, x, hxi, hxj⟩,
  wlog hlt : i < j generalizing i j,
  { exact this j hj i hi hij.symm hxj hxi (hij.lt_or_lt.resolve_left hlt) },
  simp only [set.mem_preimage, finset.mem_range] at hi hj hxi hxj,
  refine ⟨f^[i] x, hxi, j - i, ⟨tsub_pos_of_lt hlt, lt_of_le_of_lt (j.sub_le i) hj⟩, _⟩,
  rwa [← iterate_add_apply, tsub_add_cancel_of_le hlt.le]
end

/-- A self-map preserving a finite measure is conservative: if `μ s ≠ 0`, then at least one point
`x ∈ s` comes back to `s` under iterations of `f`. Actually, a.e. point of `s` comes back to `s`
infinitely many times, see `measure_theory.measure_preserving.conservative` and theorems about
`measure_theory.conservative`. -/
lemma exists_mem_image_mem [is_finite_measure μ] (hf : measure_preserving f μ μ)
  (hs : measurable_set s) (hs' : μ s ≠ 0) :
  ∃ (x ∈ s) (m ≠ 0), f^[m] x ∈ s :=
begin
  rcases ennreal.exists_nat_mul_gt hs' (measure_ne_top μ (univ : set α)) with ⟨N, hN⟩,
  rcases hf.exists_mem_image_mem_of_volume_lt_mul_volume hs hN with ⟨x, hx, m, hm, hmx⟩,
  exact ⟨x, hx, m, hm.1.ne', hmx⟩
end

end measure_preserving

namespace measurable_equiv

lemma measure_preserving_symm (μ : measure α) (e : α ≃ᵐ β) :
  measure_preserving e.symm (map e μ) μ :=
(e.measurable.measure_preserving μ).symm _

end measurable_equiv
end measure_theory
