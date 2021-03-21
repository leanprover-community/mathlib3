/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.prod

/-!
# Measure preserving maps

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

namespace measure_preserving

protected lemma id (μ : measure α) : measure_preserving id μ μ :=
⟨measurable_id, map_id⟩

protected lemma quasi_measure_preserving {f : α → β} (hf : measure_preserving f μa μb) :
  quasi_measure_preserving f μa μb :=
⟨hf.1, hf.2.absolutely_continuous⟩

lemma comp {g : β → γ} {f : α → β} (hg : measure_preserving g μb μc)
  (hf : measure_preserving f μa μb) :
  measure_preserving (g ∘ f) μa μc :=
⟨hg.1.comp hf.1, by rw [← map_map hg.1 hf.1, hf.2, hg.2]⟩

protected lemma sigma_finite {f : α → β} (hf : measure_preserving f μa μb) [sigma_finite μb] :
  sigma_finite μa :=
sigma_finite.of_map μa hf.1 (by rwa hf.map_eq)

lemma measure_preimage {f : α → β} (hf : measure_preserving f μa μb)
  {s : set β} (hs : measurable_set s) :
  μa (f ⁻¹' s) = μb s :=
by rw [← hf.map_eq, map_apply hf.1 hs]

protected lemma iterate {f : α → α} (hf : measure_preserving f μa μa) :
  ∀ n, measure_preserving (f^[n]) μa μa
| 0 := measure_preserving.id μa
| (n + 1) := (iterate n).comp hf

lemma skew_product [sigma_finite μb] [sigma_finite μd]
  {f : α → β} (hf : measure_preserving f μa μb) {g : α → γ → δ}
  (hgm : measurable (uncurry g)) (hg : ∀ᵐ x ∂μa, map (g x) μc = μd) :
  measure_preserving (λ p : α × γ, (f p.1, g p.1 p.2)) (μa.prod μc) (μb.prod μd) :=
begin
  classical,
  have : measurable (λ p : α × γ, (f p.1, g p.1 p.2)) := (hf.1.comp measurable_fst).prod_mk hgm,
  /- if `μa = 0`, then the lemma is trivial, otherwise we can use `hg`
  to deduce `sigma_finite μc`. -/
  by_cases ha : μa = 0,
  { rw [← hf.map_eq, ha, zero_prod, (map f).map_zero, zero_prod],
    exact ⟨this, (map _).map_zero⟩ },
  haveI : μa.ae.ne_bot := ae_ne_bot.2 ha,
  rcases hg.exists with ⟨x, hx⟩,
  haveI : sigma_finite μc := sigma_finite.of_map _ hgm.of_uncurry_left (by rwa hx),
  clear hx x,
  refine ⟨this, (prod_eq $ λ s t hs ht, _).symm⟩,
  rw [map_apply this (hs.prod ht)],
  refine (prod_apply (this $ hs.prod ht)).trans _,
  have : ∀ᵐ x ∂μa, μc ((λ y, (f x, g x y)) ⁻¹' s.prod t) = indicator (f ⁻¹' s) (λ y, μd t) x,
  { refine hg.mono (λ x hx, _),
    simp only [mk_preimage_prod_right_fn_eq_if, indicator_apply, mem_preimage],
    split_ifs,
    { rw [← map_apply hgm.of_uncurry_left ht, hx] },
    { exact measure_empty } },
  simp only [preimage_preimage],
  rw [lintegral_congr_ae this, lintegral_indicator _ (hf.1 hs),
    set_lintegral_const, hf.measure_preimage hs, mul_comm]
end

/-- If `f : α → β` sends the measure `μa` to `μb` and `g : γ → δ` sends the measure `μc` to `μd`,
then `prod.map f g` sends `μa.prod μc` to `μb.prod μd`. -/
lemma prod [sigma_finite μb] [sigma_finite μd] {f : α → β} {g : γ → δ}
  (hf : measure_preserving f μa μb) (hg : measure_preserving g μc μd) :
  measure_preserving (prod.map f g) (μa.prod μc) (μb.prod μd) :=
have measurable (uncurry $ λ _ : α, g), from (hg.1.comp measurable_snd),
hf.skew_product this $ filter.eventually_of_forall $ λ _, hg.map_eq

end measure_preserving

end measure_theory
