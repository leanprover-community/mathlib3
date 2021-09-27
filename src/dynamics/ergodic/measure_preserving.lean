/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.constructions.prod

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
  -- without `tactic.skip` Lean closes the extra goal but it takes a long time; not sure why
  wlog hlt : i < j := hij.lt_or_lt using [i j, j i] tactic.skip,
  { simp only [set.mem_preimage, finset.mem_range] at hi hj hxi hxj,
    refine ⟨f^[i] x, hxi, j - i, ⟨nat.sub_pos_of_lt hlt, lt_of_le_of_lt (j.sub_le i) hj⟩, _⟩,
    rwa [← iterate_add_apply, nat.sub_add_cancel hlt.le] },
  { exact λ hi hj hij hxi hxj, this hj hi hij.symm hxj hxi }
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

end measure_theory
