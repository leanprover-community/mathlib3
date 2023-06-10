/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import measure_theory.integral.lebesgue

/-!
# The Giry monad

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Let X be a measurable space. The collection of all measures on X again
forms a measurable space. This construction forms a monad on
measurable spaces and measurable functions, called the Giry monad.

Note that most sources use the term "Giry monad" for the restriction
to *probability* measures. Here we include all measures on X.

See also `measure_theory/category/Meas.lean`, containing an upgrade of the type-level
monad to an honest monad of the functor `Measure : Meas ⥤ Meas`.

## References

* <https://ncatlab.org/nlab/show/Giry+monad>

## Tags

giry monad
-/

noncomputable theory
open_locale classical big_operators ennreal

open classical set filter

variables {α β : Type*}

namespace measure_theory

namespace measure

variables [measurable_space α] [measurable_space β]

/-- Measurability structure on `measure`: Measures are measurable w.r.t. all projections -/
instance : measurable_space (measure α) :=
⨆ (s : set α) (hs : measurable_set s), (borel ℝ≥0∞).comap (λ μ, μ s)

lemma measurable_coe {s : set α} (hs : measurable_set s) : measurable (λ μ : measure α, μ s) :=
measurable.of_comap_le $ le_supr_of_le s $ le_supr_of_le hs $ le_rfl

lemma measurable_of_measurable_coe (f : β → measure α)
  (h : ∀ (s : set α) (hs : measurable_set s), measurable (λ b, f b s)) :
  measurable f :=
measurable.of_le_map $ supr₂_le $ assume s hs, measurable_space.comap_le_iff_le_map.2 $
  by rw [measurable_space.map_comp]; exact h s hs

instance {α : Type*} {m : measurable_space α} : has_measurable_add₂ (measure α) :=
begin
  refine ⟨measure.measurable_of_measurable_coe _ (λ s hs, _)⟩,
  simp_rw [measure.coe_add, pi.add_apply],
  refine measurable.add _ _,
  { exact (measure.measurable_coe hs).comp measurable_fst, },
  { exact (measure.measurable_coe hs).comp measurable_snd, },
end

lemma measurable_measure {μ : α → measure β} :
  measurable μ ↔ ∀ (s : set β) (hs : measurable_set s), measurable (λ b, μ b s) :=
⟨λ hμ s hs, (measurable_coe hs).comp hμ, measurable_of_measurable_coe μ⟩

lemma measurable_map (f : α → β) (hf : measurable f) :
  measurable (λ μ : measure α, map f μ) :=
begin
  refine measurable_of_measurable_coe _ (λ s hs, _),
  simp_rw map_apply hf hs,
  exact measurable_coe (hf hs),
end

lemma measurable_dirac : measurable (measure.dirac : α → measure α) :=
begin
  refine measurable_of_measurable_coe _ (λ s hs, _),
  simp_rw [dirac_apply' _ hs],
  exact measurable_one.indicator hs
end

lemma measurable_lintegral {f : α → ℝ≥0∞} (hf : measurable f) :
  measurable (λ μ : measure α, ∫⁻ x, f x ∂μ) :=
begin
  simp only [lintegral_eq_supr_eapprox_lintegral, hf, simple_func.lintegral],
  refine measurable_supr (λ n, finset.measurable_sum _ (λ i _, _)),
  refine measurable.const_mul _ _,
  exact measurable_coe ((simple_func.eapprox f n).measurable_set_preimage _)
end

/-- Monadic join on `measure` in the category of measurable spaces and measurable
functions. -/
def join (m : measure (measure α)) : measure α :=
measure.of_measurable
  (λ s hs, ∫⁻ μ, μ s ∂m)
  (by simp only [measure_empty, lintegral_const, zero_mul])
  begin
    assume f hf h,
    simp_rw [measure_Union h hf],
    apply lintegral_tsum,
    assume i, exact (measurable_coe (hf i)).ae_measurable
  end

@[simp] lemma join_apply {m : measure (measure α)} {s : set α} (hs : measurable_set s) :
  join m s = ∫⁻ μ, μ s ∂m :=
measure.of_measurable_apply s hs

@[simp] lemma join_zero : (0 : measure (measure α)).join = 0 :=
by { ext1 s hs, simp only [hs, join_apply, lintegral_zero_measure, coe_zero, pi.zero_apply], }

lemma measurable_join : measurable (join : measure (measure α) → measure α) :=
measurable_of_measurable_coe _ $ assume s hs,
  by simp only [join_apply hs]; exact measurable_lintegral (measurable_coe hs)

lemma lintegral_join {m : measure (measure α)} {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ x, f x ∂(join m) = ∫⁻ μ, ∫⁻ x, f x ∂μ ∂m :=
begin
  simp_rw [lintegral_eq_supr_eapprox_lintegral hf,
    simple_func.lintegral, join_apply (simple_func.measurable_set_preimage _ _)],
  suffices : ∀ (s : ℕ → finset ℝ≥0∞) (f : ℕ → ℝ≥0∞ → measure α → ℝ≥0∞)
    (hf : ∀ n r, measurable (f n r)) (hm : monotone (λ n μ, ∑ r in s n, r * f n r μ)),
    (⨆ n, ∑ r in s n, r * ∫⁻ μ, f n r μ ∂m) = ∫⁻ μ, ⨆ n, ∑ r in s n, r * f n r μ ∂m,
  { refine this (λ n, simple_func.range (simple_func.eapprox f n))
      (λ n r μ, μ (simple_func.eapprox f n ⁻¹' {r})) _ _,
    { exact λ n r, measurable_coe (simple_func.measurable_set_preimage _ _), },
    { exact λ n m h μ, simple_func.lintegral_mono (simple_func.monotone_eapprox _ h) le_rfl, }, },
  intros s f hf hm,
  rw lintegral_supr _ hm,
  swap, { exact λ n, finset.measurable_sum _ (λ r _, (hf _ _).const_mul _) },
  congr,
  funext n,
  rw lintegral_finset_sum (s n),
  { simp_rw lintegral_const_mul _ (hf _ _), },
  { exact λ r _, (hf _ _).const_mul _ },
end

/-- Monadic bind on `measure`, only works in the category of measurable spaces and measurable
functions. When the function `f` is not measurable the result is not well defined. -/
def bind (m : measure α) (f : α → measure β) : measure β := join (map f m)

@[simp] lemma bind_zero_left (f : α → measure β) : bind 0 f = 0 :=
by simp [bind]

@[simp] lemma bind_zero_right (m : measure α) :
  bind m (0 : α → measure β) = 0 :=
begin
  ext1 s hs,
  simp only [bind, hs, join_apply, coe_zero, pi.zero_apply],
  rw [lintegral_map (measurable_coe hs) measurable_zero],
  simp only [pi.zero_apply, coe_zero, lintegral_const, zero_mul],
end

@[simp] lemma bind_zero_right' (m : measure α) :
  bind m (λ _, 0 : α → measure β) = 0 :=
bind_zero_right m

@[simp] lemma bind_apply {m : measure α} {f : α → measure β} {s : set β}
  (hs : measurable_set s) (hf : measurable f) :
  bind m f s = ∫⁻ a, f a s ∂m :=
by rw [bind, join_apply hs, lintegral_map (measurable_coe hs) hf]

lemma measurable_bind' {g : α → measure β} (hg : measurable g) : measurable (λ m, bind m g) :=
measurable_join.comp (measurable_map _ hg)

lemma lintegral_bind {m : measure α} {μ : α → measure β} {f : β → ℝ≥0∞}
  (hμ : measurable μ) (hf : measurable f) :
  ∫⁻ x, f x ∂ (bind m μ) = ∫⁻ a, ∫⁻ x, f x ∂(μ a) ∂m :=
(lintegral_join hf).trans (lintegral_map (measurable_lintegral hf) hμ)

lemma bind_bind {γ} [measurable_space γ] {m : measure α} {f : α → measure β} {g : β → measure γ}
  (hf : measurable f) (hg : measurable g) :
  bind (bind m f) g = bind m (λ a, bind (f a) g) :=
begin
  ext1 s hs,
  simp_rw [bind_apply hs hg, bind_apply hs ((measurable_bind' hg).comp hf),
    lintegral_bind hf ((measurable_coe hs).comp hg), (bind_apply hs hg)],
end

lemma bind_dirac {f : α → measure β} (hf : measurable f) (a : α) : bind (dirac a) f = f a :=
by { ext1 s hs, rw [bind_apply hs hf, lintegral_dirac' a ((measurable_coe hs).comp hf)], }

lemma dirac_bind {m : measure α} : bind m dirac = m :=
begin
  ext1 s hs,
  simp only [bind_apply hs measurable_dirac, dirac_apply' _ hs, lintegral_indicator 1 hs,
    pi.one_apply, lintegral_one, restrict_apply, measurable_set.univ, univ_inter],
end

lemma join_eq_bind (μ : measure (measure α)) : join μ = bind μ id :=
by rw [bind, map_id]

lemma join_map_map {f : α → β} (hf : measurable f) (μ : measure (measure α)) :
  join (map (map f) μ) = map f (join μ) :=
begin
  ext1 s hs,
  rw [join_apply hs, map_apply hf hs, join_apply (hf hs),
    lintegral_map (measurable_coe hs) (measurable_map f hf)],
  simp_rw map_apply hf hs,
end

lemma join_map_join (μ : measure (measure (measure α))) :
  join (map join μ) = join (join μ) :=
begin
  show bind μ join = join (join μ),
  rw [join_eq_bind, join_eq_bind, bind_bind measurable_id measurable_id],
  apply congr_arg (bind μ),
  funext ν,
  exact join_eq_bind ν
end

lemma join_map_dirac (μ : measure α) : join (map dirac μ) = μ :=
dirac_bind

lemma join_dirac (μ : measure α) : join (dirac μ) = μ :=
(join_eq_bind (dirac μ)).trans (bind_dirac measurable_id _)

end measure

end measure_theory
