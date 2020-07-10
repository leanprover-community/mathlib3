/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import measure_theory.integration

/-!
# The Giry monad

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
open_locale classical big_operators

open classical set filter

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {ε : Type*}

namespace measure_theory

namespace measure

variables [measurable_space α] [measurable_space β]

/-- Measurability structure on `measure`: Measures are measurable w.r.t. all projections -/
instance : measurable_space (measure α) :=
⨆ (s : set α) (hs : is_measurable s), (borel ennreal).comap (λμ, μ s)

lemma measurable_coe {s : set α} (hs : is_measurable s) : measurable (λμ : measure α, μ s) :=
measurable_space.comap_le_iff_le_map.1 $ le_supr_of_le s $ le_supr_of_le hs $ le_refl _

lemma measurable_of_measurable_coe (f : β → measure α)
  (h : ∀(s : set α) (hs : is_measurable s), measurable (λb, f b s)) :
  measurable f :=
supr_le $ assume s, supr_le $ assume hs, measurable_space.comap_le_iff_le_map.2 $
  by rw [measurable_space.map_comp]; exact h s hs

lemma measurable_map (f : α → β) (hf : measurable f) :
  measurable (λμ : measure α, μ.map f) :=
measurable_of_measurable_coe _ $ assume s hs,
  suffices measurable (λ (μ : measure α), μ (f ⁻¹' s)),
    by simpa [map_apply, hs, hf],
  measurable_coe (hf.preimage hs)

lemma measurable_dirac :
  measurable (measure.dirac : α → measure α) :=
measurable_of_measurable_coe _ $ assume s hs,
  begin
    simp [hs, supr_eq_if],
    exact measurable_const.if hs measurable_const
  end

lemma measurable_integral (f : α → ennreal) (hf : measurable f) :
  measurable (λμ : measure α, μ.integral f) :=
suffices measurable (λμ : measure α,
  (⨆n:ℕ, @simple_func.integral α { volume := μ } (simple_func.eapprox f n)) : _ → ennreal),
begin
  convert this,
  funext μ,
  exact @lintegral_eq_supr_eapprox_integral α {volume := μ} f hf
end,
measurable_supr $ assume n,
  begin
    dunfold simple_func.integral,
    refine finset.measurable_sum (simple_func.eapprox f n).range (λ i, _),
    refine measurable_const.ennreal_mul _,
    exact measurable_coe ((simple_func.eapprox f n).preimage_measurable _)
  end

/-- Monadic join on `measure` in the category of measurable spaces and measurable
functions. -/
def join (m : measure (measure α)) : measure α :=
measure.of_measurable
  (λs hs, m.integral (λμ, μ s))
  (by simp [integral])
  begin
    assume f hf h,
    simp [measure_Union h hf],
    apply lintegral_tsum,
    assume i, exact measurable_coe (hf i)
  end

@[simp] lemma join_apply {m : measure (measure α)} :
  ∀{s : set α}, is_measurable s → join m s = m.integral (λμ, μ s) :=
measure.of_measurable_apply

lemma measurable_join : measurable (join : measure (measure α) → measure α) :=
measurable_of_measurable_coe _ $ assume s hs,
  by simp [hs]; exact measurable_integral _ (measurable_coe hs)

lemma integral_join {m : measure (measure α)} {f : α → ennreal} (hf : measurable f) :
  integral (join m) f = integral m (λμ, integral μ f) :=
begin
  transitivity,
  apply lintegral_eq_supr_eapprox_integral,
  { exact hf },
  have : ∀n x,
    @volume α { volume := join m} (⇑(simple_func.eapprox (λ (a : α), f a) n) ⁻¹' {x}) =
    m.integral (λμ, @volume α { volume := μ } ((⇑(simple_func.eapprox (λ (a : α), f a) n) ⁻¹' {x}))) :=
    assume n x, join_apply (simple_func.measurable_sn _ _),
  conv {
    to_lhs,
    congr,
    funext,
    rw [simple_func.integral] },
  simp [this],
  transitivity,
  have : ∀(s : ℕ → finset ennreal) (f : ℕ → ennreal → measure α → ennreal)
    (hf : ∀n r, measurable (f n r)) (hm : monotone (λn μ, ∑ r in s n, r * f n r μ)),
    (⨆n:ℕ, ∑ r in s n, r * integral m (f n r)) =
    integral m (λμ, ⨆n:ℕ, ∑ r in s n, r * f n r μ),
  { assume s f hf hm,
    symmetry,
    transitivity,
    apply lintegral_supr,
    { assume n,
      exact finset.measurable_sum _ (assume r, measurable_const.ennreal_mul (hf _ _)) },
    { exact hm },
    congr, funext n,
    transitivity,
    apply lintegral_finset_sum,
    { assume r, exact measurable_const.ennreal_mul (hf _ _) },
    congr, funext r,
    apply lintegral_const_mul,
    exact hf _ _ },
  specialize this (λn, simple_func.range (simple_func.eapprox f n)),
  specialize this
    (λn r μ, @volume α { volume := μ } (⇑(simple_func.eapprox (λ (a : α), f a) n) ⁻¹' {r})),
  refine this _ _; clear this,
  { assume n r,
    apply measurable_coe,
    exact simple_func.measurable_sn _ _ },
  { change monotone (λn μ, @simple_func.integral α {volume := μ} (simple_func.eapprox f n)),
    assume n m h μ,
    apply simple_func.integral_le_integral,
    apply simple_func.monotone_eapprox,
    assumption },
  congr, funext μ,
  symmetry,
  apply lintegral_eq_supr_eapprox_integral,
  exact hf
end

/-- Monadic bind on `measure`, only works in the category of measurable spaces and measurable
functions. When the function `f` is not measurable the result is not well defined. -/
def bind (m : measure α) (f : α → measure β) : measure β := join (map f m)

@[simp] lemma bind_apply {m : measure α} {f : α → measure β} {s : set β}
  (hs : is_measurable s) (hf : measurable f) : bind m f s = m.integral (λa, f a s) :=
by rw [bind, join_apply hs, integral_map (measurable_coe hs) hf]

lemma measurable_bind' {g : α → measure β} (hg : measurable g) : measurable (λm, bind m g) :=
measurable_join.comp (measurable_map _ hg)

lemma integral_bind {m : measure α} {g : α → measure β} {f : β → ennreal}
  (hg : measurable g) (hf : measurable f) :
  integral (bind m g) f = integral m (λa, integral (g a) f) :=
begin
  transitivity,
  exact integral_join hf,
  exact integral_map (measurable_integral _ hf) hg
end

lemma bind_bind {γ} [measurable_space γ] {m : measure α} {f : α → measure β} {g : β → measure γ}
  (hf : measurable f) (hg : measurable g) :
  bind (bind m f) g = bind m (λa, bind (f a) g) :=
measure.ext $ assume s hs,
begin
  rw [bind_apply hs hg, bind_apply hs ((measurable_bind' hg).comp hf), integral_bind hf],
  { congr, funext a,
    exact (bind_apply hs hg).symm },
  exact (measurable_coe hs).comp hg
end

lemma bind_dirac {f : α → measure β} (hf : measurable f) (a : α) : bind (dirac a) f = f a :=
measure.ext $ assume s hs, by rw [bind_apply hs hf, integral_dirac a ((measurable_coe hs).comp hf)]

lemma dirac_bind {m : measure α} : bind m dirac = m :=
measure.ext $ assume s hs,
begin
  rw [bind_apply hs measurable_dirac],
  simp [dirac_apply _ hs],
  transitivity,
  apply lintegral_supr_const,
  assumption,
  exact one_mul _
end

lemma map_dirac {f : α → β} (hf : measurable f) (a : α) :
  map f (dirac a) = dirac (f a) :=
measure.ext $ assume s hs,
  by rw [dirac_apply (f a) hs, map_apply hf hs, dirac_apply a (hf s hs), set.mem_preimage]

lemma join_eq_bind (μ : measure (measure α)) : join μ = bind μ id :=
by rw [bind, map_id]

lemma join_map_map {f : α → β} (hf : measurable f) (μ : measure (measure α)) :
  join (map (map f) μ) = map f (join μ) :=
measure.ext $ assume s hs,
  begin
    rw [join_apply hs, map_apply hf hs, join_apply,
      integral_map (measurable_coe hs) (measurable_map f hf)],
    { congr, funext ν, exact map_apply hf hs },
    exact hf s hs
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
eq.trans (join_eq_bind (dirac μ)) (bind_dirac measurable_id _)

end measure

end measure_theory
