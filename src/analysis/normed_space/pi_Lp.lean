/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.mean_inequalities
import data.fintype.order

/-!
# `L^p` distance on finite products of metric spaces
Given finitely many metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a parameter `p : ℝ≥0∞`, that also induce
the product topology. We define them in this file. For `0 < p < ∞`, the distance on `Π i, α i`
is given by
$$
d(x, y) = \left(\sum d(x_i, y_i)^p\right)^{1/p}.
$$,
whereas for `p = 0` it is the cardinality of the set ${ i | x_i ≠ y_i}$. For `p = ∞` the distance
is the supremum of the distances.

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Π-type, named
`pi_Lp p α`. The assumpion `[fact (1 ≤ p)]` is required for the metric and normed space instances.

We ensure that the topology, bornology and uniform structure on `pi_Lp p α` are (defeq to) the
product topology, product bornology and product uniformity, to be able to use freely continuity
statements for the coordinate functions, for instance.

## Implementation notes

We only deal with the `L^p` distance on a product of finitely many metric spaces, which may be
distinct. A closely related construction is `lp`, the `L^p` norm on a product of (possibly
infinitely many) normed spaces, where the norm is
$$
\left(\sum ∥f (x)∥^p \right)^{1/p}.
$$
However, the topology induced by this construction is not the product topology, and some functions
have infinite `L^p` norm. These subtleties are not present in the case of finitely many metric
spaces, hence it is worth devoting a file to this specific case which is particularly well behaved.

Another related construction is `measure_theory.Lp`, the `L^p` norm on the space of functions from
a measure space to a normed space, where the norm is
$$
\left(\int ∥f (x)∥^p dμ\right)^{1/p}.
$$
This has all the same subtleties as `lp`, and the further subtlety that this only
defines a seminorm (as almost everywhere zero functions have zero `L^p` norm).
The construction `pi_Lp` corresponds to the special case of `measure_theory.Lp` in which the basis
is a finite space equipped with the counting measure.

To prove that the topology (and the uniform structure) on a finite product with the `L^p` distance
are the same as those coming from the `L^∞` distance, we could argue that the `L^p` and `L^∞` norms
are equivalent on `ℝ^n` for abstract (norm equivalence) reasons. Instead, we give a more explicit
(easy) proof which provides a comparison between these two norms with explicit constants.

We also set up the theory for `pseudo_emetric_space` and `pseudo_metric_space`.
-/

open real set filter is_R_or_C bornology
open_locale big_operators uniformity topological_space nnreal ennreal

noncomputable theory

variables {ι : Type*}

/-- A copy of a Pi type, on which we will put the `L^p` distance. Since the Pi type itself is
already endowed with the `L^∞` distance, we need the type synonym to avoid confusing typeclass
resolution. Also, we let it depend on `p`, to get a whole family of type on which we can put
different distances. -/
@[nolint unused_arguments]
def pi_Lp {ι : Type*} (p : ℝ≥0∞) (α : ι → Type*) : Type* := Π (i : ι), α i

instance {ι : Type*} (p : ℝ≥0∞) (α : ι → Type*) [Π i, inhabited (α i)] : inhabited (pi_Lp p α) :=
⟨λ i, default⟩

namespace pi_Lp

variables (p : ℝ≥0∞) (𝕜 : Type*) (α : ι → Type*) (β : ι → Type*)

/-- Canonical bijection between `pi_Lp p α` and the original Pi type. We introduce it to be able
to compare the `L^p` and `L^∞` distances through it. -/
protected def equiv : pi_Lp p α ≃ Π (i : ι), α i :=
equiv.refl _

lemma equiv_apply (x : pi_Lp p α) (i : ι) : pi_Lp.equiv p α x i = x i := rfl
lemma equiv_symm_apply (x : Π i, α i) (i : ι) : (pi_Lp.equiv p α).symm x i = x i := rfl

@[simp] lemma equiv_apply' (x : pi_Lp p α) : pi_Lp.equiv p α x = x := rfl
@[simp] lemma equiv_symm_apply' (x : Π i, α i) : (pi_Lp.equiv p α).symm x = x := rfl

section
/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `pi_Lp p α`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Pi type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.
-/

variables [Π i, pseudo_metric_space (α i)] [Π i, pseudo_emetric_space (β i)] [fintype ι]

/-- Endowing the space `pi_Lp p β` with the `L^p` edistance. We register this instance
separate from `pi_Lp.pseudo_emetric` since the latter requires the type class hypothesis
`[fact (1 ≤ p)]` in order to prove the triangle inequality. Registering this separately allows
for a future quasi-emetric structure on `pi_Lp p β` for `p < 1`. -/
instance : has_edist (pi_Lp p β) :=
{ edist := λ f g, if hp : p = 0 then by subst hp; exact {i | f i ≠ g i}.to_finite.to_finset.card
    else (if p = ∞ then ⨆ i, edist (f i) (g i)
    else (∑ i, (edist (f i) (g i) ^ p.to_real)) ^ (1/p.to_real)) }

variable {β}
lemma edist_eq_card (f g : pi_Lp 0 β) : edist f g = {i | f i ≠ g i}.to_finite.to_finset.card :=
dif_pos rfl

lemma edist_eq_sum {p : ℝ≥0∞} (hp : 0 < p.to_real) (f g : pi_Lp p β) :
  edist f g = (∑ i, edist (f i) (g i) ^ p.to_real) ^ (1/p.to_real) :=
begin
  dsimp [edist],
  rw ennreal.to_real_pos_iff at hp,
  rw [dif_neg hp.1.ne', if_neg hp.2.ne],
end

lemma edist_eq_supr (f g : pi_Lp ∞ β) : edist f g = ⨆ i, edist (f i) (g i) :=
begin
  dsimp [edist],
  rw [dif_neg ennreal.top_ne_zero, if_pos rfl]
end

protected lemma edist_self (f : pi_Lp p β) : edist f f = 0 :=
begin
  rcases p.trichotomy with (rfl | rfl | h),
  { simp [edist_eq_card], },
  { simp [edist_eq_supr], },
  { simp [edist_eq_sum h, ennreal.zero_rpow_of_pos h, ennreal.zero_rpow_of_pos (inv_pos.2 $ h)]}
end

protected lemma edist_comm (f g : pi_Lp p β) : edist f g = edist g f :=
begin
  rcases p.trichotomy with (rfl | rfl | h),
  { simp only [edist_eq_card, eq_comm, ne.def] },
  { simp only [edist_eq_supr, edist_comm] },
  { simp only [edist_eq_sum h, edist_comm] }
end

variable (β)

/-- Endowing the space `pi_Lp p β` with the `L^p` pseudoemetric structure. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `pseudo_emetric_space.replace_uniformity`. -/
def pseudo_emetric_aux [fact (1 ≤ p)] : pseudo_emetric_space (pi_Lp p β) :=
{ edist_self := pi_Lp.edist_self p,
  edist_comm := pi_Lp.edist_comm p,
  edist_triangle := λ f g h,
  begin
    unfreezingI { rcases p.dichotomy with (rfl | hp) },
    { simp only [edist_eq_supr],
      casesI is_empty_or_nonempty ι,
      { simp only [csupr_of_empty, ennreal.bot_eq_zero, add_zero, nonpos_iff_eq_zero] },
      exact supr_le (λ i, (edist_triangle _ (g i) _).trans $
        add_le_add (le_supr _ i) (le_supr _ i))},
    { simp only [edist_eq_sum (zero_lt_one.trans_le hp)],
      calc (∑ i, edist (f i) (h i) ^ p.to_real) ^ (1 / p.to_real) ≤
      (∑ i, (edist (f i) (g i) + edist (g i) (h i)) ^ p.to_real) ^ (1 / p.to_real) :
      begin
        apply ennreal.rpow_le_rpow _ (one_div_nonneg.2 $ zero_le_one.trans hp),
        refine finset.sum_le_sum (λ i hi, _),
        exact ennreal.rpow_le_rpow (edist_triangle _ _ _) (zero_le_one.trans hp),
      end
      ... ≤ (∑ i, edist (f i) (g i) ^ p.to_real) ^ (1 / p.to_real)
            + (∑ i, edist (g i) (h i) ^ p.to_real) ^ (1 / p.to_real) : ennreal.Lp_add_le _ _ _ hp },
  end }

local attribute [instance] pi_Lp.pseudo_emetric_aux

/-- Endowing the space `pi_Lp p β` with the `L^p` distance. We register this instance
separate from `pi_Lp.pseudo_metric` since the latter requires the type class hypothesis
`[fact (1 ≤ p)]` in order to prove the triangle inequality. Registering this separately allows
for a future quasi-metric structure on `pi_Lp p β` for `p < 1`. -/
instance : has_dist (pi_Lp p α) :=
{ dist := λ f g, if hp : p = 0 then by subst hp; exact {i | f i ≠ g i}.to_finite.to_finset.card
    else (if p = ∞ then ⨆ i, dist (f i) (g i)
    else (∑ i, (dist (f i) (g i) ^ p.to_real)) ^ (1/p.to_real)) }

variable {α}
lemma dist_eq_card (f g : pi_Lp 0 α) : dist f g = {i | f i ≠ g i}.to_finite.to_finset.card :=
dif_pos rfl

lemma dist_eq_sum {p : ℝ≥0∞} (hp : 0 < p.to_real) (f g : pi_Lp p α) :
  dist f g = (∑ i, dist (f i) (g i) ^ p.to_real) ^ (1/p.to_real) :=
begin
  dsimp [dist],
  rw ennreal.to_real_pos_iff at hp,
  rw [dif_neg hp.1.ne', if_neg hp.2.ne],
end

lemma dist_eq_csupr (f g : pi_Lp ∞ α) : dist f g = ⨆ i, dist (f i) (g i) :=
begin
  dsimp [dist],
  rw [dif_neg ennreal.top_ne_zero, if_pos rfl]
end

variable (α)

example (f g : pi_Lp ∞ α) : (⨆ i, edist (f i) (g i)) ≠ ⊤ :=
begin
  obtain ⟨M, hM⟩ := fintype.exists_le (λ i, (⟨dist (f i) (g i), dist_nonneg⟩ : ℝ≥0)),
  refine ne_of_lt ((supr_le $ λ i, _).trans_lt (@ennreal.coe_lt_top M)),
  simp only [edist, pseudo_metric_space.edist_dist, ennreal.of_real_eq_coe_nnreal dist_nonneg],
  exact_mod_cast hM i,
end

/-- Endowing the space `pi_Lp p α` with the `L^p` pseudometric structure. This definition is not
satisfactory, as it does not register the fact that the topology, the uniform structure, and the
bornology coincide with the product ones. Therefore, we do not register it as an instance. Using
this as a temporary pseudoemetric space instance, we will show that the uniform structure is equal
(but not defeq) to the product one, and then register an instance in which we replace the uniform
structure and the bornology by the product ones using this pseudometric space,
`pseudo_metric_space.replace_uniformity`, and `pseudo_metric_space.replace_bornology`.

See note [reducible non-instances] -/
@[reducible] def pseudo_metric_aux [fact (1 ≤ p)] : pseudo_metric_space (pi_Lp p α) :=
have supr_ne_top : ∀ (f g : pi_Lp ∞ α), (⨆ i, edist (f i) (g i)) ≠ ⊤ := λ f g,
begin
  obtain ⟨M, hM⟩ := fintype.exists_le (λ i, (⟨dist (f i) (g i), dist_nonneg⟩ : ℝ≥0)),
  refine ne_of_lt ((supr_le $ λ i, _).trans_lt (@ennreal.coe_lt_top M)),
  simp only [edist, pseudo_metric_space.edist_dist, ennreal.of_real_eq_coe_nnreal dist_nonneg],
  exact_mod_cast hM i,
end,
pseudo_emetric_space.to_pseudo_metric_space_of_dist dist
  (λ f g,
  begin
    unfreezingI { rcases p.dichotomy with (rfl | h) },
    { exact supr_ne_top f g },
    { rw edist_eq_sum (zero_lt_one.trans_le h),
      exact ennreal.rpow_ne_top_of_nonneg (one_div_nonneg.2 (zero_le_one.trans h)) (ne_of_lt $
        (ennreal.sum_lt_top $ λ i hi, ennreal.rpow_ne_top_of_nonneg (zero_le_one.trans h)
        (edist_ne_top _ _)))}
  end)
  (λ f g,
  begin
    unfreezingI { rcases p.dichotomy with (rfl | h) },
    { rw [edist_eq_supr, dist_eq_csupr],
      { casesI is_empty_or_nonempty ι,
        { simp only [real.csupr_empty, csupr_of_empty, ennreal.bot_eq_zero, ennreal.zero_to_real] },
        { refine le_antisymm (csupr_le $ λ i, _) _,
          { rw [←ennreal.of_real_le_iff_le_to_real (supr_ne_top f g),
              ←pseudo_metric_space.edist_dist],
            exact le_supr _ i, },
          { refine ennreal.to_real_le_of_le_of_real (real.Sup_nonneg _ _) (supr_le $ λ i, _),
            { rintro - ⟨i, rfl⟩,
              exact dist_nonneg, },
            { unfold edist, rw pseudo_metric_space.edist_dist,
              exact ennreal.of_real_le_of_real (le_csupr (fintype.bdd_above_range _) i), } } } } },
    { have A : ∀ i, edist (f i) (g i) ^ p.to_real ≠ ⊤,
        from λ i, ennreal.rpow_ne_top_of_nonneg (zero_le_one.trans h) (edist_ne_top _ _),
      simp only [edist_eq_sum (zero_lt_one.trans_le h), dist_edist, ennreal.to_real_rpow,
        dist_eq_sum (zero_lt_one.trans_le h), ← ennreal.to_real_sum (λ i _, A i)] }
  end)

local attribute [instance] pi_Lp.pseudo_metric_aux

lemma lipschitz_with_equiv_aux [fact (1 ≤ p)] : lipschitz_with 1 (pi_Lp.equiv p β) :=
begin
  intros f g,
  unfreezingI { rcases p.dichotomy with (rfl | h) },
  { simpa only [equiv_apply', ennreal.coe_one, one_mul, edist_eq_supr, edist, finset.sup_le_iff,
      finset.mem_univ, forall_true_left] using le_supr (λ i, edist (f i) (g i)), },
  { have cancel : p.to_real * (1/p.to_real) = 1 := mul_div_cancel' 1 (zero_lt_one.trans_le h).ne',
    rw edist_eq_sum (zero_lt_one.trans_le h),
    simp only [edist, forall_prop_of_true, one_mul, finset.mem_univ, finset.sup_le_iff,
      ennreal.coe_one],
    assume i,
    calc
    edist (f i) (g i) = (edist (f i) (g i) ^ p.to_real) ^ (1/p.to_real) :
      by simp [← ennreal.rpow_mul, cancel, -one_div]
    ... ≤ (∑ i, edist (f i) (g i) ^ p.to_real) ^ (1 / p.to_real) :
    begin
      apply ennreal.rpow_le_rpow _ (one_div_nonneg.2 $ (zero_le_one.trans h)),
      exact finset.single_le_sum (λ i hi, (bot_le : (0 : ℝ≥0∞) ≤ _)) (finset.mem_univ i)
    end }
end

lemma antilipschitz_with_equiv_aux [fact (1 ≤ p)] :
  antilipschitz_with ((fintype.card ι : ℝ≥0) ^ (1 / p).to_real) (pi_Lp.equiv p β) :=
begin
  intros f g,
  unfreezingI { rcases p.dichotomy with (rfl | h) },
  { simp only [edist_eq_supr, ennreal.div_top, ennreal.zero_to_real, nnreal.rpow_zero,
      ennreal.coe_one, equiv_apply', one_mul, supr_le_iff],
    exact λ i, finset.le_sup (finset.mem_univ i), },
  { have pos : 0 < p.to_real := zero_lt_one.trans_le h,
    have nonneg : 0 ≤ 1 / p.to_real := one_div_nonneg.2 (le_of_lt pos),
    have cancel : p.to_real * (1/p.to_real) = 1 := mul_div_cancel' 1 (ne_of_gt pos),
    rw [edist_eq_sum pos, ennreal.to_real_div 1 p],
    simp only [edist, equiv_apply', ←one_div, ennreal.one_to_real],
    calc (∑ i, edist (f i) (g i) ^ p.to_real) ^ (1 / p.to_real) ≤
    (∑ i, edist (pi_Lp.equiv p β f) (pi_Lp.equiv p β g) ^ p.to_real) ^ (1 / p.to_real) :
    begin
      apply ennreal.rpow_le_rpow _ nonneg,
      apply finset.sum_le_sum (λ i hi, _),
      apply ennreal.rpow_le_rpow _ (le_of_lt pos),
      exact finset.le_sup (finset.mem_univ i)
    end
    ... = (((fintype.card ι : ℝ≥0)) ^ (1 / p.to_real) : ℝ≥0) *
      edist (pi_Lp.equiv p β f) (pi_Lp.equiv p β g) :
    begin
      simp only [nsmul_eq_mul, finset.card_univ, ennreal.rpow_one, finset.sum_const,
        ennreal.mul_rpow_of_nonneg _ _ nonneg, ←ennreal.rpow_mul, cancel],
      have : (fintype.card ι : ℝ≥0∞) = (fintype.card ι : ℝ≥0) :=
        (ennreal.coe_nat (fintype.card ι)).symm,
      rw [this, ennreal.coe_rpow_of_nonneg _ nonneg]
    end }
end

lemma aux_uniformity_eq [fact (1 ≤ p)] :
  𝓤 (pi_Lp p β) = @uniformity _ (Pi.uniform_space _) :=
begin
  have A : uniform_inducing (pi_Lp.equiv p β) :=
    (antilipschitz_with_equiv_aux p β).uniform_inducing
    (lipschitz_with_equiv_aux p β).uniform_continuous,
  have : (λ (x : pi_Lp p β × pi_Lp p β),
    ((pi_Lp.equiv p β) x.fst, (pi_Lp.equiv p β) x.snd)) = id,
    by ext i; refl,
  rw [← A.comap_uniformity, this, comap_id]
end

lemma aux_cobounded_eq [fact (1 ≤ p)] :
  cobounded (pi_Lp p α) = @cobounded _ pi.bornology :=
calc cobounded (pi_Lp p α) = comap (pi_Lp.equiv p α) (cobounded _) :
  le_antisymm (antilipschitz_with_equiv_aux p α).tendsto_cobounded.le_comap
    (lipschitz_with_equiv_aux p α).comap_cobounded_le
... = _ : comap_id

end

/-! ### Instances on finite `L^p` products -/

instance uniform_space [Π i, uniform_space (β i)] : uniform_space (pi_Lp p β) :=
Pi.uniform_space _

variable [fintype ι]

instance bornology [Π i, bornology (β i)] : bornology (pi_Lp p β) := pi.bornology

/-- pseudoemetric space instance on the product of finitely many pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance [fact (1 ≤ p)] [Π i, pseudo_emetric_space (β i)] : pseudo_emetric_space (pi_Lp p β) :=
(pseudo_emetric_aux p β).replace_uniformity (aux_uniformity_eq p β).symm

/-- emetric space instance on the product of finitely many emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance [fact (1 ≤ p)] [Π i, emetric_space (α i)] : emetric_space (pi_Lp p α) :=
@emetric.of_t0_pseudo_emetric_space (pi_Lp p α) _ pi.t0_space

/-- pseudometric space instance on the product of finitely many psuedometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance [fact (1 ≤ p)] [Π i, pseudo_metric_space (β i)] : pseudo_metric_space (pi_Lp p β) :=
((pseudo_metric_aux p β).replace_uniformity (aux_uniformity_eq p β).symm).replace_bornology $
  λ s, filter.ext_iff.1 (aux_cobounded_eq p β).symm sᶜ

/-- metric space instance on the product of finitely many metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
instance [fact (1 ≤ p)] [Π i, metric_space (α i)] : metric_space (pi_Lp p α) :=
metric.of_t0_pseudo_metric_space _

lemma nndist_eq_sum {p : ℝ≥0∞} [fact (1 ≤ p)] {β : ι → Type*}
  [Π i, pseudo_metric_space (β i)] (hp : p ≠ ∞) (x y : pi_Lp p β) :
  nndist x y = (∑ i : ι, nndist (x i) (y i) ^ p.to_real) ^ (1 / p.to_real) :=
subtype.ext $ by { push_cast, exact dist_eq_sum (p.to_real_pos_iff_ne_top.mpr hp) _ _ }

lemma nndist_eq_supr {β : ι → Type*} [Π i, pseudo_metric_space (β i)] (x y : pi_Lp ∞ β) :
  nndist x y = ⨆ i, nndist (x i) (y i) :=
subtype.ext $ by { push_cast, exact dist_eq_csupr _ _ }

lemma lipschitz_with_equiv [fact (1 ≤ p)] [Π i, pseudo_emetric_space (β i)] :
  lipschitz_with 1 (pi_Lp.equiv p β) :=
lipschitz_with_equiv_aux p β

lemma antilipschitz_with_equiv [fact (1 ≤ p)] [Π i, pseudo_emetric_space (β i)] :
  antilipschitz_with ((fintype.card ι : ℝ≥0) ^ (1 / p).to_real) (pi_Lp.equiv p β) :=
antilipschitz_with_equiv_aux p β

lemma infty_equiv_isometry [Π i, pseudo_emetric_space (β i)] :
  isometry (pi_Lp.equiv ∞ β) :=
λ x y, le_antisymm (by simpa only [ennreal.coe_one, one_mul] using lipschitz_with_equiv ∞ β x y)
  (by simpa only [ennreal.div_top, ennreal.zero_to_real, nnreal.rpow_zero, ennreal.coe_one, one_mul]
    using antilipschitz_with_equiv ∞ β x y)

instance has_norm [Π i, has_norm (β i)] [Π i, has_zero (β i)] : has_norm (pi_Lp p β) :=
{ norm := λ f, if hp : p = 0 then by subst hp; exact {i | f i ≠ 0}.to_finite.to_finset.card
   else (if p = ∞ then ⨆ i, ∥f i∥ else (∑ i, ∥f i∥ ^ p.to_real) ^ (1 / p.to_real)) }

variables {p β}
lemma norm_eq_card [Π i, has_norm (β i)] [Π i, has_zero (β i)] (f : pi_Lp 0 β) :
  ∥f∥ = {i | f i ≠ 0}.to_finite.to_finset.card :=
dif_pos rfl

lemma norm_eq_csupr [Π i, has_norm (β i)] [Π i, has_zero (β i)] (f : pi_Lp ∞ β) :
  ∥f∥ = ⨆ i, ∥f i∥ :=
begin
  dsimp [norm],
  rw [dif_neg ennreal.top_ne_zero, if_pos rfl]
end

lemma norm_eq_sum [Π i, has_norm (β i)] [Π i, has_zero (β i)] (hp : 0 < p.to_real) (f : pi_Lp p β) :
  ∥f∥ = (∑ i, ∥f i∥ ^ p.to_real) ^ (1 / p.to_real) :=
begin
  dsimp [norm],
  rw ennreal.to_real_pos_iff at hp,
  rw [dif_neg hp.1.ne', if_neg hp.2.ne],
end

variables (p β) [fact (1 ≤ p)]
/-- seminormed group instance on the product of finitely many normed groups, using the `L^p`
norm. -/
instance seminormed_add_comm_group [Π i, seminormed_add_comm_group (β i)] :
  seminormed_add_comm_group (pi_Lp p β) :=
{ dist_eq := λ x y,
  begin
    unfreezingI { rcases p.dichotomy with (rfl | h) },
    { simpa only [dist_eq_csupr, norm_eq_csupr, dist_eq_norm] },
    { have : p ≠ ∞, { intros hp, rw [hp, ennreal.top_to_real] at h, linarith,} ,
      simpa only [dist_eq_sum (zero_lt_one.trans_le h), norm_eq_sum (zero_lt_one.trans_le h),
        dist_eq_norm], }
  end,
  .. pi.add_comm_group, }

/-- normed group instance on the product of finitely many normed groups, using the `L^p` norm. -/
instance normed_add_comm_group [Π i, normed_add_comm_group (α i)] :
  normed_add_comm_group (pi_Lp p α) :=
{ ..pi_Lp.seminormed_add_comm_group p α }

lemma nnnorm_eq_sum {p : ℝ≥0∞} [fact (1 ≤ p)] {β : ι → Type*} (hp : p ≠ ∞)
  [Π i, seminormed_add_comm_group (β i)] (f : pi_Lp p β) :
  ∥f∥₊ = (∑ i, ∥f i∥₊ ^ p.to_real) ^ (1 / p.to_real) :=
by { ext, simp [nnreal.coe_sum, norm_eq_sum (p.to_real_pos_iff_ne_top.mpr hp)] }

lemma nnnorm_eq_csupr {β : ι → Type*} [Π i, seminormed_add_comm_group (β i)] (f : pi_Lp ∞ β) :
  ∥f∥₊ = ⨆ i, ∥f i∥₊ :=
by { ext, simp [nnreal.coe_supr, norm_eq_csupr] }

lemma norm_eq_of_nat {p : ℝ≥0∞} [fact (1 ≤ p)] {β : ι → Type*}
  [Π i, seminormed_add_comm_group (β i)] (n : ℕ) (h : p = n) (f : pi_Lp p β) :
  ∥f∥ = (∑ i, ∥f i∥ ^ n) ^ (1/(n : ℝ)) :=
begin
  have := p.to_real_pos_iff_ne_top.mpr (ne_of_eq_of_ne h $ ennreal.nat_ne_top n),
  simp only [one_div, h, real.rpow_nat_cast, ennreal.to_real_nat, eq_self_iff_true,
    finset.sum_congr, norm_eq_sum this],
end

lemma norm_eq_of_L2 {β : ι → Type*} [Π i, seminormed_add_comm_group (β i)] (x : pi_Lp 2 β) :
  ∥x∥ = sqrt (∑ (i : ι), ∥x i∥ ^ 2) :=
by { convert norm_eq_of_nat 2 (by norm_cast) _, rw sqrt_eq_rpow, norm_cast }

lemma nnnorm_eq_of_L2 {β : ι → Type*} [Π i, seminormed_add_comm_group (β i)] (x : pi_Lp 2 β) :
  ∥x∥₊ = nnreal.sqrt (∑ (i : ι), ∥x i∥₊ ^ 2) :=
subtype.ext $ by { push_cast, exact norm_eq_of_L2 x }

lemma norm_sq_eq_of_L2 (β : ι → Type*) [Π i, seminormed_add_comm_group (β i)] (x : pi_Lp 2 β) :
  ∥x∥ ^ 2 = ∑ (i : ι), ∥x i∥ ^ 2 :=
begin
  suffices : ∥x∥₊ ^ 2 = ∑ (i : ι), ∥x i∥₊ ^ 2,
  { simpa only [nnreal.coe_sum] using congr_arg (coe : ℝ≥0 → ℝ) this },
  rw [nnnorm_eq_of_L2, nnreal.sq_sqrt],
end

lemma dist_eq_of_L2 {β : ι → Type*} [Π i, seminormed_add_comm_group (β i)] (x y : pi_Lp 2 β) :
  dist x y = (∑ i, dist (x i) (y i) ^ 2).sqrt :=
by simp_rw [dist_eq_norm, norm_eq_of_L2, pi.sub_apply]

lemma nndist_eq_of_L2 {β : ι → Type*} [Π i, seminormed_add_comm_group (β i)] (x y : pi_Lp 2 β) :
  nndist x y = (∑ i, nndist (x i) (y i) ^ 2).sqrt :=
subtype.ext $ by { push_cast, exact dist_eq_of_L2 _ _ }

lemma edist_eq_of_L2 {β : ι → Type*} [Π i, seminormed_add_comm_group (β i)] (x y : pi_Lp 2 β) :
  edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : ℝ) :=
by simp [pi_Lp.edist_eq_sum]

variables [normed_field 𝕜]

-- this was necessary to get Lean to accept `∥c • f∥₊` in the `normed_space` instance below
-- can we just do this with `letI`?
instance module [Π i, seminormed_add_comm_group (β i)] [Π i, module 𝕜 (β i)] :
  module 𝕜 (pi_Lp p β) := pi.module ι β 𝕜

/-- The product of finitely many normed spaces is a normed space, with the `L^p` norm. -/
instance normed_space [Π i, seminormed_add_comm_group (β i)]
  [Π i, normed_space 𝕜 (β i)] : normed_space 𝕜 (pi_Lp p β) :=
{ norm_smul_le := λ c f,
  begin
    unfreezingI { rcases p.dichotomy with (rfl | hp) },
    { suffices : ∥c • f∥₊ = ∥c∥₊ * ∥f∥₊, { exact_mod_cast nnreal.coe_mono this.le },
      simpa only [nnnorm_eq_csupr, nnreal.mul_supr, ←nnnorm_smul] },
    { have : p.to_real * (1 / p.to_real) = 1 := mul_div_cancel' 1 (zero_lt_one.trans_le hp).ne',
      simp only [norm_eq_sum (zero_lt_one.trans_le hp), norm_smul, mul_rpow, norm_nonneg,
        ←finset.mul_sum, pi.smul_apply],
      rw [mul_rpow (rpow_nonneg_of_nonneg (norm_nonneg _) _), ← rpow_mul (norm_nonneg _),
        this, rpow_one],
      exact finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg (norm_nonneg _) _) },
  end, }

instance finite_dimensional [Π i, seminormed_add_comm_group (β i)]
  [Π i, normed_space 𝕜 (β i)] [I : ∀ i, finite_dimensional 𝕜 (β i)] :
  finite_dimensional 𝕜 (pi_Lp p β) :=
finite_dimensional.finite_dimensional_pi' _ _

/- Register simplification lemmas for the applications of `pi_Lp` elements, as the usual lemmas
for Pi types will not trigger. -/
variables {𝕜 p α} [Π i, seminormed_add_comm_group (β i)] [Π i, normed_space 𝕜 (β i)] (c : 𝕜)
variables (x y : pi_Lp p β) (x' y' : Π i, β i) (i : ι)

@[simp] lemma zero_apply : (0 : pi_Lp p β) i = 0 := rfl
@[simp] lemma add_apply : (x + y) i = x i + y i := rfl
@[simp] lemma sub_apply : (x - y) i = x i - y i := rfl
@[simp] lemma smul_apply : (c • x) i = c • x i := rfl
@[simp] lemma neg_apply : (-x) i = - (x i) := rfl

/-- The canonical map `pi_Lp.equiv` between `pi_Lp ∞ β` and `Π i, β i` as a linear isometric
equivalence. -/
def equivₗᵢ [Π i, seminormed_add_comm_group (β i)] [Π i, normed_space 𝕜 (β i)] :
  pi_Lp ∞ β ≃ₗᵢ[𝕜] Π i, β i :=
{ map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl,
  norm_map' := λ f,
  begin
    suffices : finset.univ.sup (λ i, ∥f i∥₊) = ⨆ i, ∥f i∥₊,
    { simpa only [nnreal.coe_supr] using congr_arg (coe : ℝ≥0 → ℝ) this },
    refine antisymm (finset.sup_le (λ i _, le_csupr (fintype.bdd_above_range (λ i, ∥f i∥₊)) _)) _,
    casesI is_empty_or_nonempty ι,
    { simp only [csupr_of_empty, finset.univ_eq_empty, finset.sup_empty], },
    { exact csupr_le (λ i, finset.le_sup (finset.mem_univ i)) },
  end,
  .. (pi_Lp.equiv p β) }

variables {ι' : Type*}
variables [fintype ι']

variables (p 𝕜) (E : Type*) [normed_add_comm_group E] [normed_space 𝕜 E]

/-- An equivalence of finite domains induces a linearly isometric equivalence of finitely supported
functions-/
def _root_.linear_isometry_equiv.pi_Lp_congr_left (e : ι ≃ ι') :
  pi_Lp p (λ i : ι, E) ≃ₗᵢ[𝕜] pi_Lp p (λ i : ι', E) :=
{ to_linear_equiv := linear_equiv.Pi_congr_left' 𝕜 (λ i : ι, E) e,
  norm_map' := λ x,
  begin
    unfreezingI { rcases p.dichotomy with (rfl | h) },
    { simp_rw [norm_eq_csupr, linear_equiv.Pi_congr_left'_apply 𝕜 (λ i : ι, E) e x _],
      exact e.symm.csupr (fintype.bdd_above_range _) (λ i, rfl), },
    { simp only [norm_eq_sum (zero_lt_one.trans_le h)],
      simp_rw linear_equiv.Pi_congr_left'_apply 𝕜 (λ i : ι, E) e x _,
      congr,
      exact (fintype.sum_equiv (e.symm) _ _ (λ i, rfl)) }
  end, }

variables {p 𝕜 E}

@[simp] lemma _root_.linear_isometry_equiv.pi_Lp_congr_left_apply
  (e : ι ≃ ι') (v : pi_Lp p (λ i : ι, E)) :
  linear_isometry_equiv.pi_Lp_congr_left p 𝕜 E e v = equiv.Pi_congr_left' (λ i : ι, E) e v :=
rfl

@[simp] lemma _root_.linear_isometry_equiv.pi_Lp_congr_left_symm (e : ι ≃ ι') :
  (linear_isometry_equiv.pi_Lp_congr_left p 𝕜 E e).symm
    = (linear_isometry_equiv.pi_Lp_congr_left p 𝕜 E e.symm) :=
linear_isometry_equiv.ext $ λ x, rfl

@[simp] lemma _root_.linear_isometry_equiv.pi_Lp_congr_left_single
  [decidable_eq ι] [decidable_eq ι'] (e : ι ≃ ι') (i : ι) (v : E) :
  linear_isometry_equiv.pi_Lp_congr_left p 𝕜 E e (pi.single i v) = pi.single (e i) v :=
begin
  funext x,
  simp [linear_isometry_equiv.pi_Lp_congr_left, linear_equiv.Pi_congr_left', equiv.Pi_congr_left',
    pi.single, function.update, equiv.symm_apply_eq],
end

@[simp] lemma equiv_zero : pi_Lp.equiv p β 0 = 0 := rfl
@[simp] lemma equiv_symm_zero : (pi_Lp.equiv p β).symm 0 = 0 := rfl

@[simp] lemma equiv_add :
  pi_Lp.equiv p β (x + y) = pi_Lp.equiv p β x + pi_Lp.equiv p β y := rfl
@[simp] lemma equiv_symm_add :
  (pi_Lp.equiv p β).symm (x' + y') = (pi_Lp.equiv p β).symm x' + (pi_Lp.equiv p β).symm y' := rfl

@[simp] lemma equiv_sub : pi_Lp.equiv p β (x - y) = pi_Lp.equiv p β x - pi_Lp.equiv p β y := rfl
@[simp] lemma equiv_symm_sub :
  (pi_Lp.equiv p β).symm (x' - y') = (pi_Lp.equiv p β).symm x' - (pi_Lp.equiv p β).symm y' := rfl

@[simp] lemma equiv_neg : pi_Lp.equiv p β (-x) = -pi_Lp.equiv p β x := rfl
@[simp] lemma equiv_symm_neg : (pi_Lp.equiv p β).symm (-x') = -(pi_Lp.equiv p β).symm x' := rfl

@[simp] lemma equiv_smul : pi_Lp.equiv p β (c • x) = c • pi_Lp.equiv p β x := rfl
@[simp] lemma equiv_symm_smul :
  (pi_Lp.equiv p β).symm (c • x') = c • (pi_Lp.equiv p β).symm x' := rfl

/-- When `p = ∞`, this lemma does not hold without the additional assumption `nonempty ι` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `∥b∥₊`. See
`pi_Lp.nnnorm_equiv_symm_const'` for a version which exchanges the hypothesis `p ≠ ∞` for
`nonempty ι`. -/
lemma nnnorm_equiv_symm_const {β} [seminormed_add_comm_group β] (hp : p ≠ ∞) (b : β) :
  ∥(pi_Lp.equiv p (λ _ : ι, β)).symm (function.const _ b)∥₊=
  fintype.card ι ^ (1 / p).to_real * ∥b∥₊ :=
begin
  rcases p.dichotomy with (h | h),
  { exact false.elim (hp h) },
  { have ne_zero : p.to_real ≠ 0 := (zero_lt_one.trans_le h).ne',
    simp_rw [nnnorm_eq_sum hp, equiv_symm_apply, function.const_apply, finset.sum_const,
      finset.card_univ, nsmul_eq_mul, nnreal.mul_rpow, ←nnreal.rpow_mul, mul_one_div_cancel ne_zero,
      nnreal.rpow_one, ennreal.to_real_div, ennreal.one_to_real], },
end

/-- When `is_empty ι`, this lemma does not hold without the additional assumption `p ≠ ∞` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `∥b∥₊`. See
`pi_Lp.nnnorm_equiv_symm_const'` for a version which exchanges the hypothesis `nonempty ι`.
for `p ≠ ∞`. -/
lemma nnnorm_equiv_symm_const' {β} [seminormed_add_comm_group β] [nonempty ι] (b : β) :
  ∥(pi_Lp.equiv p (λ _ : ι, β)).symm (function.const _ b)∥₊=
  fintype.card ι ^ (1 / p).to_real * ∥b∥₊ :=
begin
  unfreezingI { rcases (em $ p = ∞) with (rfl | hp) },
  { simp only [equiv_symm_apply', ennreal.div_top, ennreal.zero_to_real, nnreal.rpow_zero, one_mul,
      nnnorm_eq_csupr, function.const_apply, csupr_const], },
  { exact nnnorm_equiv_symm_const hp b, },
end

/-- When `p = ∞`, this lemma does not hold without the additional assumption `nonempty ι` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `∥b∥₊`. See
`pi_Lp.norm_equiv_symm_const'` for a version which exchanges the hypothesis `p ≠ ∞` for
`nonempty ι`. -/
lemma norm_equiv_symm_const {β} [seminormed_add_comm_group β] (hp : p ≠ ∞) (b : β) :
  ∥(pi_Lp.equiv p (λ _ : ι, β)).symm (function.const _ b)∥ =
  fintype.card ι ^ (1 / p).to_real * ∥b∥ :=
(congr_arg coe $ nnnorm_equiv_symm_const hp b).trans $ by simp

/-- When `is_empty ι`, this lemma does not hold without the additional assumption `p ≠ ∞` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `∥b∥₊`. See
`pi_Lp.norm_equiv_symm_const` for a version which exchanges the hypothesis `nonempty ι`.
for `p ≠ ∞`. -/
lemma norm_equiv_symm_const' {β} [seminormed_add_comm_group β] [nonempty ι] (b : β) :
  ∥(pi_Lp.equiv p (λ _ : ι, β)).symm (function.const _ b)∥ =
  fintype.card ι ^ (1 / p).to_real * ∥b∥ :=
(congr_arg coe $ nnnorm_equiv_symm_const' b).trans $ by simp

lemma nnnorm_equiv_symm_one {β} [seminormed_add_comm_group β] (hp : p ≠ ∞) [has_one β] :
  ∥(pi_Lp.equiv p (λ _ : ι, β)).symm 1∥₊ = fintype.card ι ^ (1 / p).to_real * ∥(1 : β)∥₊ :=
(nnnorm_equiv_symm_const hp (1 : β)).trans rfl

lemma norm_equiv_symm_one {β} [seminormed_add_comm_group β] (hp : p ≠ ∞) [has_one β] :
  ∥(pi_Lp.equiv p (λ _ : ι, β)).symm 1∥ = fintype.card ι ^ (1 / p).to_real * ∥(1 : β)∥ :=
(norm_equiv_symm_const hp (1 : β)).trans rfl

variables (𝕜 p)

/-- `pi_Lp.equiv` as a linear map. -/
@[simps {fully_applied := ff}]
protected def linear_equiv : pi_Lp p β ≃ₗ[𝕜] Π i, β i :=
{ to_fun := pi_Lp.equiv _ _,
  inv_fun := (pi_Lp.equiv _ _).symm,
  ..linear_equiv.refl _ _}

end pi_Lp
