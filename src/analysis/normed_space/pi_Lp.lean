/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.mean_inequalities

/-!
# `L^p` distance on finite products of metric spaces
Given finitely many metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a real parameter `p ∈ [1, ∞)`, that also induce
the product topology. We define them in this file. The distance on `Π i, α i` is given by
$$
d(x, y) = \left(\sum d(x_i, y_i)^p\right)^{1/p}.
$$

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Pi type, named
`pi_Lp p α`. The assumpion `[fact (1 ≤ p)]` is required for the metric and normed space instances.

We ensure that the topology and uniform structure on `pi_Lp p α` are (defeq to) the product
topology and product uniformity, to be able to use freely continuity statements for the coordinate
functions, for instance.

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
def pi_Lp {ι : Type*} (p : ℝ) (α : ι → Type*) : Type* := Π (i : ι), α i

instance {ι : Type*} (p : ℝ) (α : ι → Type*) [Π i, inhabited (α i)] : inhabited (pi_Lp p α) :=
⟨λ i, default⟩

instance fact_one_le_one_real : fact ((1:ℝ) ≤ 1) := ⟨rfl.le⟩
instance fact_one_le_two_real : fact ((1:ℝ) ≤ 2) := ⟨one_le_two⟩

namespace pi_Lp

variables (p : ℝ) [fact_one_le_p : fact (1 ≤ p)] (𝕜 : Type*) (α : ι → Type*) (β : ι → Type*)

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

include fact_one_le_p

private lemma pos : 0 < p := zero_lt_one.trans_le fact_one_le_p.out

/-- Endowing the space `pi_Lp p β` with the `L^p` pseudoedistance. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `pseudo_emetric_space.replace_uniformity`. -/
def pseudo_emetric_aux : pseudo_emetric_space (pi_Lp p β) :=
{ edist          := λ f g, (∑ i, edist (f i) (g i) ^ p) ^ (1/p),
  edist_self     := λ f, by simp [edist, ennreal.zero_rpow_of_pos (pos p),
    ennreal.zero_rpow_of_pos (inv_pos.2 $ pos p)],
  edist_comm     := λ f g, by simp [edist, edist_comm],
  edist_triangle := λ f g h, calc
    (∑ i, edist (f i) (h i) ^ p) ^ (1 / p) ≤
    (∑ i, (edist (f i) (g i) + edist (g i) (h i)) ^ p) ^ (1 / p) :
    begin
      apply ennreal.rpow_le_rpow _ (one_div_nonneg.2 (pos p).le),
      refine finset.sum_le_sum (λ i hi, _),
      exact ennreal.rpow_le_rpow (edist_triangle _ _ _) (pos p).le
    end
    ... ≤
    (∑ i, edist (f i) (g i) ^ p) ^ (1 / p) + (∑ i, edist (g i) (h i) ^ p) ^ (1 / p) :
      ennreal.Lp_add_le _ _ _ fact_one_le_p.out }

local attribute [instance] pi_Lp.pseudo_emetric_aux

/-- Endowing the space `pi_Lp p β` with the `L^p` pseudodistance. This definition is not
satisfactory, as it does not register the fact that the topology, the uniform structure, and the
bornology coincide with the product ones. Therefore, we do not register it as an instance. Using
this as a temporary pseudoemetric space instance, we will show that the uniform structure is equal
(but not defeq) to the product one, and then register an instance in which we replace the uniform
structure and the bornology by the product ones using this pseudometric space,
`pseudo_metric_space.replace_uniformity`, and `pseudo_metric_space.replace_bornology`.

See note [reducible non-instances] -/
@[reducible] def pseudo_metric_aux : pseudo_metric_space (pi_Lp p α) :=
pseudo_emetric_space.to_pseudo_metric_space_of_dist
  (λ f g, (∑ i, dist (f i) (g i) ^ p) ^ (1/p))
  (λ f g, ennreal.rpow_ne_top_of_nonneg (one_div_nonneg.2 (pos p).le) $ ne_of_lt $
    (ennreal.sum_lt_top $ λ i hi, ennreal.rpow_ne_top_of_nonneg (pos p).le (edist_ne_top _ _)))
  (λ f g,
    have A : ∀ i, edist (f i) (g i) ^ p ≠ ⊤,
      from λ i, ennreal.rpow_ne_top_of_nonneg (pos p).le (edist_ne_top _ _),
    have B : edist f g = (∑ i, edist (f i) (g i) ^ p) ^ (1/p), from rfl,
    by simp only [B, dist_edist, ennreal.to_real_rpow, ← ennreal.to_real_sum (λ i _, A i)])

local attribute [instance] pi_Lp.pseudo_metric_aux

lemma lipschitz_with_equiv_aux : lipschitz_with 1 (pi_Lp.equiv p β) :=
begin
  have cancel : p * (1/p) = 1 := mul_div_cancel' 1 (pos p).ne',
  assume x y,
  simp only [edist, forall_prop_of_true, one_mul, finset.mem_univ, finset.sup_le_iff,
             ennreal.coe_one],
  assume i,
  calc
  edist (x i) (y i) = (edist (x i) (y i) ^ p) ^ (1/p) :
    by simp [← ennreal.rpow_mul, cancel, -one_div]
  ... ≤ (∑ i, edist (x i) (y i) ^ p) ^ (1 / p) :
  begin
    apply ennreal.rpow_le_rpow _ (one_div_nonneg.2 $ (pos p).le),
    exact finset.single_le_sum (λ i hi, (bot_le : (0 : ℝ≥0∞) ≤ _)) (finset.mem_univ i)
  end
end

lemma antilipschitz_with_equiv_aux :
  antilipschitz_with ((fintype.card ι : ℝ≥0) ^ (1/p)) (pi_Lp.equiv p β) :=
begin
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one fact_one_le_p.out,
  have nonneg : 0 ≤ 1 / p := one_div_nonneg.2 (le_of_lt pos),
  have cancel : p * (1/p) = 1 := mul_div_cancel' 1 (ne_of_gt pos),
  assume x y,
  simp [edist, -one_div],
  calc (∑ i, edist (x i) (y i) ^ p) ^ (1 / p) ≤
  (∑ i, edist (pi_Lp.equiv p β x) (pi_Lp.equiv p β y) ^ p) ^ (1 / p) :
  begin
    apply ennreal.rpow_le_rpow _ nonneg,
    apply finset.sum_le_sum (λ i hi, _),
    apply ennreal.rpow_le_rpow _ (le_of_lt pos),
    exact finset.le_sup (finset.mem_univ i)
  end
  ... = (((fintype.card ι : ℝ≥0)) ^ (1/p) : ℝ≥0) *
    edist (pi_Lp.equiv p β x) (pi_Lp.equiv p β y) :
  begin
    simp only [nsmul_eq_mul, finset.card_univ, ennreal.rpow_one, finset.sum_const,
      ennreal.mul_rpow_of_nonneg _ _ nonneg, ←ennreal.rpow_mul, cancel],
    have : (fintype.card ι : ℝ≥0∞) = (fintype.card ι : ℝ≥0) :=
      (ennreal.coe_nat (fintype.card ι)).symm,
    rw [this, ennreal.coe_rpow_of_nonneg _ nonneg]
  end
end

lemma aux_uniformity_eq :
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

lemma aux_cobounded_eq :
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

include fact_one_le_p

/-- pseudoemetric space instance on the product of finitely many pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance [Π i, pseudo_emetric_space (β i)] : pseudo_emetric_space (pi_Lp p β) :=
(pseudo_emetric_aux p β).replace_uniformity (aux_uniformity_eq p β).symm

/-- emetric space instance on the product of finitely many emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance [Π i, emetric_space (α i)] : emetric_space (pi_Lp p α) :=
@emetric.of_t0_pseudo_emetric_space (pi_Lp p α) _ pi.t0_space

variables {p β}
lemma edist_eq [Π i, pseudo_emetric_space (β i)] (x y : pi_Lp p β) :
  edist x y = (∑ i, edist (x i) (y i) ^ p) ^ (1/p) := rfl
variables (p β)

/-- pseudometric space instance on the product of finitely many psuedometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance [Π i, pseudo_metric_space (β i)] : pseudo_metric_space (pi_Lp p β) :=
((pseudo_metric_aux p β).replace_uniformity (aux_uniformity_eq p β).symm).replace_bornology $
  λ s, filter.ext_iff.1 (aux_cobounded_eq p β).symm sᶜ

/-- metric space instance on the product of finitely many metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
instance [Π i, metric_space (α i)] : metric_space (pi_Lp p α) := metric.of_t0_pseudo_metric_space _

omit fact_one_le_p
lemma dist_eq {p : ℝ} [fact (1 ≤ p)] {β : ι → Type*}
  [Π i, pseudo_metric_space (β i)] (x y : pi_Lp p β) :
  dist x y = (∑ i : ι, dist (x i) (y i) ^ p) ^ (1/p) := rfl

lemma nndist_eq {p : ℝ} [fact (1 ≤ p)] {β : ι → Type*}
  [Π i, pseudo_metric_space (β i)] (x y : pi_Lp p β) :
  nndist x y = (∑ i : ι, nndist (x i) (y i) ^ p) ^ (1/p) :=
subtype.ext $ by { push_cast, exact dist_eq _ _ }

include fact_one_le_p

lemma lipschitz_with_equiv [Π i, pseudo_emetric_space (β i)] :
  lipschitz_with 1 (pi_Lp.equiv p β) :=
lipschitz_with_equiv_aux p β

lemma antilipschitz_with_equiv [Π i, pseudo_emetric_space (β i)] :
  antilipschitz_with ((fintype.card ι : ℝ≥0) ^ (1/p)) (pi_Lp.equiv p β) :=
antilipschitz_with_equiv_aux p β

/-- seminormed group instance on the product of finitely many normed groups, using the `L^p`
norm. -/
instance semi_normed_group [Π i, semi_normed_group (β i)] : semi_normed_group (pi_Lp p β) :=
{ norm := λf, (∑ i, ∥f i∥ ^ p) ^ (1/p),
  dist_eq := λ x y, by simp [pi_Lp.dist_eq, dist_eq_norm, sub_eq_add_neg],
  .. pi.add_comm_group }

/-- normed group instance on the product of finitely many normed groups, using the `L^p` norm. -/
instance normed_group [Π i, normed_group (α i)] : normed_group (pi_Lp p α) :=
{ ..pi_Lp.semi_normed_group p α }

omit fact_one_le_p
lemma norm_eq {p : ℝ} [fact (1 ≤ p)] {β : ι → Type*}
  [Π i, semi_normed_group (β i)] (f : pi_Lp p β) :
  ∥f∥ = (∑ i, ∥f i∥ ^ p) ^ (1/p) := rfl

lemma nnnorm_eq {p : ℝ} [fact (1 ≤ p)] {β : ι → Type*}
  [Π i, semi_normed_group (β i)] (f : pi_Lp p β) :
  ∥f∥₊ = (∑ i, ∥f i∥₊ ^ p) ^ (1/p) :=
by { ext, simp [nnreal.coe_sum, norm_eq] }

lemma norm_eq_of_nat {p : ℝ} [fact (1 ≤ p)] {β : ι → Type*}
  [Π i, semi_normed_group (β i)] (n : ℕ) (h : p = n) (f : pi_Lp p β) :
  ∥f∥ = (∑ i, ∥f i∥ ^ n) ^ (1/(n : ℝ)) :=
by simp [norm_eq, h, real.sqrt_eq_rpow, ←real.rpow_nat_cast]

lemma norm_eq_of_L2 {β : ι → Type*} [Π i, semi_normed_group (β i)] (x : pi_Lp 2 β) :
  ∥x∥ = sqrt (∑ (i : ι), ∥x i∥ ^ 2) :=
by { rw [norm_eq_of_nat 2]; simp [sqrt_eq_rpow] }

lemma nnnorm_eq_of_L2 {β : ι → Type*} [Π i, semi_normed_group (β i)] (x : pi_Lp 2 β) :
  ∥x∥₊ = nnreal.sqrt (∑ (i : ι), ∥x i∥₊ ^ 2) :=
subtype.ext $ by { push_cast, exact norm_eq_of_L2 x }

lemma dist_eq_of_L2 {β : ι → Type*} [Π i, semi_normed_group (β i)] (x y : pi_Lp 2 β) :
  dist x y = (∑ i, dist (x i) (y i) ^ 2).sqrt :=
by simp_rw [dist_eq_norm, norm_eq_of_L2, pi.sub_apply]

lemma nndist_eq_of_L2 {β : ι → Type*} [Π i, semi_normed_group (β i)] (x y : pi_Lp 2 β) :
  nndist x y = (∑ i, nndist (x i) (y i) ^ 2).sqrt :=
subtype.ext $ by { push_cast, exact dist_eq_of_L2 _ _ }

lemma edist_eq_of_L2 {β : ι → Type*} [Π i, semi_normed_group (β i)] (x y : pi_Lp 2 β) :
  edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : ℝ) :=
by simp_rw [pi_Lp.edist_eq, ennreal.rpow_two]

include fact_one_le_p

variables [normed_field 𝕜]

/-- The product of finitely many normed spaces is a normed space, with the `L^p` norm. -/
instance normed_space [Π i, semi_normed_group (β i)] [Π i, normed_space 𝕜 (β i)] :
  normed_space 𝕜 (pi_Lp p β) :=
{ norm_smul_le :=
  begin
    assume c f,
    have : p * (1 / p) = 1 := mul_div_cancel' 1 (lt_of_lt_of_le zero_lt_one fact_one_le_p.out).ne',
    simp only [pi_Lp.norm_eq, norm_smul, mul_rpow, norm_nonneg, ←finset.mul_sum, pi.smul_apply],
    rw [mul_rpow (rpow_nonneg_of_nonneg (norm_nonneg _) _), ← rpow_mul (norm_nonneg _),
        this, rpow_one],
    exact finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg (norm_nonneg _) _)
  end,
  .. pi.module ι β 𝕜 }

instance finite_dimensional [Π i, semi_normed_group (β i)] [Π i, normed_space 𝕜 (β i)]
  [I : ∀ i, finite_dimensional 𝕜 (β i)] :
  finite_dimensional 𝕜 (pi_Lp p β) :=
finite_dimensional.finite_dimensional_pi' _ _

/- Register simplification lemmas for the applications of `pi_Lp` elements, as the usual lemmas
for Pi types will not trigger. -/
variables {𝕜 p α} [Π i, semi_normed_group (β i)] [Π i, normed_space 𝕜 (β i)] (c : 𝕜)
variables (x y : pi_Lp p β) (x' y' : Π i, β i) (i : ι)

@[simp] lemma zero_apply : (0 : pi_Lp p β) i = 0 := rfl
@[simp] lemma add_apply : (x + y) i = x i + y i := rfl
@[simp] lemma sub_apply : (x - y) i = x i - y i := rfl
@[simp] lemma smul_apply : (c • x) i = c • x i := rfl
@[simp] lemma neg_apply : (-x) i = - (x i) := rfl

variables {ι' : Type*}
variables [fintype ι']

variables (p 𝕜) (E : Type*) [normed_group E] [normed_space 𝕜 E]

/-- An equivalence of finite domains induces a linearly isometric equivalence of finitely supported
functions-/
def _root_.linear_isometry_equiv.pi_Lp_congr_left (e : ι ≃ ι') :
  pi_Lp p (λ i : ι, E) ≃ₗᵢ[𝕜] pi_Lp p (λ i : ι', E) :=
{ to_linear_equiv := linear_equiv.Pi_congr_left' 𝕜 (λ i : ι, E) e,
  norm_map' :=
  begin
    intro x,
    simp only [norm],
    simp_rw linear_equiv.Pi_congr_left'_apply 𝕜 (λ i : ι, E) e x _,
    congr,
    rw fintype.sum_equiv (e.symm),
    exact λ i, rfl,
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

lemma nnnorm_equiv_symm_const {β} [semi_normed_group β] (b : β) :
  ∥(pi_Lp.equiv p (λ _ : ι, β)).symm (function.const _ b)∥₊ = fintype.card ι ^ (1 / p) * ∥b∥₊ :=
begin
  have : p ≠ 0 := (zero_lt_one.trans_le (fact.out $ 1 ≤ p)).ne',
  simp_rw [pi_Lp.nnnorm_eq, equiv_symm_apply, function.const_apply, finset.sum_const,
    finset.card_univ, nsmul_eq_mul, nnreal.mul_rpow, ←nnreal.rpow_mul, mul_one_div_cancel this,
    nnreal.rpow_one],
end

lemma norm_equiv_symm_const {β} [semi_normed_group β] (b : β) :
  ∥(pi_Lp.equiv p (λ _ : ι, β)).symm (function.const _ b)∥ = fintype.card ι ^ (1 / p) * ∥b∥ :=
(congr_arg coe $ nnnorm_equiv_symm_const b).trans $ by simp

lemma nnnorm_equiv_symm_one {β} [semi_normed_group β] [has_one β] :
  ∥(pi_Lp.equiv p (λ _ : ι, β)).symm 1∥₊ = fintype.card ι ^ (1 / p) * ∥(1 : β)∥₊ :=
(nnnorm_equiv_symm_const (1 : β)).trans rfl

lemma norm_equiv_symm_one {β} [semi_normed_group β] [has_one β] :
  ∥(pi_Lp.equiv p (λ _ : ι, β)).symm 1∥ = fintype.card ι ^ (1 / p) * ∥(1 : β)∥ :=
(norm_equiv_symm_const (1 : β)).trans rfl

variables (𝕜 p)

/-- `pi_Lp.equiv` as a linear map. -/
@[simps {fully_applied := ff}]
protected def linear_equiv : pi_Lp p β ≃ₗ[𝕜] Π i, β i :=
{ to_fun := pi_Lp.equiv _ _,
  inv_fun := (pi_Lp.equiv _ _).symm,
  ..linear_equiv.refl _ _}

end pi_Lp
