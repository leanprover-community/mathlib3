/-
Copyright (c) 2021 Ashwin Iyengar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashwin Iyengar
-/
import analysis.normed_space.basic
import ring_theory.power_series.basic
import analysis.normed_space.nonarchimedean

noncomputable theory
open filter
open mv_power_series

/-- Multivariate restricted power series, where `σ` is the index set of the
variables and `R` is the coefficient ring. This is a formal power series such
that the coefficients tend to 0 with respect to the cofinite filter on `σ → ℕ`. -/
def mv_restricted_power_series (σ R : Type*) [normed_ring R] :=
{f : mv_power_series σ R // tendsto (λ n, coeff R n f) cofinite (nhds 0)}

namespace mv_restricted_power_series

variables {σ R : Type*} [nonarchimedean_normed_ring R]

open nonarchimedean_normed_ring

instance : has_coe (mv_restricted_power_series σ R) (mv_power_series σ R) :=
⟨subtype.val⟩

lemma coe_injective :
  function.injective (coe : mv_restricted_power_series σ R → mv_power_series σ R) :=
subtype.coe_injective

instance : has_zero (mv_restricted_power_series σ R) := ⟨⟨0, tendsto_const_nhds⟩⟩
@[simp, norm_cast] lemma coe_zero :
  (↑(0 : mv_restricted_power_series σ R) : mv_power_series σ R) = 0 := rfl

instance : has_add (mv_restricted_power_series σ R) :=
  ⟨λ f g, ⟨f + g, by simpa using tendsto.add f.prop g.prop⟩⟩
@[simp, norm_cast] lemma coe_add (a b : mv_restricted_power_series σ R):
  (↑(a + b) : mv_power_series σ R) = a + b := rfl
@[simp, norm_cast] lemma coe_sub (a b : mv_restricted_power_series σ R):
  (↑(a + b) : mv_power_series σ R) = a + b := rfl

instance : has_neg (mv_restricted_power_series σ R) :=
  ⟨λ f, ⟨-f, by simpa using tendsto.neg f.prop⟩⟩
@[simp, norm_cast] lemma coe_neg (a : mv_restricted_power_series σ R):
  (↑(-a) : mv_power_series σ R) = -a := rfl

instance : has_scalar R (mv_restricted_power_series σ R) :=
  { smul := λ r f, ⟨r • f, by simpa using tendsto.comp ((mul_left_continuous r).tendsto 0) f.prop⟩ }

instance : add_comm_group (mv_restricted_power_series σ R) :=
  coe_injective.add_comm_group _ rfl coe_add coe_neg

def coe_add_monoid_hom : mv_restricted_power_series σ R →+ mv_power_series σ R :=
  { to_fun := coe,
    map_zero' := coe_zero,
    map_add' := coe_add }

instance : semimodule R (mv_restricted_power_series σ R) :=
  function.injective.semimodule R coe_add_monoid_hom coe_injective (λ _ _, rfl)

@[simp, norm_cast] lemma coe_smul (r : R) (a : mv_restricted_power_series σ R) :
  (↑(r • a) : mv_power_series σ R) = r • a := rfl

def coe_semimodule_hom : mv_restricted_power_series σ R →ₗ[R] mv_power_series σ R :=
  { to_fun := coe,
    map_add' := coe_add,
    map_smul' := coe_smul }

variables (R)

/-- The `n`th coefficient of a multivariate restricted power series.-/
def coeff (n : σ →₀ ℕ) : (mv_restricted_power_series σ R) →ₗ[R] R :=
  (coeff R n).comp coe_semimodule_hom

--@[simp, norm_cast]
--lemma coe_coeff (f : mv_restricted_power_series σ R) (n : σ →₀ ℕ) :
--  coeff R n f = mv_power_series.coeff R n f.val := rfl

/-- The `n`th monomial with coefficient `a` as multivariate restricted power series.-/
def monomial (n : σ →₀ ℕ) : R →ₗ[R] mv_restricted_power_series σ R :=
{ to_fun := λ r, ⟨mv_power_series.monomial R n r,
  begin
    refine tendsto.congr' _ (0 : mv_restricted_power_series σ R).prop,
    refine eventually_eq_of_mem (set.finite.compl_mem_cofinite (set.finite_singleton n)) _,
    intros x hx,
    simp [coeff_monomial_ne hx]
  end⟩,
  map_add' := λ _ _, by simpa only [subtype.ext_iff, subtype.coe_mk, linear_map.map_add],
  map_smul' := λ m r,
    by simp only [subtype.ext_iff, coe_smul, subtype.coe_mk, linear_map.map_smul] }

variables {R}

instance : has_one (mv_restricted_power_series σ R) := ⟨monomial R 0 1⟩
@[simp, norm_cast] lemma coe_one :
  (↑(1 : mv_restricted_power_series σ R) : mv_power_series σ R) = 1 := rfl

@[simp] lemma apply_coeff (n : σ →₀ ℕ) (f : mv_restricted_power_series σ R) :
  f.val n = coeff R n f := rfl

@[ext] lemma ext (f g : mv_restricted_power_series σ R)
  (h : ∀ (n : σ →₀ ℕ), coeff R n f = coeff R n g) :
  f = g := by {ext, exact h n}

lemma ext_iff (f g : mv_restricted_power_series σ R) :
  f = g ↔ ∀ n : σ →₀ ℕ, coeff R n f = coeff R n g :=
⟨λ h _, by {rwa h}, ext f g⟩

lemma nonzero_coeff_of_nonzero (f : mv_restricted_power_series σ R) (h : f ≠ 0) :
  ∃ n, 0 < ∥coeff R n f∥ :=
begin
  rw [ne.def, ext_iff, not_forall] at h,
  cases h with n hn,
  rw [linear_map.map_zero, push_neg.not_eq, ← norm_pos_iff] at hn,
  use n,
  assumption
end

theorem exists_max (f : mv_restricted_power_series σ R) :
  ∃ n, ∀ m, ∥coeff R n f∥ ≥ ∥coeff R m f∥ :=
begin
  cases em (f = 0),
  { simp only [h, linear_map.map_zero, forall_const, ge_iff_le, exists_const] },
  { cases (nonzero_coeff_of_nonzero f h) with n hn,
    suffices w :
      ∃ n₀, ∀ m, ∥coeff R n f∥ ≤ ∥coeff R m f∥ → ∥coeff R m f∥ ≤ ∥coeff R n₀ f∥,
    {
      cases w with nₘ hnₘ,
      use nₘ,
      intro m,
      cases (le_or_gt ∥coeff R m f∥ ∥coeff R n f∥),
      { exact le_trans h_1 (hnₘ n rfl.ge) },
      { exact hnₘ m (le_of_lt h_1) }
    },
    have f_conv := metric.tendsto_nhds.1 f.2 _ hn,
    simp only [not_lt, dist_zero_right, eventually_cofinite] at f_conv,
    have taut : {m : σ →₀ ℕ | ∥coeff R n f∥ ≤ ∥coeff R m f∥}.nonempty :=
      by {use n, rw set.mem_set_of_eq},
    have r := set.finite.exists_maximal_wrt (λ x, ∥coeff R x f∥) _ f_conv taut,
    simp only [exists_prop, set.mem_set_of_eq] at r,
    cases r with n₀ hn₀,
    use n₀,
    intros m hm,
    by_contra,
    rw not_le at h,
    have h₂ := (hn₀.right m hm) (le_of_lt h),
    rw h₂ at h,
    have : ¬∥coeff R m f∥ < ∥coeff R m f∥ := (irrefl ∥coeff R m f∥),
    contradiction
  }
end

def max_index (f : mv_restricted_power_series σ R) : σ →₀ ℕ := classical.some (exists_max f)

lemma max_index_p (f : mv_restricted_power_series σ R) :
  ∀ m, ∥coeff R m f∥ ≤ ∥coeff R (max_index f) f∥ :=
classical.some_spec (exists_max f)

lemma max_index_neg {f : mv_restricted_power_series σ R} :
  ∥coeff R (-f).max_index (-f)∥ = ∥coeff R f.max_index f∥ :=
begin
  have hf := max_index_p f (-f).max_index,
  have hfn := max_index_p (-f) f.max_index,
  simp only [norm_neg, linear_map.map_neg] at hf hfn,
  simp only [norm_neg, linear_map.map_neg],
  rw ← not_lt at hfn,
  exact eq_iff_le_not_lt.2 ⟨hf, hfn⟩,
end

lemma mul_coeff_le (f g : mv_restricted_power_series σ R) (n : σ →₀ ℕ) :
  ∃ w : (σ →₀ ℕ) × (σ →₀ ℕ),
    ∥mv_power_series.coeff R n (f.val * g.val)∥ ≤ (∥coeff R w.1 f∥ * ∥coeff R w.2 g∥)
      ∧ w ∈ n.antidiagonal.support :=
begin
  obtain ⟨w, s, h⟩ := ultrametric n.antidiagonal.support (λ x, (coeff R x.1 f) * (coeff R x.2 g)),
  use w,
  rw coeff_mul,
  exact ⟨le_trans h.1 (norm_mul_le _ _), s⟩,
  use ⟨n, 0⟩,
  rw finsupp.mem_antidiagonal_support,
  simp,
end

instance : has_mul (mv_restricted_power_series σ R) :=
  ⟨λ f g, ⟨f * g, begin
  simp only [metric.tendsto_nhds, gt_iff_lt, not_lt, dist_zero_right, eventually_cofinite],
  intros ε ε_nonzero,
  cases em (f = 0 ∨ g = 0) with is_zero is_nonzero,
  { cases is_zero,
    simp only [is_zero, coeff_zero, norm_zero, coe_zero, mul_zero],
    refine set.finite_empty.subset _,
    refine eq.subset _,
    rw set.eq_empty_iff_forall_not_mem,
    simp [ε_nonzero],
    simp only [is_zero, coeff_zero, norm_zero, coe_zero, mul_zero],
    refine set.finite_empty.subset _,
    refine eq.subset _,
    rw set.eq_empty_iff_forall_not_mem,
    simp [ε_nonzero] },
  { rw not_or_distrib at is_nonzero,

    cases (exists_max f) with nfₘ hnfₘ,
    cases (nonzero_coeff_of_nonzero f is_nonzero.1) with nf hnf,
    have f_cond : ε / ∥coeff R nfₘ f∥ > 0 := div_pos ε_nonzero (lt_of_lt_of_le hnf (hnfₘ nf)),

    cases (nonzero_coeff_of_nonzero g is_nonzero.2) with ng hng,
    cases (exists_max g) with ngₘ hngₘ,
    have g_cond : ε / ∥coeff R ngₘ g∥ > 0 := div_pos ε_nonzero (lt_of_lt_of_le hng (hngₘ ng)),

    have f_conv := (metric.tendsto_nhds.1 f.prop) (ε / ∥coeff R ngₘ g∥) g_cond,
    have g_conv := (metric.tendsto_nhds.1 g.prop) (ε / ∥coeff R nfₘ f∥) f_cond,

    refine (set.finite.image2 (+) f_conv g_conv).subset _,
    rw set.subset_def,
    intros x h,
    simp only [set.mem_add, set.image2_add, not_lt, dist_zero_right, exists_and_distrib_left,
               set.mem_set_of_eq, set.mem_compl_eq],
    obtain ⟨w, hw, supp⟩ := mul_coeff_le f g x,
    use w.1,
    have hf := le_trans (le_trans h hw) (mul_le_mul_of_nonneg_left (hngₘ w.2) (norm_nonneg _)),
    split,
    { refine (div_le_iff _).mpr hf,
      exact gt_of_ge_of_gt (hngₘ ng) hng },
    { use w.2,
      have hg := le_trans (le_trans h hw) (mul_le_mul_of_nonneg_right (hnfₘ w.1) (norm_nonneg _)),
      split,
      { rw mul_comm at hg,
        refine (div_le_iff _).mpr hg,
        exact gt_of_ge_of_gt (hnfₘ nf) hnf },
      { rw finsupp.mem_antidiagonal_support at supp,
        exact supp } }
  }
end⟩⟩
@[simp, norm_cast] lemma coe_mul (a b : mv_restricted_power_series σ R):
  (↑(a * b) : mv_power_series σ R) = a * b := rfl

instance : ring (mv_restricted_power_series σ R) :=
function.injective.ring
  (coe : mv_restricted_power_series σ R → mv_power_series σ R)
  coe_injective
  coe_zero
  coe_one
  coe_add
  coe_mul
  coe_neg

instance {R : Type*} [nonarchimedean_normed_comm_ring R] :
  comm_ring (mv_restricted_power_series σ R) :=
{ mul_comm := λ a b, by simp only [subtype.ext_iff, coe_mul, mul_comm],
  .. mv_restricted_power_series.ring }

instance : has_norm (mv_restricted_power_series σ R) := ⟨λ f, ∥coeff R (max_index f) f∥⟩

lemma norm_nonneg' (f : mv_restricted_power_series σ R) : 0 ≤ ∥f∥ :=
begin
  unfold norm,
  exact norm_nonneg _,
end

lemma ultrametric_inequality' (f g : mv_restricted_power_series σ R) : ∥f + g∥ ≤ (max ∥f∥ ∥g∥) :=
begin
  unfold norm,
  rw le_max_iff,
  cases le_max_iff.1
        (ultrametric_inequality (coeff R (f + g).max_index f) (coeff R (f + g).max_index g)),
  { left, exact le_trans h (max_index_p f (f + g).max_index) },
  { right, exact le_trans h (max_index_p g (f + g).max_index) }
end

instance : has_dist (mv_restricted_power_series σ R) := ⟨λ x y, ∥x - y∥⟩

instance : metric_space (mv_restricted_power_series σ R) :=
{ dist_self := λ x, begin unfold dist, rw sub_self, unfold norm, simp end,
  eq_of_dist_eq_zero := λ f g, begin
    unfold dist,
    unfold norm,
    intro h,
    simp only [norm_eq_zero, linear_map.map_sub] at h,
    ext,
    have h1 := max_index_p (f - g) n,
    simp only [h, norm_zero, linear_map.map_sub, norm_le_zero_iff] at h1,
    exact sub_eq_zero.mp h1
  end,
  dist_comm := λ x y, begin
    unfold dist,
    unfold norm,
    have hyp : x - y = -(y - x) := by simp only [neg_sub],
    rw [hyp, max_index_neg],
  end,
  dist_triangle := λ x y z, begin
    unfold dist,
    have hyp := ultrametric_inequality' (x - y) (y - z),
    simp only [sub_add_sub_cancel, le_max_iff] at hyp,
    cases hyp,
    { refine le_trans hyp _, rw le_add_iff_nonneg_right, exact norm_nonneg' _ },
    { refine le_trans hyp _, rw le_add_iff_nonneg_left, exact norm_nonneg' _ },
  end }

instance : normed_ring (mv_restricted_power_series σ R) :=
{ dist_eq := λ _ _, rfl,
  norm_mul := λ f g, begin
    unfold norm,
    obtain ⟨w, hw, _⟩ := mul_coeff_le f g (f * g).max_index,
    refine le_trans hw _,
    exact mul_le_mul (f.max_index_p w.1) (g.max_index_p w.2) (norm_nonneg _) (norm_nonneg _),
  end }

instance : nonarchimedean_normed_ring (mv_restricted_power_series σ R) :=
{ ultrametric_inequality := ultrametric_inequality' }

end mv_restricted_power_series
