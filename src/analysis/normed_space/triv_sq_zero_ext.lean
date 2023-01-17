/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.triv_sq_zero_ext
import analysis.normed_space.basic
import analysis.normed_space.exponential

/-!
# Topology and normed space structure on `triv_sq_zero_ext R M`

The type `triv_sq_zero_ext R M` inherits the topology and (semi)norm structure from `R`, in a way
that is consistent with the norm on complex numbers; that is,
`‖r + m‖^2 = (r + m)*(r - m) = r^2 - r•m + r•m = r^2 = ‖r‖^2`.

## Main results

* `triv_sq_zero_ext.fst_exp`
* `triv_sq_zero_ext.snd_exp`
-/



variables {S R M : Type*}

local notation `tsze` := triv_sq_zero_ext

namespace triv_sq_zero_ext

section topology

instance [topological_space R] : topological_space (tsze R M) :=
topological_space.induced fst ‹_›

lemma nhds_def [topological_space R] (x : tsze R M) : nhds x = (nhds x.fst).comap fst :=
nhds_induced _ _

lemma nhds_inl [topological_space R] [has_zero M] (x : R) :
  nhds (inl x : tsze R M) = (nhds x).comap fst :=
nhds_induced _ _

lemma nhds_inr [topological_space R] [has_zero R] (m : M) :
  nhds (inr m : tsze R M) = (nhds 0).comap fst :=
nhds_induced _ _

lemma continuous_fst [topological_space R] :
  continuous (fst : tsze R M → R) :=
continuous_induced_dom

lemma continuous_inl [topological_space R] [has_zero M] :
  continuous (inl : R → tsze R M) :=
continuous_induced_rng.mpr continuous_id

lemma embedding_inl [topological_space R] [has_zero M] :
  embedding (inl : R → tsze R M) :=
begin
  refine ⟨_, inl_injective⟩,
  rw [inducing_iff, triv_sq_zero_ext.topological_space, induced_compose, fst_comp_inl, induced_id],
end

variables (R M)

/-- `triv_sq_zero_ext.fst` as a continuous linear map. -/
@[simps]
def fst_homL [topological_space R] [comm_semiring R] [add_comm_monoid M] [module R M] :
  tsze R M →L[R] R :=
{ to_fun := fst,
  cont := continuous_fst,
  .. linear_map.fst R R M }

/-- `triv_sq_zero_ext.inl` as a continuous linear map. -/
@[simps]
def inl_homL [topological_space R] [comm_semiring R] [add_comm_monoid M] [module R M] :
  R →L[R] tsze R M :=
{ to_fun := inl,
  cont := continuous_inl,
  .. linear_map.inl R R M }

variables {R M}

instance [topological_space R] [has_add R] [has_continuous_add R] [has_add M] :
  has_continuous_add (tsze R M) :=
⟨continuous_induced_rng.2 $
  (continuous_fst.comp _root_.continuous_fst).add (continuous_fst.comp _root_.continuous_snd)⟩

instance [topological_space R] [has_mul R] [has_add M] [has_smul R M] [has_continuous_mul R] :
  has_continuous_mul (tsze R M) :=
⟨continuous_induced_rng.2 $
  (continuous_fst.comp _root_.continuous_fst).mul (continuous_fst.comp _root_.continuous_snd)⟩

instance [topological_space R] [has_neg R] [has_continuous_neg R] [has_neg M] :
  has_continuous_neg (tsze R M) :=
⟨continuous_induced_rng.2 $ continuous_neg.comp continuous_fst⟩

instance [topological_space R] [semiring R] [add_comm_monoid M] [module R M]
  [topological_semiring R] :
  topological_semiring (tsze R M) :=
{}

instance [topological_space R] [comm_ring R] [add_comm_group M] [module R M]
  [topological_ring R] :
  topological_ring (tsze R M) :=
{}

instance [has_smul S R] [has_smul S M] [topological_space R] [has_continuous_const_smul S R] :
  has_continuous_const_smul S (tsze R M) :=
⟨λ s, continuous_induced_rng.2 $ (continuous_fst).const_smul _⟩

instance [has_smul S R] [has_smul S M] [topological_space R] [topological_space S]
  [has_continuous_smul S R] :
  has_continuous_smul S (tsze R M) :=
⟨continuous_induced_rng.2 $ _root_.continuous_fst.smul (continuous_fst.comp _root_.continuous_snd)⟩

end topology

section norm

instance [has_norm R] : has_norm (tsze R M) :=
{ norm := λ x, ‖x.fst‖ }

lemma norm_def [has_norm R] (x : tsze R M) : ‖x‖ = ‖x.fst‖ := rfl

instance [pseudo_emetric_space R] : pseudo_emetric_space (tsze R M) :=
pseudo_emetric_space.induced triv_sq_zero_ext.fst ‹_›

lemma edist_def [pseudo_emetric_space R] (x y : tsze R M) :
  edist x y = edist x.fst y.fst := rfl

instance [pseudo_metric_space R] : pseudo_metric_space (tsze R M) :=
pseudo_metric_space.induced triv_sq_zero_ext.fst ‹_›

lemma dist_def [pseudo_metric_space R] (x y : tsze R M) :
  dist x y = dist x.fst y.fst := rfl

lemma nndist_def [pseudo_metric_space R] (x y : tsze R M) :
  nndist x y = nndist x.fst y.fst := rfl

instance [seminormed_add_comm_group R] [add_comm_group M] : seminormed_add_comm_group (tsze R M) :=
seminormed_add_comm_group.induced (tsze R M) R (linear_map.fst ℕ R M)

lemma nnnorm_def [seminormed_add_comm_group R] [add_comm_group M] (x : tsze R M) : ‖x‖₊ = ‖x.fst‖₊ :=
rfl

instance [normed_field R] [add_comm_group M] [module R M] :
  normed_space R (tsze R M) :=
{ norm_smul_le := λ r x, normed_space.norm_smul_le r x.1 }

instance [normed_comm_ring R] [add_comm_group M] [module R M] :
  semi_normed_comm_ring (tsze R M) :=
semi_normed_comm_ring.induced (tsze R M) R (fst_hom R M)

instance [normed_field R] [add_comm_group M] [module R M] :
  normed_algebra R (tsze R M) :=
normed_algebra.induced R (tsze R M) R (fst_hom R M)

variables (S R M)

lemma has_sum_inl [topological_space R] [add_comm_monoid R] [add_comm_monoid M]
  {α} {f : α → R} {a : R} (h : has_sum f a) : has_sum (λ x, inl (f x)) (inl a : tsze R M) :=
h.map (⟨inl, inl_zero _, inl_add _⟩ : R →+ tsze R M) continuous_inl

lemma has_sum_fst [topological_space R] [add_comm_monoid R] [add_comm_monoid M]
  {α} {f : α → tsze R M} {a : tsze R M} (h : has_sum f a) : has_sum (λ x, fst (f x)) (fst a : R) :=
h.map (⟨fst, fst_zero, fst_add⟩ : tsze R M →+ R) continuous_fst

lemma summable_inl [topological_space R] [add_comm_monoid R] [add_comm_monoid M]
  {α} (f : α → R) :
  summable (λ a, (inl (f a) : tsze R M)) ↔ summable f :=
(summable.map_iff_of_left_inverse
  (⟨inl, inl_zero _, inl_add _⟩ : R →+ tsze R M) (⟨fst, fst_zero, fst_add⟩ : tsze R M →+ R)
  continuous_inl continuous_fst (λ x, rfl) : _)

lemma has_sum_exp_series [normed_field S] [char_zero S]
  [normed_comm_ring R] [normed_algebra S R] [add_comm_group M] [module R M]
  [module S M] [is_scalar_tower S R M] (x : tsze R M) {a}
  (h : has_sum (λ n, exp_series S R n (λ _, x.fst)) a) :
  has_sum (λ n, exp_series S (tsze R M) n (λ _, x)) (inl a + a • inr x.snd) :=
begin
  simp_rw [exp_series_apply_eq] at *,
  conv {
    congr,
    funext,
    rw [←inl_fst_add_inr_snd_eq (x ^ _), fst_pow, snd_pow, smul_add, ←inr_smul,
      ←inl_smul, nsmul_eq_smul_cast S n, smul_smul, inv_mul_eq_div, ←inv_div, ←smul_assoc,
      inr_smul],
  },
  refine has_sum.add _ _,
  refine has_sum_inl R M h,
  apply has_sum.smul_const,
  rw [←has_sum_nat_add_iff' 1], swap, apply_instance,
  rw [finset.range_one, finset.sum_singleton, nat.cast_zero, div_zero, inv_zero, zero_smul,
    sub_zero],
  simp_rw [←nat.succ_eq_add_one, nat.pred_succ, nat.factorial_succ, nat.cast_mul,
    ←nat.succ_eq_add_one,
    mul_div_cancel_left _ ((@nat.cast_ne_zero S _ _ _).mpr $ nat.succ_ne_zero _)],
  exact h,
end

lemma summable_exp_series [is_R_or_C S]
  [normed_comm_ring R] [complete_space R] [normed_algebra S R] [add_comm_group M] [module R M]
  [module S M] [is_scalar_tower S R M] (x : tsze R M) :
  summable (λ n, exp_series S (tsze R M) n (λ _, x)) :=
⟨_, has_sum_exp_series S R M x $ exp_series_has_sum_exp _⟩

variables {R M}

lemma fst_exp [is_R_or_C S]
  [normed_comm_ring R] [complete_space R] [normed_algebra S R] [add_comm_group M] [module R M]
    [module S M] [is_scalar_tower S R M] (x : tsze R M) :
  fst (exp S x) = exp S x.fst :=
begin
  -- TODO: can we use `map_exp R (fst_hom R M) continuous_fst` here somehow?
  rw [exp_eq_tsum, exp_eq_tsum],
  refine ((fst_homL R M).map_tsum _).trans _,
  { simp_rw ←exp_series_apply_eq,
    exact summable_exp_series S R M x },
  { simp_rw [fst_homL_apply, fst_smul, fst_pow] },
end

lemma snd_exp [is_R_or_C S]
  [normed_comm_ring R] [complete_space R] [normed_algebra S R] [add_comm_group M] [module R M]
    [module S M] [is_scalar_tower S R M] (x : tsze R M) :
  snd (exp S x) = exp S x.fst • x.snd :=
begin
  rw [exp_eq_tsum],
  have := has_sum_exp_series S R M x (exp_series_has_sum_exp _),
  have this' := has_sum_inl R M (has_sum_fst R M this),
  rw [fst_add, inl_add, fst_inl, fst_smul, inl_smul, fst_inr, inl_zero, smul_zero,
    add_zero] at this',
  dsimp only at this',
  replace this := this.sub this', clear this',
  dsimp only at this,
  conv at this in  (exp_series S (tsze R M) _ _) {
    rw [←inl_fst_add_inr_snd_eq (exp_series S (tsze R M) _ _)],

  },
  simp_rw [add_sub_cancel', exp_series_apply_eq, snd_smul, snd_pow] at this,
  dsimp only,
  sorry,
end

end norm

end triv_sq_zero_ext
