/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/

import number_theory.padic_int_properties
import topology.discrete_quotient

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure`

## Implementation notes
Removed `weight_space` since `continuous_monoid_hom` now exists. Fixing the convention to be
  `d.coprime p` instead of `d.gcd p = 1`.

## TODO
* Move first two lemmas to right place

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

/-- The product of clopen sets is clopen. -/
lemma is_clopen_prod {α β : Type*} [topological_space α] [topological_space β] {s : set α}
  {t : set β} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s ×ˢ t) :=
  ⟨is_open_prod_iff'.2 (or.inl ⟨(hs).1, (ht).1⟩), is_closed.prod (hs).2 (ht).2⟩

/-- Any singleton in a discrete space is clopen. -/
lemma is_clopen_singleton {α : Type*} [topological_space α] [discrete_topology α] (b : α) :
  is_clopen ({b} : set α) := ⟨is_open_discrete _, is_closed_discrete _⟩

variables (p : ℕ) [fact p.prime] {d : ℕ}

open padic_int

/-- Gives the clopen sets that act as a topological basis for `ℤ_[p]`. -/
abbreviation clopen_basis : set (set ℤ_[p]) := {x : set ℤ_[p] | ∃ (n : ℕ) (a : zmod (p^n)),
  x = set.preimage (padic_int.to_zmod_pow n) {a} }

variable {p}
/-- The clopen sets that form a topological basis for `zmod d × ℤ_[p]`. It is better than
  `clopen_basis` because one need not use `classical.choice`. -/
abbreviation clopen_from {n : ℕ} (a : zmod (d * (p^n))) : set (zmod d × ℤ_[p]) :=
  ({a} : set (zmod d)) ×ˢ ((@padic_int.to_zmod_pow p _ n)⁻¹' {(a : zmod (p^n))})

local attribute [instance] zmod.topological_space

namespace clopen_from

lemma is_clopen {n : ℕ} (a : zmod (d * (p^n))) : is_clopen (clopen_from a) :=
  is_clopen_prod (is_clopen_singleton (a : zmod d)) (proj_lim_preimage_clopen d a)

lemma mem_clopen_from {n : ℕ} (a : zmod (d * p^n)) (y : zmod d × ℤ_[p]) :
  y ∈ (clopen_from a) ↔ y.fst = (a : zmod d) ∧
    (a : zmod (p^n)) = (to_zmod_pow n) y.snd :=
and.congr_right_iff.2 (λ hy, begin
  simp only [set.mem_preimage, set.mem_singleton_iff, set.mem_prod],
  rw eq_comm, end)

lemma self_mem_clopen_from {n : ℕ} (a : zmod (d * p^n)) : (a : zmod d × ℤ_[p]) ∈ clopen_from a :=
(mem_clopen_from _ _).2 ⟨prod.fst_zmod_cast _, begin
  rw [prod.snd_zmod_cast, ←zmod.int_cast_cast a],
  conv_rhs { rw ←zmod.int_cast_cast a, },
  change (int.cast_ring_hom (zmod (p^n))) (a : ℤ) =
    (ring_hom.comp (to_zmod_pow n) (int.cast_ring_hom (ℤ_[p]))) (a : ℤ),
  apply _root_.congr_fun _, congr,
  convert @ring_hom.ext_zmod 0 _ _ _ _, end⟩

end clopen_from

variables (p) (d)
/-- The version of `clopen_basis` that also incorporates `d` coprime to `p`. -/
@[reducible] abbreviation clopen_basis' :=
{ x : set ((zmod d) × ℤ_[p]) | ∃ (n : ℕ) (a : zmod (d * (p^n))), x = clopen_from a }

variables {p} {d}
lemma mem_clopen_basis {n : ℕ} (a : zmod (p^n)) :
  (padic_int.to_zmod_pow n)⁻¹' {a} ∈ (clopen_basis p) := ⟨n, a, rfl⟩

lemma clopen_basis_is_topological_basis : topological_space.is_topological_basis (clopen_basis p) :=
topological_space.is_topological_basis_of_open_of_nhds (λ u ⟨n, a, hu⟩,
  hu.symm ▸ (proj_lim_preimage_clopen_one n a).1)
  (λ a u mema hu, begin
    obtain ⟨ε, hε, h⟩ := (metric.is_open_iff.1 hu) a mema,
    obtain ⟨m, fm⟩ := exists_one_div_pow_lt_of_prime p (half_pos hε),
    set b := ((to_zmod_pow m.succ a) : ℤ_[p]) with hb,
    have arith : -(m : ℤ) = 1 - (m.succ : ℤ),
    { rw [int.coe_nat_succ, sub_add_eq_sub_sub_swap, sub_self, zero_sub], },
    refine ⟨metric.ball b (p^(-(m : ℤ))), _, _, λ c hc, h _⟩,
    { rw [arith, ←preimage_to_zmod_pow_eq_ball (to_zmod_pow m.succ a)],
      refine mem_clopen_basis ((to_zmod_pow m.succ) a), },
    { rw [metric.mem_ball, dist_eq_norm, hb, cast_to_zmod_pow_eq_appr a m.succ],
      refine gt_of_gt_of_ge _ ((norm_le_pow_iff_mem_span_pow _ m.succ).2 (appr_spec m.succ a)),
      rw [zpow_neg, ←one_div, zpow_neg, ←one_div],
      apply one_div_lt_one_div_of_lt,
      { norm_num, refine pow_pos _ m, norm_num, apply nat.prime.pos (fact.out _), apply_instance, },
      { rw zpow_lt_iff_lt _,
        { norm_num, },
        { norm_cast, apply nat.prime.one_lt, apply fact.out, }, }, },
    { simp only [metric.mem_ball, zpow_neg, zpow_coe_nat] at hc,
      simp only [metric.mem_ball],
      suffices f1 : dist c a < 2 / (p^m),
      { refine lt_trans f1 ((lt_div_iff' _).mp ((one_div ((p : ℝ)^m)) ▸ fm)), exact zero_lt_two, },
      have := dist_triangle c a b,
      refine gt_of_gt_of_ge _ (dist_triangle c b a),
      have ha : dist a b ≤ (↑p ^ m)⁻¹,
      { rw [hb, cast_to_zmod_pow_eq_appr a m.succ],
        have : (↑p ^ m)⁻¹ = (p : ℝ)^(-m : ℤ),
        { have f : (p : ℝ) ≠ 0,
          { norm_cast, apply nat.prime.ne_zero, apply fact.out, },
          rw [←one_div _, div_eq_iff _],
          { rw [←zpow_coe_nat (p : ℝ) m, ←zpow_add₀],
            { rw [neg_add_self, zpow_zero _], },
            apply f, },
          { apply pow_ne_zero _, apply f, apply_instance, }, },
        rw this, refine le_trans (dist_appr_spec a m.succ) _,
        { rw zpow_le_iff_le _,
          { apply neg_le_neg, norm_num, },
          { norm_cast, apply nat.prime.one_lt, apply fact.out, }, }, },
      rw dist_comm b a,
      convert add_lt_add_of_lt_of_le hc ha,
      rw [←one_div, div_add_div_same, one_add_one_eq_two], }, end)

theorem clopen_basis_clopen : topological_space.is_topological_basis (clopen_basis p) ∧
  ∀ x ∈ (clopen_basis p), is_clopen x :=
⟨clopen_basis_is_topological_basis, λ x ⟨n, a, hx⟩, hx.symm ▸ (proj_lim_preimage_clopen_one n a)⟩

lemma helper_1 (x : zmod d × ℤ_[p]) (n : ℕ) :
  is_clopen {b : zmod d × ℤ_[p] | (to_zmod_pow n) x.snd = (to_zmod_pow n) b.snd ∧ x.fst = b.fst} :=
begin
  set f : zmod d × ℤ_[p] → zmod d × zmod (p^n) := prod.map id (to_zmod_pow n) with hf,
  convert_to is_clopen (set.preimage f {f x}),
  { ext y,
    rw hf,
    simp only [set.mem_set_of_eq, prod_map, id.def, set.mem_preimage, set.mem_singleton_iff,
      prod.mk.inj_iff],
    rw [and_comm, eq_comm, @eq_comm _ ((to_zmod_pow n) x.snd) _], },
  have cont_f : continuous f := continuous.prod_map (continuous_id) (continuous_to_zmod_pow n),
  refine ⟨continuous_def.mp cont_f {f x} (is_open_discrete {f x}),
    continuous_iff_is_closed.mp cont_f {f x} (is_closed_discrete {f x})⟩,
end

variables (p d)

/-- A discrete quotient induced by `to_zmod_pow`. -/
def discrete_quotient_of_to_zmod_pow : ℕ → discrete_quotient (zmod d × ℤ_[p]) :=
λ n, ⟨λ a b, to_zmod_pow n a.2 = to_zmod_pow n b.2 ∧ a.1 = b.1, ⟨by tauto, by tauto,
  λ a b c hab hbc, ⟨eq.trans hab.1 hbc.1, eq.trans hab.2 hbc.2⟩⟩, λ x, helper_1 x n⟩

variables {p d}

namespace discrete_quotient_of_to_zmod_pow

lemma rel (x y : zmod d × ℤ_[p]) (n : ℕ) :
  (discrete_quotient_of_to_zmod_pow p d n).rel x y ↔
  (to_zmod_pow n) x.snd = (to_zmod_pow n) y.snd ∧ x.fst = y.fst :=
by { rw discrete_quotient_of_to_zmod_pow, }

end discrete_quotient_of_to_zmod_pow

open discrete_quotient_of_to_zmod_pow

/-- Given a natural `n`, takes an element of `zmod d × ℤ_[p]` to `zmod (d * p^n)` using CRT. -/
noncomputable abbreviation prod_padic_to_zmod (n : ℕ) (x : zmod d × ℤ_[p]) (hd : d.coprime p) :
  zmod (d * p^n) :=
(zmod.chinese_remainder (nat.coprime.pow_right _ (nat.coprime_iff_gcd_eq_one.1 hd))).symm
  (x.1, (to_zmod_pow n)x.2)

lemma prod_padic_to_zmod_def (n : ℕ) (x : zmod d × ℤ_[p]) (hd : d.coprime p) :
  prod_padic_to_zmod n x hd = (zmod.chinese_remainder (nat.coprime.pow_right _
  (nat.coprime_iff_gcd_eq_one.1 hd))).symm (x.1, (to_zmod_pow n)x.2) := rfl

/-- Given an open set `U` of `zmod d × ℤ_[p]`, this is the set of all `n` such that
  all clopen sets of level `n` are contained in `U`. -/
def bound_set (U : set (zmod d × ℤ_[p])) (hd : d.coprime p) :=
{n : ℕ | ∀ (a : zmod d × ℤ_[p]) (H : a ∈ U), (clopen_from (prod_padic_to_zmod n a hd)) ⊆ U }

/-- Given a set `U`, it is the infimum of the `bound_set`. It is the least `n` for which all
  clopen basis elements of level `n` and above are contained in `U`. -/
noncomputable def bound (U : set (zmod d × ℤ_[p])) (hd : d.coprime p) : ℕ := Inf (bound_set U hd)

open nat clopen_from

namespace clopen_from

lemma mem_clopen_from' (n : ℕ) (x y : zmod d × ℤ_[p]) (hd : d.coprime p) :
  y ∈ (clopen_from (prod_padic_to_zmod n x hd)) ↔
  (discrete_quotient_of_to_zmod_pow p d n).rel x y :=
begin
  rw [mem_clopen_from, discrete_quotient_of_to_zmod_pow.rel, prod_padic_to_zmod_def],
  refine ⟨λ h, _, λ h, _⟩,
  { rw [and_comm, eq_comm], convert h,
    { apply (proj_fst _ _).symm, },
    { apply (proj_snd _ _).symm, }, },
  { rw [←h.2, ←h.1],
    refine ⟨(proj_fst x (coprime.pow_right n hd)).symm, (proj_snd x (coprime.pow_right n hd))⟩, },
end

lemma mem_clopen_from_prod_padic_to_zmod (n : ℕ) (x : zmod d × ℤ_[p]) (hd : d.coprime p) :
  x ∈ (clopen_from (prod_padic_to_zmod n x hd)) :=
(mem_clopen_from' _ _ _ hd).2 ((discrete_quotient_of_to_zmod_pow p d n).refl x)

lemma mem_clopen_from'' (n : ℕ) (x y : zmod d × ℤ_[p]) (hd : d.coprime p)
  (hy : y ∈ (clopen_from (prod_padic_to_zmod n x hd))) :
  (clopen_from (prod_padic_to_zmod n x hd)) = (clopen_from (prod_padic_to_zmod n y hd)) :=
begin
  ext z,
  repeat { rw mem_clopen_from at *, },
  rw [←hy.1, hy.2, prod_padic_to_zmod_def, proj_fst y (coprime.pow_right n hd),
    proj_snd y (coprime.pow_right n hd)],
end

end clopen_from

namespace discrete_quotient_of_to_zmod_pow
variables (p d)
lemma le_of_ge {k n : ℕ} (h : k ≤ n) :
  (discrete_quotient_of_to_zmod_pow p d n) ≤ (discrete_quotient_of_to_zmod_pow p d k) :=
λ x y hn, begin rw rel at *,
  refine ⟨_, hn.2⟩,
  simp_rw ←cast_to_zmod_pow _ _ h _,
  refine congr_arg _ hn.1, end

variables {p d}
open clopen_from

lemma self_rel_prod_padic_to_zmod (n : ℕ) (x : zmod d × ℤ_[p]) (hd : d.coprime p) :
  (discrete_quotient_of_to_zmod_pow p d n).rel x (prod_padic_to_zmod n x hd) :=
(mem_clopen_from' _ _ _ hd).1 (self_mem_clopen_from _)

end discrete_quotient_of_to_zmod_pow

namespace clopen_from

lemma clopen_sub_clopen {k n : ℕ} (h : k ≤ n) (x : zmod d × ℤ_[p]) (hd : d.coprime p) :
  (clopen_from (prod_padic_to_zmod n x hd)) ⊆ (clopen_from (prod_padic_to_zmod k x hd)) :=
λ z hz, (mem_clopen_from' k x z hd).2 (discrete_quotient_of_to_zmod_pow.le_of_ge p d h x z
  ((mem_clopen_from' n x z hd).1 hz))

end clopen_from

theorem clopen_basis'_topo_basis (hd : d.coprime p) : topological_space.is_topological_basis
  (clopen_basis' p d) :=
begin
  convert (topological_space.is_topological_basis.prod
    (@discrete_topology.is_topological_basis (zmod d) _ _ _) clopen_basis_clopen.1),
  ext V,
  refine ⟨λ ⟨n, w, h⟩, ⟨{(w : zmod d)}, ((to_zmod_pow n) ⁻¹' {↑w}),
    ⟨(w : zmod d), set.singleton_monoid_hom_apply _⟩, ⟨n, (w : zmod (p^n)), rfl⟩,
    by { rw h, }⟩, λ hy, _⟩,
  { rcases hy with ⟨x', y', ⟨x, hx⟩, ⟨n, y, hy⟩, h⟩,
    set U' : set (zmod d × ℤ_[p]) := ({x} : set (zmod d)) ×ˢ ((padic_int.to_zmod_pow n)⁻¹' {y})
      with hU',
    have hU : U' ∈ clopen_basis' p d,
    { refine ⟨n, ((zmod.chinese_remainder (coprime.pow_right n hd)).inv_fun (x, y)), _⟩,
      rw hU',
      congr,
      { apply (proj_fst' (coprime.pow_right _ hd) _ _).symm, },
      { apply (proj_snd' (coprime.pow_right _ hd) _ _).symm, }, },
    { convert hU,
      rw [←h, hU'],
      congr,
      { rw [←hx, set.singleton_monoid_hom_apply], },
      { rw hy, }, }, },
end

lemma clopen_basis'_clopen (U : clopen_basis' p d) : is_clopen U.val :=
begin
  obtain ⟨n, a, h⟩ := U.prop,
  rw [subtype.val_eq_coe, h],
  apply clopen_from.is_clopen,
end

namespace clopen_from
lemma exists_clopen_from_subset {U : set (zmod d × ℤ_[p])} (hU : is_open U) (hd : d.coprime p)
  {x : zmod d × ℤ_[p]} (memU : x ∈ U) : ∃ n : ℕ, (clopen_from (prod_padic_to_zmod n x hd)) ⊆ U :=
begin
  obtain ⟨V, ⟨n, a, H⟩, memV, U_sub_V⟩ :=
    topological_space.is_topological_basis.exists_subset_of_mem_open
    (clopen_basis'_topo_basis hd) memU hU,
  refine ⟨n, λ y hy, U_sub_V _⟩,
  rw [H, mem_clopen_from] at memV,
  rw [mem_clopen_from, prod_padic_to_zmod_def, proj_snd, proj_fst] at hy,
  simp [H, mem_clopen_from, memV, hy],
end

end clopen_from

open clopen_from

lemma bound_set_inhabited [fact (0 < d)] {U : set (zmod d × ℤ_[p])} (hU : is_clopen U)
  (hd : d.coprime p) : (bound_set U hd).nonempty :=
begin
  have com : U ⊆ ⋃ (x : zmod d × ℤ_[p]) (hx : x ∈ U),
  (clopen_from (prod_padic_to_zmod (classical.some (exists_clopen_from_subset hU.1 hd hx)) x hd)),
  { refine λ y hy, set.mem_Union.2 ⟨y, set.mem_Union.2 ⟨hy, _⟩⟩,
    rw [mem_clopen_from, prod_padic_to_zmod_def, proj_fst, proj_snd],
    simp only [eq_self_iff_true, and_self], },
  obtain ⟨t, ht⟩ := is_compact.elim_finite_subcover (compact_of_is_closed_subset compact_univ hU.2
    (set.subset_univ _)) _ _ com,
  { simp only at ht,
    set n : ℕ := Sup ⨆ (x : zmod d × ℤ_[p]) (H : x ∈ t) (hx : x ∈ U),
      {(classical.some (exists_clopen_from_subset hU.1 hd hx))} with hn,
    refine ⟨n, λ y hy, _⟩,
    obtain ⟨z, hz⟩ := set.mem_Union.1 (ht hy),
    obtain ⟨H, hz⟩ := set.mem_Union.1 hz,
    obtain ⟨hz, h⟩ := set.mem_Union.1 hz,
    transitivity (clopen_from (prod_padic_to_zmod (classical.some _) z hd)),
    { rw mem_clopen_from'' _ _ _ hd h,
      apply (clopen_sub_clopen (le_cSup _ _) _ _),
      { refine (set.finite.bdd_above_bUnion (finset.finite_to_set t)).2 (λ i hi,
          (set.finite.bdd_above (set.finite_Union (λ i, set.finite_singleton _)))), },
      { refine set.mem_Union.2 ⟨z, set.mem_Union.2 ⟨H, set.mem_Union.2 ⟨hz, rfl⟩⟩⟩, }, },
    { apply classical.some_spec (exists_clopen_from_subset _ _ hz), }, },
  { refine λ i, is_open_Union (λ hi, (clopen_from.is_clopen _).1), },
end

lemma bound_mem_bound_set [fact(0 < d)] {U : set (zmod d × ℤ_[p])} (hU : is_clopen U)
  (hd : d.coprime p) : bound U hd ∈ bound_set U hd := nat.Inf_mem (bound_set_inhabited hU _)

namespace clopen_from
lemma clopen_from_subset_of_bound_le [fact (0 < d)] {U : set (zmod d × ℤ_[p])}
  (hU : _root_.is_clopen U) (hd : d.coprime p) {x : zmod d × ℤ_[p]} (memU : x ∈ U) (n : ℕ)
  (h : bound U hd ≤ n) : (clopen_from (prod_padic_to_zmod n x hd)) ⊆ U :=
begin
  transitivity (clopen_from (prod_padic_to_zmod (bound U hd) x hd)),
  intros y,
  repeat { rw mem_clopen_from', },
  suffices :  (discrete_quotient_of_to_zmod_pow  p d n) ≤
    (discrete_quotient_of_to_zmod_pow  p d (bound U hd)),
  { apply this x y, },
  { apply discrete_quotient_of_to_zmod_pow.le_of_ge p d h, },
  { apply bound_mem_bound_set hU hd x memU, },
end

/-- The `units` version of `clopen_from` -/
abbreviation units {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  set ((zmod d)ˣ × ℤ_[p]ˣ) :=
({a.1} : set (zmod d)ˣ) ×ˢ ((units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom)⁻¹' {a.2})

lemma is_clopen_units {n : ℕ} (a : (zmod d)ˣ × (zmod (p^n))ˣ) :
  _root_.is_clopen (clopen_from.units a) :=
is_clopen_prod (is_clopen_singleton a.1) (proj_lim_preimage_units_clopen a.2)

end clopen_from

namespace discrete_quotient_of_to_zmod_pow
lemma le {R : Type*} [normed_comm_ring R] [fact (0 < d)]
  (hd : d.coprime p) (f : locally_constant (zmod d × ℤ_[p]) R) :
  ∃ N : ℕ, discrete_quotient_of_to_zmod_pow p d N ≤ f.discrete_quotient :=
begin
  have : ∀ x : R, is_open (f⁻¹' {x}) := λ x, f.is_locally_constant _,
  have pre_univ : f⁻¹' (set.univ : set R) = ⋃ (x : R), f⁻¹' {x},
  { ext y,
    simp only [set.mem_preimage, set.mem_Union, set.mem_univ, set.mem_singleton_iff, exists_eq'], },
  obtain ⟨t, ht⟩ := is_compact.elim_finite_subcover compact_univ _ this
    (set.univ_subset_iff.2 pre_univ.symm),
  set n : ℕ := Sup ⨆ (x : R) (H : x ∈ t), {bound (f⁻¹' {x}) hd} with hn,
  refine ⟨n, λ x y hF, _⟩,
  obtain ⟨i, hi⟩ := set.mem_Union.1 (ht (set.mem_univ x)),
  obtain ⟨hi, htx⟩ := set.mem_Union.1 hi,
  simp only [set.mem_preimage, set.mem_singleton_iff] at htx,
  rw rel at hF,
  change f y = f x,
  rw htx,
  have h1 : y ∈ (clopen_from (prod_padic_to_zmod n x hd)),
  { rw [mem_clopen_from, prod_padic_to_zmod_def, proj_fst, proj_snd],
    simp only [hF, eq_self_iff_true, and_self], },
  rw [←set.mem_singleton_iff, ←set.mem_preimage],
  refine clopen_from.clopen_from_subset_of_bound_le ⟨this i,
    is_closed.preimage (locally_constant.continuous f) (t1_space.t1 i)⟩ hd
    (set.mem_preimage.2 (set.mem_singleton_iff.2 htx)) _ (le_cSup _ _) h1,
  { refine (set.finite.bdd_above_bUnion (finset.finite_to_set t)).2 (λ i hi, bdd_above_singleton), },
  { refine set.mem_Union.2 ⟨i, set.mem_Union.2 ⟨hi, rfl⟩⟩, },
end

end discrete_quotient_of_to_zmod_pow

variables (p d) (R : Type*) [normed_comm_ring R]

open locally_constant

/-- Looking at the set of characteristic functions obtained from the clopen basis. -/
abbreviation char_fn_set : set (locally_constant (zmod d × ℤ_[p]) R) := ⨆ n : ℕ, set.range
  (λ (a : zmod (d * p^n)), char_fn R (clopen_from.is_clopen a))

variables {p d}

lemma mem_char_fn_set (U : clopen_basis' p d) :
  (char_fn R (clopen_basis'_clopen U)) ∈ (char_fn_set p d R) :=
begin
  delta char_fn_set,
  rw [set.supr_eq_Union, set.mem_Union],
  obtain ⟨n, a, hU⟩ := U.prop,
  refine ⟨n, set.mem_range.2 ⟨a, _⟩⟩,
  congr,
  rw [subtype.val_eq_coe, hU],
end

variable {R}
lemma mem_char_fn_set' (x : char_fn_set p d R) : ∃ (i : ℕ) (y : zmod (d * p ^ i)),
  char_fn R (clopen_from.is_clopen y) = x := set.mem_Union.1 x.prop

variable (R)
/-- An equivalence between the clopen basis and the characteristic functions corresponding to it.-/
noncomputable def clopen_char_fn_equiv [nontrivial R] : clopen_basis' p d ≃ char_fn_set p d R :=
{ to_fun := λ U, ⟨(char_fn R (clopen_basis'_clopen U)), mem_char_fn_set R U⟩,
  inv_fun := λ f, ⟨clopen_from (classical.some (classical.some_spec (set.mem_Union.1 f.prop))),
    ⟨classical.some (set.mem_Union.1 f.prop), classical.some (classical.some_spec
      (set.mem_Union.1 f.prop)), rfl⟩ ⟩,
  left_inv := function.left_inverse_iff_comp.mpr (function.funext_iff.2 (λ U, subtype.ext_iff_val.2
    (char_fn_inj R (clopen_from.is_clopen _) (clopen_basis'_clopen U) (classical.some_spec
    (classical.some_spec (set.mem_Union.1 (mem_char_fn_set R U))))))),
  right_inv := function.right_inverse_iff_comp.mpr (begin ext,
    simp only [id.def, function.comp_app, subtype.coe_mk, subtype.val_eq_coe],
    congr,
    refine classical.some_spec (classical.some_spec (mem_char_fn_set' x)), end), }
