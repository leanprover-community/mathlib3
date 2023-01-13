/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
--import number_theory.L_functions
--import ring_theory.witt_vector.teichmuller
import number_theory.zmod_properties
--import data.nat.modeq
--import topology.discrete_quotient
--import data.set.prod
--import algebra.order.sub
--import algebra.pointwise
--import data.real.basic
--import topology.algebra.continuous_monoid_hom

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
* Separate into different files : `padic_int_properties`, `zmod_properties`,
  `dirichlet_char_properties`, and `teich_char_properties`
* Delete `pri_dir_char_extend'` and replace with `dirichlet_char_extend`

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

lemma discrete_topology.is_topological_basis {α : Type*} [topological_space α]
  [discrete_topology α] [monoid α] :
  @topological_space.is_topological_basis α _ (set.range set.singleton_monoid_hom) :=
  topological_space.is_topological_basis_of_open_of_nhds (λ u hu, is_open_discrete u)
    (λ  a u mema openu, ⟨({a} : set α), ⟨a, rfl⟩,
      set.mem_singleton a, set.singleton_subset_iff.2 mema⟩)

variables {p : ℕ} [fact p.prime]

namespace padic_int

lemma unit_pow_eq_one (a : units ℤ_[p]) :
  (padic_int.to_zmod (a : ℤ_[p]))^(p - 1) = (1 : (zmod p)) :=
begin
  -- applying FLT
  apply zmod.pow_card_sub_one_eq_one,
  rw [← ring_hom.coe_monoid_hom, ← units.coe_map],
  apply units.ne_zero _,
  apply_instance,
end

/-- The ideal p^n ℤ_[p] is the closed ball B(0, 1/p^n) -/
lemma span_eq_closed_ball (n : ℕ) :
  metric.closed_ball 0 (1/p^n) = (@ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : set ℤ_[p]) :=
begin
  ext,
  simp only [one_div, dist_zero_right, metric.mem_closed_ball, set_like.mem_coe],
  rw ←padic_int.norm_le_pow_iff_mem_span_pow, simp,
end

variable (p)
/-- The ideal p^n ℤ_[p] is closed -/
lemma is_closed_span (n : ℕ) : is_closed (@ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : set ℤ_[p]) :=
(@span_eq_closed_ball p _ n) ▸ metric.is_closed_ball

variable {p}
/-- The ideal p^n ℤ_[p] is the open ball B(0, 1/p^(1 - n)) -/
lemma span_eq_open_ball (n : ℕ) :
  metric.ball 0 ((p : ℝ) ^ (1 - (n : ℤ))) = (@ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : set ℤ_[p]) :=
begin
  ext,
  simp only [mem_ball_zero_iff, set_like.mem_coe],
  rw [←padic_int.norm_le_pow_iff_mem_span_pow, padic_int.norm_le_pow_iff_norm_lt_pow_add_one,
    sub_eq_neg_add 1 (n : ℤ)],
end

variable (p)
/-- The ideal p^n ℤ_[p] is open -/
lemma is_open_span (n : ℕ) : is_open ((ideal.span {p ^ n} : ideal ℤ_[p]) : set ℤ_[p]) :=
(@span_eq_open_ball p _ n) ▸ metric.is_open_ball

/-- The ideal p^n ℤ_[p] is clopen -/
lemma is_clopen_span (n : ℕ) : is_clopen ((ideal.span {p ^ n} : ideal ℤ_[p]) : set ℤ_[p]) :=
⟨is_open_span p n, is_closed_span p n⟩

variable {p}
-- enable set addition for additive groups
open_locale pointwise
open zmod

-- this is more generally a property of profinite groups
lemma preimage_to_zmod_pow {n : ℕ} (x : zmod (p^n)) : (@to_zmod_pow p _ n) ⁻¹' {x} =
 {(x : ℤ_[p])} + (((@to_zmod_pow p _ n).ker : ideal ℤ_[p]) : set ℤ_[p]) :=
begin
  ext y,
  simp only [set.image_add_left, set.mem_preimage, set.singleton_add, set.mem_singleton_iff,
    set_like.mem_coe, ring_hom.mem_ker, neg_add_eq_zero, ring_hom.map_add, ring_hom.map_neg,
    ring_hom_map_cast],
  rw eq_comm,
end

/-- The map `to_zmod_pow` is continuous. -/
lemma continuous_to_zmod_pow (n : ℕ) : continuous (@padic_int.to_zmod_pow p _ n) :=
topological_space.is_topological_basis.continuous discrete_topology.is_topological_basis _
  (λ s ⟨x, hx⟩, begin
    change {x} = s at hx,
    rw [←hx, preimage_to_zmod_pow, ker_to_zmod_pow],
    refine is_open.add_left (is_open_span p n), end )

variable (d : ℕ)

/-- The preimage of any singleton under `to_zmod_pow` is clopen. -/
lemma proj_lim_preimage_clopen {n : ℕ} (a : zmod (d*(p^n))) :
  is_clopen (set.preimage (padic_int.to_zmod_pow n) {a} : set ℤ_[p]) :=
⟨continuous_def.mp (continuous_to_zmod_pow n) {a} trivial,
  continuous_iff_is_closed.mp (continuous_to_zmod_pow n) {a} (is_closed_discrete {a})⟩

/-- The preimage of any singleton under `to_zmod_pow` is clopen. -/
lemma proj_lim_preimage_clopen_one (n : ℕ) (a : zmod (p^n)) :
  is_clopen (set.preimage (padic_int.to_zmod_pow n) {a} : set ℤ_[p]) :=
by { have := proj_lim_preimage_clopen 1 a, rw one_mul at this, convert this, simp, }

lemma singleton_add_ball {S : Type*} [normed_group S] (x y : S) (r : ℝ) :
  ({x} : set S) + metric.ball y r = metric.ball (x + y) r :=
begin
  ext z,
  have : dist (-x + z) y = dist z (x + y),
  { simp_rw [dist_eq_norm],
    refine congr_arg _ _,
    rw [← sub_sub, sub_eq_add_neg z x, add_comm z _], },
  simp [this, add_comm],
end

/-- The preimage of a singleton x is a ball centered at x. -/
lemma preimage_to_zmod_pow_eq_ball {n : ℕ} (x : zmod (p^n)) :
  (padic_int.to_zmod_pow n) ⁻¹' {(x : zmod (p^n))} =
  metric.ball (x : ℤ_[p]) ((p : ℝ) ^ (1 - (n : ℤ))) :=
by { rw [preimage_to_zmod_pow, ker_to_zmod_pow, ←span_eq_open_ball, singleton_add_ball, add_zero], }

open nat

lemma cast_to_zmod_pow_eq_appr (a : ℤ_[p]) (n : ℕ) : ((to_zmod_pow n a) : ℤ_[p]) = a.appr n :=
begin
  dsimp [to_zmod_pow, to_zmod_hom], rw ←zmod.nat_cast_comp_val ℤ_[p],
  { simp only [nat.cast_inj], apply zmod.val_cast_of_lt (appr_lt _ _), },
  exact fact.pow.pos,
end

variable (p)
lemma exists_one_div_pow_lt_of_prime {ε : ℝ} (h : (0 < ε)) : ∃ (n : ℕ), (1 / (p^n) : ℝ) < ε :=
begin
  convert exists_pow_lt_of_lt_one h _,
  swap, { exact 1/p, },
  { simp only [one_div, inv_pow], },
  rw div_lt_iff _,
  { simp only [one_mul, one_lt_cast], apply nat.prime.one_lt (fact.out _), assumption, },
  simp only [cast_pos], apply nat.prime.pos (fact.out _), assumption,
end

variable {p}
lemma dist_appr_spec (a : ℤ_[p]) (n : ℕ) : dist a ((a.appr n) : ℤ_[p]) ≤ (p : ℝ)^(-n : ℤ) :=
(dist_eq_norm a (a.appr n)).symm ▸ ((norm_le_pow_iff_mem_span_pow _ _).2 (appr_spec n a))

instance [fact (0 < d)] : compact_space (zmod d) := fintype.compact_space

lemma totally_bounded : totally_bounded (λ (x : ℚ_[p]), ∥x∥ ≤ 1) :=
metric.totally_bounded_of_finite_discretization (λ ε hε, begin
  obtain ⟨m, fm⟩ := exists_one_div_pow_lt_of_prime p (half_pos hε),
  have f : (2 : ℝ) / (p^m) = (1 / (p^m)) + (1 : ℝ) / (p^m), { rw ← _root_.add_div, refl, },
  have fm' : (2 : ℝ)/(p^m) < ε, { rw [f, ← add_halves ε], apply add_lt_add fm fm, },
  have f' : ↑p ^ (1 - (m.succ : ℤ)) = (1 : ℝ) / (p^m),
  { symmetry, rw [div_eq_iff _, ←zpow_coe_nat, ← zpow_add₀ _],
    norm_num, rw sub_add, rw add_sub_cancel', rw sub_self, rw zpow_zero,
    any_goals { apply pow_ne_zero, },
    all_goals { norm_cast, apply nat.prime.ne_zero, apply fact.out, }, },
  have f'' : ↑p ^ -(m.succ : ℤ) < (1 : ℝ) / (p^m),
  { rw div_eq_inv_mul, rw mul_one, rw zpow_neg, rw inv_lt_inv,
    { rw zpow_coe_nat, apply pow_lt_pow _ (lt_add_one _), norm_cast,
      apply nat.prime.one_lt (fact.out _), assumption, },
    any_goals { norm_cast, apply pow_pos, apply nat.prime.pos, rw fact_iff at *, assumption, }, },
  refine ⟨zmod (p^m.succ), @zmod.fintype _ fact.pow.pos, to_zmod_pow m.succ, λ x y h,
    lt_trans (gt_of_gt_of_ge _ (dist_triangle x (appr y m.succ) y)) fm'⟩,
  rw [←set.mem_singleton_iff, ←set.mem_preimage, preimage_to_zmod_pow_eq_ball, metric.mem_ball,
    cast_to_zmod_pow_eq_appr, f'] at h,
  rw [f, dist_comm _ ↑y, add_comm (dist _ _) _],
  have := add_lt_add (gt_of_gt_of_ge f'' (ge_iff_le.2 (dist_appr_spec y (m.succ)))) h,
  rw [subtype.dist_eq y _, subtype.dist_eq x _, padic_int.coe_coe] at this,
  exact this, end)

instance : compact_space ℤ_[p] := is_compact_iff_compact_space.mp
  (compact_iff_totally_bounded_complete.mpr ⟨totally_bounded,
  complete_space_coe_iff_is_complete.mp (show complete_space ℤ_[p], from infer_instance)⟩)

-- this implies tot disc, hence `ℤ_[p]` is profinite!
instance : totally_separated_space ℤ_[p] :=
{ is_totally_separated_univ := λ x hx y hx ne, begin
    obtain ⟨n,hn⟩ : ∃ (n : ℕ), to_zmod_pow n x ≠ to_zmod_pow n y,
    { contrapose ne, push_neg at ne, rw ext_of_to_zmod_pow at ne,
      simp only [ne, _root_.ne.def, eq_self_iff_true, not_true, not_false_iff], },
    obtain ⟨u, v, hu, hv, memu, memv, univ, disj⟩ :=
      (totally_separated_space.is_totally_separated_univ (zmod (p ^ n))) (to_zmod_pow n x)
      (set.mem_univ _) (to_zmod_pow n y) (set.mem_univ _) hn,
    refine ⟨(to_zmod_pow n)⁻¹' u, (to_zmod_pow n)⁻¹' v,
      continuous_def.mp (continuous_to_zmod_pow n) u hu,
      continuous_def.mp (continuous_to_zmod_pow n) v hv,
      set.mem_preimage.mpr memu, set.mem_preimage.mpr memv, λ z hz, _, _⟩,
    { rw set.mem_union,
      have univ' := univ (set.mem_univ (to_zmod_pow n z)),
      cases univ',
      { left, apply set.mem_preimage.mpr univ', },
      { right, apply set.mem_preimage.mpr univ', }, },
    { ext z,
      rw [←@set.preimage_empty _ _ (to_zmod_pow n), set.mem_preimage],
      rw set.ext_iff at disj, specialize disj (to_zmod_pow n z),
      simp only [set.mem_inter_eq, set.mem_preimage, set.mem_empty_eq, iff_false, not_and],
      simp only [set.mem_inter_eq, set.mem_empty_eq, iff_false, not_and] at disj, assumption, },
    end, }

lemma proj_lim_preimage_clopen' {n : ℕ} (a : zmod (p^n)) :
  is_clopen (set.preimage (padic_int.to_zmod_pow n) {a} : set ℤ_[p]) :=
⟨continuous_def.mp (continuous_to_zmod_pow n) {a} trivial,
  continuous_iff_is_closed.mp (continuous_to_zmod_pow n) {a} (by simp)⟩

variables {p}

lemma ball_mem_unit {x z : ℤ_[p]} (hx : is_unit x) {r : ℝ} (memz : z ∈ metric.ball x r)
  (le_one : r ≤ 1) : is_unit z :=
begin
  rw [is_unit_iff, ←(is_unit_iff.1 hx), ←norm_neg x],
  apply norm_eq_of_norm_add_lt_right,
  rw [norm_neg x, ←sub_eq_add_neg, is_unit_iff.1 hx],
  refine gt_of_ge_of_gt le_one (dist_eq_norm z x ▸ metric.mem_ball.1 memz),
end

lemma inv_mem_inv_ball {x z : units ℤ_[p]} {r : ℝ} (h : r ≤ 1) (hz : z.val ∈ metric.ball x.val r) :
  z.inv ∈ metric.ball x.inv r :=
begin
  rw mem_ball_iff_norm,
  suffices : ∥z.val * x.val∥ * ∥z.inv - x.inv∥ < r,
  { rw [padic_int.norm_mul, is_unit_iff.1 (ball_mem_unit (units.is_unit _) hz h),
      units.val_eq_coe, is_unit_iff.1 (units.is_unit x), one_mul, one_mul] at this,
    exact this, },
  { rw [←padic_int.norm_mul, mul_sub, mul_right_comm, mul_assoc _ x.val _, units.val_inv,
      units.val_inv, one_mul, mul_one, norm_sub_rev],
    exact mem_ball_iff_norm.1 hz, },
end

lemma top_eq_if_cont_inv' {α : Type*} [topological_space α] [monoid α]
 (h : @continuous _ _ (topological_space.induced (units.coe_hom α) infer_instance)
  infer_instance (@units.inv α _)) :
  topological_space.induced (units.coe_hom α) infer_instance ≤ units.topological_space :=
continuous_iff_le_induced.1 begin
  -- if I replace this with refine or try to bring it into term mode, I get an incorrect typeclass
  -- instance synthesized error
  apply continuous.prod_mk continuous_induced_dom (continuous.comp mul_opposite.continuous_op _),
  { convert h, }, end

lemma cont_inv : @continuous _ _ (topological_space.induced (units.coe_hom ℤ_[p]) infer_instance)
  infer_instance (@units.inv ℤ_[p] _) :=
  begin
  -- it is very hard to work in term mode because Lean always infers the incorrect topological
  -- structure on the units
  rw continuous_def, intros s hs,
  rw is_open_iff_forall_mem_open,
  rintros x hx,
  rw metric.is_open_iff at hs,
  obtain ⟨r, r_pos, hs⟩ := hs _ hx,
  by_cases r ≤ 1,
  { refine ⟨(units.inv)⁻¹' metric.ball x.inv r, λ z hz, hs hz, is_open_induced_iff.2
      ⟨metric.ball x.val r, metric.is_open_ball, _⟩, metric.mem_ball_self r_pos⟩,
    ext z,
    rw [set.mem_preimage, set.mem_preimage],
    refine ⟨λ hz, inv_mem_inv_ball h hz, λ hz, _⟩,
    repeat { rw [units.inv_eq_coe_inv, ←units.val_eq_coe] at hz },
    rw [←inv_inv x, ←inv_inv z],
    apply inv_mem_inv_ball h hz, },
  { refine ⟨(units.inv)⁻¹' metric.ball x.inv 1, λ z hz, hs (metric.ball_subset_ball (le_of_lt
      (not_le.1 h)) hz), is_open_induced_iff.2 ⟨metric.ball x.val 1, metric.is_open_ball, _⟩,
      metric.mem_ball_self (zero_lt_one)⟩,
    ext z,
    rw [set.mem_preimage, set.mem_preimage],
    refine ⟨λ hz, inv_mem_inv_ball rfl.ge hz, λ hz, _⟩,
    repeat { rw [units.inv_eq_coe_inv, ←units.val_eq_coe] at hz, },
    rw [←inv_inv x, ←inv_inv z],
    convert inv_mem_inv_ball (rfl.ge) hz, rw inv_inv, },
end

lemma top_eq_iff_cont_inv {α : Type*} [monoid α] [topological_space α] :
  topological_space.induced (units.coe_hom α) infer_instance = units.topological_space ↔
    @continuous _ _ (topological_space.induced (units.coe_hom α) infer_instance)
      infer_instance (@units.inv α _) :=
begin
  refine ⟨λ h, _, λ h,
    le_antisymm (top_eq_if_cont_inv' h) (continuous_iff_le_induced.1 units.continuous_coe)⟩,
  { rw h,
    have h1 : prod.snd ∘ (units.embed_product α) = mul_opposite.op ∘ units.val ∘ units.has_inv.inv,
    { ext,
      rw units.embed_product,
      simp only [function.comp_app, units.val_eq_coe, monoid_hom.coe_mk], },
    have h2 : continuous (prod.snd ∘ (units.embed_product α)) :=
      continuous.comp continuous_snd continuous_induced_dom,
    rw h1 at h2,
    have h3 := continuous.comp (@mul_opposite.continuous_unop α _) h2,
    -- cant substitute h3 as it is, get errors
    exact h3, },
end

lemma is_open_coe : is_open_map (coe : units ℤ_[p] → ℤ_[p]) := λ U hU,
begin
  rw ←(top_eq_iff_cont_inv.2 cont_inv) at hU, -- need this!
  rw is_open_induced_iff at hU,
  rcases hU with ⟨t, ht, htU⟩,
  refine is_open_iff_forall_mem_open.2 (λ x hx, _),
  rcases hx with ⟨y, hy, hyx⟩,
  have memt : x ∈ t,
  { rw [←htU, set.mem_preimage, units.coe_hom_apply, hyx] at hy,
    apply hy, },
  rw metric.is_open_iff at ht,
  obtain ⟨r, r_pos, ht⟩ := ht x memt,
  have is_unit_x : is_unit x,
  { rw ←hyx, simp only [units.is_unit], },
  by_cases r ≤ 1,
  { refine ⟨metric.ball x r, λ z hz, ⟨is_unit.unit (ball_mem_unit is_unit_x hz h), htU ▸ (ht hz),
      is_unit.unit_spec (ball_mem_unit is_unit_x hz h)⟩, metric.is_open_ball,
      metric.mem_ball_self r_pos⟩, },
  { refine ⟨metric.ball x 1, λ z hz, ⟨is_unit.unit (ball_mem_unit is_unit_x hz le_rfl),
      htU ▸ (ht ((metric.ball_subset_ball (le_of_lt (not_le.1 h))) hz)), is_unit.unit_spec
      (ball_mem_unit is_unit_x hz le_rfl)⟩, metric.is_open_ball, metric.mem_ball_self zero_lt_one⟩, },
end

lemma is_open_coe' : is_open_map (coe : units (zmod d) → zmod d) :=
inducing.is_open_map { induced := (top_eq_iff_cont_inv.2 begin
  convert continuous_of_discrete_topology, apply discrete_topology_induced,
  exact units.ext, end).symm } trivial

lemma is_closed_coe : is_closed (set.range (coe : units ℤ_[p] → ℤ_[p])) :=
begin
  have : set.range (coe : units ℤ_[p] → ℤ_[p]) = set.preimage norm {1},
  { ext x,
    simp only [set.mem_range, set.mem_preimage, set.mem_singleton_iff],
    rw ←is_unit_iff,
    refine ⟨λ h, h.some_spec ▸ (units.is_unit h.some), λ h, ⟨is_unit.unit h, is_unit.unit_spec _⟩⟩, },
  { refine this.symm ▸ continuous_iff_is_closed.mp continuous_norm {1} (t1_space.t1 1), },
end

lemma emb_coe : embedding (coe : units ℤ_[p] → ℤ_[p]) :=
{ induced := (top_eq_iff_cont_inv.2 cont_inv).symm,
  inj := units.ext, }

lemma open_embedding_coe : open_embedding (coe : ℤ_[p]ˣ → ℤ_[p]) :=
⟨emb_coe, (is_open_coe).is_open_range⟩

instance : compact_space ℤ_[p]ˣ :=
{ compact_univ := (embedding.is_compact_iff_is_compact_image emb_coe).2
   (compact_of_is_closed_subset compact_univ
   ((@set.image_univ ℤ_[p]ˣ ℤ_[p] coe).symm ▸ is_closed_coe) (set.subset_univ _)) }

instance : t2_space ℤ_[p]ˣ := embedding.t2_space emb_coe

instance : totally_disconnected_space ℤ_[p]ˣ :=
{ is_totally_disconnected_univ := embedding.is_totally_disconnected emb_coe
    (is_totally_disconnected_of_totally_disconnected_space (coe '' set.univ)) }

open_locale pointwise -- needed for has_add (set ℤ_[p])

lemma preimage_to_zmod (x : zmod p) : (@to_zmod p _) ⁻¹' {x} =
 {(x : ℤ_[p])} + (((@to_zmod p _).ker : ideal ℤ_[p]) : set ℤ_[p]) :=
begin
 ext y,
  simp only [set.image_add_left, set.mem_preimage, set.singleton_add,
    set.mem_singleton_iff, set_like.mem_coe],
  refine ⟨λ h, _, λ h, _⟩,
  { simp only [ring_hom.mem_ker, map_add, map_neg, ring_hom_map_cast, neg_add_eq_zero, h.symm], },
  { simp only [ring_hom.mem_ker, map_add, map_neg, ring_hom_map_cast, neg_add_eq_zero] at h,
    exact h.symm, },
end

lemma continuous_to_zmod : continuous (@padic_int.to_zmod p _) :=
topological_space.is_topological_basis.continuous discrete_topology.is_topological_basis _ (λ s hs,
  begin
  cases hs with x hx,
  change {x} = s at hx,
  rw [←hx, preimage_to_zmod, ker_to_zmod],
  refine is_open.add_left _,
  convert is_open_span p 1,
  rw [pow_one, maximal_ideal_eq_span_p], end)

lemma is_unit_padic_of_is_unit_zmod {x : ℕ} (hx : is_unit (x : zmod p)) (h : x.coprime p) :
  is_unit (x : ℤ_[p]) :=
begin
  rw is_unit_iff,
  contrapose h,
  have hx' := lt_of_le_of_ne (norm_le_one _) h,
  change ∥((x : ℤ) : ℤ_[p])∥ < 1 at hx',
  rw norm_int_lt_one_iff_dvd at hx',
  norm_cast at hx',
  rw [nat.coprime_comm, nat.prime.coprime_iff_not_dvd _, not_not],
  { assumption, },
  { apply fact.out, },
end

lemma nat_is_unit_of_not_dvd {z : ℕ} (h : ¬ p ∣ z) : is_unit (z : ℤ_[p]) :=
begin
  contrapose h,
  rw [not_not, ←int.coe_nat_dvd, ←padic_int.norm_int_lt_one_iff_dvd],
  apply padic_int.mem_nonunits.1 h,
end

lemma cont_units_map {α β : Type*} [topological_space α] [monoid α] [topological_space β] [monoid β]
  (ha : @continuous _ _ (topological_space.induced (units.coe_hom α) infer_instance)
      infer_instance (@units.inv α _))
  (hb : @continuous _ _ (topological_space.induced (units.coe_hom β) infer_instance)
      infer_instance (@units.inv β _)) {f : α →* β} (hf : continuous f) :
      continuous (units.map f) :=
{ is_open_preimage := λ s hs, begin
  rw (top_eq_iff_cont_inv.2 ha).symm,
  rw [(top_eq_iff_cont_inv.2 hb).symm, is_open_induced_iff] at hs,
  rcases hs with ⟨t, ht, hs⟩,
  rw ←hs,
  convert_to is_open ((units.coe_hom α)⁻¹' (f⁻¹' t)),
  { rw top_eq_iff_cont_inv.2 ha, },
  { apply continuous.is_open_preimage (continuous.comp hf units.continuous_coe) t ht, }, end, }

lemma continuous_units (n : ℕ) :
  continuous (units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom) :=
cont_units_map cont_inv induced_top_cont_inv (padic_int.continuous_to_zmod_pow n)

lemma proj_lim_preimage_units_clopen {n : ℕ} (a : (zmod (p^n))ˣ) :
  is_clopen ((units.map (@padic_int.to_zmod_pow p _ n).to_monoid_hom) ⁻¹' {a}) :=
⟨continuous_def.mp (continuous_units n) {a} (is_open_discrete _),
  continuous_iff_is_closed.mp (continuous_units n) {a} (is_closed_discrete {a})⟩

end padic_int
