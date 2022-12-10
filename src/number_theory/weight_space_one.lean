/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.L_functions
import ring_theory.witt_vector.teichmuller
import ring_theory.witt_vector.compare
import data.nat.modeq
import topology.discrete_quotient
import data.set.prod
import algebra.order.sub
--import algebra.pointwise
import data.real.basic

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure_of_measure`
 * `p_adic_L_function`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

/-- Making `zmod` a discrete topological space. -/
def zmod.topological_space (d : ℕ) : topological_space (zmod d) := ⊥

local attribute [instance] zmod.topological_space

variables (X : Type*) [mul_one_class X] [topological_space X]
variables (A : Type*) [topological_space A] [mul_one_class A] (p : ℕ) [fact p.prime] (d : ℕ)

set_option old_structure_cmd true

/-- A-valued points of weight space -/ --shouldn't this be a category theory statement?
@[ancestor continuous_map monoid_hom]
structure weight_space extends monoid_hom X A, C(X, A)

instance : inhabited (weight_space X A) :=
{ default := { to_fun := λ x, 1,
  map_one' := rfl,
  map_mul' := λ x y, (mul_one 1).symm, }, }

attribute [nolint doc_blame] weight_space.to_continuous_map
attribute [nolint doc_blame] weight_space.to_monoid_hom
attribute [nolint doc_blame] weight_space.to_fun

namespace weight_space
instance : has_coe_to_fun (weight_space X A) _ :=
{ coe := to_fun, }

/-lemma ext_iff (A : Type*) [topological_space A] [mul_one_class A]
  (a b : (units (zmod d)) × (units ℤ_[p]) →* A) [ha : continuous a] [hb : continuous b] :
  (⟨a.to_fun, monoid_hom.map_one' a, monoid_hom.map_mul' a, ha⟩ : weight_space p d A) =
  (⟨b.to_fun, monoid_hom.map_one' b, monoid_hom.map_mul' b, hb⟩ : weight_space p d A) ↔
  a.to_fun = b.to_fun :=
begin
  split,
  { rintros h, simp only [monoid_hom.to_fun_eq_coe] at h, simp [h], },
  { rintros h, simp only [monoid_hom.to_fun_eq_coe], simp at h, simp [h], },
end-/

variables {A} {p} {d}

@[ext] lemma ext (w₁ w₂ : weight_space X A) (h : ∀ u : X, w₁ u = w₂ u) :
  w₁ = w₂ :=
begin
  cases w₁, cases w₂,
  simp only, ext u,
  apply h u,
end

instance : has_one (weight_space X A) :=
{ one := ⟨monoid_hom.has_one.one, rfl, by simp only [mul_one, forall_const, monoid_hom.one_apply],
  continuous_const ⟩ }

instance (A : Type*) [topological_space A] [comm_group A] [topological_group A] :
 has_mul (weight_space X A) :=
{ mul := λ f g, ⟨f.to_fun * g.to_fun,
    begin simp only [pi.mul_apply], repeat {rw weight_space.map_one',}, rw one_mul, end,
    λ x y, begin simp only [pi.mul_apply], repeat {rw weight_space.map_mul',},
    refine mul_mul_mul_comm (f.to_fun x) (f.to_fun y) (g.to_fun x) (g.to_fun y), end,
    -- can we pls have a tactic to solve commutativity and associativity
    continuous.mul (weight_space.continuous_to_fun f) (weight_space.continuous_to_fun g)⟩, }

instance (A : Type*) [topological_space A] [comm_group A] [topological_group A] :
 monoid (weight_space X A) := --is group really needed
{ mul := (*),
  mul_assoc := λ f g h, begin ext, apply mul_assoc, end,
  one := has_one.one,
  one_mul := λ a, begin ext, apply one_mul, end,
  mul_one := λ a, begin ext, apply mul_one, end, }

end weight_space

/-lemma padic_units_modp_units (b : units ℤ_[p]) :
  is_unit ((padic_int.appr (b : ℤ_[p]) 1) : (zmod p)) :=
begin
  rw padic_int.appr,
  sorry
end

lemma blahs' (a : units ℤ_[p]) : ∃ (b : roots_of_unity (nat.to_pnat' p) ℤ_[p]),
  (a - b : ℤ_[p]) ∈ (ideal.span {p} : ideal ℤ_[p]) :=
begin
  set f : roots_of_unity (nat.to_pnat' p) ℤ_[p] → units (zmod p) :=
    λ b, classical.some (padic_units_modp_units p (b : units ℤ_[p])) with hf,
  have h : function.surjective f, sorry,
  set b := classical.some (h (classical.some (padic_units_modp_units p a))) with hb,
  refine ⟨b, _⟩,
  have h1b : padic_int.appr (a - b : ℤ_[p]) 1 = 0, sorry,
  rw ←sub_zero (a - b : ℤ_[p]),
  show (a - b : ℤ_[p]) - ((0 : ℕ) : ℤ_[p]) ∈ ideal.span {↑p}, rw ←h1b,
  have := padic_int.appr_spec 1 (a - b : ℤ_[p]), rw pow_one at this, exact this,
end

lemma blahs (a : units ℤ_[p]) : ∃ (b : units ℤ_[p]),
  (a - b : ℤ_[p]) ∈ (ideal.span {p} : ideal ℤ_[p]) :=
begin
  obtain ⟨b, hb⟩ := blahs' p a, refine ⟨(b : units ℤ_[p]), hb⟩,
end-/

/-lemma inj' {B : Type*} [monoid B] (inj : B → A) [hinj : (function.injective inj)] :
  ∃ inj' : (units B) → (units A), ∀ (x : (units B)), inj' x = inj (x : B) -/

--[fact (function.injective inj)]
variables (R : Type*) [normed_comm_ring R] [complete_space R] [char_zero R] (inj : ℤ_[p] → R) (m : ℕ)
  (χ : mul_hom (units (zmod (d*(p^m)))) R) (w : weight_space (units (zmod d) × units (ℤ_[p])) R)
--variables (d : ℕ) (hd : gcd d p = 1) (χ : dirichlet_char_space A p d) (w : weight_space A p)
--need χ to be primitive

namespace nat

lemma coprime_pow_spl (n : ℕ) (hd : gcd d p = 1) : d.coprime (p^n) :=
  nat.coprime.pow_right _ (nat.coprime_iff_gcd_eq_one.1 hd)

end nat

open locally_constant zmod nat

/-- Extending the primitive Dirichlet character χ with conductor (d* p^m) ; We use the composition
  of χ with the Chinese remainder and `to_zmod_pow` -/
noncomputable abbreviation pri_dir_char_extend [fact (0 < m)] (h : nat.gcd d p = 1)
  (χ : mul_hom (units (zmod (d*(p^m)))) R) : mul_hom ((units (zmod d)) × (units ℤ_[p])) R :=
  mul_hom.comp χ (mul_hom.comp (mul_equiv.symm (units.map_equiv
  (zmod.chinese_remainder (coprime_pow_spl p d m h)).to_mul_equiv)).to_mul_hom
  (mul_hom.comp (mul_equiv.symm (mul_equiv.prod_units)).to_mul_hom
      (monoid_hom.to_mul_hom (monoid_hom.prod_map (monoid_hom.id _) (units.map
        ((padic_int.to_zmod_pow _).to_monoid_hom)))) ))
-- units A instead of A ; use monoid_hom instead of mul_hom

/-- The Teichmuller character defined on `p`-adic units -/
noncomputable abbreviation teichmuller_character : monoid_hom (units ℤ_[p]) ℤ_[p] :=
{ to_fun := λ a, witt_vector.equiv p (witt_vector.teichmuller_fun p (padic_int.to_zmod (a : ℤ_[p]))),
  ..monoid_hom.comp (witt_vector.equiv p).to_monoid_hom (monoid_hom.comp (witt_vector.teichmuller p)
    (monoid_hom.comp (padic_int.to_zmod).to_monoid_hom
    ⟨(coe : units ℤ_[p] → ℤ_[p]), units.coe_one, units.coe_mul⟩)), }
-- is this just taking (a : ℤ_[p]) to (to_zmod a : ℤ_[p])?

namespace padic_int

lemma unit_pow_eq_one (a : units ℤ_[p]) :
  (padic_int.to_zmod (a : ℤ_[p]))^(p - 1) = (1 : (zmod p)) :=
begin
  -- applying FLT
  apply zmod.pow_card_sub_one_eq_one,
  by_contra, --push_neg at h,
  have h' : (a : ℤ_[p]) ∈ (@padic_int.to_zmod p _).ker,
  { exact (@padic_int.to_zmod p _).mem_ker.mpr h, },
  rw [padic_int.ker_to_zmod, local_ring.mem_maximal_ideal, mem_nonunits_iff] at h',
  apply h', simp,
end

end padic_int

lemma teichmuller_character_root_of_unity (a : units ℤ_[p]) :
  (teichmuller_character p a)^(p - 1) = 1 :=
begin
  rw [←monoid_hom.map_pow, monoid_hom.coe_mk, units.coe_pow],
  simp only [padic_int.unit_pow_eq_one p a, ring_hom.map_pow, ring_equiv.map_eq_one_iff],
  refine monoid_hom.map_one (witt_vector.teichmuller p),
end

variables (p)

namespace padic_int

/-- The ideal p^n ℤ_[p] is the closed ball B(0, 1/p^n) -/
lemma span_eq_closed_ball (n : ℕ) :
  metric.closed_ball 0 (1/p^n) = (@ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : set ℤ_[p]) :=
begin
  ext, simp only [one_div, dist_zero_right, metric.mem_closed_ball, set_like.mem_coe],
  rw ←padic_int.norm_le_pow_iff_mem_span_pow, simp,
end

/-- The ideal p^n ℤ_[p] is closed -/
lemma is_closed_span (n : ℕ) : is_closed (@ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : set ℤ_[p]) :=
by { rw ←span_eq_closed_ball, exact metric.is_closed_ball, }

/-- The ideal p^n ℤ_[p] is the open ball B(0, 1/p^(1 - n)) -/
lemma span_eq_open_ball (n : ℕ) :
  metric.ball 0 ((p : ℝ) ^ (1 - (n : ℤ))) = (@ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : set ℤ_[p]) :=
begin
  ext, simp only [mem_ball_zero_iff, set_like.mem_coe],
  rw [←padic_int.norm_le_pow_iff_mem_span_pow, padic_int.norm_le_pow_iff_norm_lt_pow_add_one,
    sub_eq_neg_add 1 (n : ℤ)],
end

/-- The ideal p^n ℤ_[p] is open -/
lemma is_open_span (n : ℕ) : is_open ((ideal.span {p ^ n} : ideal ℤ_[p]) : set ℤ_[p]) :=
by { rw ←span_eq_open_ball, exact metric.is_open_ball, }

/-- The ideal p^n ℤ_[p] is clopen -/
lemma is_clopen_span (n : ℕ) : is_clopen ((ideal.span {p ^ n} : ideal ℤ_[p]) : set ℤ_[p]) :=
  ⟨is_open_span p n, is_closed_span p n⟩

end padic_int

lemma discrete_topology.is_topological_basis {α : Type*} [topological_space α]
  [discrete_topology α] [monoid α] :
  @topological_space.is_topological_basis α _ (set.range set.singleton_monoid_hom) :=
  topological_space.is_topological_basis_of_open_of_nhds (λ u hu, is_open_discrete u)
    (λ  a u mema openu, ⟨({a} : set α), ⟨a, rfl⟩,
      set.mem_singleton a, set.singleton_subset_iff.2 mema⟩)

namespace padic_int
open padic_int

/-
lemma eq_zero_of_dvd_of_lt' {a b c : ℕ} (w : a ∣ (b - c)) (h : b < a) : b - c = 0 :=
begin
  have f := nat.eq_zero_of_dvd_of_div_eq_zero w, apply f,
  have h' : b - c < a, sorry,
  rw nat.div_eq_zero_iff _, { exact h', },
  apply lt_of_le_of_lt _ h', simp,
end

lemma preimage_to_zmod_pow_eq_ball (n : ℕ) (x : ℕ) :
  (padic_int.to_zmod_pow n) ⁻¹' {(x : zmod (p^n))} =
  metric.ball (x : ℤ_[p]) ((p : ℝ) ^ (1 - (n : ℤ))) :=
begin
  ext y,
  simp only [set.mem_preimage, metric.mem_ball, set.mem_singleton_iff],
  rw [dist_eq_norm, sub_eq_neg_add 1 (n : ℤ), ←norm_le_pow_iff_norm_lt_pow_add_one,
    padic_int.norm_le_pow_iff_mem_span_pow], dsimp [to_zmod_pow, to_zmod_hom],
  split,
  { intro h, convert appr_spec n y,
    have := le_total x (appr y n), cases this,
    { rw ←sub_eq_zero at h,
      have h' : ((((y.appr n) - x) : ℕ) : zmod (p^n)) = 0,
      { norm_cast at *, exact h, },
      rw zmod.nat_coe_zmod_eq_zero_iff_dvd at h',
      have h'' := eq_zero_of_dvd_of_lt' h' (appr_lt _ _),
      rw nat.sub_eq_zero_iff_le at h'', refine antisymm this h'', },
    { symmetry' at h, rw ←sub_eq_zero at h,
      have h' : (((x - (y.appr n)) : ℕ) : zmod (p^n)) = 0,
      { norm_cast at *, exact h, },
      rw zmod.nat_coe_zmod_eq_zero_iff_dvd at h',
      have h'' := eq_zero_of_dvd_of_lt' h' (appr_lt _ _),
      rw nat.sub_eq_zero_iff_le at h'', refine antisymm this h'', },
    rw zmod.nat_coe_eq_nat_coe_iff at h, rw nat.modeq.modeq_iff_dvd at h,
    --apply int.eq_zero_of_dvd_of_nat_abs_lt_nat_abs,
    sorry, },
  { intro h, apply zmod_congr_of_sub_mem_span n y _ _ _ h, apply appr_spec n y, },
end
--is there a nicer way of doing this using translation properties and x = 0?
-/

-- enable set addition for additive groups
open_locale pointwise

lemma preimage_to_zmod_pow (n : ℕ) (x : zmod (p^n)) : (@to_zmod_pow p _ n) ⁻¹' {x} =
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
begin
  refine topological_space.is_topological_basis.continuous discrete_topology.is_topological_basis _
    (λ s hs, _),
  cases hs with x hx,
  change {x} = s at hx,
  rw [←hx, preimage_to_zmod_pow, ker_to_zmod_pow],
  refine is_open.add_left (is_open_span p n),
end

/-- The preimage of any singleton under `to_zmod_pow` is clopen. -/
lemma proj_lim_preimage_clopen (n : ℕ) (a : zmod (d*(p^n))) :
  is_clopen (set.preimage (padic_int.to_zmod_pow n) {a} : set ℤ_[p]) :=
  ⟨continuous_def.mp (continuous_to_zmod_pow p n) {a} trivial,
    continuous_iff_is_closed.mp (continuous_to_zmod_pow p n) {a} (is_closed_discrete {a})⟩

lemma add_ball (x y : ℤ_[p]) (r : ℝ) :
  ({x} : set ℤ_[p]) + metric.ball y r = metric.ball (x + y) r :=
begin
  ext z,
  have : dist (-x + z) y = dist z (x + y),
  { rw [dist_eq_norm, dist_eq_norm], refine congr_arg _ _, ring, }, -- why can't I unfold this?
  simp [this, add_comm],
end
-- this should ideally be true for any add_comm_normed_group

/-- The preimage of a singleton x is a ball centered at x. -/
lemma preimage_to_zmod_pow_eq_ball (n : ℕ) (x : zmod (p^n)) :
  (padic_int.to_zmod_pow n) ⁻¹' {(x : zmod (p^n))} =
  metric.ball (x : ℤ_[p]) ((p : ℝ) ^ (1 - (n : ℤ))) :=
  by { rw [preimage_to_zmod_pow, ker_to_zmod_pow, ←span_eq_open_ball, add_ball, add_zero], }

end padic_int

/-- The product of clopen sets is clopen. -/
lemma is_clopen_prod {α β : Type*} [topological_space α] [topological_space β] {s : set α}
  {t : set β} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s ×ˢ t) :=
  ⟨is_open_prod_iff'.2 (or.inl ⟨(hs).1, (ht).1⟩), is_closed.prod (hs).2 (ht).2⟩

/-- Any singleton in a discrete space is clopen. -/
lemma is_clopen_singleton {α : Type*} [topological_space α] [discrete_topology α] (b : α) :
  is_clopen ({b} : set α) := ⟨is_open_discrete _, is_closed_discrete _⟩

open padic_int

/-- Gives the clopen sets that act as a topological basis for `ℤ_[p]`. -/
abbreviation clopen_basis : set (set ℤ_[p]) := {x : set ℤ_[p] | ∃ (n : ℕ) (a : zmod (p^n)),
  x = set.preimage (padic_int.to_zmod_pow n) {a} }

/-- The clopen sets that form a topological basis for `zmod d × ℤ_[p]`. It is better than
  `clopen_basis` because one need not use `classical.choice`. -/
abbreviation clopen_from (n : ℕ) (a : zmod (d * (p^n))) : set (zmod d × ℤ_[p]) :=
  ({a} : set (zmod d)) ×ˢ ((@padic_int.to_zmod_pow p _ n)⁻¹' {(a : zmod (p^n))})

lemma is_clopen_clopen_from (n : ℕ) (a : zmod (d * (p^n))) : is_clopen (clopen_from p d n a) :=
  is_clopen_prod (is_clopen_singleton (a : zmod d)) (proj_lim_preimage_clopen p d n a)

/-- The version of `clopen_basis` that also incorporates `d` coprime to `p`. -/
@[reducible] abbreviation clopen_basis' :=
{ x : set ((zmod d) × ℤ_[p]) // ∃ (n : ℕ) (a : zmod (d * (p^n))), x = clopen_from p d n a }

-- lemma mem_clopen_basis' (U : clopen_sets ((zmod d) × ℤ_[p])) (hU : U ∈ clopen_basis' p d) :
--   ∃ (n : ℕ) (a : zmod (d * (p^n))),
--   U = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
--     is_clopen_prod (is_clopen_singleton (a : zmod d))
--       (proj_lim_preimage_clopen p d n a) ⟩ := sorry

lemma find_this_out (ε : ℝ) (h : (0 < ε)) : ∃ (n : ℕ), (1 / (p^n) : ℝ) < ε :=
begin
  convert exists_pow_lt_of_lt_one h _, swap, exact 1/p,
  { simp only [one_div, inv_pow], },
  rw div_lt_iff _,
  { simp only [one_mul, one_lt_cast], apply nat.prime.one_lt, apply fact_iff.1 _, assumption, },
  simp only [cast_pos], apply nat.prime.pos, apply fact_iff.1 _, assumption,
end

lemma mem_clopen_basis (n : ℕ) (a : zmod (p^n)) :
  (padic_int.to_zmod_pow n)⁻¹' {a} ∈ (clopen_basis p) := ⟨n, a, rfl⟩

--lemma mem_clopen_basis'
--∃ (n : ℕ) (a : zmod (p^n)), x = set.preimage (padic_int.to_zmod_pow n) a

lemma has_coe_t_eq_coe (a : ℤ_[p]) (n : ℕ) : ((to_zmod_pow n a) : ℤ_[p]) = a.appr n :=
begin
  dsimp [to_zmod_pow, to_zmod_hom], rw ←zmod.nat_cast_comp_val ℤ_[p],
  { simp, apply zmod.val_cast_of_lt (appr_lt _ _), },
  exact fact.pow.pos,
end

lemma dist_appr_spec (a : ℤ_[p]) (n : ℕ) : dist a ((a.appr n) : ℤ_[p]) ≤ (p : ℝ)^(-n : ℤ) :=
begin
  rw dist_eq_norm,
  have := appr_spec n a,
  rw ←norm_le_pow_iff_mem_span_pow at this, exact this,
end

example (a b c : ℤ) (h1 : a < c) (h2 : b ≤ d) : a + b < c + d := add_lt_add_of_lt_of_le h1 h2

example (m : ℕ) : 1/((p : ℝ)^m) = ((p^m) : ℝ)⁻¹ := one_div (↑p ^ m)

example (a : ℝ) (m n : ℤ) : a^(0 : ℤ) = 1 := zpow_zero a

theorem clopen_basis_clopen : topological_space.is_topological_basis (clopen_basis p) ∧
  ∀ x ∈ (clopen_basis p), is_clopen x :=
begin
  split,
  { refine topological_space.is_topological_basis_of_open_of_nhds _ _,
    { rintros u hu, rcases hu with ⟨n, a, hu⟩,
      have := proj_lim_preimage_clopen p 1 n,
      rw one_mul at this, rw hu, convert (this a).1, simp only [zmod.cast_id', id.def], },
    rintros a u mema hu, rw metric.is_open_iff at hu,
    obtain ⟨ε, hε, h⟩ := hu a mema,
    obtain ⟨m, fm⟩ := find_this_out p (ε/2) (half_pos hε),
    set b := ((to_zmod_pow m.succ a) : ℤ_[p]) with hb,
    refine ⟨metric.ball b (p^(-(m : ℤ))), _, _, _⟩,
    dsimp [to_zmod_pow, to_zmod_hom] at hb,
    { have arith : -(m : ℤ) = 1 - (m.succ : ℤ),
      { simp only [int.coe_nat_succ], rw sub_add_eq_sub_sub_swap, rw sub_self, rw zero_sub, },
      rw [arith],
      rw ←preimage_to_zmod_pow_eq_ball p (m.succ) (to_zmod_pow m.succ a),
      convert mem_clopen_basis p m.succ ((to_zmod_pow m.succ) a), },
    { simp only [metric.mem_ball], rw dist_eq_norm, rw hb,
      rw has_coe_t_eq_coe p a m.succ,
      have := appr_spec m.succ a, rw ←norm_le_pow_iff_mem_span_pow _ m.succ at this,
      refine gt_of_gt_of_ge _ this,
      repeat{rw zpow_neg, rw ←one_div,},
      apply one_div_lt_one_div_of_lt, norm_num, convert pow_pos _ m,
      { norm_num, apply lt_of_le_of_ne,
        { apply nat.zero_le, },
        { symmetry, apply nat.prime.ne_zero, apply fact.out, }, },
      { rw zpow_lt_iff_lt _,
        { norm_num, },
        { norm_cast, apply nat.prime.one_lt, apply fact.out, }, }, },
    { rintros c hc, apply h, simp only [metric.mem_ball, zpow_neg, zpow_coe_nat] at hc,
      simp only [metric.mem_ball],
      suffices f1 : dist c a < 2 / (p^m),
      { refine lt_trans f1 _, simp only, refine (lt_div_iff' _).mp _, exact zero_lt_two,
        rw ←one_div, exact fm, },
      have := dist_triangle c b a, rw dist_comm b a at this, refine gt_of_gt_of_ge _ this,
      have ha : dist a b ≤ (↑p ^ m)⁻¹,
      { rw hb, rw has_coe_t_eq_coe p a m.succ,
        have : (↑p ^ m)⁻¹ = (p : ℝ)^(-m : ℤ),
        { have f : (p : ℝ) ≠ 0,
          { norm_cast, apply nat.prime.ne_zero, apply fact.out, },
          rw ←one_div _, rw div_eq_iff _,
          { rw ←zpow_coe_nat (p : ℝ) m, rw ←zpow_add₀,
            { rw neg_add_self, rw zpow_zero _, },
            apply f, },
          { apply pow_ne_zero _, apply f, apply_instance, }, },
        rw this, refine le_trans (dist_appr_spec p a m.succ) _,
        { rw zpow_le_iff_le _,
          { apply neg_le_neg, norm_num, },
          { norm_cast, apply nat.prime.one_lt, apply fact.out, }, }, },
      convert add_lt_add_of_lt_of_le hc ha,
      rw [←one_div, div_add_div_same, one_add_one_eq_two], }, },
  { rintros x hx,
    --rw clopen_basis at hx, simp only [set.mem_set_of_eq] at hx,
    simp only [set.mem_set_of_eq] at hx,
    rcases hx with ⟨n, a, hx⟩, rw hx,
    have := proj_lim_preimage_clopen p 1 n, rw one_mul at this, convert this a,
    simp only [zmod.cast_id', id.def], },
end

--lemma char_fn_basis_of_loc_const : is_basis A (@char_fn ℤ_[p] _ _ _ _ A _ _ _) := sorry

--instance : semimodule A (units ℤ_[p]) := sorry
-- a + pZ_p a from0 to (p - 2) [for linear independence]
-- set up a bijection between disj union
-- construct distri prove eval at canonical basis gives (a,n)

variables {c : ℕ}

--def clopen_nat_equiv : clopen_basis' p d ≃ (ℕ → )

/-- A Bernoulli measure, as defined by Washington. -/
def E_c (hc : c.gcd p = 1) := λ (n : ℕ) (a : (zmod (d * (p^n)))), int.fract ((a.val : ℚ) / (d*p^n))
    - c * int.fract ( ((((((c : zmod (d * p^(2 * n)))⁻¹).val : ℚ) * (a : ℚ))) : ℚ) / (d * p^n)) + (c - 1)/2

-- I don't understand why this works!
example (n : ℕ) (a b : zmod n) : ((a * b) : ℚ) = (a : ℚ) * (b : ℚ) :=
begin
  have : zmod n → ℤ, exact zmod.val_min_abs,
  rw coe_to_lift,
end
--instance {α : Type*} [topological_space α] : semimodule A (locally_constant α A) := sorry

instance [fact (0 < d)] : compact_space (zmod d) := fintype.compact_space
--instance : totally_bounded (set.univ ℤ_[p]) :=
instance : compact_space ℤ_[p] :=
begin
  refine is_compact_iff_compact_space.mp _,
  rw compact_iff_totally_bounded_complete,
  split,
  {
    refine metric.totally_bounded_of_finite_discretization _,
    rintros ε hε,
    obtain ⟨m, fm⟩ := find_this_out p (ε/2) (half_pos hε),
    have fm' : (2 : ℝ)/(p^m) < ε,
    { rw ←mul_one (2 : ℝ), rw mul_div_assoc, rw mul_comm, rw ←lt_div_iff _, assumption,
      norm_num, },
    refine ⟨zmod (p^m.succ), _, to_zmod_pow m.succ, λ x y h, _ ⟩,
    { have : fact (0 < (p^(m.succ))), { exact fact.pow.pos, },
      apply zmod.fintype _, assumption, },
    apply lt_trans _ fm',
    rw ←set.mem_singleton_iff at h, rw ←set.mem_preimage at h,
    rw preimage_to_zmod_pow_eq_ball at h, rw metric.mem_ball at h,
    rw has_coe_t_eq_coe at h,
    refine gt_of_gt_of_ge _ (dist_triangle x (appr y m.succ) y),
    have f : (2 : ℝ) / (p^m) = (1 / (p^m)) + (1 : ℝ) / (p^m), {  rw ← _root_.add_div, refl, },
    rw f, rw dist_comm _ ↑y,
    have f' : ↑p ^ (1 - (m.succ : ℤ)) = (1 : ℝ) / (p^m),
    { symmetry, rw div_eq_iff _, rw ←zpow_coe_nat, rw ← zpow_add₀ _, --rw ←zpow_add (p : ℝ),
      norm_num, rw sub_add, rw add_sub_cancel', rw sub_self, rw zpow_zero,
      any_goals { apply pow_ne_zero, },
      all_goals { norm_cast, apply nat.prime.ne_zero, apply fact.out, }, },
    rw f' at h,
    rw add_comm (dist _ _) _,
    have f'' : ↑p ^ -(m.succ : ℤ) < (1 : ℝ) / (p^m),
    { rw div_eq_inv_mul, rw mul_one, rw zpow_neg, rw inv_lt_inv,
      { simp, rw zpow_add₀, simp, rw ←mul_one ((p : ℝ)^m), rw mul_comm, rw mul_comm _ (p : ℝ), apply mul_lt_mul,
          { norm_cast, apply nat.prime.one_lt, rw fact_iff at *, assumption, },
          { rw one_mul, },
          { norm_cast, apply pow_pos, apply nat.prime.pos, rw fact_iff at *, assumption, },
          { norm_cast, exact zero_le p, },
        { exact nonzero_of_invertible ↑p, }, },
      { norm_cast, apply pow_pos, apply nat.prime.pos, rw fact_iff at *, assumption, },
      { norm_cast, apply pow_pos, apply nat.prime.pos, rw fact_iff at *, assumption, }, },
    have := add_lt_add (gt_of_gt_of_ge f'' (ge_iff_le.2 (dist_appr_spec p y (m.succ)))) h,
    rw [subtype.dist_eq y _, subtype.dist_eq x _, padic_int.coe_coe] at this,
    exact this, },
  { refine complete_space_coe_iff_is_complete.mp _,
    show complete_space ℤ_[p],
    apply_instance, },
end
--better way to do it? maybe without showing totally bounded (should that be a separate lemma?)?
-- better stick to either div or inv. which is easier to work with?

--instance [fact (0 < d)] : compact_space (zmod d × ℤ_[p]) := infer_instance
instance : totally_disconnected_space ℤ_[p] :=
begin
  rw compact_t2_tot_disc_iff_tot_sep,
  refine {is_totally_separated_univ := _},
  rintros x hx y hx ne,
  obtain ⟨n,hn⟩ : ∃ (n : ℕ), to_zmod_pow n x ≠ to_zmod_pow n y,
  { contrapose ne, push_neg at ne, rw ext_of_to_zmod_pow at ne, simp [ne], },
  have f : is_totally_separated (set.univ : set (zmod (p^n))),
  { exact totally_separated_space.is_totally_separated_univ (zmod (p ^ n)), },
  obtain ⟨u, v, hu, hv, memu, memv, univ, disj⟩ :=
    f (to_zmod_pow n x) (set.mem_univ _) (to_zmod_pow n y) (set.mem_univ _) hn,
  refine ⟨(to_zmod_pow n)⁻¹' u, (to_zmod_pow n)⁻¹' v,
    continuous_def.mp (continuous_to_zmod_pow p n) u hu,
    continuous_def.mp (continuous_to_zmod_pow p n) v hv,
    set.mem_preimage.mpr memu, set.mem_preimage.mpr memv,
    λ z hz, _, _⟩,
  { rw set.mem_union,
    have univ' := univ (set.mem_univ (to_zmod_pow n z)),
    cases univ',
    { left, apply set.mem_preimage.mpr univ', },
    { right, apply set.mem_preimage.mpr univ', }, },
  { ext z, rw ←@set.preimage_empty _ _ (to_zmod_pow n), rw set.mem_preimage,
    rw set.ext_iff at disj, specialize disj (to_zmod_pow n z), simp [disj], simp at disj,
    assumption, },
end
--ℤ_[p] is now profinite!
--instance sigh : totally_disconnected_space (zmod d × ℤ_[p]) := infer_instance

/-
@[reducible] def clopen_basis' :=
{x : clopen_sets ((zmod d) × ℤ_[p]) // ∃ (n : ℕ) (a : zmod (d * (p^n))),
  x = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_singleton (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩ }
-/
variables [fact (0 < d)]
variables [algebra ℚ R] [norm_one_class R]

/-- The set of Bernoulli measures. -/
def bernoulli_measure (hc : c.gcd p = 1) :=
 {x : locally_constant (zmod d × ℤ_[p]) R →ₗ[R] R |
   ∀ (n : ℕ) (a : zmod (d * (p^n))), x (char_fn R (is_clopen_clopen_from p d n a)) =
   (algebra_map ℚ R) (E_c p d hc n a) }

/-
@[reducible] def clopen_basis' :=
{x : clopen_sets ((zmod d) × ℤ_[p]) // ∃ (n : ℕ) (a : zmod (d * (p^n))),
  x = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_singleton (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩ }
-/
