/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.L_functions
import ring_theory.witt_vector.teichmuller
import ring_theory.witt_vector.compare
import data.nat.modeq

/-!
# Weight spaces

This file defines ... and proves ...

## Main definitions
 * `foo`
 * `bar`

## Implementation notes
TODO (optional)

## References
TODO (optional)

## Tags
p-adic, L-function, Bernoulli measure, ...
-/

--variables (A : Type*) [normed_comm_ring A] (p : ℕ) [fact p.prime] (d : ℕ) (hd : gcd d p = 1)

def zmod.topological_space (d : ℕ) : topological_space (zmod d) := ⊥

local attribute [instance] zmod.topological_space

--instance is_this_needed : topological_space (units (zmod d) × units ℤ_[p]) := infer_instance

variables (A : Type*) [topological_space A] [mul_one_class A] (p : ℕ) [fact p.prime] (d : ℕ)

set_option old_structure_cmd true
/-- A-valued points of weight space -/ --shouldn't this be a category theory statement?
@[ancestor continuous_map monoid_hom]
structure weight_space extends
  monoid_hom ((units (zmod d)) × (units ℤ_[p])) A,
  C((units (zmod d)) × (units ℤ_[p]), A)
--generalize domain to a compact space?

attribute [nolint doc_blame] weight_space.to_continuous_map
attribute [nolint doc_blame] weight_space.to_monoid_hom
attribute [nolint doc_blame] weight_space.to_fun

/-lemma weight_space_continuous_to_fun {A : Type*} [topological_space A] [mul_one_class A]
  (f : weight_space p d A) : continuous f.to_fun :=
  (weight_space.to_continuous_map f).continuous_to_fun-/

example {α β : Type*} [topological_space α] [topological_space β] [group β] [topological_group β]
(f g h : α → β) [continuous f] [continuous g] [continuous h] : f*g*h = f*(g*h) :=
begin
  refine mul_assoc f g h,
end

namespace weight_space

instance : has_coe_to_fun (weight_space A p d) :=
{
  F := _,
  coe := to_fun, }

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

@[ext] lemma ext (w₁ w₂ : weight_space A p d)
  (h : ∀ u : (units (zmod d)) × (units ℤ_[p]), w₁ u = w₂ u) : w₁ = w₂ :=
begin
  cases w₁, cases w₂,
  simp, ext u,
  apply h u,
end

noncomputable instance (A : Type*) [topological_space A] [group A] [topological_group A] :
  has_one (weight_space A p d) :=
{ one := ⟨monoid_hom.has_one.one, rfl, is_mul_hom.map_mul 1, continuous_const ⟩ }

instance (A : Type*) [topological_space A] [comm_group A] [topological_group A] :
  has_mul (weight_space A p d) :=
{ mul := λ f g, ⟨f.to_fun * g.to_fun,
    begin simp only [pi.mul_apply], repeat {rw weight_space.map_one',}, rw one_mul, end,
    λ x y, begin simp only [pi.mul_apply], repeat {rw weight_space.map_mul',},
    refine mul_mul_mul_comm (f.to_fun x) (f.to_fun y) (g.to_fun x) (g.to_fun y), end,
    -- can we pls have a tactic to solve commutativity and associativity
    continuous.mul (weight_space.continuous_to_fun f) (weight_space.continuous_to_fun g)⟩, }

noncomputable instance (A : Type*) [topological_space A] [comm_group A] [topological_group A] :
  monoid (weight_space A p d) := --is group really needed
{
  mul := (*),
  mul_assoc := λ f g h, begin ext, apply mul_assoc,
  end,
  --what is simp only doing
  one := has_one.one,
  one_mul := λ a,
  begin
    ext, apply one_mul,
  end,
  --have := one_mul a.to_fun, have h : (1 : weight_space p d A).to_fun = 1, simp only,
  --apply weight_space.mk.inj, refine one_mul a.to_fun, sorry, end,
  mul_one := λ a, begin ext, apply mul_one, end,
--  inv := λ f, ⟨λ x, (f.to_fun x)⁻¹, begin sorry end, _, _⟩,
--  mul_left_inv := sorry,
}

end weight_space

--instance : has_mod ℤ_[p] := sorry

/-lemma padic_units_modp_units (b : units ℤ_[p]) :
  is_unit ((padic_int.appr (b : ℤ_[p]) 1) : (zmod p)) :=
begin
  rw padic_int.appr,
  sorry
end

example {α β : Type*} (f : α → β) (h : function.surjective f) (b : β) : ∃ a, f a = b :=
begin
  have := h b,
  exact h b,
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
variables (R : Type*) [normed_comm_ring R] [complete_space R] (inj : ℤ_[p] → R)

variables (m : ℕ) (χ : mul_hom (units (zmod (d*(p^m)))) R) (w : weight_space R p d)
--variables (d : ℕ) (hd : gcd d p = 1) (χ : dirichlet_char_space A p d) (w : weight_space A p)
--need χ to be primitive

/-- Extending the primitive dirichlet character χ with conductor (d* p^m) -/
def pri_dir_char_extend : mul_hom ((units (zmod d)) × (units ℤ_[p])) R := sorry
--should this be def or lemma? ; units A instead of A ; use monoid_hom instead of mul_hom
-- so use def not lemma, because def gives Type, lemma gives Prop

--variables (ψ : pri_dir_char_extend A p d)

/-- The Teichmuller character defined on `p`-adic units -/
--noncomputable def teichmuller_character (a : units ℤ_[p]) : R := inj (classical.some (blahs p a))
noncomputable def teichmuller_character : monoid_hom (units ℤ_[p]) ℤ_[p] :=
{
  to_fun := λ a,
    witt_vector.equiv p (witt_vector.teichmuller_fun p (padic_int.to_zmod (a : ℤ_[p]))),
  ..monoid_hom.comp (witt_vector.equiv p).to_monoid_hom
  (monoid_hom.comp (witt_vector.teichmuller p)
    (monoid_hom.comp (padic_int.to_zmod).to_monoid_hom
      ⟨(coe : units ℤ_[p] → ℤ_[p]), units.coe_one, units.coe_mul⟩)),
}

lemma unit_to_zmod_nonzero (a : units ℤ_[p]) :
  (padic_int.to_zmod (a : ℤ_[p]))^(p - 1) = (1 : (zmod p)) :=
begin
  apply zmod.pow_card_sub_one_eq_one,
  by_contra, push_neg at h,
  have h' : (a : ℤ_[p]) ∈ padic_int.to_zmod.ker,
  { exact padic_int.to_zmod.mem_ker.mpr h, },
  rw [padic_int.ker_to_zmod, local_ring.mem_maximal_ideal, mem_nonunits_iff] at h',
  apply h', simp,
end

lemma teichmuller_character_root_of_unity (a : units ℤ_[p]) :
  (teichmuller_character p a)^(p - 1) = 1 :=
begin
  have : (padic_int.to_zmod (a : ℤ_[p]))^(p - 1) = (1 : (zmod p)),
  exact unit_to_zmod_nonzero p a, --rw witt_vector.from_padic_int,
  rw [←monoid_hom.map_pow, teichmuller_character, monoid_hom.coe_mk, units.coe_pow],
  simp only [this, ring_hom.map_pow, ring_equiv.map_eq_one_iff],
  have f := monoid_hom.map_one (witt_vector.teichmuller p), refine f,
end

variables (p)

def clopen_basis : set (set ℤ_[p]) := {x : set ℤ_[p] | ∃ (n : ℕ) (a : zmod (p^n)),
  x = set.preimage (padic_int.to_zmod_pow n) {a} }

lemma span_eq_closed_ball (n : ℕ) :
  metric.closed_ball 0 (1/p^n) = (@ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : set ℤ_[p]) :=
begin
  ext, simp, rw ←padic_int.norm_le_pow_iff_mem_span_pow, simp,
end

lemma is_closed_span (n : ℕ) : is_closed (@ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : set ℤ_[p]) :=
begin
  rw ←span_eq_closed_ball, exact metric.is_closed_ball,
end

lemma span_eq_open_ball (n : ℕ) :
  metric.ball 0 ((p : ℝ) ^ (1 - (n : ℤ))) = (@ideal.span ℤ_[p] _ {(p^n : ℤ_[p])} : set ℤ_[p]) :=
begin
  ext, simp only [mem_ball_0_iff, set_like.mem_coe],
  rw [←padic_int.norm_le_pow_iff_mem_span_pow, padic_int.norm_le_pow_iff_norm_lt_pow_add_one],
  have : 1 - (n : ℤ) = -(n : ℤ) + 1 := sub_eq_neg_add 1 ↑n,
  rw this,
end

lemma is_open_span (n : ℕ) : is_open ((ideal.span {p ^ n} : ideal ℤ_[p]) : set ℤ_[p]) :=
begin
  rw ←span_eq_open_ball,
  exact metric.is_open_ball,
end

lemma continuous_of_topological_basis {α β : Type*} {B : set (set β)} [topological_space α]
  [topological_space β] (f : α → β) (hB : topological_space.is_topological_basis B)
  (h : ∀ s ∈ B, is_open (f⁻¹' s)) : continuous f :=
begin
  refine {is_open_preimage := _}, rintros t ht,
  obtain ⟨S, hS, tsUnion⟩ := topological_space.is_topological_basis.open_eq_sUnion hB ht,
  rw tsUnion, simp, apply is_open_Union, rintros i, apply is_open_Union, intro memi,
  exact h i (hS memi),
end

lemma discrete_topology.is_topological_basis
  {α : Type*} [topological_space α] [discrete_topology α] [monoid α] :
  @topological_space.is_topological_basis α _ (set.range set.singleton_hom) :=
begin
  refine topological_space.is_topological_basis_of_open_of_nhds _ _,
  { simp, },
  rintros a u mema openu,
  refine ⟨({a} : set α), _, _, _⟩,
  { simp, use a, rw set.singleton_hom, simp, },
  { simp, },
  simp [mema],
end

open padic_int

/-example (a b n : ℕ) (h : b ≤ a) : (a : zmod n) - (b : zmod n) = (((a - b) : ℕ) : zmod n) :=
begin
  norm_cast at *,
end

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

lemma preimage_to_zmod_pow (n : ℕ) (x : zmod (p^n)) : (to_zmod_pow n) ⁻¹' {x} =
  {(x : ℤ_[p])} + (((to_zmod_pow n).ker : ideal ℤ_[p]) : set ℤ_[p]) :=
begin
 ext y,
    simp only [set.image_add_left, set.mem_preimage, set.singleton_add,
      set.mem_singleton_iff, set_like.mem_coe],
    split,
    { intro h, rw ring_hom.mem_ker, simp [h], },
    { intro h, rw ring_hom.mem_ker at h, simp at *, rw neg_add_eq_zero at h, exact h.symm, },
end

lemma continuous_to_zmod_pow (n : ℕ) : continuous (@padic_int.to_zmod_pow p _ n) :=
begin
  refine continuous_of_topological_basis _ discrete_topology.is_topological_basis _,
  rintros s hs, simp only [set.mem_range] at hs, cases hs with x hx,
  change {x} = s at hx, rw ←hx,
  rw [preimage_to_zmod_pow, ker_to_zmod_pow], refine is_open.add_left _, exact is_open_span p n,
end

lemma proj_lim_preimage_clopen (n : ℕ) (a : zmod (d*(p^n))) :
  is_clopen (set.preimage (padic_int.to_zmod_pow n) {a} : set ℤ_[p]) :=
begin
  split,
  { refine continuous_def.mp (continuous_to_zmod_pow p n) {a} trivial, },
  { refine continuous_iff_is_closed.mp (continuous_to_zmod_pow p n) {a} _, simp, },
end

lemma add_ball (x y : ℤ_[p]) (r : ℝ) :
  ({x} : set ℤ_[p]) + metric.ball y r = metric.ball (x + y) r :=
begin
  ext z, simp,
  have : dist (-x + z) y = dist z (x + y),
  { rw dist_eq_norm, rw dist_eq_norm, apply congr_arg, ring, },
  rw this,
end

lemma preimage_to_zmod_pow_eq_ball (n : ℕ) (x : zmod (p^n)) :
  (padic_int.to_zmod_pow n) ⁻¹' {(x : zmod (p^n))} =
  metric.ball (x : ℤ_[p]) ((p : ℝ) ^ (1 - (n : ℤ))) :=
begin
  rw preimage_to_zmod_pow, rw ker_to_zmod_pow, rw ←span_eq_open_ball, rw add_ball,
  rw add_zero,
end

lemma is_clopen_prod {α β : Type*} [topological_space α] [topological_space β] {s : set α}
  {t : set β} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s.prod t) :=
begin
  split,
  { rw is_open_prod_iff', fconstructor, refine ⟨(hs).1, (ht).1⟩, },
  { apply is_closed.prod (hs).2 (ht).2, },
end

lemma is_clopen_discrete {α : Type*} [topological_space α] [discrete_topology α] (b : α) :
  is_clopen ({b} : set α) :=
 ⟨is_open_discrete _, is_closed_discrete _⟩

def clopen_basis' : set (clopen_sets ((zmod d) × ℤ_[p])) :=
{x : clopen_sets ((zmod d) × ℤ_[p]) | ∃ (n : ℕ) (a : zmod (d * (p^n))),
  x = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_discrete (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩ }

/-def clopen_basis' : set (clopen_sets ((zmod d) × ℤ_[p])) :=
{x : clopen_sets ((zmod d) × ℤ_[p]) | ∃ (n : ℕ) (a : zmod (p^n)) (b : zmod d),
  x = ⟨({b} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) a),
    is_clopen_prod (is_clopen_discrete b) (proj_lim_preimage_clopen p n a) ⟩ }-/

lemma find_this_out (ε : ℝ) (h : 0 < ε) : ∃ (n : ℕ), (1 / (p^n) : ℝ) < ε :=
begin
  convert exists_pow_lt_of_lt_one h _, swap, exact 1/p,
  { simp only [one_div, inv_pow'], },
  rw div_lt_iff _, { simp, apply nat.prime.one_lt, apply fact_iff.1 _, assumption, },
  simp, apply nat.prime.pos, apply fact_iff.1 _, assumption,
end

lemma mem_clopen_basis (n : ℕ) (a : zmod (p^n)) :
  (padic_int.to_zmod_pow n)⁻¹' {a} ∈ (clopen_basis p) := ⟨n, a, rfl⟩

--example {α : Type*} (x : α) : x ∈ (x : set α) :=

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

theorem clopen_basis_clopen : topological_space.is_topological_basis (clopen_basis p) ∧
  ∀ x ∈ (clopen_basis p), is_clopen x :=
begin
  split,
  { refine topological_space.is_topological_basis_of_open_of_nhds _ _,
    { rintros u hu, rcases hu with ⟨n, a, hu⟩,
      have := proj_lim_preimage_clopen p 1 n,
      rw one_mul at this, rw hu, convert (this a).1, simp, },
    rintros a u mema hu, rw metric.is_open_iff at hu,
    obtain ⟨ε, hε, h⟩ := hu a mema,
    obtain ⟨m, fm⟩ := find_this_out p (ε/2) (half_pos hε),
    set b := ((to_zmod_pow m.succ a) : ℤ_[p]) with hb,
    refine ⟨metric.ball b (p^(-(m : ℤ))), _, _, _⟩,
    dsimp [to_zmod_pow, to_zmod_hom] at hb,
    { have arith : -(m : ℤ) = 1 - (m.succ : ℤ), simp, linarith,
      rw [arith],
      rw ←preimage_to_zmod_pow_eq_ball p (m.succ) (to_zmod_pow m.succ a),
      convert mem_clopen_basis p m.succ ((to_zmod_pow m.succ) a), },
    { simp only [metric.mem_ball], rw dist_eq_norm, rw hb,
      rw has_coe_t_eq_coe p a m.succ,
      have := appr_spec m.succ a, rw ←norm_le_pow_iff_mem_span_pow _ m.succ at this,
      refine gt_of_gt_of_ge _ this,
      repeat{rw fpow_neg, rw ←one_div,},
      apply one_div_lt_one_div_of_lt, norm_num, convert pow_pos _ m, simp, sorry, sorry, },
    { rintros c hc, apply h, simp at hc, simp,
      suffices f1 : dist c a < 2 / (p^m),
      { refine lt_trans f1 _, simp [fm], refine (lt_div_iff' _).mp _, exact zero_lt_two,
        rw ←one_div, exact fm, },
      have := dist_triangle c b a, rw dist_comm b a at this, refine gt_of_gt_of_ge _ this,
      have ha : dist a b ≤ (↑p ^ m)⁻¹,
      { rw hb, rw has_coe_t_eq_coe p a m.succ,
        have : (↑p ^ m)⁻¹ = (p : ℝ)^(-m : ℤ), sorry,
        rw this, refine le_trans (dist_appr_spec p a m.succ) _, sorry, },
      convert add_lt_add_of_lt_of_le hc ha,
      rw [←one_div, div_add_div_same, one_add_one_eq_two], }, },
  { rintros x hx,
    rw clopen_basis at hx, simp at hx, rcases hx with ⟨n, a, hx⟩, rw hx,
    have := proj_lim_preimage_clopen p 1 n, rw one_mul at this, convert this a, simp, },
end

--lemma char_fn_basis_of_loc_const : is_basis A (@char_fn ℤ_[p] _ _ _ _ A _ _ _) := sorry

--instance : semimodule A (units ℤ_[p]) := sorry
-- a + pZ_p a from0 to (p - 2) [for linear independence]
-- set up a bijection between disj union
-- construct distri prove eval at canonical basis gives (a,n)

variables {c : ℤ}

def E_c (hc : gcd c p = 1) := λ (n : ℕ) (a : (zmod (d * (p^n)))), fract ((a : ℤ) / (d*p^(n + 1)))
    - c * fract ((a : ℤ) / (c * (d*p^(n + 1)))) + (c - 1)/2

--instance {α : Type*} [topological_space α] : semimodule A (locally_constant α A) := sorry

example (x : ℕ) : ((x : ℤ_[p]) : ℚ_[p]) = (x : ℚ_[p]) :=
coe_coe x

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
    have fm' : (2 : ℝ)/(p^m) < ε, sorry,
    refine ⟨zmod (p^m.succ), _, to_zmod_pow m.succ, λ x y h, _ ⟩,
    { have : fact (0 < (p^(m.succ))), { exact fact.pow.pos, },
      apply zmod.fintype _, assumption, },
    apply lt_trans _ fm',
    rw ←set.mem_singleton_iff at h, rw ←set.mem_preimage at h,
    rw preimage_to_zmod_pow_eq_ball at h, rw metric.mem_ball at h,
    rw has_coe_t_eq_coe at h,
    refine gt_of_gt_of_ge _ (dist_triangle x (appr y m.succ) y),
    have f : (2 : ℝ) / (p^m) = (1 / (p^m)) + (1 : ℝ) / (p^m), sorry,
    rw f, rw dist_comm _ ↑y,
    have f' : ↑p ^ (1 - (m.succ : ℤ)) = (1 : ℝ) / (p^m), sorry, rw f' at h,
    rw add_comm (dist _ _) _,
    have f'' : ↑p ^ -(m.succ : ℤ) < (1 : ℝ) / (p^m), sorry,
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

variables [fact (0 < d)]
def bernoulli_measure (hc : gcd c p = 1) :=
{x : locally_constant (zmod d × ℤ_[p]) R →ₗ[R] R |
  ∀ U : (clopen_basis' p d), x (char_fn (zmod d × ℤ_[p]) U.val) =
    E_c p d hc (classical.some U.prop) (classical.some (classical.some_spec U.prop)) }

variables (d)

open_locale big_operators

lemma what_to_do (f : locally_constant (zmod d × ℤ_[p]) R) : ∃ (s : finset ℕ)
  (i : s → (clopen_basis' p d)) (j : s → R), f = ∑ k : s, j(k) • (char_fn (zmod d × ℤ_[p]) (i k)) :=
begin
  sorry,
end

lemma bernoulli_measure_nonempty (hc : gcd c p = 1) :
  nonempty (@bernoulli_measure p _ d R _ _ _ _ hc) :=
begin
  refine mem_nonempty _,
  { constructor, swap 3,
    { intro f,
      have s := classical.some (what_to_do p d R f),
      have hs := classical.some_spec (what_to_do p d R f),
      have hs' := classical.some_spec (classical.some_spec (what_to_do p d R f)),
       },
    sorry,
    sorry, },
sorry,
end

/-instance (c : ℤ) (hc : gcd c p = 1) : distribution' (ℤ_[p]) :=
{
  phi := (classical.choice (bernoulli_measure_nonempty p c hc)).val
} -/

/-lemma subspace_induces_locally_constant (U : set X) [hU : semimodule A (locally_constant ↥U A)]
  (f : locally_constant U A) :
  ∃ (g : locally_constant X A), f.to_fun = (set.restrict g.to_fun U) := sorry -/

example {A B C D : Type*} (f : A → B) (g : C → D) : A × C → B × D := by refine prod.map f g

lemma subspace_induces_locally_constant (f : locally_constant (units (zmod d) × units ℤ_[p]) A) :
  ∃ (g : locally_constant (zmod d × ℤ_[p]) A),
    f.to_fun = g.to_fun ∘ (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])) :=
sorry
--generalize to units X
#print uniform_continuous_uniformly_extend
instance is_this_even_true : compact_space (units (zmod d) × units ℤ_[p]) := sorry
instance why_is_it_not_recognized : t2_space (units (zmod d) × units ℤ_[p]) := sorry
instance so_many_times : totally_disconnected_space (units (zmod d) × units ℤ_[p]) := sorry

noncomputable lemma bernoulli_measure_of_measure (hc : gcd c p = 1) :
  measures'' (units (zmod d) × units ℤ_[p]) R :=
begin
  constructor, swap,
  constructor,
  constructor, swap 3, rintros f,
  choose g hg using subspace_induces_locally_constant R p d f, --cases does not work as no prop
  exact (classical.choice (bernoulli_measure_nonempty p d R hc)).val g,
  { sorry, },
  { sorry, },
  { sorry, },
end
--function on clopen subsets of Z/dZ* x Z_p* or work in Z_p and restrict
--(i,a + p^nZ_p) (i,d) = 1

lemma cont_paLf : continuous (λ (a : (units (zmod d) × units ℤ_[p])),
  ((pri_dir_char_extend p d R) a) * (inj (teichmuller_character p (a.snd)))^(p - 2)
  * (w.to_fun a : R)) :=
sorry

def f : R := sorry

--h wont go in the system if you put it in [], is this independent of c?
noncomputable def p_adic_L_function [h : function.injective inj] (hc : gcd c p = 1) :=
 (f R) * (integral (units (zmod d) × units ℤ_[p]) R _ (bernoulli_measure_of_measure p d R hc)
⟨(λ (a : (units (zmod d) × units ℤ_[p])), ((pri_dir_char_extend p d R) a) *
  (inj (teichmuller_character p a.snd))^(p - 2) * (w.to_fun a : R)), cont_paLf p d R inj w ⟩)
--is it accurate to say that ω⁻¹ = ω^(p - 2)? I think so
