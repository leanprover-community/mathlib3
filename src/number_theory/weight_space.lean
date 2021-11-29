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
import algebra.pointwise
import data.real.basic

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

/-structure system {X : Type*} [set X] :=
( h : ℕ → finset X )
( projlim : X = Prop ) --inverse limit -/

/-- Making `zmod` a discrete topological space. -/
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

instance : inhabited (weight_space A p d) :=
begin
  constructor,
  constructor,
  swap, { rintros, refine (mul_one 1).symm, },
  refl,
end

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
{ one := ⟨monoid_hom.has_one.one, rfl, by simp, continuous_const ⟩ }

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
variables (R : Type*) [normed_comm_ring R] [complete_space R] (inj : ℤ_[p] → R) (m : ℕ)
  (χ : mul_hom (units (zmod (d*(p^m)))) R) (w : weight_space R p d)
--variables (d : ℕ) (hd : gcd d p = 1) (χ : dirichlet_char_space A p d) (w : weight_space A p)
--need χ to be primitive

--lemma units_coprime : units (zmod (d*(p^m))) = ((units (zmod d)) × (units (zmod (p^m)))) :=

example {α β : Type*} [has_mul α] [has_mul β] [has_add α] [has_add β] (h : α ≃+* β) : α ≃* β :=
  by refine ring_equiv.to_mul_equiv h

example {α β γ : Type*} [mul_one_class β] [mul_one_class γ] [mul_one_class α]
  [monoid α] [monoid β] [monoid γ] (h : β →* γ) :
 mul_hom (α × β) (α × γ) := monoid_hom.to_mul_hom (monoid_hom.prod_map (monoid_hom.id _) h)

/- example {α β : Type*} [monoid α] [monoid β] : units (α × β) ≃ units α × units β :=
{
  to_fun :=
  inv_fun :=
  right_inv := sorry
  left_inv := sorry
}-/

/-- Extending the primitive dirichlet character χ with conductor (d* p^m) -/
noncomputable def pri_dir_char_extend [fact (0 < m)] (h : gcd d p = 1)
  (χ : mul_hom (units (zmod (d*(p^m)))) R) : mul_hom ((units (zmod d)) × (units ℤ_[p])) R :=
begin
  have : nat.coprime d (p^m),
  { rw nat.coprime_pow_right_iff, rw nat.coprime_iff_gcd_eq_one,
    { exact h, },
    { apply fact.out, }, },
  refine mul_hom.comp χ
    (mul_hom.comp (mul_equiv.symm (units.map_equiv
      (zmod.chinese_remainder this).to_mul_equiv)).to_mul_hom _),
  { refine mul_hom.comp (mul_equiv.symm (mul_equiv.prod_units)).to_mul_hom
      (monoid_hom.to_mul_hom (monoid_hom.prod_map (monoid_hom.id _) (units.map _))),
    refine (padic_int.to_zmod_pow _).to_monoid_hom, },
end
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

/-- Gives the clopen sets that act as a topological basis for `ℤ_[p`. -/
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
  ext, simp only [mem_ball_zero_iff, set_like.mem_coe],
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

-- enable set addition for additive groups
open_locale pointwise

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
  rw [preimage_to_zmod_pow, ker_to_zmod_pow],
  refine is_open.add_left _, exact is_open_span p n,
end

lemma proj_lim_preimage_clopen (n : ℕ) (a : zmod (d*(p^n))) :
  is_clopen (set.preimage (padic_int.to_zmod_pow n) {a} : set ℤ_[p]) :=
begin
  split,
  { refine continuous_def.mp (continuous_to_zmod_pow p n) {a} trivial, },
  { refine continuous_iff_is_closed.mp (continuous_to_zmod_pow p n) {a} _, simp, },
end

example {α : Type*} [h : has_add α] : has_add (set α) := by refine set.has_add

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

lemma is_clopen_singleton {α : Type*} [topological_space α] [discrete_topology α] (b : α) :
  is_clopen ({b} : set α) :=
 ⟨is_open_discrete _, is_closed_discrete _⟩

/-- The clopen sets that form a topological basis for `zmod d × ℤ_[p]`. It is better than
  `clopen_basis` because one need not use `classical.choice`. -/
def clopen_from (n : ℕ) (a : zmod (d * (p^n))) : clopen_sets (zmod d × ℤ_[p]) :=
⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_singleton (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩

/-- The version of `clopen_basis` that also incorporates `d` coprime to `p`. -/
@[reducible] def clopen_basis' :=
{x : clopen_sets ((zmod d) × ℤ_[p]) // ∃ (n : ℕ) (a : zmod (d * (p^n))),
  x = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_singleton (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩ }

example (n : ℕ) (a : zmod (d * (p^n))) : clopen_basis' p d :=
⟨clopen_from p d n a, ⟨n, a, rfl⟩⟩

example (U : clopen_basis' p d) : clopen_sets (zmod d × ℤ_[p]) := U.val

-- lemma mem_clopen_basis' (U : clopen_sets ((zmod d) × ℤ_[p])) (hU : U ∈ clopen_basis' p d) :
--   ∃ (n : ℕ) (a : zmod (d * (p^n))),
--   U = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
--     is_clopen_prod (is_clopen_singleton (a : zmod d))
--       (proj_lim_preimage_clopen p d n a) ⟩ := sorry

/-def clopen_basis' : set (clopen_sets ((zmod d) × ℤ_[p])) :=
{x : clopen_sets ((zmod d) × ℤ_[p]) | ∃ (n : ℕ) (a : zmod (p^n)) (b : zmod d),
  x = ⟨({b} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) a),
    is_clopen_prod (is_clopen_singleton b) (proj_lim_preimage_clopen p n a) ⟩ }-/


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

example (a : ℝ) (m n : ℤ) : a^(0 : ℤ) = 1 := gpow_zero a

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
      repeat{rw fpow_neg, rw ←one_div,},
      apply one_div_lt_one_div_of_lt, norm_num, convert pow_pos _ m,
      { norm_num, apply lt_of_le_of_ne,
        { apply nat.zero_le, },
        { symmetry, apply nat.prime.ne_zero, apply fact.out, }, },
      { rw fpow_lt_iff_lt _,
        { norm_num, },
        { norm_cast, apply nat.prime.one_lt, apply fact.out, }, }, },
    { rintros c hc, apply h, simp only [metric.mem_ball, fpow_neg, gpow_coe_nat] at hc,
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
          { rw ←gpow_coe_nat (p : ℝ) m, rw ←fpow_add,
            { rw neg_add_self, rw gpow_zero _, },
            apply f, },
          { apply pow_ne_zero _, apply f, apply_instance, }, },
        rw this, refine le_trans (dist_appr_spec p a m.succ) _,
        { rw fpow_le_iff_le _,
          { apply neg_le_neg, norm_num, },
          { norm_cast, apply nat.prime.one_lt, apply fact.out, }, }, },
      convert add_lt_add_of_lt_of_le hc ha,
      rw [←one_div, div_add_div_same, one_add_one_eq_two], }, },
  { rintros x hx,
    rw clopen_basis at hx, simp only [set.mem_set_of_eq] at hx, rcases hx with ⟨n, a, hx⟩, rw hx,
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
def E_c (hc : gcd c p = 1) := λ (n : ℕ) (a : (zmod (d * (p^n)))), fract ((a.val : ℚ) / (d*p^n))
    - c * fract ( (((((c : zmod (d * p^(2 * n)))⁻¹ : zmod (d * p^n)) * a) : zmod (d * p^n)) : ℚ) / (d * p^n)) + (c - 1)/2

-- I don't understand why this works!
example (n : ℕ) (a b : zmod n) : ((a * b) : ℚ) = (a : ℚ) * (b : ℚ) :=
begin
  have : zmod n → ℤ, exact zmod.val_min_abs,
  rw coe_to_lift,
end
--instance {α : Type*} [topological_space α] : semimodule A (locally_constant α A) := sorry

example (x y : ℤ) : x + y - x = y := add_sub_cancel' x y

example (m : ℕ) : (2 : ℝ) / (p^m) = (1 / (p^m)) + (1 : ℝ) / (p^m) :=
begin
  rw ←add_div, refl,
end

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
    have f : (2 : ℝ) / (p^m) = (1 / (p^m)) + (1 : ℝ) / (p^m), {  rw ←add_div, refl, },
    rw f, rw dist_comm _ ↑y,
    have f' : ↑p ^ (1 - (m.succ : ℤ)) = (1 : ℝ) / (p^m),
    { symmetry, rw div_eq_iff _, rw ←gpow_coe_nat, rw ←fpow_add _,
      norm_num, rw sub_add, rw add_sub_cancel', rw sub_self, rw gpow_zero,
      any_goals { apply pow_ne_zero, },
      all_goals { norm_cast, apply nat.prime.ne_zero, apply fact.out, }, },
    rw f' at h,
    rw add_comm (dist _ _) _,
    have f'' : ↑p ^ -(m.succ : ℤ) < (1 : ℝ) / (p^m),
    { rw div_eq_inv_mul, rw mul_one, rw fpow_neg, rw inv_lt_inv,
      { simp, rw fpow_add, simp, rw ←mul_one ((p : ℝ)^m), rw mul_comm, rw mul_comm _ (p : ℝ), apply mul_lt_mul,
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

/-- The set of Bernoulli measures. -/
def bernoulli_measure (hc : gcd c p = 1) [has_coe ℚ R] :=
 {x : locally_constant (zmod d × ℤ_[p]) R →ₗ[R] R |
   ∀ (n : ℕ) (a : zmod (d * (p^n))), x (char_fn (zmod d × ℤ_[p]) ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
     is_clopen_prod (is_clopen_singleton (a : zmod d))
       (proj_lim_preimage_clopen p d n a) ⟩) =
     E_c p d hc n a }

/-
@[reducible] def clopen_basis' :=
{x : clopen_sets ((zmod d) × ℤ_[p]) // ∃ (n : ℕ) (a : zmod (d * (p^n))),
  x = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_singleton (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩ }
-/
variables (d)

open_locale big_operators

-- lemma what_to_do (f : locally_constant (zmod d × ℤ_[p]) R) : ∃ (s : finset ℕ)
--   (j : s → R) (i : s → (clopen_basis' p d)), f = ∑ k : s, j(k) • (char_fn (zmod d × ℤ_[p]) (i k)) :=
-- begin
--   sorry,
-- end

-- /-- To define a linear map on locally constant functions, it is sufficient to define it for
--   characteristic functions on the topological basis `clopen_basis'`. -/
-- noncomputable lemma pls_work (f : clopen_basis' p d → R) : locally_constant (zmod d × ℤ_[p]) R →ₗ[R] R :=
-- begin
-- constructor, swap 3,
-- { intro g,
--   set s := classical.some (what_to_do p d R g) with hs,
--  --     have hs := classical.some_spec (what_to_do p d R f),
--   set i := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R g))) with hi,
--   set j := classical.some (classical.some_spec (what_to_do p d R g)) with hj,
--   have hs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R g))),
--   exact ∑ k : s, j(k) * f(i(k)), },
--   { sorry, },
--   sorry,
-- end

--import linear_algebra.finsupp
variables (R' M N : Type*) [ring R'] [add_comm_group M] [add_comm_group N]
  [module R' M] [module R' N] (S : set M)

lemma mem_nonempty {α : Type*} {s : set α} {x : α} (h : x ∈ s) : nonempty s := ⟨⟨x, h⟩⟩

/-instance : is_absolute_value (norm : R → ℝ) :=
begin
  constructor, repeat {simp,}, refine norm_add_le, sorry,
end-/

/-instance partial_order_R : partial_order R :=
begin
  fconstructor,
  exact λ a b, true,
  repeat {simp,},
end-/

/-- A sequence has the `is_eventually_constant` predicate if all the elements of the sequence
  are eventually the same. -/
def is_eventually_constant {α : Type*} (a : ℕ → α) : Prop :=
 { n | ∀ m, n ≤ m → a (nat.succ m) = a m }.nonempty

/-- An eventually constant sequence is a sequence which has the `is_eventually_constant`
  predicate. -/
structure eventually_constant_seq {α : Type*} :=
(to_seq : ℕ → α)
(is_eventually_const : is_eventually_constant to_seq)

/-- The smallest number `m` for the sequence `a` such that `a n = a (n + 1)` for all `n ≥ m`. -/
noncomputable def sequence_limit_index' {α : Type*} (a : @eventually_constant_seq α) : ℕ :=
Inf { n | ∀ m, n ≤ m → a.to_seq m.succ = a.to_seq m }

/-- The smallest number `m` for the sequence `a` such that `a n = a m` for all `n ≥ m`. -/
noncomputable def sequence_limit_index {α : Type*} (a : ℕ → α) : ℕ :=
Inf { n | ∀ m, n ≤ m → a n = a m }

/-- The limit of an `eventually_constant_seq`. -/
noncomputable def sequence_limit {α : Type*} (a : @eventually_constant_seq α) :=
a.to_seq (sequence_limit_index' a)

example (m n : ℕ) (h : m ≤ n.succ) : m ≤ n ∨ m = n.succ := nat.of_le_succ h

lemma sequence_limit_eq {α : Type*} (a : @eventually_constant_seq α) (m : ℕ)
  (hm : sequence_limit_index' a ≤ m) : sequence_limit a = a.to_seq m :=
begin
  rw sequence_limit,
  induction m with d hd,
  { rw nat.le_zero_iff at hm,rw hm, },
  { have := nat.of_le_succ hm,
    cases this,
    { have le_d := hd this, rw le_d,
      have mem := nat.Inf_mem a.is_eventually_const, --simp at mem,
      simp only [set.mem_set_of_eq] at mem,
      refine (mem d _).symm,
      exact this, },
    { rw this, }, },
end

/-- Given `a ∈ zmod (d * p^n)`, and `n < m`, the set of all `b ∈ zmod (d * p^m)` such that
  `b = a mod (d * p^n)`. -/
def equi_class (n m : ℕ) (h : n < m) (a : zmod (d * p^n)) :=
 {b : zmod (d * p^m) | (b : zmod (d * p^n)) = a}
-- change def to a + k*dp^m

lemma mem_equi_class (n m : ℕ) (h : n < m) (a : zmod (d * p^n)) (b : zmod (d * p^m)) :
  b ∈ equi_class p d n m h a ↔ (b : zmod (d * p^n)) = a :=
⟨λ hb, begin rw equi_class at hb, simp at hb, exact hb, end,
  λ hb, begin rw equi_class, simp, exact hb, end⟩

lemma equi_class_some (n : ℕ) (x : zmod (d * p^n)) (y : equi_class p d n n.succ (lt_add_one n) x) :
  ∃ k : ℕ, k < p ∧ (y : zmod (d * p^n.succ)).val = x.val + k * d * p^n :=
begin
  have := (mem_equi_class p d n n.succ (lt_add_one n) x y).1 (y.prop),
  conv { congr, funext, conv { congr, skip, to_rhs, rw ←((mem_equi_class p d n n.succ (lt_add_one n) x y).1 (y.prop)), }, },
  rw ←@zmod.nat_cast_comp_val _ _ _ _,
  show ∃ (k : ℕ), k < p ∧ (y : zmod (d * p^n.succ)).val = ((y : zmod (d * p^n.succ)).val : zmod (d * p^n)).val + k * d * p ^ n,
  rw zmod.val_nat_cast,
  use (y : zmod (d * p^n.succ)).val / (d * p^n), split,
  { apply nat.div_lt_of_lt_mul, rw nat.mul_assoc,
    rw ←pow_succ',
    apply @zmod.val_lt _ (fact_iff.2 _) (y : zmod (d * p^n.succ)),
    apply mul_pos, rw fact_iff at *, assumption,
    apply pow_pos, apply nat.prime.pos, rw fact_iff at *, assumption, },
  { rw mul_assoc,
    rw nat.mod_add_div' (y : zmod (d * p^n.succ)).val (d * p^n), },
  { rw fact_iff at *,
    apply mul_pos, rw fact_iff at *, assumption,
    apply pow_pos, apply nat.prime.pos, assumption, },
end

/-- Giving an equivalence between `equi_class` and `fin p`. -/
def equi_iso_fin (m : ℕ) (a : zmod (d * p^m)) : equi_class p d m m.succ (lt_add_one m) a ≃ fin p :=
{ to_fun := λ y, ⟨((y.val).val - a.val) / (d * p^m), begin
    apply nat.div_lt_of_lt_mul,
    have : 0 < d * p ^ m.succ,
      rw fact_iff at *, apply mul_pos, assumption, apply ((pow_pos (nat.prime.pos _)) _), assumption,
    have := @zmod.val_lt _ (fact_iff.2 this) y.val,
    rw [mul_assoc, ←pow_succ'],
    have f := nat.sub_le (y.val).val a.val,
    exact lt_of_le_of_lt f this,
end⟩,
  inv_fun := λ k, ⟨(a.val + k * d * p^m : ℕ), begin
    rw mem_equi_class,
    have g : (d * (p^m)) ∣ (d * p^(m.succ)),
    { apply mul_dvd_mul,
      { refl, },
      { rw pow_succ' p m, exact dvd.intro p rfl, }, },
    rw zmod.cast_nat_cast g _, swap, apply_instance,
    rw nat.cast_add,
    rw @zmod.nat_cast_zmod_val _ _ _, swap,
    { rw fact_iff at *, apply mul_pos, assumption, apply ((pow_pos (nat.prime.pos _)) m), assumption, },
    rw mul_assoc,
    simp,
  end⟩,
  left_inv := begin
    rintros x,
    rw subtype.ext_iff_val, simp only [fin.coe_mk, subtype.val_eq_coe, _root_.coe_coe],
    rw mul_assoc,
    obtain ⟨k, hk, h⟩ := equi_class_some p d m a x,
    rw nat.div_mul_cancel,
    { have : fact (0 < d * p ^ m.succ),
      { rw fact_iff at *, apply mul_pos, assumption, apply ((pow_pos (nat.prime.pos _)) m.succ), assumption, },
      rw nat.add_sub_cancel',
      { rw @zmod.nat_cast_val _ _ _ this _, norm_cast, },
      { rw h, apply nat.le_add_right, }, },
    { rw [h, nat.add_sub_cancel_left, mul_assoc], simp, },
  end,
  right_inv := begin
    rintros x,
    simp only [nat.cast_pow],
    rw subtype.ext_iff_val,
    simp only [fin.coe_mk, subtype.val_eq_coe, _root_.coe_coe],
    have : fact (0 < d * p ^ m.succ),
    { rw fact_iff at *, apply mul_pos, assumption, apply ((pow_pos (nat.prime.pos _)) m.succ), assumption, },
    have h2 : fact (0 < d * p ^ m),
    { rw fact_iff at *, apply mul_pos, assumption, apply ((pow_pos (nat.prime.pos _)) m), assumption, },
    apply nat.div_eq_of_eq_mul_left,
    { apply fact_iff.1 h2, },
    apply nat.sub_eq_of_eq_add,
    rw [mul_assoc, zmod.val_nat_cast, nat.mod_eq_of_lt],
    have h1 := @zmod.val_lt _ h2 a,
    have h2 : ↑x * (d * p ^ m) ≤ (d * p ^ m) * (p - 1),
    { rw mul_comm, apply nat.mul_le_mul_left, rw [←nat.lt_succ_iff, nat.succ_eq_add_one, nat.sub_add_cancel], apply x.2,
      { apply le_of_lt (fact_iff.1 (nat.prime.one_lt' p)), }, },
    have := add_lt_add_of_lt_of_le h1 h2,
    convert this,
    ring_nf, rw nat.sub_add_cancel,
    { rw ←pow_succ, },
    { apply le_of_lt, apply fact_iff.1 (nat.prime.one_lt' p), },
  end }

instance imp [fact (0 < d)] : ∀ n : ℕ, fact (0 < d * p^n) :=
begin
  rintros n, rw fact_iff at *, apply mul_pos,
  { assumption, },
  { apply ((pow_pos (nat.prime.pos _)) n), assumption, },
end

--example {α β : Type*} (h : α ≃ β) [fintype α] {s : set α} : fintype s := by library_search

noncomputable instance (n m : ℕ) (h : n < m) (a : zmod (d * p^n)) :
  fintype (equi_class p d n m h a) :=
begin
  suffices : fintype (zmod (d * p^m)),
  { refine set.finite.fintype _,
    refine set.finite.subset _ _,
    { exact set.univ, },
    { rw set.univ_finite_iff_nonempty_fintype,
      exact nonempty.intro this, },
    { simp only [set.subset_univ], }, },
  refine zmod.fintype (d * p^m),
end

/-
/-- For m > n, E_c(χ_(b,a,n)) = ∑_{j, b_j = a mod p^n} E_c(χ_(b,b_j,m)) -/
lemma sum_char_fn_dependent_Ec (m : ℕ) (a : zmod (p^m)) (b : zmod d) (hc : gcd c p = 1) :
  E_c p d hc m a = ∑ x in set.to_finset (equi_class p d m m.succ (lt_add_one m) a), E_c p d hc m.succ x :=
sorry

lemma loc_const_const (f : locally_constant (zmod d × ℤ_[p]) R) (a : zmod d × ℤ_[p]) : ∃ N : ℕ, ∀ m ≥ N,
  ∀ y ∈ {b : zmod d × ℤ_[p] | (to_zmod_pow m) a.2 = (to_zmod_pow m) b.2}, f y = f a :=
sorry -/

lemma remove_extras (x : zmod d × ℤ_[p]) (n : ℕ) :
  is_clopen {b : zmod d × ℤ_[p] | (to_zmod_pow n) x.snd = (to_zmod_pow n) b.snd ∧ x.fst = b.fst} :=
begin
  set f : zmod d × ℤ_[p] → zmod d × zmod (p^n) := prod.map id (to_zmod_pow n) with hf,
  convert_to is_clopen (set.preimage f {f x}),
  { ext y, rw set.mem_preimage, rw set.mem_singleton_iff, rw hf, simp, rw and_comm, rw eq_comm,
    rw @eq_comm _ ((to_zmod_pow n) x.snd) _, },
  have : continuous f,
  { refine continuous.prod_map (continuous_id) (continuous_to_zmod_pow p n), },
  split,
  { refine continuous_def.mp this {f x} _,
    exact is_open_discrete {f x}, },
  { refine continuous_iff_is_closed.mp this {f x} _, simp, },
end

/-- TBD -/
noncomputable def F : ℕ → discrete_quotient (zmod d × ℤ_[p]) := λ n,
  ⟨λ a b, to_zmod_pow n a.2 = to_zmod_pow n b.2 ∧ a.1 = b.1,
    ⟨ by tauto, by tauto, λ a b c hab hbc, begin simp at *, split, rw [hab.1, hbc.1], rw [hab.2, hbc.2], end⟩,
    λ x, begin apply remove_extras p d x n,
--      convert_to is_clopen ((({x.1} : set (zmod d)) × (set.preimage (to_zmod_pow n) {to_zmod_pow n x.2})) : set ((zmod d) × ℤ_[p])),
--      { ext1 y, simp, split; try { intro h, rw set.mem_singleton_iff at *, rw h, }, },
--      { convert proj_lim_preimage_clopen p 1 n (to_zmod_pow n x), rw one_mul, simp, },
end⟩

/-lemma loc_const_const' (f : locally_constant (zmod d × ℤ_[p]) R) : ∃ N : ℕ, ∀ m ≥ N,
  ∀ y ∈ {b : zmod d × ℤ_[p] | (to_zmod_pow m) a.2 = (to_zmod_pow m) b.2}, f y = f a :=
sorry-/

noncomputable def coe_padic_to_zmod (n : ℕ) (x : zmod d × ℤ_[p]) (hd : gcd d p = 1) : zmod (d * p^n) :=
--  ((x.1, (to_zmod_pow n)x.2) : zmod (d * p ^ n))
  (zmod.chinese_remainder (nat.coprime.pow_right _ (nat.coprime_iff_gcd_eq_one.1 hd))).inv_fun (x.1, (to_zmod_pow n)x.2)
-- should this be used

/-def bound_set (U : set (zmod d × ℤ_[p])) (hU : is_open U) (hd : gcd d p = 1) :=
  {n : ℕ | ∀ (a : zmod d × ℤ_[p]) (H : a ∈ U), ∃ m : ℕ, n ≤ m ∧
    (clopen_from p d m (coe_padic_to_zmod p d m a hd)).val ⊆ U } -/

def bound_set (U : set (zmod d × ℤ_[p])) (hU : is_open U) (hd : gcd d p = 1) :=
  {n : ℕ | ∀ (a : zmod d × ℤ_[p]) (H : a ∈ U),
    (clopen_from p d n (coe_padic_to_zmod p d n a hd)).val ⊆ U }

noncomputable def bound (U : set (zmod d × ℤ_[p])) (hU : is_open U) (hd : gcd d p = 1) : ℕ :=
  Inf (bound_set p d U hU hd)
/-noncomputable def bound (U : set (zmod d × ℤ_[p])) (hU : is_open U) := ⨅ (n : ℕ),
  ∃ (a : zmod (d * p^n)), (clopen_from p d n a).val ⊆ U -/

lemma F_rel (x y : zmod d × ℤ_[p]) (n : ℕ) : (F p d n).rel x y ↔
  (to_zmod_pow n) x.snd = (to_zmod_pow n) y.snd ∧ x.fst = y.fst := by { rw F, }

example {X} {α : Type*} [topological_space X] (f : locally_constant X α) (x y : X)
  (h : f.discrete_quotient.rel x y) : f y = f x := h

example {α : Type*} (a b : α) (c : α × α) (h : c = (a,b)) : c.fst = a := by refine (congr_arg prod.fst h).trans rfl

lemma mem_clopen_from (n : ℕ) (a : zmod (d * p^n)) (y : zmod d × ℤ_[p]) :
  y ∈ (clopen_from p d n a).val ↔ y.fst = (a : zmod d) ∧
    (a : zmod (p^n)) = (to_zmod_pow n) y.snd :=
begin
  dsimp [clopen_from],
  simp only [set.mem_preimage, set.mem_image, set.mem_singleton_iff, set.singleton_prod],
  split, all_goals { intro h, },
  { cases h with x hx, split,
    { rw ←(congr_arg prod.fst hx.2).trans rfl, },
    { rw ←hx.1, apply congr_arg, rw ←(congr_arg prod.snd hx.2).trans rfl, }, },
  { refine ⟨y.snd, h.2.symm, _⟩, rw ←h.1, simp only [prod.mk.eta], },
end

lemma proj_fst' (m n : ℕ) (h : m.coprime n) (a : zmod m) (b : zmod n) :
  zmod.cast_hom (show m ∣ m * n, from dvd.intro n rfl) (zmod m)
    ((zmod.chinese_remainder h).inv_fun (a,b)) = a :=
begin
  have h2 : zmod.cast_hom (show m.lcm n ∣ m * n, by simp [nat.lcm_dvd_iff]) (zmod m × zmod n) _ = _,
    exact (zmod.chinese_remainder h).right_inv (a,b),
  change _ = prod.fst (a, b),
  conv_rhs { rw ←h2, },
  convert_to _ = (ring_hom.comp (ring_hom.fst (zmod m) (zmod n))
    (zmod.cast_hom _ (zmod m × zmod n))) ((zmod.chinese_remainder h).inv_fun (a, b)) using 1,
  apply congr _ rfl, congr,
  refine ring_hom.ext_zmod _ _,
end

lemma proj_fst (n : ℕ) (x : zmod d × ℤ_[p]) (cop : d.coprime (p^n)) :
  ↑((zmod.chinese_remainder cop).inv_fun (x.fst, (to_zmod_pow n) x.snd)) = x.fst :=
  proj_fst' _ _ _ _ _

lemma proj_snd' (m n : ℕ) (h : m.coprime n) (a : zmod m) (b : zmod n) :
  zmod.cast_hom (show n ∣ m * n, from dvd.intro_left m rfl) (zmod n)
    ((zmod.chinese_remainder h).inv_fun (a,b)) = b :=
begin
  have h2 : zmod.cast_hom (show m.lcm n ∣ m * n, by simp [nat.lcm_dvd_iff]) (zmod m × zmod n) _ = _,
    exact (zmod.chinese_remainder h).right_inv (a,b),
  change _ = prod.snd (a, b),
  conv_rhs { rw ←h2, },
  convert_to _ = (ring_hom.comp (ring_hom.snd (zmod m) (zmod n))
    (zmod.cast_hom _ (zmod m × zmod n))) ((zmod.chinese_remainder h).inv_fun (a, b)) using 1,
  apply congr _ rfl, congr,
  refine ring_hom.ext_zmod _ _,
end

lemma proj_snd (n : ℕ) (x : zmod d × ℤ_[p]) (cop : d.coprime (p^n)) :
  ↑((zmod.chinese_remainder cop).inv_fun (x.fst, (to_zmod_pow n) x.snd)) =
  (to_zmod_pow n) x.snd :=
proj_snd' _ _ _ _ _

lemma coprime_pow_spl (n : ℕ) (hd : gcd d p = 1) : d.coprime (p^n) :=
  nat.coprime.pow_right _ (nat.coprime_iff_gcd_eq_one.1 hd)

lemma mem_clopen_from' (n : ℕ) (x : zmod d × ℤ_[p]) (y : zmod d × ℤ_[p]) (hd : gcd d p = 1) :
  y ∈ (clopen_from p d n (coe_padic_to_zmod p d n x hd)).val ↔ (F p d n).rel x y :=
begin
  rw mem_clopen_from, rw F_rel, rw coe_padic_to_zmod,
  split, all_goals {intro h,},
  { rw and_comm, rw eq_comm, convert h,
    { --split_ifs,
      have := (zmod.chinese_remainder (coprime_pow_spl p d n hd)).inv_fun,
      apply (proj_fst _ _ _ _ _).symm, assumption, },
    { apply (proj_snd _ _ _ _ _).symm, assumption, }, },
  { rw ←h.2, rw ←h.1,
    refine ⟨(proj_fst p d n x (coprime_pow_spl p d n hd)).symm,
      (proj_snd p d n x (coprime_pow_spl p d n hd))⟩, },
end

lemma mem_clopen_from'' (n : ℕ) (x : zmod d × ℤ_[p]) (y : zmod d × ℤ_[p]) (hd : gcd d p = 1)
  (hy : y ∈ (clopen_from p d n (coe_padic_to_zmod p d n x hd)).val) :
  (clopen_from p d n (coe_padic_to_zmod p d n x hd)).val =
  (clopen_from p d n (coe_padic_to_zmod p d n y hd)).val :=
begin
  ext z,
  repeat { rw mem_clopen_from at *, }, rw ←hy.1, rw hy.2,
  rw coe_padic_to_zmod,
  rw proj_fst p d n y (coprime_pow_spl p d n hd),
  rw proj_snd p d n y (coprime_pow_spl p d n hd),
end

lemma le_F_of_ge (k n : ℕ) (h : k ≤ n) : (F p d n) ≤ (F p d k) :=
begin
  rintros x y hn, rw F_rel at *,
  refine ⟨_, hn.2⟩, repeat { rw ←cast_to_zmod_pow _ _ h _, },
  apply congr_arg, exact hn.1,
end

lemma clopen_sub_clopen (k n : ℕ) (h : k ≤ n) (x : zmod d × ℤ_[p]) (hd : gcd d p = 1) :
  (clopen_from p d n (coe_padic_to_zmod p d n x hd)).val ⊆
    (clopen_from p d k (coe_padic_to_zmod p d k x hd)).val :=
begin
  intros z hz,
  rw mem_clopen_from' at *,
  apply (le_F_of_ge p d k n h) x z hz,
end

/-example {U : set (zmod d × ℤ_[p])} (hd : gcd d p = 1) (hU : is_open U)(n : ℕ)
  (hn : n ∈ (bound_set p d U hU hd)) (x : zmod (d * p^n)) (memU : x ∈ U) :
    (clopen_from p d n x).val ⊆ U := hn _ memU-/

example {α : Type*} [topological_space α] {U : set α} (hU :is_clopen U) : is_open U := hU.1

--instance : topological_space (zmod d × ℤ_[p]) := prod.topological_space

/-example (n : ℕ) (y : zmod (p^n)) : is_clopen ((to_zmod_pow n) ⁻¹' ({y} : set (zmod (p^n)))) :=
  by refine is_locally_constant.is_clopen_fiber _ y-/

lemma proj_lim_preimage_clopen' (n : ℕ) (a : zmod (p^n)) :
  is_clopen (set.preimage (padic_int.to_zmod_pow n) {a} : set ℤ_[p]) :=
begin
  split,
  { refine continuous_def.mp (continuous_to_zmod_pow p n) {a} trivial, },
  { refine continuous_iff_is_closed.mp (continuous_to_zmod_pow p n) {a} _, simp, },
end

theorem clopen_basis'_topo_basis (hd : gcd d p = 1) : topological_space.is_topological_basis
  {V | ∃ (U : clopen_basis' p d), V = (U.val).val} :=
begin
  have := topological_space.is_topological_basis.prod
    (@discrete_topology.is_topological_basis (zmod d) _ _ _) (clopen_basis_clopen p).1,
  convert this,
  ext V,
  split, any_goals { intro hy, },
  { cases hy with U hU,
    obtain ⟨n, w, h⟩ := U.prop,
    refine ⟨{(w : zmod d)}, ((to_zmod_pow n) ⁻¹' {↑w}), _, _⟩,
    { rw set.mem_range, use (w : zmod d),
      rw set.singleton_hom, simp only [monoid_hom.coe_mk], },
    { rw clopen_basis, rw hU,
      have := subtype.ext_iff_val.1 h, simp only [subtype.val_eq_coe] at this,
      repeat { rw subtype.val_eq_coe, }, rw ←this,
      simp only [and_true, eq_self_iff_true, set.mem_set_of_eq],
      refine ⟨n, (w : zmod (p^n)), rfl⟩, }, },
  { rcases hy with ⟨x', y', hx, hy, h⟩,
    rw set.mem_range at hx, cases hx with x hx,
    rw clopen_basis at hy,
    simp only [set.mem_set_of_eq] at hy,
    rcases hy with ⟨n, y, hy⟩,
    set U' : clopen_sets (zmod d × ℤ_[p]) := ⟨({x} : set (zmod d)).prod
      (set.preimage (padic_int.to_zmod_pow n) {y}), is_clopen_prod (is_clopen_singleton x)
      (proj_lim_preimage_clopen' p n y) ⟩ with hU',
    set U : clopen_basis' p d := ⟨U', _⟩ with hU,
    any_goals { refine ⟨n, ((zmod.chinese_remainder (coprime_pow_spl p d n hd)).inv_fun (x, y)), _⟩,
      rw hU', congr,
      { convert (proj_fst' _ _ _ _ _).symm, },
      { convert (proj_snd' _ _ _ _ _).symm, }, },
    { refine ⟨U, _⟩,
      rw ←h, rw hU, simp only, congr,
      { rw ←hx, rw set.singleton_hom, simp only [monoid_hom.coe_mk], },
      { rw hy, }, }, },
end

--example {U : set (clopen_sets (zmod d × ℤ_[p]))} : set (zmod d × ℤ_[p]) ≃ set (zmod d) × set ℤ_[p] :=

lemma exists_clopen_from {U : set (zmod d × ℤ_[p])} (hU : is_open U) (hd : gcd d p = 1)
  {x : zmod d × ℤ_[p]} (memU : x ∈ U) : ∃ n : ℕ,
  (clopen_from p d n (coe_padic_to_zmod p d n x hd)).val ⊆ U :=
begin
  obtain ⟨V, H, memV, U_sub_V⟩ := topological_space.is_topological_basis.exists_subset_of_mem_open
    (clopen_basis'_topo_basis p d hd) memU hU,
  simp only [exists_prop, subtype.exists, set.mem_set_of_eq] at H,
  rcases H with ⟨W, H⟩, cases H with H hV,
  rcases H with ⟨n, a, H⟩, rw hV at U_sub_V,
  rw hV at memV, rw H at memV,
  simp only [set.mem_preimage, set.mem_image, set.mem_singleton_iff,
    set.singleton_prod] at memV,
  rcases memV with ⟨z', h'1, h'2⟩,
  use n, intros y hy,
  rw mem_clopen_from at hy, rw coe_padic_to_zmod at hy, rw proj_snd at hy, rw proj_fst at hy,
  rw ←h'2 at hy, simp only at hy,
  apply U_sub_V, rw H,
  simp only [set.mem_preimage, set.mem_image, set.mem_singleton_iff, set.singleton_prod],
  use y.snd,
  rw ←h'1, rw hy.2, rw ←hy.1,
  simp only [prod.mk.eta, eq_self_iff_true, and_self],
end

lemma bound_set_inhabited {U : set (zmod d × ℤ_[p])} (hU : is_clopen U) (hd : gcd d p = 1)
  (ne : nonempty U) : (bound_set p d U hU.1 hd).nonempty :=
begin
  have com : U ⊆ ⋃ (x : zmod d × ℤ_[p]) (hx : x ∈ U),
  (clopen_from p d (classical.some (exists_clopen_from p d hU.1 hd hx))
  (coe_padic_to_zmod p d (classical.some (exists_clopen_from p d hU.1 hd hx)) x hd)).val,
  { intros y hy, rw set.mem_Union, use y, rw set.mem_Union,
    refine ⟨hy, _⟩,
    rw mem_clopen_from, rw coe_padic_to_zmod, rw proj_fst, rw proj_snd,
    simp only [eq_self_iff_true, and_self], },
  obtain ⟨t, ht⟩ := is_compact.elim_finite_subcover _ _ _ com,
  { simp only at ht,
    set n : ℕ := Sup ⨆ (x : zmod d × ℤ_[p]) (H : x ∈ t) (hx : x ∈ U),
      {(classical.some (exists_clopen_from p d hU.1 hd hx))} with hn,
    use n, intros y hy,
    obtain ⟨z, hz⟩ := set.mem_Union.1 (ht hy),
    obtain ⟨H, hz⟩ := set.mem_Union.1 hz,
    obtain ⟨hz, h⟩ := set.mem_Union.1 hz,
    have h'' := mem_clopen_from'' p d _ z y hd h,
    transitivity (clopen_from p d (classical.some (exists_clopen_from p d hU.1 hd hz))
      (coe_padic_to_zmod p d (classical.some _) z hd)).val,
    { rw mem_clopen_from'' _ _ _ _ _ _ h,
      apply clopen_sub_clopen _ _ _ _ _ _ _,
      rw hn, apply le_cSup,
      { simp only [set.supr_eq_Union],
        --refine set.finite.bdd_above _, refine set.finite_of_finite_image _ _, simp, refine set.finite_def.mpr _,
        refine (set.finite.bdd_above_bUnion _).2 _,
        { exact finset.finite_to_set t, },
        { rintros i hi,
          refine set.finite.bdd_above _, refine set.finite_Union _, simp, }, },
      { simp only [exists_prop, set.mem_Union, set.mem_singleton_iff, set.supr_eq_Union],
        refine ⟨z, H, hz, rfl⟩, }, },
    { apply classical.some_spec (exists_clopen_from _ _ _ _ hz), }, },
  { apply compact_of_is_closed_subset _ _,
    swap 2, exact set.univ,
    simp,
    exact compact_univ,
    apply hU.2, },
  { rintros i,
    apply @is_open_Union _ _,
    intro hi, refine (clopen_from _ _ _ _).prop.1, },
end

lemma bound_mem_bound_set {U : set (zmod d × ℤ_[p])} (hU : is_clopen U) (hd : gcd d p = 1)
  (ne : nonempty U) : bound p d U hU.1 hd ∈ bound_set p d U hU.1 hd :=
  nat.Inf_mem (bound_set_inhabited _ _ hU _ ne)

lemma le_bound (U : set (zmod d × ℤ_[p])) (hU : is_clopen U) (hd : gcd d p = 1) (x : zmod d × ℤ_[p])
  (memU : x ∈ U) (n : ℕ) (h : bound p d U hU.1 hd ≤ n) (hd : gcd d p = 1) (ne : nonempty U) :
  (clopen_from p d n (coe_padic_to_zmod p d n x hd)).val ⊆ U :=
begin
  transitivity (clopen_from p d (bound p d U hU.1 hd)
    (coe_padic_to_zmod p d (bound p d U hU.1 hd) x hd)).val,
  intros y,
  repeat { rw mem_clopen_from', },
  suffices : (F p d n) ≤ (F p d (bound p d U hU.1 hd)),
  { apply this x y, },
  { apply le_F_of_ge p d _ _ h, },
  { apply bound_mem_bound_set p d hU hd ne x memU, },
end

lemma factor_F (hd : gcd d p = 1) (f : locally_constant (zmod d × ℤ_[p]) R) :
  ∃ N : ℕ, F p d N ≤ f.discrete_quotient :=
begin
  have : ∀ x : R, is_open (f⁻¹' {x}),
  { intros x, apply f.is_locally_constant, },
  have univ : f⁻¹' (set.univ : set R) = ⋃ (x : R), f⁻¹' {x},
  { rw set.preimage_univ, ext y,
    simp only [set.mem_preimage, set.mem_Union, set.mem_univ, set.mem_singleton_iff, exists_eq'], },
  rw set.preimage_univ at univ,
  have univ' := univ.symm,
  rw ←set.univ_subset_iff at univ',
  obtain ⟨t, ht⟩ := is_compact.elim_finite_subcover _ _ this univ',
  { simp only at ht,
    set n : ℕ := Sup ⨆ (x : R) (H : x ∈ t), {bound p d (f⁻¹' {x}) (this x) hd} with hn,
    refine ⟨n, _⟩,
    rintros x y hF,
    obtain ⟨i, hi⟩ := set.mem_Union.1 (ht (set.mem_univ x)),
    obtain ⟨hi, htx⟩ := set.mem_Union.1 hi,
    simp only [set.mem_preimage, set.mem_singleton_iff] at htx,
    rw F_rel at hF,
    change f y = f x,
    rw htx,
    have memU := set.mem_preimage.2 (set.mem_singleton_iff.2 htx),
    --have n_mem_bs : n ∈ bound_set p d (f⁻¹' {i}) (this i) hd, sorry, -- is this true?
    --set m := classical.some_spec (n_mem_bs x memU) with hm,
    have h1 : y ∈ (clopen_from p d n (coe_padic_to_zmod p d n x hd)).val,
    { rw mem_clopen_from, rw coe_padic_to_zmod, rw proj_fst, rw proj_snd,
      simp only [hF, eq_self_iff_true, and_self], },
    rw ←set.mem_singleton_iff,
    rw ←set.mem_preimage,
    refine le_bound _ _ _ _ hd _ memU _ _ _ _ h1,
    { refine ⟨this i, is_closed.preimage (locally_constant.continuous f) (t1_space.t1 i)⟩, },
    { apply le_cSup,
      { simp only [set.supr_eq_Union], refine (set.finite.bdd_above_bUnion _).2 _,
        { exact finset.finite_to_set t, },
        { rintros i hi,
          exact bdd_above_singleton, }, },
      { simp only [exists_prop, set.mem_Union, set.mem_singleton_iff, set.supr_eq_Union],
        refine ⟨i, hi, rfl⟩, }, },
    exact mem_nonempty htx, },
  { exact compact_univ, },
end

example {α : Type*} [h : fintype α] : fintype (@set.univ α) := by refine set_fintype set.univ

lemma mul_prime_pow_pos (m : ℕ) : 0 < d * p^m :=
begin
  rw fact_iff at *,
  refine mul_pos _ _,
  { assumption, },
  { apply pow_pos (nat.prime.pos _), assumption, },
end

/-- A variant of `zmod` which has type `finset _`. -/
def zmod' (n : ℕ) (h : 0 < n) : finset (zmod n) :=
  @finset.univ _ (@zmod.fintype n (fact_iff.2 h))

--def zmod' (n : ℕ) (h : fact (0 < n)) : finset (zmod n) :=
--  @set.to_finset _ (@set.univ (zmod n)) (@set_fintype _ (@zmod.fintype n h) set.univ _)

lemma succ_eq_bUnion_equi_class : zmod' (d*p^m.succ) (mul_prime_pow_pos p d m.succ) =
  (zmod' (d*p^m) (mul_prime_pow_pos p d m)).bUnion
    (λ a : zmod (d * p ^ m), set.to_finset ((equi_class p d m m.succ (lt_add_one m)) a)) :=
sorry

example {R S : Type*} [ring R] [ring S] {f : R →+* S} {x y : R} (h : f x = 0) :
  x ∈ ring_hom.ker f := by refine (ring_hom.mem_ker f).mpr h

example {a b c : ℤ} (h : a ∣ (b - c) ) : -(b - c) = c - b := neg_sub b c

lemma mul_pow_lt_mul_pow_succ (m : ℕ) : d * p ^ m < d * p ^ m.succ :=
begin
  apply mul_lt_mul',
  any_goals { simp, },
  { apply nat.pow_lt_pow_succ, apply nat.prime.one_lt, apply fact.out, },
  { apply fact.out, },
end

example (a b c : ℕ) (h1 : a < b) (h2 : b ≤ c) : a < c := gt_of_ge_of_gt h2 h1

lemma val_le_val (n m : ℕ) [fact (0 < m)] (h : m ≤ n) (y : zmod n) : (y.val : zmod m).val ≤ y.val :=
begin
  by_cases y.val < m,
  { have := zmod.val_cast_of_lt h, rw this, },
  { push_neg at h,
    apply le_of_lt, apply gt_of_ge_of_gt h _, apply zmod.val_lt (y.val : zmod m), },
end

lemma equi_class_eq (f : locally_constant (zmod d × ℤ_[p]) R) (x : zmod (d * p^m)) (hd : gcd d p = 1)
  (h : classical.some (factor_F p d R hd f) ≤ m)
  (y : zmod (d * p^m.succ))
  (hy : y ∈ ((λ a : zmod (d * p ^ m), set.to_finset ((equi_class p d m m.succ (lt_add_one m)) a)) x)) :
  f y = f x :=
begin
  -- note that y ≠ ↑x !
  simp at hy, rw mem_equi_class at hy, rw ←locally_constant.factors,
  repeat { rw function.comp_apply, }, apply congr_arg,
  have h' := classical.some_spec (factor_F p d R hd f),
  have h'' := le_F_of_ge p d _ _ h,
  have h3 := le_trans h'' h',
--  have h4 := h3 x y,
  rw ←discrete_quotient.of_le_proj h3,
  repeat { rw function.comp_apply, }, apply congr_arg,
  suffices : ↑y ∈ ((F p d m).proj)⁻¹' {(F p d m).proj x},
  { rw set.mem_preimage at this, rw set.mem_singleton_iff at this, exact this, },
  rw discrete_quotient.fiber_eq, simp only [set.mem_set_of_eq],
  rw F_rel, simp only [prod.fst_zmod_cast, prod.snd_zmod_cast],
  rw ←hy,
  have val_le_val : (y.val : zmod (d * p^m)).val ≤ y.val,
  { apply val_le_val, apply le_of_lt, exact mul_pow_lt_mul_pow_succ p d m, },
  have : (d * p^m) ∣ y.val - (y.val : zmod (d * p^m)).val,
  { rw ←zmod.nat_coe_zmod_eq_zero_iff_dvd, rw nat.cast_sub val_le_val,
    { simp only [zmod.cast_id', id.def, sub_self, zmod.nat_cast_val], }, },
  split,
  { rw ←sub_eq_zero, rw ←ring_hom.map_sub, rw ←ring_hom.mem_ker, rw ker_to_zmod_pow,
    rw ideal.mem_span_singleton, repeat { rw ←zmod.nat_cast_val, }, rw ←dvd_neg, rw neg_sub,
    rw ←nat.cast_pow, rw ←nat.cast_sub val_le_val,
    { apply nat.coe_nat_dvd,
      apply dvd_trans (dvd_mul_left _ _) this, }, },
  { repeat { rw ←zmod.nat_cast_val, }, rw zmod.nat_coe_eq_nat_coe_iff,
    rw nat.modeq_iff_dvd' val_le_val, apply dvd_trans (dvd_mul_right _ _) this, },
end
-- This lemma has a lot of mini lemmas that can be generalized.

lemma fract_eq_self {a : ℚ} (h : 0 ≤ a) (ha : a < 1) : fract a = a :=
begin
   rw fract_eq_iff,
   refine ⟨h, ha, ⟨0, _⟩⟩, simp,
end

/-lemma coe_addd (m : ℕ) (b c : zmod (d * p^m.succ)) : (b + c : zmod (d * p^m)) = (b : zmod (d * p^m)) + (c : zmod (d * p^m)) :=
begin
  simp only [eq_self_iff_true],
end -/
-- (fact_iff.2 ((pow_pos (nat.prime.pos (fact_iff.1 _inst_3))) m))
lemma maybe_generalize (m : ℕ) : (coe : zmod (p^(m.succ)) → zmod (p^m)) ∘ (coe : zmod (p^m) → zmod (p^(m.succ))) = id :=
begin
 ext x,
  simp only [id.def, function.comp_app],
  have : p^m ∣ (p^(m+1)),
  { apply pow_dvd_pow, simp, },
  rw ← @zmod.nat_cast_val (p^m) _ _ (fact_iff.2 ((pow_pos (nat.prime.pos (fact_iff.1 _inst_3))) m)) x,
  conv_rhs {
    rw ← zmod.cast_id (p^m) x,
    rw ← @zmod.nat_cast_val (p^m) _ _ (fact_iff.2 ((pow_pos (nat.prime.pos (fact_iff.1 _inst_3))) m)) x, },
  exact zmod.cast_nat_cast this x.val,
end

lemma val_coe_eq_val (n m : ℕ) (b : zmod n) [h1 : fact (0 < n)] [h2 : fact (n < m)] :
  (b.val : zmod m).val = b.val :=
begin
  have : b.val = (b : zmod m).val,
  { have h1 := zmod.val_lt b,
    have h2 : b.val < m, { transitivity n, assumption, apply fact.out, },
    have := zmod.val_cast_of_lt h2, rw ←this, apply congr_arg, simp, },
  conv_rhs { rw this, },
  apply congr_arg, rw @zmod.nat_cast_val _ _ _ _ _, assumption,
end

example (a b c d : ℕ) (h : a ≤ b) : a < b.succ :=
begin
  exact nat.lt_succ_iff.mpr h,
end

lemma sum_lt (m : ℕ) (a : zmod (d * p^m)) (x : fin p) : a.val + ↑x * (d * p ^ m) < d * p ^ m.succ :=
begin
  have h1 := zmod.val_lt a,
  have h2 : ↑x * (d * p ^ m) ≤ (d * p ^ m) * (p - 1),
  { rw mul_comm, apply nat.mul_le_mul_left, rw [←nat.lt_succ_iff, nat.succ_eq_add_one, nat.sub_add_cancel], apply x.2,
    { apply le_of_lt (fact_iff.1 (nat.prime.one_lt' p)), }, },
  have := add_lt_add_of_lt_of_le h1 h2,
  convert this,
  ring_nf, rw nat.sub_add_cancel,
  { rw ←pow_succ, },
  { apply le_of_lt, apply fact_iff.1 (nat.prime.one_lt' p), },
end

lemma sum_equiv {α β γ : Type*} {s : finset α} {s' : finset β} {φ : s ≃ s'} {f : α → γ}
  [add_comm_monoid γ] : ∑ x : s, f x = ∑ y : s', f(φ.inv_fun y) :=
begin
  apply finset.sum_bij',
  swap 4, rintros, exact φ.to_fun a,
  swap 5, rintros, exact φ.inv_fun a,
  all_goals {simp},
end

lemma why_no_find (a b : ℤ) : a = b ↔ a.succ = b.succ :=
begin
  split,
  exact congr_arg (λ (a : ℤ), a.succ),
  rintros, rw int.succ at *, rw int.succ at *, simp at *, assumption,
end

lemma this_must_exist (n : ℕ) [fact (0 < n)] (a : zmod n) : (a.val : ℤ) = (a : ℤ) :=
begin
  rw ←zmod.nat_cast_val a, congr, rw nat.cast_coe, rw coe_base,
  congr, ext, rw coe_b,
  induction x,
  { norm_num, change int.of_nat 0 = _, change int.of_nat 0 = (0 : ℤ), simp, },
  { norm_num, change int.of_nat x_n.succ = _, change (int.of_nat x_n).succ = _,
    rw why_no_find at x_ih, convert x_ih, },
end

lemma zmod_int_add (n : ℕ) [fact (0 < n)] (a b : zmod n) : (((a + b) : zmod n) : ℤ) = (a + (b : ℤ)) % n :=
begin
  rw [←this_must_exist, zmod.val_add],
  simp only [int.coe_nat_add, int.coe_nat_mod],
  apply congr_fun,
  apply congr_arg,
  rw [←this_must_exist, ←this_must_exist],
end

example (n : ℕ) (h : 0 < n) : n ≠ 0 := ne_of_gt h

lemma zero_le_and_lt_one (n : ℕ) (x : zmod (d * p^n)) :
  0 ≤ (x.val : ℚ) / (d * p^n) ∧ (x.val : ℚ) / (d * p^n) < 1 :=
begin
  split,
  { norm_cast, refine div_nonneg _ _,
    all_goals { norm_cast, apply nat.zero_le _, }, },
  { rw div_lt_one,
    { norm_cast, apply @zmod.val_lt _ _, apply imp p d n, },
    { norm_cast,apply fact_iff.1 (imp p d n), }, },
end

lemma sum_rat_fin (n : ℕ) : (((∑ (x : fin n), (x : ℤ)) : ℤ) : ℚ) = (n - 1) * (n : ℚ) / 2 :=
begin
  have : ∀ (x : fin n), (x : ℤ)= ((x : ℕ) : ℤ), { simp, },
  conv_lhs { congr, congr, skip, funext, rw this x, },
  rw ←finset.sum_range,
  induction n with d hd, { simp, },
  { rw finset.sum_range_succ, rw int.cast_add, rw hd _,
    { simp, rw div_add',
      { rw mul_comm _ (d : ℚ), rw ←mul_add, ring, },
      { simp, }, },
    { simp, }, },
end

lemma coe_add_eq_ite' {n : ℕ} [fact (0 < n)] (a b : zmod n) (h : (a + b : ℤ) < n) :
  (((a + b) : zmod n) : ℤ) = (a : ℤ) + (b : ℤ) :=
begin
  rw zmod.coe_add_eq_ite,
  rw if_neg, push_neg, assumption,
end

lemma coe_nat_int (n a : ℕ) (h : a < n) : ((a : zmod n) : ℤ) = (a : ℤ) :=
begin
  by_cases h' : 0 < n,
  { rw ←zmod.nat_cast_val _,
    { apply congr, { ext y, simp, },
      rw zmod.val_cast_of_lt, assumption, },
    apply fact_iff.2, assumption, },
  simp only [not_lt, le_zero_iff] at h',
  rw h', simp only [zmod.cast_id', id.def, int.nat_cast_eq_coe_nat],
end

lemma lt_mul_pow (m a b : ℕ) (h1 : 0 < b) (h2 : 1 < a) (h3 : 1 < m) : a < b * a^m :=
begin
  have : a ≤ b * a, apply (le_mul_iff_one_le_left _).2,
  { assumption, },
  { apply lt_trans _ h2, linarith, },
  apply lt_of_le_of_lt this _,
  apply mul_lt_mul',
  any_goals { linarith, },
  conv { congr, rw ←pow_one a, skip, skip, },
  apply pow_lt_pow,
  any_goals { assumption, },
end

example (m n : ℕ) (h : (m : ℤ) < n) : m < n := int.coe_nat_lt.mp h

lemma fin_le_val (m n : ℕ) (y : fin m) (h : m ≤ n) : (y : zmod n).val = y :=
begin
  dsimp,
  rw zmod.val_cast_of_lt _,
  refine lt_of_lt_of_le _ h,
  exact fin.is_lt y,
end
--example (m n : ℕ) (h : m < n) : (m : zmod n).val = m := zmod.val_cast_of_lt h

--example : ¬ (1 = 2 ∧ 3 < 4) := by push_neg

lemma pow_lt_mul_pow (m : ℕ) : p ^ m < d * p ^ m.succ :=
begin
  rw pow_succ, rw ←mul_assoc, apply lt_mul_of_one_lt_left,
  { apply pow_pos, apply nat.prime.pos, apply fact.out, },
  { apply one_lt_mul,
    { apply (nat.succ_le_iff).2, apply fact.out, },
    { apply nat.prime.one_lt, apply fact.out, }, },
end

lemma nat_cast_eq_coe_b (x : ℕ) : @nat.cast ℤ _ _ _ x = coe_b x :=
begin
  induction x with d hd,
  { change 0 = @has_coe.coe ℕ ℤ _ 0,
    change _ = int.of_nat 0, simp only [int.coe_nat_zero, int.of_nat_eq_coe], },
  { show d.cast + 1 = @has_coe.coe ℕ ℤ _ d.succ,
    change _ = int.of_nat d.succ, simp,
    change _ = int.of_nat d at hd, simp [hd], },
end

lemma fin_coe_coe (m : ℕ) (y : fin p) : (y : zmod (d * p^m.succ)) = ((y : ℕ) : zmod (d * p^m.succ)) :=
  coe_coe y

lemma fin_mul_lt (y : fin p) (m : ℕ) : (y : ℕ) * (d * p ^ m) < d * p ^ m.succ :=
begin
  rw pow_succ', rw ←mul_assoc d _ _, rw mul_comm (y : ℕ) _,
  apply mul_lt_mul', any_goals { linarith, },
  { exact fin.is_lt y, },
  { apply fact_iff.1, exact imp p d m, },
end

example (m : ℕ) : m^1 = m := pow_one m

lemma sum_fract (m : ℕ) [fact (0 < m)] (x : zmod (d * p^m)) : ∑ (x_1 : (equi_class p d m m.succ (lt_add_one m) x)),
  fract (((x_1 : zmod (d * p^m.succ)).val : ℚ) / ((d : ℚ) * (p : ℚ)^m.succ)) =
    (x.val : ℚ) / (d * p^m) + (p - 1) / 2 :=
begin
  conv_lhs { congr, skip, funext, rw [fract_eq_self ((zero_le_and_lt_one p d m.succ x_1).1)
    ((zero_le_and_lt_one p d m.succ x_1).2)], },
  rw fintype.sum_equiv (equi_iso_fin p d m x) _ (λ k, (((equi_iso_fin p d m x).inv_fun k).val : ℚ) / (d * p ^ m.succ)),
  { rw ←finset.sum_div,
    have : ∀ k : fin p, ((equi_iso_fin p d m x).inv_fun k).val = x.val + ↑k * (d * p^m),
--  sorry, sorry, }, sorry end #exit -- 0.1 seconds!
    { intro k, unfold equi_iso_fin, dsimp, norm_cast, rw mul_assoc, },
--  sorry, }, sorry end #exit -- 0.15s
    conv_lhs { congr, congr, skip, funext, rw this x, rw ←zmod.int_cast_cast,
      skip, },
    --rw [coe_add_eq_ite'],
--  sorry, }, sorry end #exit -- 0.22 seconds
--    classical,
    --push_neg,
--  sorry, }, sorry end #exit -- 0.5 seconds
    convert_to (∑ x_1 : fin p, ((((x.val) : zmod (d * p^m.succ)) : ℤ) +
      (↑x_1 * ((d : zmod (d * p^m.succ)) * (p : zmod (d * p^m.succ)) ^ m) : ℤ) : ℚ)) / (d * p^m.succ : ℚ) = _,
--  sorry, sorry }, sorry, recover, sorry, end #exit -- 0.6 seconds
    { congr,
      ext y,
--sorry }, sorry }, sorry, end #exit -- 0.8 seconds
      rw ←int.cast_add, congr,
      --rw nat.cast_add,
--sorry }, sorry }, sorry, end #exit -- 1.6 seconds
      rw coe_add_eq_ite' _,
      { congr, rw ←zmod.nat_cast_val,
        rw zmod.val_mul, rw nat.mod_eq_of_lt _,
        { rw nat.cast_mul, apply congr_arg2,
          { rw fin_le_val, simp, rw mul_comm,
            apply le_mul_of_le_of_le_one,
            { conv { congr, rw ←pow_one p, skip, skip, },
              apply (nat.pow_le_iff_le_right _).2,
              { apply nat.succ_le_succ, linarith, },
              { apply nat.prime.two_le, apply fact.out, }, },
            apply (nat.succ_le_iff).2, apply fact.out, },
          { --rw nat.cast_mul,
            --rw ←zmod.nat_cast_val,
            rw zmod.val_mul, rw nat.mod_eq_of_lt _,
            { rw nat.cast_mul, rw zmod.nat_cast_val, rw zmod.nat_cast_val,
              congr, rw ←nat.cast_pow, rw coe_nat_int, rw coe_nat_int, simp,
              { refine lt_mul_pow (m.succ) p d _ _ _,
                apply fact.out,
                apply nat.prime.one_lt, apply fact.out,
                apply nat.succ_lt_succ, apply fact.out, },
              apply pow_lt_mul_pow, },
            { rw ←nat.cast_pow, rw zmod.val_cast_of_lt _, rw zmod.val_cast_of_lt _,
              { apply mul_pow_lt_mul_pow_succ, },
              { apply pow_lt_mul_pow, },
              { apply lt_mul_of_one_lt_right,
                { apply fact.out, },
                { apply nat.one_lt_pow,
                  { apply nat.succ_pos, },
                  { apply nat.prime.one_lt, apply fact.out, }, }, }, }, }, },
        { rw ←nat.cast_pow, rw ←nat.cast_mul, rw zmod.val_cast_of_lt _, rw fin_le_val _ _ _ _,
          { apply fin_mul_lt, },
          { apply le_of_lt, apply lt_mul_pow,
            { apply fact.out, },
            { apply nat.prime.one_lt, apply fact.out, },
            { apply nat.succ_lt_succ, apply fact.out, }, },
          { apply mul_pow_lt_mul_pow_succ, }, }, },
      { rw zmod.nat_cast_val, rw ←zmod.nat_cast_val, rw ←zmod.nat_cast_val (↑y * (_ * _)),
        rw ←nat.cast_add,
        { have := sum_lt p d m x y,
          have f := (int.coe_nat_lt).2 this,
          convert f using 1,
          apply congr,
          { ext y, simp, },
          { apply congr_arg2,
            { rw ←zmod.nat_cast_val, rw val_coe_eq_val _ _ _,
              { apply imp p d m, },
              { apply fact_iff.2, apply mul_pow_lt_mul_pow_succ, }, },
            { rw ←nat.cast_pow, rw ←nat.cast_mul, rw fin_coe_coe, rw ←nat.cast_mul,
              rw zmod.val_cast_of_lt,
              apply fin_mul_lt, }, }, }, --convert sum_lt p d m x y using 1, },
        { apply imp p d m.succ, }, },
      { apply imp p d m.succ, }, },
--    sorry, }, sorry, end #exit -- 2.7 seconds
    { rw finset.sum_add_distrib, rw finset.sum_const, rw finset.card_univ, rw fintype.card_fin _,
      norm_cast, rw ←finset.sum_mul, rw add_div, apply congr_arg2,
      { rw div_eq_iff _,
        { rw div_mul_comm', rw nsmul_eq_mul, apply congr_arg2,
          { norm_num, rw mul_div_mul_left _, rw pow_succ, rw mul_div_cancel _,
            { norm_cast, apply pow_ne_zero m (nat.prime.ne_zero (fact_iff.1 _)), assumption, },
            { norm_num, apply ne_of_gt, apply fact_iff.1, assumption, }, },
          { rw zmod.int_cast_cast,
            rw zmod.nat_cast_val, rw ←zmod.nat_cast_val (x : zmod (d * p^m.succ)),
            apply congr_arg, rw ←zmod.nat_cast_val x, rw val_coe_eq_val _ _ _,
            { apply imp p d m, },
            { rw mul_comm d (p^m), rw mul_comm d (p^m.succ), apply fact_iff.2, apply mul_lt_mul,
--sorry, sorry, sorry, sorry }, }, }, sorry, }, sorry, }, }, sorry, end #exit -- 4.72
              any_goals { simp, },
--sorry, sorry }, }, }, sorry, }, sorry, }, }, sorry, end #exit -- 5.3s
              { apply pow_lt_pow _ (nat.lt_succ_self m), apply nat.prime.one_lt, apply fact_iff.1,
                assumption, },
              { apply fact_iff.1, assumption, }, }, }, },
        { norm_cast, apply ne_of_gt, apply fact_iff.1, apply imp p d m.succ, }, },
--      sorry, }, }, sorry, end #exit -- 4.94 seconds
      { rw int.cast_mul, rw mul_div_assoc,
        --have : (((∑ (x : fin p), (x : ℤ)) : ℤ) : ℚ) = (p - 1) * (p : ℚ) / 2, sorry,
        rw sum_rat_fin, rw nat.cast_mul, rw int.cast_mul,
        have one : ((p : ℚ) - 1) * (p : ℚ) / 2 * (1 / (p : ℚ)) = ((p : ℚ) - 1) / 2,
        { rw div_mul_div, rw mul_one, rw mul_div_mul_right,
          norm_cast, apply ne_of_gt, apply nat.prime.pos, apply fact_iff.1, assumption, },
        convert one using 2, rw div_eq_div_iff _ _,
--        sorry, sorry, sorry, }, }, }, sorry, end #exit -- 5.14 seconds
        { rw one_mul, rw zmod.int_cast_cast, rw int.cast_pow, rw zmod.int_cast_cast,
          rw pow_succ', rw nat.cast_mul, rw nat.cast_pow, rw mul_assoc, apply congr_arg2,
          { rw ←zmod.nat_cast_val _,
            { rw zmod.val_nat_cast, congr, apply nat.mod_eq_of_lt, rw lt_mul_iff_one_lt_right _,
              { rw ←pow_succ', apply one_lt_pow,
                { apply nat.prime.one_lt, apply fact_iff.1, assumption, },
                { simp, }, },
              { apply fact_iff.1, assumption, }, },
            { rw ←pow_succ', apply imp p d (m + 1), } },
          { apply congr_arg2,
            { apply congr_arg2,
              { rw ←zmod.nat_cast_val _,
                { rw zmod.val_nat_cast, congr, apply nat.mod_eq_of_lt,
                  rw ←mul_assoc,
                  rw lt_mul_iff_one_lt_left _,
                  { apply one_lt_mul,
                    { rw nat.succ_le_iff, apply fact_iff.1, assumption, },
                    { apply one_lt_pow,
                      { apply nat.prime.one_lt, apply fact_iff.1, assumption, },
                      { rw nat.succ_le_iff, apply fact.out, }, }, },
                  { apply nat.prime.pos, apply fact_iff.1, assumption, }, },
                { rw ←pow_succ', apply imp p d (m + 1), }, },
              { refl, }, },
            { refl, }, }, },
        { rw ←nat.cast_mul, norm_cast, apply ne_of_gt, apply fact_iff.1, apply imp p d _, },
        { norm_cast, apply ne_of_gt, apply nat.prime.pos, apply fact_iff.1, assumption, }, }, }, },
  { rintros y,
    simp only [equiv.symm_apply_apply, subtype.val_eq_coe, equiv.inv_fun_as_coe,
      zmod.nat_cast_val], },
end

lemma div_coe (m n : ℕ) (h : m ∣ n) (a : zmod m) : ((a : zmod n) : zmod m) = a :=
begin
  conv_rhs
  { rw ←zmod.ring_hom_map_cast (zmod.cast_hom h (zmod m)) a, },
  rw zmod.cast_hom_apply,
end

lemma fract_eq_val (n : ℕ) [h : fact (0 < n)] (a : zmod n) : fract ((a : ℚ) / n) = (a.val : ℚ) / n :=
begin
  rw fract_eq_iff, split,
  { apply div_nonneg _ _,
    { exact (zmod.val a).cast_nonneg, },
    { exact nat.cast_nonneg n, }, },
  split,
  { rw div_lt_one,
    { norm_cast, apply zmod.val_lt, },
    { norm_cast, apply fact_iff.1, assumption, }, },
  { rw ←zmod.nat_cast_val, use 0, simp, },
end

lemma card_equi_class (m : ℕ) (x : zmod (d * p^m)) :
  finset.card (@finset.univ (equi_class p d m m.succ (lt_add_one m) x) _) = p :=
begin
  rw finset.card_univ,
  rw ←fintype.of_equiv_card (equi_iso_fin p d m x),
  convert fintype.card_fin p,
end

lemma is_unit_mul (hc : gcd c p = 1) (hc' : gcd c d = 1) :
  is_unit ((c : zmod (d * p^(2 * (m.succ)))) : zmod (d * p^(m.succ))) :=
begin
  rw is_unit, refine ⟨(zmod.unit_of_coprime c _), _⟩,
  { apply nat.coprime.symm (nat.coprime.mul (nat.coprime.symm hc')
      (nat.coprime.pow_left m.succ (nat.coprime.symm hc))), },
  { rw zmod.coe_unit_of_coprime c _,
    rw zmod.cast_nat_cast _,
    swap, { refine zmod.char_p _, },
    { apply mul_dvd_mul_left, apply pow_dvd_pow, linarith, }, },
end

lemma is_unit_mul' (hc : gcd c p = 1) (hc' : gcd c d = 1) :
  is_unit ((c : zmod (d * p^(2 * (m.succ)))) : zmod (d * p^m)) :=
begin
  rw is_unit, refine ⟨(zmod.unit_of_coprime c _), _⟩,
  { apply nat.coprime.symm (nat.coprime.mul (nat.coprime.symm hc')
      (nat.coprime.pow_left m (nat.coprime.symm hc))), },
  { rw zmod.coe_unit_of_coprime c _,
    rw zmod.cast_nat_cast _,
    swap, { refine zmod.char_p _, },
    { apply mul_dvd_mul_left, apply pow_dvd_pow, rw ←one_mul m,
      apply mul_le_mul, any_goals { linarith, },
      { rw one_mul, apply nat.le_succ, }, }, },
end

--example (a b c : ℤ) (h : a = b) : c * a = c * b := congr_arg (has_mul.mul c) h

-- A lot of goals are recurring, maybe make them local instances / lemmas?
lemma coe_inv (m : ℕ) (hc : gcd c p = 1) (hc' : gcd c d = 1) :
  ((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m))⁻¹ =
  ((((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ))⁻¹ : zmod (d * p^m.succ)) : zmod (d * p^m)) :=
begin
  have : ((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m)) =
    (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m)),
    { repeat { rw zmod.cast_nat_cast _, },
      any_goals { refine zmod.char_p _ },
      any_goals { apply mul_dvd_mul_left, },
      any_goals { apply pow_dvd_pow _, },
      { apply nat.le_succ, },
      { linarith, },
      { rw ←one_mul m, apply mul_le_mul, any_goals { linarith, },
        { rw one_mul, apply nat.le_succ, }, }, },
  convert_to (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m))⁻¹ = _,
  { apply congr_arg, assumption, },
  { have g1 : (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m))
      * (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m))⁻¹ = 1,
    { rw zmod.mul_inv_of_unit, rw ←this, apply is_unit_mul' p d m hc hc', },
    have g2 : (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m))
      * ((((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ))⁻¹ : zmod (d * p^m.succ)) : zmod (d * p^m)) = 1,
    { rw ←zmod.cast_mul _,
      { rw ←zmod.cast_one _,
        { congr, rw zmod.mul_inv_of_unit, apply is_unit_mul p d m hc hc', },
        swap, { refine zmod.char_p _, },
        { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, }, },
        swap, { refine zmod.char_p _, },
        { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, }, },
    rw ←g1 at g2,
    have g3 := congr_arg (has_mul.mul
      ((((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ))⁻¹ : zmod (d * p^m)))) g2,
    rw [←mul_assoc, ←mul_assoc, zmod.inv_mul_of_unit _, one_mul, one_mul] at g3,
    { rw g3, },
    { rw ←this, apply is_unit_mul' p d m hc hc', }, },
end

lemma rep (m : ℕ) : (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m)) =
  ((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m)) :=
begin
  repeat { rw zmod.cast_nat_cast _, },
  any_goals { refine zmod.char_p _, },
  any_goals { apply mul_dvd_mul_left, apply pow_dvd_pow, },
  { rw ←one_mul m, apply mul_le_mul, any_goals { linarith, },
      { rw one_mul, apply nat.le_succ, }, },
  { apply nat.le_succ, },
  { linarith, },
end

/---is this true?
lemma E_c_sum_equi_class'' [has_coe ℝ R] (x : zmod d) (hc : gcd c p = 1)
  (hc' : gcd c d = 1) :
  ∑ (y : equi_class p d 0 1 (lt_add_one 0) x), (E_c p d hc 1 y) = (E_c p d hc 0 x) :=
begin
  rw E_c, simp,
  sorry
end-/

lemma E_c_sum_equi_class' [has_coe ℝ R] [fact (0 < m)] (x : zmod (d * p^m)) (hc : gcd c p = 1)
  (hc' : gcd c d = 1) :
  ∑ (y : equi_class p d m m.succ (lt_add_one m) x), (E_c p d hc m.succ y) = (E_c p d hc m x) :=
begin
  rw E_c, simp only,
  rw [finset.sum_add_distrib, finset.sum_sub_distrib, sum_fract, ←finset.mul_sum],
  convert_to ((x.val : ℚ) / (d * p ^ m) + (p - 1) / 2) - (c : ℚ) *
    ∑ (x_1 : (equi_class p d m m.succ (lt_add_one m)
      ( ((c : zmod (d * p^(2*m.succ)))⁻¹ : zmod (d * p^m)) * x))),
    fract (((x_1 : zmod (d * p^m.succ)).val : ℚ) / ((d : ℚ) * (p : ℚ)^m.succ)) +
    (∑ (x : (equi_class p d m m.succ _ x)), ((c : ℚ) - 1) / 2) = _ - _ + _,
  { rw [add_right_cancel_iff, sub_right_inj], apply congr_arg,
    apply finset.sum_bij,
    swap 5,
    { rintros, constructor, swap,
      { exact ((c : zmod (d * p^(2*m.succ)))⁻¹ : zmod (d * p^m.succ)) * a, },
      { rw mem_equi_class,
        have := (mem_equi_class p d m m.succ _ x a).1 a.prop,
        conv_rhs { congr, skip, rw ←this, },
        rw zmod.cast_mul _,
        { congr, rw coe_inv p d m hc hc', },
        swap, { exact zmod.char_p (d * p^m), },
        { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, }, }, },
    { simp, }, --squeeze_simp does not work!
    { rintros, rw fract_eq_fract, simp only [subtype.coe_mk],
      rw [div_sub_div_same, zmod.nat_cast_val], use 0, simp, },
    { simp, rintros a1 ha1 a2 ha2 h, rw is_unit.mul_right_inj at h, assumption,
      { rw is_unit_iff_exists_inv',
        refine ⟨((c : zmod (d * p^(2 * (m.succ)))) : zmod (d * p^(m.succ))),
          zmod.mul_inv_of_unit _ (is_unit_mul p d m hc hc')⟩, }, },
    { simp, rintros a ha, rw mem_equi_class at *,
      use ((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) * a,
      split,
      { rw [mem_equi_class, zmod.cast_mul _],
        { rw ha,
          --have rep : (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m)) =
            --((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m)), sorry,
          -- if I remove the above line, the convert below does not work?
          rw ←mul_assoc, convert one_mul x, norm_cast,
          convert zmod.mul_inv_of_unit _ (is_unit_mul' p d m hc hc') using 2, rw rep, },
           -- using 1,
          --{ apply is_unit_mul' p d m hc hc', }, },
        swap, { refine zmod.char_p _, },
        { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, }, },
      { rw [←mul_assoc, zmod.inv_mul_of_unit _ _],
        { rw one_mul a, },
        apply is_unit_mul p d m hc hc', }, }, },
  rw [sum_fract, fract_eq_self (zero_le_and_lt_one p d m x).1 (zero_le_and_lt_one p d m x).2,
      mul_add, finset.sum_const, card_equi_class],
  simp only [nsmul_eq_mul],
  rw [sub_add_eq_add_sub, sub_add_eq_add_sub, sub_add_eq_sub_sub, sub_right_comm], congr,
  { rw [add_assoc, add_sub_assoc], congr, linarith, },
  { rw [←nat.cast_pow, ←nat.cast_mul, ←fract_eq_val _ _], repeat { apply congr_arg, },
    apply congr_fun, repeat { apply congr_arg, }, apply congr_fun, repeat { apply congr_arg, },
    repeat { rw zmod.cast_nat_cast _, }, repeat { any_goals { refine zmod.char_p _, }, },
    { apply mul_dvd_mul_left, apply pow_dvd_pow, linarith, },
    { apply mul_dvd_mul_left, apply pow_dvd_pow, rw ←one_mul m,
      apply mul_le_mul, any_goals { linarith, },
      { rw one_mul, apply nat.le_succ, }, },
    apply imp p d m, },
end

lemma E_c_sum_equi_class [has_coe ℝ R] [has_coe ℚ R] [fact (0 < m)] (x : zmod (d * p^m)) (hc : gcd c p = 1) (hc' : gcd c d = 1) :
∑ (y : zmod (d * p ^ m.succ)) in (λ a : zmod (d * p ^ m), set.to_finset ((equi_class p d m m.succ (lt_add_one m)) a)) x,
  ((E_c p d hc m.succ y) : R) = (E_c p d hc m x) :=
begin
  rw ←E_c_sum_equi_class' p d R _,
  { sorry, },
  any_goals { assumption, },

/-  rw E_c, simp,
  have : ∀ (n : ℕ) (x : zmod (d * p^n)), 0 ≤ (x.val : ℝ) / (d * p^n) ∧ (x.val : ℝ) / (d * p^n) < 1,
  { rintros n x, split, sorry, sorry, },
  have : ∀ (n : ℕ) (x : zmod (d * p^n)), 0 ≤ (x : ℚ) / (d * p^n) ∧ (x : ℚ) / (d * p^n) < 1,
  { rintros n x, split, sorry, sorry, },
  conv_lhs { congr, skip, funext, rw [fract_eq_self ((this m.succ x).1) ((this m.succ x).2)], },
  rw [fract_eq_self ((this m x).1) ((this m x).2)],
  rw ←finset.sum_finset_coe,
  -- conv_lhs { congr, },
  have := set.coe_to_finset (equi_class p d m m.succ _ x), rw [this],
  rw fintype.sum_equiv (equi_iso_fin p d m x),
  rw [finset.sum_add_distrib],

  --conv_lhs { congr, skip, funext, rw fract_eq_self, skip,
  --{ apply_congr (this _ _).1, }, },
  sorry,-/
end
-- why does has_div exist for ℤ and ℕ!?

lemma inter_nonempty_of_not_disjoint {α : Type*} {s t : set α} (h : ¬disjoint s t) :
  ∃ x, x ∈ s ∧ x ∈ t :=
begin
  contrapose h, push_neg at h, rw not_not, rw disjoint_iff, simp [h], ext, split,
  { intro h', rw set.mem_inter_iff at h', specialize h x h'.1, simp, apply h h'.2, },
  { simp, },
end

lemma inter_nonempty_of_not_disjoint' {α : Type*} {s t : finset α} [decidable_eq α] (h : ¬disjoint s t) : ∃ x, x ∈ s ∧ x ∈ t :=
begin
  suffices : finset.nonempty (s ⊓ t),
  cases this with x hx, use x,
  rw ←finset.mem_inter, convert hx,
  rw finset.inf_eq_inter,
  rw finset.nonempty_iff_ne_empty,
  contrapose h, push_neg at h, rw not_not,
  rw disjoint, simp, -- simp does not work without rw disjoint
  rw finset.subset_empty, rw h,
end

/-- An eventually constant sequence constructed from a locally constant function. -/
noncomputable def g (hc : gcd c p = 1) (hc' : gcd c d = 1) [has_coe ℝ R] [has_coe ℚ R] (hd : 0 < d)
  (f : locally_constant (zmod d × ℤ_[p]) R) (hd' : gcd d p = 1) : @eventually_constant_seq R :=
{ to_seq := λ (n : ℕ),
    --have hpos : 0 < d * p^n := mul_pos hd (pow_pos (nat.prime.pos (fact_iff.1 _inst_3)) n),
    --by
       --letI : fintype (zmod (d * p^n)) := @zmod.fintype _ ⟨hpos⟩; exact
    ∑ a in (zmod' (d * p^n) (mul_prime_pow_pos p d n)), f(a) • ((E_c p d hc n a) : R),
  is_eventually_const := ⟨classical.some (factor_F p d R hd' f),
  begin
  simp, rintros l hl, -- why is the simp needed?
  set t := λ a : zmod (d * p ^ l), set.to_finset ((equi_class p d l l.succ (lt_add_one l)) a) with ht,
  rw succ_eq_bUnion_equi_class,
  rw @finset.sum_bUnion _ _ _ _ _ _ (zmod' (d*p^l) (mul_prime_pow_pos p d l)) t _,
  { haveI : fact (0 < l), sorry,
    conv_lhs { apply_congr, skip, conv { apply_congr, skip, rw equi_class_eq p d R l f x hd' hl x_1 H_1, },
    rw [←finset.mul_sum], rw E_c_sum_equi_class p d R l x hc hc', }, },
  { rintros x hx y hy hxy, contrapose hxy, push_neg,
    obtain ⟨z, hz⟩ := inter_nonempty_of_not_disjoint' hxy,
    rw ht at hz, simp at hz, rw mem_equi_class p d l l.succ at hz,
    rw mem_equi_class p d l l.succ at hz, cases hz with h1 h2, rw h1 at h2,
    exact h2, }, end⟩, }

lemma g_def [has_coe ℝ R] [has_coe ℚ R] (hc : gcd c p = 1) (hc' : gcd c d = 1) (hd : 0 < d)
  (f : locally_constant (zmod d × ℤ_[p]) R) (n : ℕ) (hd' : gcd d p = 1) :
  (g p d R hc hc' hd f hd').to_seq n = ∑ a in (finset.range (d * p^n)),f(a) • ((E_c p d hc n a) : R) := sorry

/-
def clopen_basis' :=
{x : clopen_sets ((zmod d) × ℤ_[p]) // ∃ (n : ℕ) (a : zmod (d * (p^n))),
  x = ⟨({a} : set (zmod d)).prod (set.preimage (padic_int.to_zmod_pow n) {(a : zmod (p^n))}),
    is_clopen_prod (is_clopen_singleton (a : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩ }

example (U : clopen_basis' p d) : clopen_sets (zmod d × ℤ_[p]) := U


lemma char_fn_clopen_basis' (U : clopen_basis' p d) :
  char_fn _ U.val (coe (classical.some (classical.some_spec U.prop))) = (1 : R) :=
sorry

example {α : Type*} (s : set α) : s = {x : α | x ∈ s} := by simp only [set.set_of_mem_eq]

-- lemma ideally_not_needed (x : clopen_sets (zmod d × ℤ_[p])) (h : x ∈ clopen_basis' p d) :
--   clopen_basis' p d := ⟨x, h⟩

example (a b : R) (h : a + b = a) : b = 0 := add_right_eq_self.mp (congr_fun (congr_arg has_add.add h) b)

--example : clopen_basis' p d = {x // x ∈ clopen_basis' p d}

--lemma blahs : has_lift_t (clopen_basis' p d) (clopen_sets (zmod d × ℤ_[p])) :=

--example (U : clopen_sets (zmod d × ℤ_[p])) (hU : U ∈ clopen_basis' p d) : clopen_basis' p d := ⟨U, hU⟩
-/
instance : semilattice_sup ℕ := infer_instance

-- set_option pp.proofs true

-- def G (f : locally_constant ℤ_[p] R) (a : ℤ_[p]) : ℕ := ⨅ n : ℕ, loc_const_const -- is this really needed?

-- lemma loc_const_comp (f : locally_constant ℤ_[p] R)
variable [has_coe ℚ R]
-- can hd be removed?
lemma bernoulli_measure_nonempty [has_coe ℝ R] (hc : gcd c p = 1) (hc' : gcd c d = 1)
  [hd : ∀ n : ℕ, fact (0 < d * p^n)] (h' : gcd d p = 1) :
  nonempty (@bernoulli_measure p _ d R _ _ _ _ hc _) :=
begin
  refine mem_nonempty _,
  have hd' : 0 < d, sorry,
  refine { to_fun := λ f, sequence_limit (g p d R hc hc' _ f h'),
  map_add' := _,
  map_smul' := _ },
  { assumption, },
  { rintros,
    set n := (sequence_limit_index' (g p d R hc hc' hd' (x + y) h')) ⊔ (sequence_limit_index' (g p d R hc hc' hd' x h'))
      ⊔ (sequence_limit_index' (g p d R hc hc' hd' y h')) with hn,
    --rw sequence_limit_eq (g p d R hc (x + y)) n _,
    repeat { rw sequence_limit_eq (g p d R hc hc' hd' _ h') n _, },
    { rw g_def p d R hc hc' hd' _ n h', rw g_def p d R hc hc' hd' _ n h', rw g_def p d R hc hc' hd' _ n h',
      simp only [algebra.id.smul_eq_mul, pi.add_apply, locally_constant.coe_add],
      rw ←finset.sum_add_distrib,
      apply finset.sum_congr, refl,
      rintros, rw add_mul, },
    { rw le_sup_iff, right, apply le_refl, },
    { rw le_sup_iff, left, rw le_sup_iff, right, apply le_refl, },
    { rw le_sup_iff, left, rw le_sup_iff, left, apply le_refl, }, },
  { rintros m x,
    set n := (sequence_limit_index' (g p d R hc hc' hd' x h')) ⊔ (sequence_limit_index' (g p d R hc hc' hd' (m • x) h'))
      with hn,
    repeat { rw sequence_limit_eq (g p d R hc hc' hd' _ h') n _, },
    { repeat { rw g_def p d R hc hc' hd' _ n h', }, simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply], rw finset.mul_sum,
      apply finset.sum_congr, refl,
      rintros, rw mul_assoc, },
    { rw le_sup_iff, left, apply le_refl, },
    { rw le_sup_iff, right, apply le_refl, }, }, --there has to be a less repetitive way of doing this
    { rw bernoulli_measure, simp only [le_refl, algebra.id.smul_eq_mul, pi.add_apply, locally_constant.coe_add, linear_map.coe_mk, locally_constant.coe_smul,
  subtype.forall, le_sup_iff, set.mem_set_of_eq, pi.smul_apply, subtype.coe_mk, set.singleton_prod, subtype.val_eq_coe],
  intros n a,
--      set V : clopen_basis' p d := ⟨U, hU⟩ with hV,
      --set V :=  with hV,
--      have : U = V.val, rw hV, simp,
--      set n := classical.some U.prop with hn,
--      set a := classical.some (classical.some_spec U.prop) with ha,
--      set n' := classical.some (mem_clopen_basis' p d U hU) with hn,
--      set a' := classical.some (classical.some_spec (mem_clopen_basis' p d U hU)) with ha,
/-/      have h1 : classical.some (bernoulli_measure._proof_5 p d
  ⟨U, (iff.refl (U ∈ clopen_basis' p d)).mpr ((iff.refl (U ∈ clopen_basis' p d)).mpr hU)⟩) = n,
      rw hn,
  have h2 : classical.some (classical.some_spec (bernoulli_measure._proof_5 p d
  ⟨U, (iff.refl (U ∈ clopen_basis' p d)).mpr ((iff.refl (U ∈ clopen_basis' p d)).mpr hU)⟩)) = a,
      rw ha, rw h1,
      rw ←hn, rw ←ha,
      show _ = E_c p d hc n a, -/
--      change' _ = E_c p d hc n _,
      have hd' : 0 < d, sorry,
      rw sequence_limit_eq (g p d R hc hc' hd' _ h') n _,
      { rw g_def p d R hc hc' hd' _ n h',
        rw finset.sum_eq_add_sum_diff_singleton, swap 3, exact a.val,
        swap, simp,
        apply (@zmod.val_lt (d * p^(n)) (hd n) a),
        rw zmod.nat_cast_val a, rw zmod.nat_cast_val a,
        convert_to (1 • ((E_c p d hc n a) : R)) + _ = ((E_c p d hc n a) : R),
        swap, rw one_smul, rw add_zero,
        congr,
        { simp, convert one_mul ((E_c p d hc n a) : R),
          rw char_fn, simp only [not_exists, set.mem_preimage, set.mem_image, not_and,
          set.mem_singleton_iff, locally_constant.coe_mk, ite_eq_right_iff], rw if_pos,
          use ((a : zmod (p^n)) : ℤ_[p]), simp, sorry, },
        { apply finset.sum_eq_zero, rintros x hx, rw char_fn, simp only [not_exists,
          set.mem_preimage, set.mem_image, not_and, set.mem_singleton_iff, locally_constant.coe_mk,
          ite_eq_right_iff], rw if_neg,
          { rw zero_smul, },
          { push_neg, rintros y hy h'', sorry, }, }, },
      sorry, }, -- is this true?
end

-- not used, delete?
/-- Constructing a linear map, given that _. -/
noncomputable
def linear_map_from_span (η : S → N)
  (cond : ∀ (f : S →₀ R'), finsupp.total S M R' coe f = 0 → finsupp.total S N R' η f = 0) :
  submodule.span R' S →ₗ[R'] N :=
begin
  let F := finsupp.total S M R' coe,
  let K := F.ker,
  let e := linear_map.quot_ker_equiv_range F,
  let ee : F.range ≃ₗ[R'] submodule.span R' S :=
    linear_equiv.of_eq _ _ (finsupp.span_eq_range_total _ _).symm,
  refine linear_map.comp _ ee.symm.to_linear_map,
  refine linear_map.comp _ e.symm.to_linear_map,
  refine F.ker.liftq (finsupp.total S N R' η) _,
  apply cond,
end

/-- Looking at the set of characteristic functions obtained from the clopen basis. -/
abbreviation s : set (locally_constant (zmod d × ℤ_[p]) R) := set.image (char_fn (zmod d × ℤ_[p]))
  (⨆ n : ℕ, set.range (clopen_from p d n))

/-- An equivalence between the clopen basis and the characteristic functions corresponding to it. -/
def clopen_char_fn_equiv : clopen_basis' p d ≃ s p d R := sorry

instance general_version (n m : ℕ) (h : n < m) (a : zmod (p^n)) : fintype (equi_class p d n m h a) := sorry

/-
--construct a map from `ℤ/dℤ × ℤ_p → clopen_basis' p d` ?
/-- For m > n, χ_(b,a,n) = ∑_{j, b_j = a mod p^n} χ_(b,b_j,m) -/
lemma sum_char_fn_dependent (m n : ℕ) (h : m > n) (a : zmod (p^n)) (b : zmod d) :
  @char_fn (zmod d × ℤ_[p]) _ _ _ _ R _ _ _ (⟨_,
    is_clopen_prod (is_clopen_singleton (b : zmod d))
      (proj_lim_preimage_clopen p d n a) ⟩) = ∑ x in set.to_finset (equi_class p d n m h a),
  char_fn _ (⟨_,
    is_clopen_prod (is_clopen_singleton (b : zmod d)) (proj_lim_preimage_clopen p d n x) ⟩) :=
sorry -/

/-
/-- For m > n, E_c(χ_(b,a,n)) = ∑_{j, b_j = a mod p^n} E_c(χ_(b,b_j,m)) -/
lemma sum_char_fn_dependent_Ec' (m n : ℕ) [fact (0 < n)] (h : m > n) (a : zmod (p^n)) (b : zmod d) (hc : gcd c p = 1) :
  E_c p d hc n a = ∑ x in set.to_finset (equi_class p d n m h a), E_c p d hc m x :=
sorry

lemma seems_useless (x : s p d R) : (x : locally_constant (zmod d × ℤ_[p]) R) =
  char_fn (zmod d × ℤ_[p]) ((clopen_char_fn_equiv p d R).inv_fun x) :=
begin
  sorry,
end -/

/-lemma guess (n : ℕ) : zmod (d * (p^n)) ≃+* zmod d × zmod (p^n) :=
begin
  sorry,
end-/

lemma clopen_char_fn (U : clopen_basis' p d) : char_fn (zmod d × ℤ_[p]) U =
  @char_fn (zmod d × ℤ_[p]) _ _ _ _ R _ _ _ (⟨_,
    is_clopen_prod (is_clopen_singleton (coe (classical.some (classical.some_spec U.prop)) : zmod d))
      (proj_lim_preimage_clopen p d (classical.some U.prop) (classical.some (classical.some_spec U.prop))) ⟩) := sorry

--lemma trial : locally_constant (zmod d × ℤ_[p]) R = submodule.span R (s p d R) := sorry

-- TODO Remove this lemma
lemma mem_nonempty' {α : Type*} {s : set α} {x : α} (h : x ∈ s) : nonempty s := ⟨⟨x, h⟩⟩

/-lemma bernoulli_measure_nonempty' (hc : gcd c p = 1) :
  nonempty (@bernoulli_measure p _ d R _ _ _ _ hc _) :=
begin
  refine mem_nonempty _,
  {
    --constructor, swap 3,
    suffices : submodule.span R (s p d R) →ₗ[R] R, sorry, -- why you no work
      refine linear_map_from_span R _ _ (s p d R) _ _,
      { intro χ,
        --have : ∃ U : (clopen_basis' p d), char_fn _ U.val = (χ : locally_constant (zmod d × ℤ_[p]) R),
        --construct a bijection between `clopen_basis' p d` and `char_fn`?
        --sorry,
        --set U := classical.some this with hU,
        set U := (clopen_char_fn_equiv p d R).inv_fun χ with hU,
        exact E_c p d hc (classical.some U.prop) (classical.some (classical.some_spec U.prop)), },
      rintros f h, -- f is a relation, taking v in s to a; h says that ∑ a_i v_i = 0, tpt ∑ a_i E_c(v_i) = 0
      --apply finsupp.induction_linear f,
      rw finsupp.total_apply at *,
      simp,
      convert_to ∑ l in finsupp.support f, f(l) * (E_c p d hc (classical.some
        ((clopen_char_fn_equiv p d R).inv_fun l).prop) (classical.some (classical.some_spec
          ((clopen_char_fn_equiv p d R).inv_fun l).prop))) = 0,
      { rw finsupp.sum_of_support_subset,
        swap 4, exact f.support,
        simp, simp,
        { rintros i hi, rw zero_mul, }, },
      set n := ⨆ (l : finsupp.support f), classical.some
        ((clopen_char_fn_equiv p d R).inv_fun l).prop + 1 with hn,
--      set n := ⨆ (l : finsupp.support f), ((clopen_char_fn_equiv p d R).inv_fun l) with hn,
      rw finsupp.sum_of_support_subset at h,
      swap 4, exact f.support,
      swap, simp, swap, simp,
      conv_lhs at h { apply_congr, skip, rw seems_useless p d R x,
        rw clopen_char_fn _,
        rw [sum_char_fn_dependent p d R n (classical.some
          ((clopen_char_fn_equiv p d R).inv_fun x).prop) _ (coe (classical.some (classical.some_spec
          ((clopen_char_fn_equiv p d R).inv_fun x).prop))) _], },

      /-apply finsupp.induction f, { simp, },
      { rintros χ a g hg nza rel_g_zero h, rw finsupp.total_apply at *,
        rw finsupp.sum_add_index at *,
        {  }, sorry, sorry, sorry, sorry, },-/

      rw finsupp.total_apply,
      apply submodule.span_induction (trial p d R f),
      set s := classical.some (what_to_do p d R f) with hs,
 --     have hs := classical.some_spec (what_to_do p d R f),
      set i := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R f))) with hi,
      set j := classical.some (classical.some_spec (what_to_do p d R f)) with hj,
      have hs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R f))),
      exact ∑ (k : s), (j k) •
      (E_c p d hc (classical.some (i k).prop) (classical.some (classical.some_spec (i k).prop))),
    { rintros f g,
      set fs := classical.some (what_to_do p d R f) with hfs,
 --     have hs := classical.some_spec (what_to_do p d R f),
      set fi := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R f))) with hfi,
      set fj := classical.some (classical.some_spec (what_to_do p d R f)) with hfj,
      have hfs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R f))),
      set gs := classical.some (what_to_do p d R g) with hgs,
 --     have hs := classical.some_spec (what_to_do p d R f),
      set gi := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R g))) with hgi,
      set gj := classical.some (classical.some_spec (what_to_do p d R g)) with hgj,
      have hgs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R g))),
      set fgs := classical.some (what_to_do p d R (f + g)) with hfgs,
 --     have hs := classical.some_spec (what_to_do p d R f),
      set fgi := classical.some (classical.some_spec (classical.some_spec (what_to_do p d R (f + g)))) with hfgi,
      set fgj := classical.some (classical.some_spec (what_to_do p d R (f + g))) with hfgj,
      have hfgs' := classical.some_spec (classical.some_spec (classical.some_spec (what_to_do p d R (f + g)))),
      convert_to ∑ (k : fgs), (fgj k) •
      (E_c p d hc (classical.some (fgi k).prop) (classical.some (classical.some_spec (fgi k).prop)) : R) =
      ∑ (k : fs), (fj k) •
      (E_c p d hc (classical.some (fi k).prop) (classical.some (classical.some_spec (fi k).prop)) : R) +
      ∑ (k : gs), (gj k) •
      (E_c p d hc (classical.some (gi k).prop) (classical.some (classical.some_spec (gi k).prop))),
  sorry, },
    sorry, },
sorry,
end -/

/-instance (c : ℤ) (hc : gcd c p = 1) : distribution' (ℤ_[p]) :=
{
  phi := (classical.choice (bernoulli_measure_nonempty p c hc)).val
} -/

/-lemma subspace_induces_locally_constant (U : set X) [hU : semimodule A (locally_constant ↥U A)]
  (f : locally_constant U A) :
  ∃ (g : locally_constant X A), f.to_fun = (set.restrict g.to_fun U) := sorry -/

lemma subspace_induces_locally_constant (f : locally_constant (units (zmod d) × units ℤ_[p]) A) :
  ∃ (g : locally_constant (zmod d × ℤ_[p]) A),
    f.to_fun = g.to_fun ∘ (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])) :=
sorry
--generalize to units X
instance is_this_even_true : compact_space (units (zmod d) × units ℤ_[p]) := sorry
instance why_is_it_not_recognized : t2_space (units (zmod d) × units ℤ_[p]) := sorry
instance so_many_times : totally_disconnected_space (units (zmod d) × units ℤ_[p]) := sorry

variable [has_coe ℝ R]

/-- Constructs a measure from the Bernoulli measure `E_c`. -/
noncomputable def bernoulli_measure_of_measure (hc : gcd c p = 1) (hc' : gcd c d = 1) (h' : gcd d p = 1) :
  measures'' (units (zmod d) × units ℤ_[p]) R :=
begin
  constructor, swap,
  constructor,
  constructor, swap 3, rintros f,
  choose g hg using subspace_induces_locally_constant R p d f, --cases does not work as no prop
  exact (classical.choice (bernoulli_measure_nonempty p d R hc hc' h')).val g, -- do you want nonempty or nonempty'?
  { rintros f1 f2, simp, sorry, },
  { rintros r f, simp, sorry, },
  { sorry, },
end
--function on clopen subsets of Z/dZ* x Z_p* or work in Z_p and restrict
--(i,a + p^nZ_p) (i,d) = 1

lemma cont_paLf [fact (0 < m)] (h : gcd d p = 1) : continuous (λ (a : (units (zmod d) × units ℤ_[p])),
  ((pri_dir_char_extend p d R m h χ) a) * (inj (teichmuller_character p (a.snd)))^(p - 2)
  * (w.to_fun a : R)) :=
sorry

/-- Constant used in `p_adic_L_function`. -/
def f : R := sorry

--h wont go in the system if you put it in [], is this independent of c? is it accurate to say that ω⁻¹ = ω^(p - 2)? I think so
/-- The `p_adic_L_function` defined in terms of the p-adic integral and the
  Bernoulli measure `E_c`. -/
noncomputable def p_adic_L_function (hd : gcd d p = 1) [fact (0 < m)] (h : function.injective inj) (hc : gcd c p = 1) (hc' : gcd c d = 1) :=
 (f R) * (integral (units (zmod d) × units ℤ_[p]) R (bernoulli_measure_of_measure p d R hc hc' hd)
⟨(λ (a : (units (zmod d) × units ℤ_[p])), ((pri_dir_char_extend p d R m hd χ) a) *
  (inj (teichmuller_character p a.snd))^(p - 2) * (w.to_fun a : R)), cont_paLf p d R inj m χ w hd ⟩)
