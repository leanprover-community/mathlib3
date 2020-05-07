/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/

import data.polynomial
import data.equiv.ring
import data.zmod.basic
import group_theory.order_of_element
import linear_algebra.basis
import algebra.geom_sum

universes u v
variables {K : Type u} {R : Type v}

open function finset polynomial nat

section

variables [integral_domain R] (S : set (units R)) [is_subgroup S] [fintype S]

lemma card_nth_roots_subgroup_units [decidable_eq R] {n : ℕ} (hn : 0 < n) (a : S) :
  (univ.filter (λ b : S, b ^ n = a)).card ≤ (nth_roots n ((a : units R) : R)).card :=
card_le_card_of_inj_on (λ a, ((a : units R) : R))
  (by simp [mem_nth_roots hn, (units.coe_pow _ _).symm, -units.coe_pow, units.ext_iff.symm, subtype.coe_ext])
  (by simp [units.ext_iff.symm, subtype.coe_ext.symm])

instance subgroup_units_cyclic : is_cyclic S :=
by haveI := classical.dec_eq R; exact
is_cyclic_of_card_pow_eq_one_le
  (λ n hn, le_trans (card_nth_roots_subgroup_units S hn 1) (card_nth_roots _ _))

end

namespace finite_field

def field_of_integral_domain [fintype R] [decidable_eq R] [integral_domain R] :
  field R :=
{ inv := λ a, if h : a = 0 then 0
    else fintype.bij_inv (show function.bijective (* a),
      from fintype.injective_iff_bijective.1 $ λ _ _, (domain.mul_right_inj h).1) 1,
  mul_inv_cancel := λ a ha, show a * dite _ _ _ = _, by rw [dif_neg ha, mul_comm];
    exact fintype.right_inverse_bij_inv (show function.bijective (* a), from _) 1,
  inv_zero := dif_pos rfl,
  ..show integral_domain R, by apply_instance }

section polynomial

variables [fintype R] [integral_domain R]

open finset polynomial

/-- The cardinality of a field is at most n times the cardinality of the image of a degree n
  polynomial -/
lemma card_image_polynomial_eval [decidable_eq R] {p : polynomial R} (hp : 0 < p.degree) :
  fintype.card R ≤ nat_degree p * (univ.image (λ x, eval x p)).card :=
finset.card_le_mul_card_image _ _
  (λ a _, calc _ = (p - C a).roots.card : congr_arg card
    (by simp [finset.ext, mem_roots_sub_C hp, -sub_eq_add_neg])
    ... ≤ _ : card_roots_sub_C' hp)

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
lemma exists_root_sum_quadratic {f g : polynomial R} (hf2 : degree f = 2)
  (hg2 : degree g = 2) (hR : fintype.card R % 2 = 1) : ∃ a b, f.eval a + g.eval b = 0 :=
by letI := classical.dec_eq R; exact
suffices ¬ disjoint (univ.image (λ x : R, eval x f)) (univ.image (λ x : R, eval x (-g))),
begin
  simp only [disjoint_left, mem_image] at this,
  push_neg at this,
  rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩,
  exact ⟨a, b, by rw [ha, ← hb, eval_neg, neg_add_self]⟩
end,
assume hd : disjoint _ _,
lt_irrefl (2 * ((univ.image (λ x : R, eval x f)) ∪ (univ.image (λ x : R, eval x (-g)))).card) $
calc 2 * ((univ.image (λ x : R, eval x f)) ∪ (univ.image (λ x : R, eval x (-g)))).card
    ≤ 2 * fintype.card R : nat.mul_le_mul_left _ (finset.card_le_of_subset (subset_univ _))
... = fintype.card R + fintype.card R : two_mul _
... < nat_degree f * (univ.image (λ x : R, eval x f)).card +
      nat_degree (-g) * (univ.image (λ x : R, eval x (-g))).card :
    add_lt_add_of_lt_of_le
      (lt_of_le_of_ne
        (card_image_polynomial_eval (by rw hf2; exact dec_trivial))
        (mt (congr_arg (%2)) (by simp [nat_degree_eq_of_degree_eq_some hf2, hR])))
      (card_image_polynomial_eval (by rw [degree_neg, hg2]; exact dec_trivial))
... = 2 * (univ.image (λ x : R, eval x f) ∪ univ.image (λ x : R, eval x (-g))).card :
  by rw [card_disjoint_union hd]; simp [nat_degree_eq_of_degree_eq_some hf2,
    nat_degree_eq_of_degree_eq_some hg2, bit0, mul_add]

end polynomial

section
variables [field K] [fintype K]

lemma card_units : fintype.card (units K) = fintype.card K - 1 :=
begin
  classical,
  rw [eq_comm, nat.sub_eq_iff_eq_add (fintype.card_pos_iff.2 ⟨(0 : K)⟩)],
  haveI := set_fintype {a : K | a ≠ 0},
  haveI := set_fintype (@set.univ K),
  rw [fintype.card_congr (equiv.units_equiv_ne_zero _),
    ← @set.card_insert _ _ {a : K | a ≠ 0} _ (not_not.2 (eq.refl (0 : K)))
    (set.fintype_insert _ _), fintype.card_congr (equiv.set.univ K).symm],
  congr; simp [set.ext_iff, classical.em]
end

instance : is_cyclic (units K) :=
by haveI := classical.dec_eq K;
haveI := set_fintype (@set.univ (units K)); exact
let ⟨g, hg⟩ := is_cyclic.exists_generator (@set.univ (units K)) in
⟨⟨g, λ x, let ⟨n, hn⟩ := hg ⟨x, trivial⟩ in ⟨n, by rw [← is_subgroup.coe_gpow, hn]; refl⟩⟩⟩

lemma prod_univ_units_id_eq_neg_one :
  univ.prod (λ x, x) = (-1 : units K) :=
begin
  classical,
  have : ((@univ (units K) _).erase (-1)).prod (λ x, x) = 1,
  from prod_involution (λ x _, x⁻¹) (by simp)
    (λ a, by simp [units.inv_eq_self_iff] {contextual := tt})
    (λ a, by simp [@inv_eq_iff_inv_eq _ _ a, eq_comm] {contextual := tt})
    (by simp),
  rw [← insert_erase (mem_univ (-1 : units K)), prod_insert (not_mem_erase _ _),
      this, mul_one]
end

theorem card (p : ℕ) [char_p K p] : ∃ (n : ℕ+), nat.prime p ∧ fintype.card K = p^(n : ℕ) :=
begin
  haveI hp : fact p.prime := char_p.char_is_prime K p,
  have V : vector_space (zmod p) K, from { .. (zmod.cast_hom p K).to_module },
  obtain ⟨n, h⟩ := @vector_space.card_fintype _ _ _ _ V _ _,
  rw zmod.card at h,
  refine ⟨⟨n, _⟩, hp, h⟩,
  apply or.resolve_left (nat.eq_zero_or_pos n),
  rintro rfl,
  rw nat.pow_zero at h,
  have : (0 : K) = 1, { apply fintype.card_le_one_iff.mp (le_of_eq h) },
  exact absurd this zero_ne_one,
end

theorem card' : ∃ (p : ℕ) (n : ℕ+), nat.prime p ∧ fintype.card K = p^(n : ℕ) :=
let ⟨p, hc⟩ := char_p.exists K in ⟨p, @finite_field.card K _ _ p hc⟩

end

lemma pow_card_sub_one_eq_one [field K] [fintype K] (a : K) (ha : a ≠ 0) :
  a ^ (fintype.card K - 1) = 1 :=
calc a ^ (fintype.card K - 1) = (units.mk0 a ha ^ (fintype.card K - 1) : units K) :
    by rw [units.coe_pow, units.coe_mk0]
  ... = 1 : by { classical, rw [← card_units, pow_card_eq_one], refl }

end finite_field

namespace zmod

open finite_field

lemma sum_two_squares (p : ℕ) [hp : fact p.prime] (x : zmod p) :
  ∃ a b : zmod p, a^2 + b^2 = x :=
begin
  cases hp.eq_two_or_odd with hp2 hp_odd,
  { unfreezeI, subst p, revert x, exact dec_trivial },
  let f : polynomial (zmod p) := X^2,
  let g : polynomial (zmod p) := X^2 - C x,
  obtain ⟨a, b, hab⟩ : ∃ a b, f.eval a + g.eval b = 0 :=
    @exists_root_sum_quadratic _ _ _ f g
      (degree_X_pow 2) (degree_X_pow_sub_C dec_trivial _) (by rw [zmod.card, hp_odd]),
  refine ⟨a, b, _⟩,
  rw ← sub_eq_zero,
  simpa only [eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab,
end

end zmod

namespace char_p

lemma sum_two_squares (R : Type*) [integral_domain R] (p : ℕ) [fact (0 < p)] [char_p R p] (x : ℤ) :
  ∃ a b : ℕ, (a^2 + b^2 : R) = x :=
begin
  haveI := char_is_prime_of_pos R p,
  obtain ⟨a, b, hab⟩ := zmod.sum_two_squares p x,
  refine ⟨a.val, b.val, _⟩,
  have := congr_arg (zmod.cast_hom p R) hab,
  simpa only [zmod.cast_int_cast, zmod.cast_hom_apply, zmod.cast_add,
    zmod.nat_cast_val, _root_.pow_two, zmod.cast_mul]
end

end char_p

open_locale nat
open zmod

/-- The Fermat-Euler totient theorem. `nat.modeq.pow_totient` is an alternative statement
  of the same theorem. -/
@[simp] lemma zmod.pow_totient {n : ℕ} [fact (0 < n)] (x : units (zmod n)) : x ^ φ n = 1 :=
by rw [← card_units_eq_totient, pow_card_eq_one]

/-- The Fermat-Euler totient theorem. `zmod.pow_totient` is an alternative statement
  of the same theorem. -/
lemma nat.modeq.pow_totient {x n : ℕ} (h : nat.coprime x n) : x ^ φ n ≡ 1 [MOD n] :=
begin
  cases n, {simp},
  rw ← zmod.eq_iff_modeq_nat,
  let x' : units (zmod (n+1)) := zmod.unit_of_coprime _ h,
  have := zmod.pow_totient x',
  apply_fun (coe : units (zmod (n+1)) → zmod (n+1)) at this,
  simpa only [-zmod.pow_totient, succ_eq_add_one, cast_pow, units.coe_one,
    nat.cast_one, cast_unit_of_coprime, units.coe_pow],
end

section
variables {G : Type*} [group G] [integral_domain R]

open_locale big_operators
open finset

-- /-- If `f` is a homomorphism from a group `G` to a monoid `M`,
-- then its image lies in the units of `M`,
-- and `f.to_hom_units` is the corresponding monoid homomorphism from `G` to `units M`. -/
-- @[to_additive "If `f` is a homomorphism from an additive group `G` to an additive monoid `M`,
-- then its image lies in the `add_units` of `M`,
-- and `f.to_hom_units` is the corresponding homomorphism from `G` to `add_units M`."]
-- def monoid_hom.to_hom_units {G M : Type*} [group G] [monoid M] (f : G →* M) : G →* units M :=
-- { to_fun := λ g,
--     ⟨f g, f (g⁻¹),
--       by rw [← monoid_hom.map_mul, mul_inv_self, monoid_hom.map_one],
--       by rw [← monoid_hom.map_mul, inv_mul_self, monoid_hom.map_one]⟩,
--   map_one' := units.ext (monoid_hom.map_one _),
--   map_mul' := λ _ _, units.ext (monoid_hom.map_mul _ _ _) }

-- @[simp] lemma monoid_hom.coe_to_hom_units {G M : Type*} [group G] [monoid M] (f : G →* M) (g : G):
--   (monoid_hom.to_hom_units f g : M) = f g := rfl

lemma card_fiber_eq_of_mem_range [fintype G]
  {H : Type*} [group H] [decidable_eq H] (f : G →* H) {x y : H}
  (hx : x ∈ set.range f) (hy : y ∈ set.range f) :
  (univ.filter $ λ g, f g = x).card = (univ.filter $ λ g, f g = y).card :=
begin
  rcases hx with ⟨x, rfl⟩,
  rcases hy with ⟨y, rfl⟩,
  refine card_congr (λ g _, g * x⁻¹ * y) _ _ (λ g hg, ⟨g * y⁻¹ * x, _⟩),
  { simp only [mem_filter, one_mul, monoid_hom.map_mul, mem_univ, mul_right_inv,
      eq_self_iff_true, monoid_hom.map_mul_inv, and_self, forall_true_iff] {contextual := tt} },
  { simp only [mul_right_inj, imp_self, forall_2_true_iff], },
  { simp only [true_and, mem_filter, mem_univ] at hg,
    simp only [hg, mem_filter, one_mul, monoid_hom.map_mul, mem_univ, mul_right_inv,
      eq_self_iff_true, exists_prop_of_true, monoid_hom.map_mul_inv, and_self,
      mul_inv_cancel_right, inv_mul_cancel_right], }
end

-- @[to_additive]
-- lemma prod_subtype {R M : Type*} [comm_monoid M]
--   {p : R → Prop} {F : fintype (subtype p)} {s : finset R} (h : ∀ x, x ∈ s ↔ p x) (f : R → M) :
--   ∏ a in s, f a = ∏ a : subtype p, f a :=
-- have (∈ s) = p, from set.ext h,
-- begin
--   rw ← prod_attach,
--   resetI,
--   subst p,
--   congr,
--   simp [finset.ext]
-- end

variable [fintype G]

section

variables [decidable_eq G]
variable (G)
-- lemma is_cyclic.exists_monoid_generator [is_cyclic G] :
--   ∃ x : G, ∀ y : G, y ∈ powers x :=
-- by simp only [powers_eq_gpowers]; exact is_cyclic.exists_generator G

open_locale classical add_monoid

end

-- lemma finset.mem_image_univ_iff {α : Type*} {β : Type*} [fintype α] [decidable_eq β] (f : α → β) (b : β) :
--   b ∈ finset.univ.image f ↔ b ∈ set.range f :=
-- begin
--   simp only [mem_image, set.mem_range, mem_univ, exists_prop_of_true],
-- end

variable {G}
/-- In an integral domain, a sum indexed by a nontrivial homomorphism from a finite group is zero. -/
lemma sum_hom_units_eq_zero (f : G →* R) (hf : f ≠ 1) : ∑ g : G, f g = 0 :=
begin
  classical,
  obtain ⟨x, hx⟩ : ∃ x : set.range f.to_hom_units, ∀ y : set.range f.to_hom_units, y ∈ powers x,
    from is_cyclic.exists_monoid_generator (set.range (f.to_hom_units)),
  have hx1 : x ≠ 1,
  { rintro rfl,
    apply hf,
    ext g,
    rw [monoid_hom.one_apply],
    cases hx ⟨f.to_hom_units g, g, rfl⟩ with n hn,
    rwa [subtype.coe_ext, units.ext_iff, subtype.coe_mk, monoid_hom.coe_to_hom_units,
      is_submonoid.coe_pow, units.coe_pow, is_submonoid.coe_one, units.coe_one,
      _root_.one_pow, eq_comm] at hn, },
  replace hx1 : (x : R) - 1 ≠ 0,
    from λ h, hx1 (subtype.eq (units.ext (sub_eq_zero.1 h))),
  let c := (univ.filter (λ g, f.to_hom_units g = 1)).card,
  calc ∑ g : G, f g
      = ∑ g : G, f.to_hom_units g : rfl
  ... = ∑ u : units R in univ.image f.to_hom_units, (univ.filter (λ g, f.to_hom_units g = u)).card • u :
    sum_comp (coe : units R → R) f.to_hom_units
  ... = ∑ u : units R in univ.image f.to_hom_units, c • u : sum_congr rfl (λ u hu, congr_arg2 _ _ rfl)
  ... = ∑ b : set.range f.to_hom_units, c • ↑b : finset.sum_subtype
      (by simp only [mem_image, set.mem_range, forall_const, iff_self, mem_univ, exists_prop_of_true]) _
  ... = c • ∑ b : set.range f.to_hom_units, (b : R) : smul_sum.symm
  ... = c • 0 : congr_arg2 _ rfl _
  ... = 0 : smul_zero _,
  { apply card_fiber_eq_of_mem_range f.to_hom_units,
    { simpa only [mem_image, mem_univ, exists_prop_of_true, set.mem_range] using hu, },
    { exact ⟨1, f.to_hom_units.map_one⟩ } },
  calc ∑ b : set.range f.to_hom_units, (b : R)
      = ∑ n in range (order_of x), x ^ n :
    eq.symm $ sum_bij (λ n _, x ^ n)
      (by simp only [mem_univ, forall_true_iff])
      (by simp only [is_submonoid.coe_pow, eq_self_iff_true, units.coe_pow, coe_coe, forall_true_iff])
      (λ m n hm hn, pow_injective_of_lt_order_of _
        (by simpa only [mem_range] using hm)
        (by simpa only [mem_range] using hn))
      (λ b hb, let ⟨n, hn⟩ := hx b in ⟨n % order_of x, mem_range.2 (nat.mod_lt _ (order_of_pos _)),
        by rw [← pow_eq_mod_order_of, hn]⟩)
  ... = 0 : _,
  rw [← domain.mul_right_inj hx1, zero_mul, ← geom_series, geom_sum_mul, coe_coe],
  norm_cast,
  rw [pow_order_of_eq_one, is_submonoid.coe_one, units.coe_one, sub_self],
end

/-- In an integral domain, a sum indexed by a homomorphism from a finite group is zero,
unless the homomorphism is trivial, in which case the sum is equal to the cardinality of the group. -/
lemma sum_hom_units (f : G →* R) [decidable (f = 1)] :
  ∑ g : G, f g = if f = 1 then fintype.card G else 0 :=
begin
  split_ifs with h h,
  { simp [h, card_univ] },
  { exact sum_hom_units_eq_zero f h }
end

end
