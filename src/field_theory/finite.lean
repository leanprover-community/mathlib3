/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/
import group_theory.order_of_element
import data.polynomial
import data.equiv.ring
import data.zmod.basic
import linear_algebra.basis
import algebra.geom_sum

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, `K` denotes a finite field with `q` elements.

## Main results

1. Every finite integral domain is a field (`field_of_integral_domain`).
2. The unit group of a finite field is a cyclic group of order `q - 1`.
   (`finite_field.is_cyclic` and `card_units`)
3. `sum_pow_units`: The sum of `x^i`, where `x` ranges over the units of `K`, is
   - `q-1` if `q-1 ∣ i`
   - `0`   otherwise
4. `finite_field.card`: The cardinality `q` is a power of the characteristic of `K`.
   See `card'` for a variant.
-/

variables {K : Type*} [field K] [fintype K]
variables {R : Type*} [integral_domain R]
local notation `q` := fintype.card K

open_locale big_operators

section

open function finset polynomial nat

variables {G : Type*} [group G] [fintype G]

lemma card_nth_roots_subgroup_units (f : G →* R) (hf : injective f) {n : ℕ} (hn : 0 < n) (g₀ : G) :
  ({g ∈ univ | g ^ n = g₀} : finset G).card ≤ (nth_roots n (f g₀)).card :=
begin
  apply card_le_card_of_inj_on f,
  { intros g hg, rw [sep_def, mem_filter] at hg, rw [mem_nth_roots hn, ← f.map_pow, hg.2] },
  { intros, apply hf, assumption }
end

/-- A finite subgroup of the unit group of an integral domain is cyclic. -/
lemma is_cyclic_of_subgroup_integral_domain (f : G →* R) (hf : injective f) : is_cyclic G :=
begin
  haveI := classical.dec_eq G,
  apply is_cyclic_of_card_pow_eq_one_le,
  intros n hn,
  convert (le_trans (card_nth_roots_subgroup_units f hf hn 1) (card_nth_roots n (f 1)))
end

/-- The sum of `x ^ i` as `x` ranges over a finite subgroup `G` of the units of an integral domain
is equal to `0` unless the cardinality of `G` divides `i`,
in which case the sum is the cardinality of `G`. -/
lemma sum_pow_units_subgroup (f : G →* R) (hf : injective f) (i : ℕ) :
  ∑ g : G, f g ^ i = if fintype.card G ∣ i then fintype.card G else 0 :=
begin
  haveI : decidable_eq G := classical.dec_eq G,
  haveI : is_cyclic G := is_cyclic_of_subgroup_integral_domain f hf,
  obtain ⟨g₀, hG⟩ := is_cyclic.exists_generator G,
  calc ∑ g : G, f g ^ i = ∑ g in (range (order_of g₀)).image (λ i, g₀ ^ i), f g ^ i :
  by rw [is_cyclic.image_range_order_of hG]
    ... = ∑ k in range (order_of g₀), f (g₀ ^ k) ^ i :
  by { apply finset.sum_image, intros i hi j hj h, rw [mem_range] at hi hj,
       exact pow_injective_of_lt_order_of g₀ hi hj h }
    ... = geom_series (f g₀ ^ i) (fintype.card G) :
  by { rw [order_of_eq_card_of_forall_mem_gpowers hG],
       apply sum_congr rfl, intros k hk, rw [← pow_mul', pow_mul, f.map_pow] }
    ... = if (fintype.card G) ∣ i then fintype.card G else 0 : _,
  split_ifs with H H,
  { rcases H with ⟨d, rfl⟩,
    rw [pow_mul, ← f.map_pow, pow_card_eq_one, f.map_one, geom_series_def],
    simp only [_root_.one_pow, add_monoid.smul_one, sum_const, card_range] },
  { have key : geom_series (f g₀ ^ i) (fintype.card G) * (f g₀ ^ i - 1) = 0,
    { rw [geom_sum_mul (f g₀ ^ i) (fintype.card G), ← f.map_pow, ← f.map_pow,
          pow_card_eq_one, f.map_one, sub_self] },
    apply (eq_zero_or_eq_zero_of_mul_eq_zero key).resolve_right,
    rw [sub_eq_zero, ← f.map_one, ← f.map_pow],
    apply hf.ne,
    contrapose! H,
    rw [← order_of_eq_card_of_forall_mem_gpowers hG],
    exact order_of_dvd_of_pow_eq_one H },
end

variables (S : set (units R)) [is_subgroup S] [fintype S]

/-- A finite subgroup of the units of an integral domain is cyclic. -/
instance subgroup_units_cyclic : is_cyclic S :=
let φ : S →* R :=
{ to_fun := coe,
  map_one' := by simp only [is_submonoid.coe_one, units.coe_one, coe_coe],
  map_mul' := by intros; simp only [is_submonoid.coe_mul, units.coe_mul, coe_coe] } in
is_cyclic_of_subgroup_integral_domain φ $ injective_comp units.ext subtype.val_injective

end

namespace finite_field
open function finset polynomial

/-- The unit group of a finite integral domain is cyclic. -/
instance [fintype R] : is_cyclic (units R) :=
let φ : units R →* R := { to_fun := coe, map_one' := units.coe_one, map_mul' := units.coe_mul } in
is_cyclic_of_subgroup_integral_domain φ $ units.ext

/-- Every finite integral domain is a field. -/
def field_of_integral_domain [fintype R] [decidable_eq R] : field R :=
{ inv := λ a, if h : a = 0 then 0
    else fintype.bij_inv (show function.bijective (* a),
      from fintype.injective_iff_bijective.1 $ λ _ _, (domain.mul_right_inj h).1) 1,
  mul_inv_cancel := λ a ha, show a * dite _ _ _ = _, by rw [dif_neg ha, mul_comm];
    exact fintype.right_inverse_bij_inv (show function.bijective (* a), from _) 1,
  inv_zero := dif_pos rfl,
  ..show integral_domain R, by apply_instance }

section polynomial

open finset polynomial

/-- The cardinality of a field is at most `n` times the cardinality of the image of a degree `n`
  polynomial -/
lemma card_image_polynomial_eval [fintype R] [decidable_eq R] {p : polynomial R} (hp : 0 < p.degree) :
  fintype.card R ≤ nat_degree p * (univ.image (λ x, eval x p)).card :=
finset.card_le_mul_card_image _ _
  (λ a _, calc _ = (p - C a).roots.card : congr_arg card
    (by simp [finset.ext, mem_roots_sub_C hp, -sub_eq_add_neg])
    ... ≤ _ : card_roots_sub_C' hp)

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
lemma exists_root_sum_quadratic [fintype R] {f g : polynomial R} (hf2 : degree f = 2)
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

/-- A finite field of cardinality `q` has a unit group of cardinality `q - 1`. -/
lemma card_units : fintype.card (units K) = q - 1 :=
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

lemma prod_univ_units_id_eq_neg_one :
  ∏ x : units K, x = -1 :=
begin
  classical,
  suffices : ∏ (x : units K) in univ.erase (-1), x = 1,
  by rw [← insert_erase (mem_univ (-1 : units K)), prod_insert (not_mem_erase _ _), this, mul_one],
  apply prod_involution (λ x _, x⁻¹),
  { intros, exact mul_right_inv _, },
  { intros u hu h1, rw mem_erase at hu, rw [ne.def, units.inv_eq_self_iff], tauto },
  { intros, simp only [inv_inv] },
  { intros u hu, rw mem_erase at hu ⊢,
    show ¬u⁻¹ = -1 ∧ u⁻¹ ∈ univ,
    rw [inv_eq_iff_inv_eq, units.neg_inv, one_inv, eq_comm],
    exact ⟨hu.1, mem_univ _⟩, }
end

/-- In a finite field of cardinality `q`, one has `a^(q-1) = 1` for all nonzero `a`. -/
lemma pow_card_sub_one_eq_one  (a : K) (ha : a ≠ 0) :
  a ^ (q - 1) = 1 :=
calc a ^ (q - 1) = (units.mk0 a ha ^ (q - 1) : units K) :
    by rw [units.coe_pow, units.coe_mk0]
  ... = 1 : by { classical, rw [← card_units, pow_card_eq_one], refl }

variable (K)

theorem card (p : ℕ) [char_p K p] : ∃ (n : ℕ+), nat.prime p ∧ q = p^(n : ℕ) :=
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

theorem card' : ∃ (p : ℕ) (n : ℕ+), nat.prime p ∧ q = p^(n : ℕ) :=
let ⟨p, hc⟩ := char_p.exists K in ⟨p, @finite_field.card K _ _ p hc⟩

@[simp] lemma cast_card_eq_zero : (q : K) = 0 :=
begin
  rcases char_p.exists K with ⟨p, _char_p⟩, resetI,
  rcases card K p with ⟨n, hp, hn⟩,
  simp only [char_p.cast_eq_zero_iff K p, hn],
  conv { congr, rw [← nat.pow_one p] },
  exact nat.pow_dvd_pow _ n.2,
end

/-- The sum of `x ^ i` as `x` ranges over the units of a finite field of cardinality `q`
is equal to `0` unless `(q - 1) ∣ i`, in which case the sum is `q - 1`. -/
lemma sum_pow_units (i : ℕ) :
  ∑ x : units K, (x ^ i : K) = if (q - 1) ∣ i then -1 else 0 :=
begin
  calc ∑ x : units K, (x ^ i : K) = if fintype.card (units K) ∣ i then fintype.card (units K) else 0 :
      sum_pow_units_subgroup ⟨(coe : units K → K), units.coe_one, units.coe_mul⟩ units.ext i
    ... = if (q - 1) ∣ i then -1 else 0 : _,
  suffices : 1 ≤ q,
  { simp only [card_units, nat.cast_sub this, cast_card_eq_zero, nat.cast_one, zero_sub],
    split_ifs; refl },
  exact fintype.card_pos_iff.mpr ⟨0⟩
end

/-- The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`
is equal to `0` if `i < q - 1`. -/
lemma sum_pow_lt_card_sub_one (i : ℕ) (h : i < q - 1) :
  ∑ x : K, x ^ i = 0 :=
begin
  by_cases hi : i = 0,
  { simp only [hi, add_monoid.smul_one, sum_const, pow_zero, card_univ, cast_card_eq_zero], },
  classical,
  have hiq : ¬ (q - 1) ∣ i, { contrapose! h,  exact nat.le_of_dvd (nat.pos_of_ne_zero hi) h },
  let φ : units K ↪ K := ⟨coe, units.ext⟩,
  have : univ.map φ = univ \ finset.singleton 0,
  { ext x,
    simp only [true_and, embedding.coe_fn_mk, mem_sdiff, units.exists_iff_ne_zero,
               mem_univ, mem_map, exists_prop_of_true, mem_singleton] },
  calc ∑ x : K, x ^ i = ∑ x in univ \ finset.singleton 0, x ^ i :
    by rw [← sum_sdiff (subset_univ (finset.singleton (0:K))), sum_singleton,
           zero_pow (nat.pos_of_ne_zero hi), add_zero]
    ... = ∑ x : units K, x ^ i : by { rw [← this, univ.sum_map φ], refl }
    ... = 0 : by { rw [sum_pow_units K i, if_neg], exact hiq, }
end

end finite_field

namespace zmod

open finite_field polynomial

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
open zmod nat

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
