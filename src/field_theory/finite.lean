/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.order_of_element data.polynomial data.equiv.algebra data.zmod.basic
import algebra.char_p

universes u v
variables {α : Type u} {β : Type v}

open function finset polynomial nat

section

variables [integral_domain α] [decidable_eq α] (S : set (units α)) [is_subgroup S] [fintype S]

lemma card_nth_roots_subgroup_units {n : ℕ} (hn : 0 < n) (a : S) :
  (univ.filter (λ b : S, b ^ n = a)).card ≤ (nth_roots n ((a : units α) : α)).card :=
card_le_card_of_inj_on (λ a, ((a : units α) : α))
  (by simp [mem_nth_roots hn, (units.coe_pow _ _).symm, -units.coe_pow, units.ext_iff.symm, subtype.coe_ext])
  (by simp [units.ext_iff.symm, subtype.coe_ext.symm])

instance subgroup_units_cyclic : is_cyclic S :=
by haveI := classical.dec_eq α; exact
is_cyclic_of_card_pow_eq_one_le
  (λ n hn, le_trans (card_nth_roots_subgroup_units S hn 1) (card_nth_roots _ _))

end

namespace finite_field

def field_of_integral_domain [fintype α] [decidable_eq α] [integral_domain α] :
  discrete_field α :=
{ has_decidable_eq := by apply_instance,
  inv := λ a, if h : a = 0 then 0
    else fintype.bij_inv (show function.bijective (* a),
      from fintype.injective_iff_bijective.1 $ λ _ _, (domain.mul_right_inj h).1) 1,
  inv_mul_cancel := λ a ha, show dite _ _ _ * a = _, by rw dif_neg ha;
    exact fintype.right_inverse_bij_inv (show function.bijective (* a), from _) 1,
  mul_inv_cancel :=  λ a ha, show a * dite _ _ _ = _, by rw [dif_neg ha, mul_comm];
    exact fintype.right_inverse_bij_inv (show function.bijective (* a), from _) 1,
  inv_zero := dif_pos rfl,
  ..show integral_domain α, by apply_instance }

section polynomial

variables [fintype α] [integral_domain α]

open finset polynomial

/-- The cardinality of a field is at most n times the cardinality of the image of a degree n
  polnyomial -/
lemma card_image_polynomial_eval [decidable_eq α] {p : polynomial α} (hp : 0 < p.degree) :
  fintype.card α ≤ nat_degree p * (univ.image (λ x, eval x p)).card :=
finset.card_le_mul_card_image _ _
  (λ a _, calc _ = (p - C a).roots.card : congr_arg card
    (by simp [finset.ext, mem_roots_sub_C hp, -sub_eq_add_neg])
    ... ≤ _ : card_roots_sub_C' hp)

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
lemma exists_root_sum_quadratic {f g : polynomial α} (hf2 : degree f = 2)
  (hg2 : degree g = 2) (hα : fintype.card α % 2 = 1) : ∃ a b, f.eval a + g.eval b = 0 :=
by letI := classical.dec_eq α; exact
suffices ¬ disjoint (univ.image (λ x : α, eval x f)) (univ.image (λ x : α, eval x (-g))),
begin
  simp only [disjoint_left, mem_image] at this,
  push_neg at this,
  rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩,
  exact ⟨a, b, by rw [ha, ← hb, eval_neg, neg_add_self]⟩
end,
assume hd : disjoint _ _,
lt_irrefl (2 * ((univ.image (λ x : α, eval x f)) ∪ (univ.image (λ x : α, eval x (-g)))).card) $
calc 2 * ((univ.image (λ x : α, eval x f)) ∪ (univ.image (λ x : α, eval x (-g)))).card
    ≤ 2 * fintype.card α : nat.mul_le_mul_left _ (finset.card_le_of_subset (subset_univ _))
... = fintype.card α + fintype.card α : two_mul _
... < nat_degree f * (univ.image (λ x : α, eval x f)).card +
      nat_degree (-g) * (univ.image (λ x : α, eval x (-g))).card :
    add_lt_add_of_lt_of_le
      (lt_of_le_of_ne
        (card_image_polynomial_eval (by rw hf2; exact dec_trivial))
        (mt (congr_arg (%2)) (by simp [nat_degree_eq_of_degree_eq_some hf2, hα])))
      (card_image_polynomial_eval (by rw [degree_neg, hg2]; exact dec_trivial))
... = 2 * (univ.image (λ x : α, eval x f) ∪ univ.image (λ x : α, eval x (-g))).card :
  by rw [card_disjoint_union hd]; simp [nat_degree_eq_of_degree_eq_some hf2,
    nat_degree_eq_of_degree_eq_some hg2, bit0, mul_add]

end polynomial

section
variables [field α] [fintype α]

instance [decidable_eq α] : fintype (units α) :=
by haveI := set_fintype {a : α | a ≠ 0}; exact
fintype.of_equiv _ (equiv.units_equiv_ne_zero α).symm

lemma card_units [decidable_eq α] : fintype.card (units α) = fintype.card α - 1 :=
begin
  rw [eq_comm, nat.sub_eq_iff_eq_add (fintype.card_pos_iff.2 ⟨(0 : α)⟩)],
  haveI := set_fintype {a : α | a ≠ 0},
  haveI := set_fintype (@set.univ α),
  rw [fintype.card_congr (equiv.units_equiv_ne_zero _),
    ← @set.card_insert _ _ {a : α | a ≠ 0} _ (not_not.2 (eq.refl (0 : α)))
    (set.fintype_insert _ _), fintype.card_congr (equiv.set.univ α).symm],
  congr; simp [set.ext_iff, classical.em]
end

instance : is_cyclic (units α) :=
by haveI := classical.dec_eq α;
haveI := set_fintype (@set.univ (units α)); exact
let ⟨g, hg⟩ := is_cyclic.exists_generator (@set.univ (units α)) in
⟨⟨g, λ x, let ⟨n, hn⟩ := hg ⟨x, trivial⟩ in ⟨n, by rw [← is_subgroup.coe_gpow, hn]; refl⟩⟩⟩

lemma prod_univ_units_id_eq_neg_one [decidable_eq α] :
  univ.prod (λ x, x) = (-1 : units α) :=
have ((@univ (units α) _).erase (-1)).prod (λ x, x) = 1,
from prod_involution (λ x _, x⁻¹) (by simp)
  (λ a, by simp [units.inv_eq_self_iff] {contextual := tt})
  (λ a, by simp [@inv_eq_iff_inv_eq _ _ a, eq_comm] {contextual := tt})
  (by simp),
by rw [← insert_erase (mem_univ (-1 : units α)), prod_insert (not_mem_erase _ _),
    this, mul_one]

end

lemma pow_card_sub_one_eq_one [discrete_field α] [fintype α] (a : α) (ha : a ≠ 0) :
  a ^ (fintype.card α - 1) = 1 :=
calc a ^ (fintype.card α - 1) = (units.mk0 a ha ^ (fintype.card α - 1) : units α) :
    by rw [units.coe_pow, units.mk0_val]
  ... = 1 : by rw [← card_units, pow_card_eq_one]; refl

end finite_field

namespace zmodp

open finite_field

lemma sum_two_squares_of_odd {p : ℕ} (hp : p.prime) (hp2 : p % 2 = 1) (x : zmodp p hp) :
  ∃ a b : zmodp p hp, a^2 + b^2 = x :=
let ⟨a, b, hab⟩ := @exists_root_sum_quadratic _ _ _
  (X^2 : polynomial (zmodp p hp)) (X^2 - C x) (by simp)
  (degree_X_pow_sub_C dec_trivial _) (by simp *) in
⟨a, b, by simpa only [eval_add, eval_pow, eval_neg, eval_X, eval_sub, eval_C,
    (add_sub_assoc _ _ _).symm, sub_eq_zero] using hab⟩

lemma sum_two_squares {p : ℕ} (hp : p.prime) (x : zmodp p hp) (h2x : 2 ∣ (x - 1)) :
  ∃ a b : zmodp p hp, a^2 + b^2 = x :=
hp.eq_two_or_odd.elim (λ hp2, by resetI; subst hp2; revert x; exact dec_trivial)
  (λ hp2, sum_two_squares_of_odd _ hp2 _)

end zmodp

namespace char_p

lemma sum_two_squares_of_odd {α : Type*} [integral_domain α] {n : ℕ+} [char_p α n]
  (hn2 : (n : ℕ) % 2 = 1) (x : ℤ) : ∃ a b : ℕ, (a^2 + b^2 : α) = x :=
let ⟨a, b, hab⟩ := zmodp.sum_two_squares_of_odd (show nat.prime n,
  from (char_p.char_is_prime_or_zero α _).resolve_right (nat.pos_iff_ne_zero.1 n.2)) hn2 x in
⟨a.val, b.val, begin
  have := congr_arg (zmod.cast : zmod n → α) hab,
  rw [← zmod.cast_val a, ← zmod.cast_val b] at this,
  simpa only [is_ring_hom.map_add (zmod.cast : zmod n → α),
    is_semiring_hom.map_pow (zmod.cast : zmod n → α),
    is_semiring_hom.map_nat_cast (zmod.cast : zmod n → α),
    is_ring_hom.map_int_cast (zmod.cast : zmod n → α)]
end⟩

lemma sum_two_squares {α : Type*} [integral_domain α] {n : ℕ+} [char_p α n]
  (hn2 : (n : ℕ) % 2 = 1) (x : ℤ) (h2x : 2 ∣ (x - 1 : zmod n)) :
  ∃ a b : ℕ, (a^2 + b^2 : α) = x :=
let ⟨a, b, hab⟩ := zmodp.sum_two_squares (show nat.prime n,
  from (char_p.char_is_prime_or_zero α _).resolve_right (nat.pos_iff_ne_zero.1 n.2)) x h2x in
⟨a.val, b.val, begin
  have := congr_arg (zmod.cast : zmod n → α) hab,
  rw [← zmod.cast_val a, ← zmod.cast_val b] at this,
  simpa only [is_ring_hom.map_add (zmod.cast : zmod n → α),
    is_semiring_hom.map_pow (zmod.cast : zmod n → α),
    is_semiring_hom.map_nat_cast (zmod.cast : zmod n → α),
    is_ring_hom.map_int_cast (zmod.cast : zmod n → α)]
end⟩

end char_p
