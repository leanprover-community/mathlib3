/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.order_of_element data.polynomial data.equiv.algebra

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
have ∀ f : polynomial α, degree f = 2 →
    fintype.card α ≤ 2 * (univ.image (λ x : α, eval x f)).card,
  from λ f hf, have hf0 : f ≠ 0, from λ h, by simp * at *; contradiction,
    calc fintype.card α ≤ nat_degree f * (univ.image (λ x, eval x f)).card :
      card_image_polynomial_eval (hf.symm ▸ dec_trivial)
    ... = _ : by rw [degree_eq_nat_degree hf0, show (2 : with_bot ℕ) = (2 : ℕ), from rfl,
      with_bot.coe_eq_coe] at hf; rw hf,
have ∀ f : polynomial α, degree f = 2 →
    fintype.card α < 2 * (univ.image (λ x : α, eval x f)).card,
  from λ f hf, lt_of_le_of_ne (this _ hf) (mt (congr_arg (% 2)) (by simp *)),
have h : fintype.card α < (univ.image (λ x : α, eval x f)).card +
    (univ.image (λ x : α, eval x (-g))).card,
  from (mul_lt_mul_left (show 2 > 0, by norm_num)).1 $
    by rw [two_mul, mul_add]; exact add_lt_add (this _ hf2) (this _ (by simpa)),
have hd : ¬ disjoint (univ.image (λ x : α, eval x f)) (univ.image (λ x : α, eval x (-g))),
  from λ hd, by rw [← card_disjoint_union hd, ← not_le] at h;
    exact h (card_le_of_subset $ subset_univ _),
begin
  simp only [disjoint_left, mem_image] at hd,
  push_neg at hd,
  rcases hd with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩,
  use [a, b],
  rw [ha, ← hb, eval_neg, neg_add_self]
end

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
