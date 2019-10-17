/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import set_theory.cardinal
import data.equiv.algebra
import data.mv_polynomial
import algebra.pi_instances
import algebra.geom_sum
import group_theory.order_of_element
import field_theory.finite_card

universes u v
variables {α : Type u} {β : Type v}

section

open function finset polynomial nat

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
local notation `q` := fintype.card α

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

section
open function finset polynomial

variables [discrete_field α] [fintype α]

instance : fintype (units α) :=
by haveI := set_fintype {a : α | a ≠ 0}; exact
fintype.of_equiv _ (equiv.units_equiv_ne_zero α).symm

lemma card_units : fintype.card (units α) = q - 1 :=
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
by haveI := set_fintype (@set.univ (units α)); exact
let ⟨g, hg⟩ := is_cyclic.exists_generator (@set.univ (units α)) in
⟨⟨g, λ x, let ⟨n, hn⟩ := hg ⟨x, trivial⟩ in ⟨n, by rw [← is_subgroup.coe_gpow, hn]; refl⟩⟩⟩

lemma prod_univ_units_id_eq_neg_one : univ.prod (λ x, x) = (-1 : units α) :=
have ((@univ (units α) _).erase (-1)).prod (λ x, x) = 1,
from prod_involution (λ x _, x⁻¹) (by simp)
  (λ a, by simp [units.inv_eq_self_iff] {contextual := tt})
  (λ a, by simp [@inv_eq_iff_inv_eq _ _ a, eq_comm] {contextual := tt})
  (by simp),
by rw [← insert_erase (mem_univ (-1 : units α)), prod_insert (not_mem_erase _ _),
    this, mul_one]

lemma pow_card_sub_one_eq_one (a : α) (ha : a ≠ 0) : a ^ (q - 1) = 1 :=
calc a ^ (q - 1) = (units.mk0 a ha ^ (q - 1) : units α) : by rw [units.coe_pow, units.mk0_val]
             ... = 1 : by rw [← card_units, pow_card_eq_one]; refl

variable (α)

lemma sum_pow_units (i : ℕ) :
  univ.sum (λ (x : units α), (x^i : α)) = if (q - 1) ∣ i then q - 1 else 0 :=
begin
  have hq : 0 < q - 1,
  { rw [← card_units, fintype.card_pos_iff],
    exact ⟨1⟩ },
  cases is_cyclic.exists_generator (units α) with a ha,
  calc univ.sum (λ (x : units α), (x^i : α)) = (range (order_of a)).sum (λ k, ((a^k)^i : α)) :
  begin
    symmetry,
    refine sum_bij (λ i hi, a^i) (λ _ _, mem_univ _) (λ _ _, by rw units.coe_pow) _ _,
    { intros i j hi hj h, rw [mem_range] at hi hj,
      exact pow_injective_of_lt_order_of a hi hj h, },
    { intros x hx, specialize ha x,
      rwa [mem_gpowers_iff_mem_range_order_of, mem_image] at ha,
      rcases ha with ⟨i, hi, rfl⟩, exact ⟨i, hi, rfl⟩ }
  end
    ... = geom_series (a^i : α) (q-1) :
  begin
    rw [order_of_eq_card_of_forall_mem_gpowers ha, card_units],
    apply sum_congr rfl, intros k hk, rw [← pow_mul, mul_comm, pow_mul]
  end
    ... = if (q - 1) ∣ i then q - 1 else 0 :
  begin
    split_ifs with H H,
    { rcases H with ⟨d, rfl⟩,
      have aux : (λ (i:ℕ), ((a : α) ^ ((q - 1) * d)) ^ i) = λ i, 1,
      { funext i, rw [pow_mul, pow_card_sub_one_eq_one _ (units.ne_zero _), one_pow, one_pow], },
      rw [geom_series_def, aux, sum_const, card_range, add_monoid.smul_one,
        nat.cast_sub, nat.cast_one],
      exact le_trans hq (nat.pred_le _), },
    { have key := geom_sum_mul (a^i : α) (q-1),
      have hai : (a^i : α) ≠ 0, { rw ← units.coe_pow, apply units.ne_zero },
      rw [pow_card_sub_one_eq_one _ hai, sub_self] at key,
      replace key := eq_zero_or_eq_zero_of_mul_eq_zero key,
      rw classical.or_iff_not_imp_right at key, apply key, contrapose! H,
      rw [← card_units, ← order_of_eq_card_of_forall_mem_gpowers ha],
      apply order_of_dvd_of_pow_eq_one,
      rwa [units.ext_iff, units.coe_pow, units.coe_one, ← sub_eq_zero], }
  end
end

lemma sum_pow_lt_card_sub_one (i : ℕ) (h : i < q - 1) :
  univ.sum (λ x, x^i) = (0:α) :=
begin
  have hq : 0 < q - 1,
  { rw [← card_units, fintype.card_pos_iff],
    exact ⟨1⟩ },
  by_cases hi : i = 0,
  { rcases char_p.exists α with ⟨p, _char_p⟩, resetI,
    rcases card α p with ⟨n, hp, hn⟩,
    simp only [hi, add_monoid.smul_one, sum_const, pow_zero, card_univ, cast_card_eq_zero], },
  rw [← sum_sdiff (subset_univ (finset.singleton (0:α))), sum_singleton,
    zero_pow (nat.pos_of_ne_zero hi), add_zero],
  have := sum_pow_units α i,
  have not_dvd_i : ¬q - 1 ∣ i,
  { rintro ⟨d, rfl⟩, apply hi, rw nat.mul_eq_zero, right, contrapose! h,
    conv { congr, rw ← mul_one (q-1), },
    rw mul_le_mul_left hq, exact nat.pos_of_ne_zero h },
  rw if_neg not_dvd_i at this,
  conv_rhs {rw ← this}, symmetry,
  refine sum_bij (λ x _, x) (λ _ _, by simp) (λ _ _, rfl) (λ _ _ _ _, units.ext_iff.mpr) _,
  { intros, refine ⟨units.mk0 b _, mem_univ _, rfl⟩,
    simpa only [true_and, mem_sdiff, mem_univ, mem_singleton] using H, },
end

end

section chevalley_warning
open mv_polynomial function finset

variables [discrete_field α] [fintype α] {σ : Type*} [fintype σ] [decidable_eq σ]

-- move this
lemma sum_mul_sum {ι₁ : Type*} {ι₂ : Type*} (s₁ : finset ι₁) (s₂ : finset ι₂)
  (f₁ : ι₁ → α) (f₂ : ι₂ → α) :
  s₁.sum f₁ * s₂.sum f₂ = (s₁.product s₂).sum (λ p, f₁ p.1 * f₂ p.2) :=
begin
  sorry
end

lemma sum_mv_polynomial_eq_zero (f : mv_polynomial σ α)
  (h : f.total_degree < (q - 1) * fintype.card σ) :
  univ.sum (λ x, f.eval x) = (0:α) :=
begin
  have hq : 0 < q - 1,
  { rw [← card_units, fintype.card_pos_iff],
    exact ⟨1⟩ },
  rcases char_p.exists α with ⟨p, _char_p⟩, resetI,
  rcases card α p with ⟨n, hp, hn⟩,
  simp only [eval, eval₂, finsupp.sum, id.def],
  rw [sum_comm, sum_eq_zero],
  intros d hd,
  rw [← mul_sum, mul_eq_zero], right,
  simp [finsupp.prod],
  obtain ⟨i, hi⟩ : ∃ i, d i < q - 1,
  { contrapose! h,
    refine le_trans _ (finset.le_sup hd),
    have : univ.sum (λ s:σ, q-1) ≤ univ.sum (λ s, d s) := sum_le_sum (λ s _, h s),
    rw [sum_const, nat.smul_eq_mul, mul_comm, card_univ] at this,
    rwa [finsupp.sum, show d.support = univ, from _],
    rw eq_univ_iff_forall,
    intro i, rw [finsupp.mem_support_iff, ne.def, ← nat.le_zero_iff],
    push_neg, exact lt_of_lt_of_le hq (h _), },
  suffices claim : (univ.filter (λ (x : σ → α), ∀ j, j ≠ i → x j = 0)).sum (λ x, x i ^ d i) *
    (univ.filter (λ (x : σ → α), x i = 0)).sum
    (λ (x : σ → α), (univ \ finset.singleton i).prod (λ j, x j ^ d j)) = 0,
  { rw sum_mul_sum at claim, rw ← claim, symmetry,
    refine sum_bij (λ p _ j, if j = i then p.1 j else p.2 j) (λ _ _, mem_univ _) _ _ _,
    { rintros ⟨x,y⟩ hxy, rw [mem_product, mem_filter, mem_filter] at hxy,
      sorry -- is this even true??
      -- simp at hxy,
      -- simp,
       },
      all_goals { sorry } },
  { rw mul_eq_zero, left,
    conv_rhs {rw ← sum_pow_lt_card_sub_one (d i) hi},
    refine sum_bij (λ x _, x i) (λ _ _, mem_univ _) (λ _ _, rfl) _ _,
    { intros x y hx hy H, rw mem_filter at hx hy,
      funext j, by_cases hj : j = i, {rwa hj},
      rw [hx.2 _ hj, hy.2 _ hj], },
    { intros a ha,
      refine ⟨λ j, if j = i then a else 0, _, (if_pos rfl).symm⟩,
      rw mem_filter,
      exact ⟨mem_univ _, λ j hj, dif_neg hj⟩ } }
end

-- move this
@[move_cast]
lemma cast_prod {ι : Type*} (s : finset ι) (f : ι → ℕ) :
  s.prod (λ i, (f i : α)) = ((s.prod f : ℕ) : α) :=
finset.prod_hom _

-- move this
@[move_cast]
lemma cast_sum {ι : Type*} (s : finset ι) (f : ι → ℕ) :
  s.sum (λ i, (f i : α)) = ((s.sum f : ℕ) : α) :=
finset.sum_hom _

open_locale classical

-- move this
@[to_additive]
lemma prod_extend_by_one {α} [comm_monoid α] {ι : Type*} [fintype ι] (s : finset ι) (f : ι → α) :
  univ.prod (λ i, if i ∈ s then f i else 1) = s.prod f :=
begin
  rw [← prod_sdiff (subset_univ s), prod_eq_one, one_mul, prod_congr rfl],
  { intros i hi, exact dif_pos hi },
  { intros i hi, rw mem_sdiff at hi, exact dif_neg hi.2 }
end

/-- The Chevalley–Warning theorem. -/
theorem char_dvd_card_solutions (p : nat.primes) [char_p α p]
  {ι : Type*} (s : finset ι) (f : ι → (mv_polynomial σ α))
  (h : (s.sum $ λ i, (f i).total_degree) < fintype.card σ) :
  (p:ℕ) ∣ fintype.card {x : σ → α // ∀ i ∈ s, (f i).eval x = 0} :=
begin
  have hq : 0 < q - 1,
  { rw [← card_units, fintype.card_pos_iff],
    exact ⟨1⟩ },
  let F : mv_polynomial σ α := s.prod (λ i, (1 - (f i)^(q-1))),
  suffices : univ.sum (λ x, F.eval x) =
    fintype.card {x : σ → α // ∀ i ∈ s, (f i).eval x = 0},
  { rw [← char_p.cast_eq_zero_iff α, ← this],
    apply sum_mv_polynomial_eq_zero,
    calc F.total_degree ≤ s.sum (λ i, (1 - (f i)^(q-1)).total_degree) :
      total_degree_finset_prod_le s _
      ... ≤ s.sum (λ i, (q - 1) * (f i).total_degree) :
      begin
        apply sum_le_sum,
        intros i hi,
        refine le_trans (total_degree_sub _ _)
          (le_trans _ (total_degree_pow_le _ _)),
        simp only [max_eq_right, nat.zero_le, total_degree_one]
      end
      ... = (q - 1) * (s.sum $ λ i, (f i).total_degree) : mul_sum.symm
      ... < (q - 1) * (fintype.card σ) : by rwa mul_lt_mul_left hq },
  { let S : finset (σ → α) := univ.filter (λ x : σ → α, ∀ i ∈ s, (f i).eval x = 0),
    rw_mod_cast [fintype.card_of_subtype S, card_eq_sum_ones, ← sum_extend_by_zero S],
    { apply sum_congr rfl,
      intros x hx, clear hx,
      rw show F.eval x = finset.prod s (λ (i : ι), (1 - f i ^ (q - 1)).eval x),
      { convert eval₂_prod _ _ _ _, exact is_semiring_hom.id },
      split_ifs with hx hx,
      { rw finset.prod_eq_one, intros i hi,
        rw mem_filter at hx,
        simp only [hx.right i hi, add_right_eq_self, neg_eq_zero, sub_eq_add_neg,
          eval_add, eval_pow, eval_one, eval_neg],
        exact zero_pow hq },
      { rw mem_filter at hx, push_neg at hx, simp only [false_or, mem_univ, not_true] at hx,
        rcases hx with ⟨i, hi, hx⟩,
        rw finset.prod_eq_zero hi,
        simp only [pow_card_sub_one_eq_one (eval x (f i)) hx, add_right_neg, sub_eq_add_neg,
          eval_add, eval_pow, eval_one, eval_neg], } },
    { intros x, simp only [mem_filter, mem_univ, true_and] } }
end

end chevalley_warning

end finite_field
