/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import data.real.basic
import algebra.category.Group.abelian
import group_theory.finiteness
import data.set.finite
import algebra.geom_sum
import analysis.specific_limits
import some_lemmas

/-!
# definition of height function and descent theorem (about finite-generatedness of abelian group)
-/

noncomputable theory

open_locale classical pointwise big_operators
open finset

universe u

variable (A : Ab.{u})

/--definition of height function-/
@[nolint has_inhabited_instance]
structure height_function :=
(to_fun : A → ℝ)
(nonneg : ∀ P, 0 ≤ to_fun P)
(C1 : A → ℝ) (C1_pos: ∀ a, 0 < C1 a)
(height_add_le : ∀ (Q P : A), to_fun (P + Q) ≤ 2 * to_fun P + C1 Q)
(m : ℕ)
(hm : 2 ≤ m)
(C2 : ℝ) (C2_pos : 0 < C2)
(height_nsmul_ge : ∀ (P : A), ↑m^2 * to_fun P - C2 ≤ to_fun (m • P))
(finite : ∀ (C : ℝ), set.finite { P : A | to_fun P < C })

lemma height_function.height_nsmul_ge' (f : height_function A) :
  ∀ P : A, f.to_fun P ≤ (f.m^2)⁻¹ * (f.to_fun (f.m • P) + f.C2) := λ P,
have ineq1 : _ := f.height_nsmul_ge P,
begin
  rw [sub_le_iff_le_add] at ineq1,
  rwa [←inv_mul_le_iff, inv_inv₀],
  rw [inv_pos],
  apply pow_pos, norm_cast, linarith [f.hm],
end

lemma height_function.height_sub_le (f : height_function A) :
  ∀ (Q P : A), f.to_fun (P - Q) ≤ 2 * f.to_fun P + f.C1 (- Q) := λ Q P,
have ineq1 : _ := f.height_add_le (-Q) P,
begin
  rw [sub_eq_add_neg],
  exact ineq1,
end



variables (m : ℕ)
local notation A`/`m := A⧸(m • (⊤ : add_subgroup A))

variable [fin_quot : fintype (A/m)]
include fin_quot

/--the $Q_i$ in Silverman's book-/
def represents : finset A :=
  image (λ (q : A/m), Exists.some (add_mk_surjective A _ q))
    (fin_quot.elems)

variables {A}
lemma represents_represent_A_quot_mA :
  ∀ (a : A/m), ∃ (q : A), q ∈ represents A m ∧ quotient_add_group.mk q = a := λ a,
begin
  have mem1 : a ∈ fin_quot.elems := fintype.complete a,
    have mem2 : Exists.some (add_mk_surjective A _ a) ∈ represents A m,
      rw [represents, mem_image], use a, refine ⟨mem1, rfl⟩,
    refine ⟨_, mem2, _⟩,
    exact Exists.some_spec (add_mk_surjective A _ a)
end

lemma new_aux (P : A) : ∃ (p : A × represents A m), P = m • p.1 + p.2 :=
have mem1 : quotient_add_group.mk P ∈ fin_quot.elems, from fintype.complete _,
begin
  obtain ⟨a, ha1, ha2⟩ := represents_represent_A_quot_mA m (quotient_add_group.mk P),
  rw [quotient_add_group.eq', mem_smul A m] at ha2,
  obtain ⟨q, hq⟩ := ha2,
  refine ⟨⟨q, ⟨a, ha1⟩⟩, _⟩, dsimp only,
  rw [←hq, add_assoc, add_comm P, ←add_assoc, ←subtype.val_eq_coe, neg_add_self, zero_add],
end

/--$P_{n+1}$ in Silverman's book-/
abbreviation next (P : A) : A := (Exists.some (new_aux m P)).1
/--$Q_{i_n}$ in Silverman's book-/
abbreviation next_rep (P : A) : represents A m := (Exists.some (new_aux m P)).2
/--$P_n$ and $P_{n+1}$ and $Q_{i_n}$ satisfies this property-/
@[nolint def_lemma]
abbreviation next_prop (P : A) := Exists.some_spec (new_aux m P)

lemma property_next (P : A) : m • (next m P) = P - (next_rep m P) :=
suffices h : P = m • (next m P) + (next_rep m P), by rw [eq_sub_iff_add_eq, ←h],
by convert next_prop m P

lemma property_next_rep (P : A) : (next_rep m P : A) ∈ represents A m :=
by simp only [coe_mem]

variable (f : height_function A)
omit fin_quot

variables [fin_quot_f : fintype (A/f.m)] [non_empty_quot_f : nonempty (A/f.m)]
include fin_quot_f non_empty_quot_f

lemma nemp1 : (image (λ a, f.C1 (-a)) (represents A f.m)).nonempty :=
begin
  apply non_empty_quot_f.elim, intro a,
  simp_rw [finset.nonempty, mem_image],
  obtain ⟨x, hx⟩ := represents_represent_A_quot_mA f.m a,
  use f.C1 (- x), use x, refine ⟨hx.1, rfl⟩,
end

/--The maximum height of $-Q_i$'s-/
def C1' : ℝ :=
finset.max' (image (λ a, f.C1 (-a)) (represents A f.m)) (nemp1 f)

lemma C1'_is_max :
  ∀ (a : represents A f.m), (f.C1 (-a)) ≤ C1' f := λ a,
begin
  unfold C1',
  apply finset.le_max' (image (λ a, f.C1 (-a)) (represents A f.m)),
  rw [mem_image], use a, refine ⟨a.2, rfl⟩,
end

lemma C1'_nonneg : 0 ≤ C1' f :=
have H : _ := nemp1 f,
begin
  rw finset.nonempty at H,
  obtain ⟨x, hx⟩ := H,
  rw mem_image at hx,
  obtain ⟨a, ha1, ha2⟩ := hx,
  refine le_trans _ (C1'_is_max f ⟨a, ha1⟩),
  rw ←subtype.val_eq_coe, dsimp,
  linarith [f.C1_pos (-a)],
end

lemma C1'_pos : 0 < C1' f :=
have H : _ := nemp1 f,
begin
  rw finset.nonempty at H,
  obtain ⟨x, hx⟩ := H,
  rw mem_image at hx,
  obtain ⟨a, ha1, ha2⟩ := hx,
  refine lt_of_lt_of_le _ (C1'_is_max f ⟨a, ha1⟩),
  rw ←subtype.val_eq_coe, dsimp,
  linarith [f.C1_pos (-a)],
end

lemma property_next_height (P : A) :
  f.to_fun (next f.m P) ≤ (f.m ^ 2)⁻¹ * (2 * f.to_fun P + C1' f + f.C2) :=
have ineq1 : _ := height_function.height_nsmul_ge' A f (next f.m P),
have ineq2 : _ := height_function.height_sub_le A f (next_rep f.m P) P,
have ineq3 : 2 * f.to_fun P + f.C1 (-(next_rep f.m P)) ≤ 2 * f.to_fun P + C1' f,
begin
  apply add_le_add, refl, apply C1'_is_max,
end,
have ineq4 : f.to_fun (P - (next_rep f.m P)) ≤ 2 * f.to_fun P + C1' f, from le_trans ineq2 ineq3,
begin
  refine le_trans ineq1 _,
  rw [mul_add, mul_add], apply add_le_add,
  apply mul_le_mul, refl, refine le_trans _ ineq4,
  rw property_next, apply f.nonneg,
  rw inv_nonneg, norm_cast, apply pow_nonneg (show 0 ≤ f.m, by linarith) 2,
  refl
end

local notation ` C ` := C1' f + f.C2

lemma property_next_height_aux (P : A) :
  f.to_fun (next f.m P) ≤ 2⁻¹ * f.to_fun P + 4⁻¹ * C :=
have ineq1 : _ := property_next_height f P,
have ineq2 : ((f.m : ℝ) ^ 2)⁻¹ * 2 ≤ 2⁻¹, begin
  rw [le_inv, mul_comm, ←div_eq_mul_inv, inv_div, le_div_iff, pow_two],
  apply mul_le_mul, norm_cast, linarith [f.hm], norm_cast, linarith [f.hm],
  norm_cast, exact zero_le _, norm_cast, linarith [f.hm], norm_cast, exact nat.zero_lt_succ 1,
  apply mul_pos, rw inv_pos, norm_cast, apply pow_pos, linarith [f.hm], norm_cast,
  exact nat.zero_lt_succ 1, norm_cast, exact nat.zero_lt_succ 1,
end,
begin
  apply le_trans ineq1,
  rw [add_assoc, mul_add], apply add_le_add,
  rw [←mul_assoc],
  apply mul_le_mul, exact ineq2, refl, exact f.nonneg _,
  rw inv_nonneg, norm_cast, exact nat.zero_le 2, apply mul_le_mul,
  rw inv_le_inv, norm_cast, rw [show 4 = 2^2, by norm_num],
  apply nat.pow_le_pow_of_le_left, exact f.hm,
  norm_cast, apply pow_pos, linarith [f.hm], norm_cast, exact nat.zero_lt_succ 3,
  refl, apply add_nonneg, exact C1'_nonneg f, linarith [f.C2_pos], rw inv_nonneg,
  norm_cast, exact zero_le 4,
end

lemma property_next_height_iter_aux (P : A) (n : ℕ) :
  f.to_fun ((next f.m)^[n.succ] P) ≤
  (2⁻¹)^n.succ * f.to_fun P + (4⁻¹ * C) * ∑ i in range n.succ, (2⁻¹)^i :=
begin
  induction n with n ih,
  { rw [function.iterate_one, pow_one, range_one,sum_singleton, pow_zero, mul_one],
    apply property_next_height_aux, },
  { rw [function.iterate_succ'],
    have ineq1 := property_next_height f (next f.m^[n.succ] P),
    apply le_trans ineq1,
    conv_lhs { rw [add_assoc, mul_add, ←mul_assoc] },
    have ineq2 := mul_le_mul (show ((f.m : ℝ)^2)⁻¹ * 2 ≤ (f.m ^ 2)⁻¹ * 2, by refl) ih (f.nonneg _)
    begin
      apply mul_nonneg,
      rw inv_nonneg, norm_cast, apply pow_nonneg, linarith [f.hm],
      norm_num,
    end,
    have ineq3 := add_le_add ineq2 (show ((f.m : ℝ) ^ 2)⁻¹ * C ≤ (f.m ^ 2)⁻¹ * C, by refl),
    apply le_trans ineq3,
    conv_lhs { rw [mul_add, add_assoc] },
    apply add_le_add,
    { conv_lhs { rw [←mul_assoc] },
      apply mul_le_mul, conv_rhs { rw pow_succ },
      apply mul_le_mul, rw [le_inv, mul_comm, ←div_eq_mul_inv, inv_div, le_div_iff, pow_two],
      apply mul_le_mul, norm_cast, exact f.hm, norm_cast, exact f.hm, norm_num,
      norm_cast, linarith [f.hm], norm_num, apply mul_pos,
      rw inv_pos, norm_cast, apply pow_pos, linarith [f.hm], norm_num, norm_num, refl,
      apply pow_nonneg, rw inv_nonneg, norm_num, rw inv_nonneg, norm_num, refl, exact f.nonneg _,
      apply pow_nonneg, rw inv_nonneg, norm_num, },
    { rw [mul_assoc, ←mul_add, ←mul_assoc (2 : ℝ), ←mul_assoc (2 : ℝ), mul_comm _ C, mul_assoc C,
        show ∀ x, C * x + C = C * (x + 1), by {intros x, rw [mul_add, mul_one]},
        mul_assoc (4 : ℝ)⁻¹],
      apply mul_le_mul, rw inv_le_inv, norm_cast, rw [show 4 = 2^2, by norm_num],
      apply nat.pow_le_pow_of_le_left, exact f.hm, norm_cast,
      apply pow_pos, linarith [f.hm], norm_num,

      apply mul_le_mul, refl, rw [←geom_sum_def, ←geom_sum_def, geom_sum_eq, geom_sum_eq,
        show (2 : ℝ) * 4⁻¹ = 2⁻¹, by norm_num, show (2 : ℝ)⁻¹ - 1 = -2⁻¹, by norm_num, div_neg,
        mul_neg_eq_neg_mul_symm, div_neg, ←mul_div_assoc, mul_comm, mul_div_assoc, div_self,
        mul_one, neg_sub, sub_add_eq_add_sub, one_add_one_eq_two],
      conv_rhs { rw [div_eq_mul_inv, inv_inv₀, mul_comm, mul_sub, neg_sub, mul_one] },
      apply sub_le_sub, refl, conv_lhs { rw [pow_succ, ←mul_assoc] },
      rw [mul_inv_cancel, one_mul], norm_num, apply inv_ne_zero, norm_num,
      intro rid, rw inv_eq_one₀ at rid, linarith,
      intro rid, rw inv_eq_one₀ at rid, linarith,
      apply add_nonneg, apply mul_nonneg, norm_num,
      apply finset.sum_nonneg, intros i hi, apply pow_nonneg, rw inv_nonneg,
      norm_num, norm_num, apply add_nonneg, exact C1'_nonneg f,
      linarith [f.C2_pos], apply mul_nonneg, apply add_nonneg, exact C1'_nonneg f,
      linarith [f.C2_pos], apply add_nonneg, apply mul_nonneg, norm_num,
      apply finset.sum_nonneg, intros i hi, apply pow_nonneg, rw inv_nonneg,
      norm_num, norm_num, rw inv_nonneg, norm_num }, },
end

lemma property_next_height_iter (P : A) (n : ℕ) :
  f.to_fun ((next f.m)^[n.succ] P) ≤
  (2⁻¹)^n.succ * f.to_fun P + (2⁻¹ * C) :=
have ineq1 : _ := property_next_height_iter_aux f P n,
have eq1 : (∑' (i : ℕ), ite (i ∈ range n.succ) ((2:ℝ)⁻¹ ^ i) 0) =
  ∑ (i : ℕ) in range n.succ, 2⁻¹ ^ i,
begin
  rw tsum_eq_sum, apply finset.sum_congr, refl, intros i hi, split_ifs, refl,
  intros i hi, split_ifs, exfalso, exact hi h, refl,
end,
have summable1 : summable (λ (i : ℕ), (2 : ℝ)⁻¹^i), begin
  apply summable_geometric_of_lt_1, norm_num, norm_num,
end,
have ineq2 : ∑ (i : ℕ) in range n.succ, (2 : ℝ)⁻¹ ^ i ≤ 2,
begin
  transitivity ∑' (i : ℕ), (2:ℝ)⁻¹ ^ i,
  transitivity (∑' (i : ℕ), ite (i ∈ range n.succ) ((2:ℝ)⁻¹ ^ i) 0),
  rw eq1, apply tsum_le_tsum_of_inj (id : ℕ → ℕ) function.injective_id,
  intros i hi, apply pow_nonneg, rw inv_nonneg, norm_num,
  intro i, split_ifs, rw [id.def], apply pow_nonneg, rw inv_nonneg, norm_num,
  apply summable1.summable_of_eq_zero_or_self, intro i, split_ifs, right, refl,
  left, refl, exact summable1, exact order_topology.to_order_closed_topology,
  rw [tsum_geometric_of_lt_1, show (1 : ℝ) - 2⁻¹ = 2⁻¹, by ring, inv_inv₀],
  rw inv_nonneg, norm_num, norm_num,
end,
have ineq3 : _ := mul_le_mul (show 4⁻¹ * C ≤ 4⁻¹ * C, by refl) ineq2 begin
  apply finset.sum_nonneg, intros i hi, apply pow_nonneg, norm_num
end begin
  apply mul_nonneg, norm_num, apply add_nonneg, exact C1'_nonneg f, linarith [f.C2_pos],
end,
begin
  apply le_trans ineq1,
  apply add_le_add, refl,
  apply le_trans ineq3, rw [mul_assoc, mul_comm _ (2 : ℝ), ←mul_assoc],
  apply mul_le_mul, norm_num, refl, apply add_nonneg,
  exact C1'_nonneg f, linarith [f.C2_pos], norm_num,
end

lemma property_next_height_eventually (P : A) :
  ∃ (M : ℕ), ∀ (n : ℕ), M ≤ n → f.to_fun ((next f.m)^[n.succ] P) ≤ 1 + (2⁻¹ * C) :=
begin
  obtain ⟨M, hM⟩ := eventually_le_one (f.to_fun P) (f.nonneg P),
  use M, intros n hn, specialize hM n.succ _,transitivity n, exact hn, exact nat.le_succ n,
  apply le_trans (property_next_height_iter f P n), apply add_le_add,
  exact hM, refl,
end

omit non_empty_quot_f
lemma eq_linear_combination (P : A) (n : ℕ) :
  P = (f.m) ^ n.succ • ((next f.m)^[n.succ] P) +
    ∑ i in range n.succ, (f.m) ^ i •  (next_rep f.m ((next f.m)^[i] P)) :=
begin
  induction n with n ih,
  { rw [pow_one, function.iterate_one, range_one, sum_singleton, pow_zero, one_smul,
    function.iterate_zero, id.def, property_next, sub_add_cancel], },

  { conv_rhs { rw [function.iterate_succ',
      show (next f.m ∘ (next f.m^[n.succ])) P = next f.m (next f.m^[n.succ] P), from rfl,
      next_prop f.m (next f.m^[n.succ] P), finset.sum_range_succ, pow_succ, mul_nsmul',
      show ∀ (a b c : A), a + (b + c) = (a + c) + b, begin
        intros a b c, rw [add_comm b c, add_assoc],
      end, ←next_prop f.m (next f.m^[n.succ] P), ←nsmul_add,
      ←next_prop f.m (next f.m^[n.succ] P)], },
    conv_lhs { rw ih }, },
end

/--the set of generators of $A$-/
abbreviation generators : set A := { a | f.to_fun a < 2 + (2⁻¹ * C) } ∪ (represents A f.m)

lemma subset_generators_left : { a | f.to_fun a < 2 + (2⁻¹ * C) } ⊆ generators f :=
set.subset_union_left _ _

lemma subset_generators_right : ↑(represents A f.m) ⊆ generators f :=
set.subset_union_right _ _

lemma finite_generators : (generators f).finite :=
begin
  apply set.finite.union,
  exact f.finite (2 + (2⁻¹ * C)),
  exact (represents A f.m).finite_to_set,
end

theorem descent :
  add_subgroup.fg (⊤ : add_subgroup A) :=
begin
  rw add_subgroup.fg_iff,
  use (generators f),
  refine ⟨_, finite_generators f⟩,
  rw add_subgroup.eq_top_iff',
  intro P, rw add_subgroup.mem_closure, intros K hK,
  obtain ⟨M, hM⟩ := property_next_height_eventually f P,
  specialize hM M (le_refl _),
  have eq1 := eq_linear_combination f P M,
  rw eq1,
  apply add_subgroup.add_mem,
  apply add_subgroup.nsmul_mem,
  suffices : f.to_fun (next f.m^[M.succ] P) < 2 + 2⁻¹ * C,
  have mem1 := subset_generators_left f this,
  apply hK, exact mem1, linarith,
  apply add_subgroup.sum_mem, intros i hi,
  apply add_subgroup.nsmul_mem, apply hK,
  apply subset_generators_right, apply property_next_rep,
end
