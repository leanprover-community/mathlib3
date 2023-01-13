import data.zmod.basic
import ring_theory.witt_vector.compare

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

variables {p : ℕ} [fact p.prime] {d : ℕ}
open zmod

lemma proj_fst' {m n : ℕ} (h : m.coprime n) (a : zmod m) (b : zmod n) :
  zmod.cast_hom (show m ∣ m * n, from dvd.intro n rfl) (zmod m)
    ((zmod.chinese_remainder h).symm (a,b)) = a :=
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

open padic_int

lemma proj_fst {n : ℕ} (x : zmod d × ℤ_[p]) (cop : d.coprime (p^n)) :
  ↑((zmod.chinese_remainder cop).symm (x.fst, (to_zmod_pow n) x.snd)) = x.fst := proj_fst' _ _ _

lemma proj_snd' {m n : ℕ} (h : m.coprime n) (a : zmod m) (b : zmod n) :
  zmod.cast_hom (show n ∣ m * n, from dvd.intro_left m rfl) (zmod n)
    ((zmod.chinese_remainder h).symm (a,b)) = b :=
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

lemma proj_snd {n : ℕ} (x : zmod d × ℤ_[p]) (cop : d.coprime (p^n)) :
  ↑((zmod.chinese_remainder cop).symm (x.fst, (to_zmod_pow n) x.snd)) =
  (to_zmod_pow n) x.snd :=
proj_snd' _ _ _

lemma inv_fst' {m n : ℕ} (x : zmod (m * n)) (cop : m.coprime n) :
  (((zmod.chinese_remainder cop).to_equiv) x).fst = (x : zmod m) :=
begin
  rw zmod.chinese_remainder,
  simp only [ring_equiv.to_equiv_eq_coe, ring_equiv.coe_to_equiv, ring_equiv.coe_mk,
    zmod.cast_hom_apply, prod.fst_zmod_cast],
end

lemma inv_fst [fact (0 < d)] {n : ℕ} (x : zmod (d * p^n)) (cop : d.coprime (p^n)) :
  (((zmod.chinese_remainder cop).to_equiv) x).fst = (x : zmod d) := inv_fst' x _

lemma inv_snd' {m n : ℕ} (x : zmod (m * n)) (cop : m.coprime n) :
  (((zmod.chinese_remainder cop).to_equiv) x).snd = (x : zmod n) :=
begin
  rw zmod.chinese_remainder,
  simp only [ring_equiv.to_equiv_eq_coe, ring_equiv.coe_to_equiv, ring_equiv.coe_mk,
    zmod.cast_hom_apply, prod.snd_zmod_cast],
end

lemma inv_snd {n : ℕ} (x : zmod (d * p^n)) (cop : d.coprime (p^n)) :
  (((zmod.chinese_remainder cop).to_equiv) x).snd = (x : zmod (p^n)) := inv_snd' _ _

lemma val_coe_val_le_val {n m : ℕ} [fact (0 < m)] (y : zmod n) : (y.val : zmod m).val ≤ y.val :=
begin
  by_cases y.val < m,
  { rw zmod.val_cast_of_lt h, },
  { push_neg at h,
    apply le_of_lt (gt_of_ge_of_gt h (zmod.val_lt (y.val : zmod m))), },
end

lemma val_coe_val_le_val' {n m : ℕ} [fact (0 < m)] [fact (0 < n)] (y : zmod n) :
  (y : zmod m).val ≤ y.val := (@zmod.nat_cast_val _ (zmod m) _ _ y) ▸ val_coe_val_le_val y

lemma coe_val_eq_val_of_lt {n m : ℕ} [fact (0 < n)] (h : n < m) (b : zmod n) :
  (b.val : zmod m).val = b.val :=
begin
  have h2 : b.val = (b : zmod m).val,
  { have h2 : b.val < m, { transitivity n, apply zmod.val_lt b, assumption, },
    rw ←zmod.val_cast_of_lt h2,
    refine congr_arg _ (zmod.nat_cast_val _), },
  conv_rhs { rw h2, },
  refine congr_arg _ _,
  rw zmod.nat_cast_val _,
  assumption,
end

namespace int
lemma eq_iff_succ_eq {a b : ℤ} : a = b ↔ a.succ = b.succ :=
⟨congr_arg (λ (a : ℤ), a.succ), λ h, (add_left_inj 1).1 h⟩

lemma nat_cast_coe_eq_coe_base : (nat.cast_coe : has_coe_t ℕ ℤ) = coe_base :=
begin
  rw [nat.cast_coe, coe_base],
  congr,
  ext,
  rw coe_b,
  induction x,
  { norm_num,
    change int.of_nat 0 = _, change int.of_nat 0 = (0 : ℤ),
    simp only [int.of_nat_eq_coe, int.coe_nat_zero], },
  { rw int.eq_iff_succ_eq at x_ih,
    convert x_ih, },
end

end int

namespace nat
lemma dvd_sub_comm (a b n : ℕ) (h : (n : ℤ) ∣ (a : ℤ) - (b : ℤ)) : (n : ℤ) ∣ (b : ℤ) - (a : ℤ) :=
(dvd_neg ↑n (↑b - ↑a)).mp (by {simp only [h, neg_sub]})

end nat

namespace zmod
lemma nat_cast_val_to_int {n : ℕ} [fact (0 < n)] (a : zmod n) : (a.val : ℤ) = (a : ℤ) :=
begin
  rw ←nat_cast_val a,
  congr,
  rw int.nat_cast_coe_eq_coe_base,
end

lemma coe_int_add {n : ℕ} [fact (0 < n)] (a b : zmod n) :
  (((a + b) : zmod n) : ℤ) = (a + (b : ℤ)) % n :=
begin
  rw [←nat_cast_val_to_int, val_add],
  simp only [int.coe_nat_add, int.coe_nat_mod],
  apply _root_.congr_fun,
  refine congr_arg _ _,
  rw [←nat_cast_val_to_int, ←nat_cast_val_to_int],
end

open nat

instance [fact (0 < d)] {n : ℕ} : fact (0 < d * p^n) :=
fact_iff.2 (mul_pos (fact.out _) (pow_pos (nat.prime.pos (fact.out _)) _))

lemma zero_le_div_and_div_lt_one {n : ℕ} [fact (0 < n)] (x : zmod n) :
  0 ≤ (x.val : ℚ) / n ∧ (x.val : ℚ) / n < 1 :=
⟨div_nonneg (cast_le.2 (nat.zero_le _)) (cast_le.2 (nat.zero_le _)), (div_lt_one
  begin refine cast_pos.2 (fact_iff.1 infer_instance), end).2 -- this does not work?
    (cast_lt.2 (zmod.val_lt _))⟩

lemma coe_add_eq_pos' {n : ℕ} [fact (0 < n)] {a b : zmod n} (h : (a + b : ℤ) < n) :
  (((a + b) : zmod n) : ℤ) = (a : ℤ) + (b : ℤ) :=
begin
  rw [zmod.coe_add_eq_ite, if_neg],
  push_neg, assumption,
end

lemma val_add_fin_mul_lt [fact (0 < d)] {m : ℕ} (a : zmod (d * p^m)) (x : fin p) :
  a.val + ↑x * (d * p ^ m) < d * p ^ m.succ :=
begin
  have h : ↑x * (d * p ^ m) ≤ (d * p ^ m) * (p - 1),
  { rw mul_comm,
    apply nat.mul_le_mul_left,
    rw [←nat.lt_succ_iff, nat.succ_eq_add_one, nat.sub_add_cancel
      (le_of_lt (fact_iff.1 (nat.prime.one_lt' p)))],
    apply x.2, },
  convert add_lt_add_of_lt_of_le (zmod.val_lt a) h,
  ring_nf,
  rw [nat.sub_add_cancel (le_of_lt (fact_iff.1 (nat.prime.one_lt' p))), ←pow_succ],
end

lemma nat_cast_zmod_cast_int {n a : ℕ} (h : a < n) : ((a : zmod n) : ℤ) = (a : ℤ) :=
begin
  by_cases h' : 0 < n,
  { rw ←zmod.nat_cast_val _,
    { apply congr (funext int.nat_cast_eq_coe_nat) (zmod.val_cast_of_lt h), },
    { apply fact_iff.2, assumption, }, },
  simp only [not_lt, _root_.le_zero_iff] at h',
  rw h',
  simp only [zmod.cast_id', id.def, int.nat_cast_eq_coe_nat],
end

lemma cast_val_eq_of_le {m n : ℕ} (y : fin m) (h : m ≤ n) : (y : zmod n).val = y :=
zmod.val_cast_of_lt (lt_of_lt_of_le (fin.is_lt y) h)

lemma fin_prime_coe_coe (m : ℕ) (y : fin p) :
  (y : zmod (d * p^m.succ)) = ((y : ℕ) : zmod (d * p^m.succ)) := coe_coe y

lemma fin_prime_mul_prime_pow_lt_mul_prime_pow_succ [fact (0 < d)] (y : fin p) (m : ℕ) :
  (y : ℕ) * (d * p ^ m) < d * p ^ m.succ :=
begin
  rw [pow_succ', ←mul_assoc d _ _, mul_comm (y : ℕ) _],
  apply mul_lt_mul' le_rfl y.prop (nat.zero_le _) (fact_iff.1 infer_instance),
  apply_instance,
end

lemma cast_int_one {n : ℕ} [fact (1 < n)] : ((1 : zmod n) : ℤ) = 1 :=
begin
  rw [←zmod.nat_cast_val _, zmod.val_one _],
  simp only [int.coe_nat_zero, int.coe_nat_succ, zero_add, int.nat_cast_eq_coe_nat],
  { assumption, },
  { apply fact_iff.2 (lt_trans zero_lt_one (fact.out _)),
    all_goals { apply_instance, }, },
end

lemma cast_eq_of_dvd {m n : ℕ} (h : m ∣ n) (a : zmod m) : ((a : zmod n) : zmod m) = a :=
begin
  conv_rhs { rw ←zmod.ring_hom_map_cast (zmod.cast_hom h (zmod m)) a, },
  rw zmod.cast_hom_apply,
end

lemma fract_eq_val {n : ℕ} [h : fact (0 < n)] (a : zmod n) :
  int.fract ((a : ℚ) / n) = (a.val : ℚ) / n :=
int.fract_eq_iff.2 ⟨div_nonneg (zmod.val a).cast_nonneg n.cast_nonneg,
  ⟨(div_lt_one ((@cast_pos ℚ _ _ _).2 (fact_iff.1 infer_instance))).2
  (cast_lt.2 (zmod.val_lt _)), ⟨0, by { rw [←zmod.nat_cast_val, sub_self, int.cast_zero], }⟩⟩⟩

/-- Same as `zmod.cast_hom_apply` with some hypotheses being made explicit. -/
lemma cast_hom_apply' {n : ℕ} (R : Type*) [_inst_1 : ring R] {m : ℕ} [_inst_2 : char_p R m]
  (h : m ∣ n) (i : zmod n) : (cast_hom h R) i = ↑i := cast_hom_apply i

lemma coe_map_of_dvd {a b : ℕ} (h : a ∣ b) (x : units (zmod b)) :
  is_unit (x : zmod a) :=
begin
  change is_unit ((x : zmod b) : zmod a),
  rw [←zmod.cast_hom_apply' (zmod a) h (x : zmod b), ←ring_hom.coe_monoid_hom, ←units.coe_map],
  apply units.is_unit,
end

lemma is_unit_of_is_coprime_dvd {a b : ℕ} (h : a ∣ b) {x : ℕ} (hx : x.coprime b) :
  is_unit (x : zmod a) :=
begin
  convert_to is_unit ((zmod.unit_of_coprime _ hx : zmod b) : zmod a),
  { rw ←cast_nat_cast h x,
    { congr, },
    { refine zmod.char_p _, }, },
    { apply coe_map_of_dvd h _, },
end

lemma is_unit_mul {a b g : ℕ} (n : ℕ) (h1 : g.coprime a) (h2 : g.coprime b) :
  is_unit (g : zmod (a * b^n)) :=
is_unit_of_is_coprime_dvd dvd_rfl ((coprime.mul_right h1 (coprime.pow_right _ h2)))

lemma cast_inv {a m n : ℕ} (ha : a.coprime n) (h : m ∣ n) :
  (((a : zmod n)⁻¹ : zmod n) : zmod m) = ((a : zmod n) : zmod m)⁻¹ :=
begin
  change ((((zmod.unit_of_coprime a ha)⁻¹ : units (zmod n)) : zmod n) : zmod m) = _,
  have h1 : ∀ c : (zmod m)ˣ, (c : zmod m)⁻¹ = ((c⁻¹ : units (zmod m)) : zmod m),
  { intro c, simp only [inv_coe_unit], },
  rw [← zmod.cast_hom_apply' (zmod m) h _, ← ring_hom.coe_monoid_hom,
    ← units.coe_map_inv _ (zmod.unit_of_coprime a ha), ← h1],
  congr,
end

lemma fract_eq_of_zmod_eq {n a b : ℕ} [fact (0 < n)] (h : (a : zmod n) = (b : zmod n)) :
  int.fract (a / n : ℚ) = int.fract (b / n : ℚ) :=
begin
  rw [int.fract_eq_fract, div_sub_div_same],
  obtain ⟨z, hz⟩ := dvd_sub_comm _ _ _ (modeq_iff_dvd.1 ((eq_iff_modeq_nat _).1 h)),
  refine ⟨z, _⟩,
  have h : ∀ z : ℕ, (z : ℚ) = ((z : ℤ) : ℚ),
  { intro z, norm_cast, },
  rw [h a, h b, ← int.cast_sub, hz, int.cast_mul, ← h n, mul_comm, mul_div_cancel],
  norm_cast,
  apply ne_of_gt (fact.out _),
  any_goals { apply_instance, },
end

lemma dvd_val_sub_cast_val {m : ℕ} (n : ℕ) [fact (0 < m)] [fact (0 < n)] (a : zmod m) :
  n ∣ a.val - (a : zmod n).val :=
begin
  have : (a.val : zmod n) = ((a : zmod n).val : zmod n),
  { rw [nat_cast_val, nat_cast_val], norm_cast, },
  exact (dvd_iff_mod_eq_zero _ _).2 (sub_mod_eq_zero_of_mod_eq ((eq_iff_modeq_nat _).1 this)),
end

instance {p : ℕ} [fact (nat.prime p)] [fact (2 < p)] : nontrivial (units (zmod p)) :=
fintype.one_lt_card_iff_nontrivial.mp ((zmod.card_units p).symm ▸ lt_tsub_iff_right.mpr (fact.out _))

@[continuity]
lemma induced_top_cont_inv {n : ℕ} : @continuous _ _ (topological_space.induced
  (units.coe_hom (zmod n)) infer_instance) _ (units.inv : (zmod n)ˣ → zmod n) :=
by { convert continuous_of_discrete_topology,
  refine discrete_topology_induced (λ a b h, units.eq_iff.1 h), }

instance {α : Type*} [_root_.topological_space α] : _root_.topological_space αᵒᵖ :=
topological_space.induced opposite.unop infer_instance

instance {α : Type*} [_root_.topological_space α] [discrete_topology α] : discrete_topology αᵒᵖ :=
discrete_topology_induced opposite.unop_injective

instance {α : Type*} [_root_.topological_space α] [discrete_topology α] : discrete_topology αᵐᵒᵖ :=
discrete_topology_induced mul_opposite.unop_injective

instance {k : ℕ} : discrete_topology (units (zmod k)) :=
begin
  convert @discrete_topology_induced _ _ _ _ _ (units.embed_product_injective _),
  apply @prod.discrete_topology _ _ infer_instance infer_instance infer_instance infer_instance,
  swap, apply discrete_topology_induced mul_opposite.unop_injective,
  any_goals { apply_instance, },
end

instance disc_top_units {m n : ℕ} : discrete_topology (units (zmod m × zmod n)) :=
begin
  apply discrete_topology_induced (λ x y h, _),
  { apply prod.discrete_topology, },
  { rw units.embed_product at h,
    simp only [prod.mk.inj_iff, opposite.op_inj_iff, monoid_hom.coe_mk] at h,
    rw [units.ext_iff, h.1], },
end
end zmod
