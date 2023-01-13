/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.bernoulli_measure.bernoulli_measure_four
import topology.algebra.group

/-!
# Bernoulli measure and the p-adic L-function

This file defines the Bernoulli distribution on `zmod d × ℤ_[p]`. One of the main theorems is that
this p-adic distribution is indeed a p-adic measure. As a consequence, we are also able to define
the p-adic L-function in terms of a p-adic integral.

## Main definitions
 * `bernoulli_measure_of_measure`
 * `p_adic_L_function`

## Implementation notes
 * Changed `s` to `char_fn_set`
 * changed def of `ind_fn` from `dite` to `function.extend`
 * `coe_padic_to_zmod` replaced with `prod_padic_to_zmod`
 * `coprime_mul_pow` replaced with `coprime.mul_pow`
 * replace `ne_zero_of_lt` with `ne_zero_of_lt'` where needed
 * `one_lt_mul_of_ne_one` replaced with `one_lt_mul_pow_of_ne_one`
 * `exists_V_h1_1` replaced with `exists_mul_inv_val_eq`
 * `meas_E_c` removed
 * `s_nonempty` removed

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure
-/

local attribute [instance] zmod.topological_space

variables {A : Type*} [has_zero A]
variables {p : ℕ} [fact p.prime] {d : ℕ} (R : Type*) [normed_comm_ring R] (m : ℕ) {c : ℕ}
open_locale big_operators

open padic_int zmod nat locally_constant

/-- Given a function from `(zmod d)ˣ × ℤ_[p]ˣ)` to `A`, this gives the induced
  function on `(zmod d) × ℤ_[p]`, which is 0 everywhere else. -/
noncomputable abbreviation ind_fn (f : (zmod d)ˣ × ℤ_[p]ˣ → A) : zmod d × ℤ_[p] → A :=
function.extend (prod.map coe coe) f 0
--set.indicator {z : zmod d × ℤ_[p] | is_unit z.1 ∧ is_unit z.2} f
-- λ x : (zmod d × ℤ_[p]), @dite _ (is_unit x.1 ∧ is_unit x.2) (classical.dec
--   (is_unit x.fst ∧ is_unit x.snd)) (λ h, f (is_unit.unit h.1, is_unit.unit h.2)) (λ h, 0)

open function
namespace ind_fn

lemma ind_fn_def (f : (zmod d)ˣ × ℤ_[p]ˣ → A) :
  ind_fn f = function.extend (prod.map coe coe) f 0 := rfl

lemma ind_fn_eq_fun (f : (zmod d)ˣ × ℤ_[p]ˣ → A) :
  f = (ind_fn f) ∘ (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])) :=
by { ext x, rw [ind_fn_def, comp_apply, extend_apply (injective.prod_map units.ext units.ext)], }

lemma map_ind_fn_eq_fn (f : (zmod d)ˣ × ℤ_[p]ˣ → A) {z : zmod d × ℤ_[p]}
  (h' : (is_unit z.fst ∧ is_unit z.snd)) : ind_fn f z = f (is_unit.unit h'.1, is_unit.unit h'.2) :=
begin
  conv_rhs { rw ind_fn_eq_fun f },
  congr,
  simp [prod.ext_iff, is_unit.unit_spec],
end

lemma map_ind_fn_eq_fn' (f : (zmod d)ˣ × ℤ_[p]ˣ → A) {z : (zmod d)ˣ × ℤ_[p]ˣ} :
  ind_fn f (prod.map coe coe z) = f z := by { conv_rhs { rw ind_fn_eq_fun f } }

lemma map_ind_fn_eq_zero (f : (zmod d)ˣ × ℤ_[p]ˣ → A) {z : zmod d × ℤ_[p]}
  (h' : ¬(is_unit z.fst ∧ is_unit z.snd)) : ind_fn f z = 0 :=
begin
  rw [ind_fn_def, extend_apply', pi.zero_apply],
  contrapose h',
  rw not_not at *,
  cases h' with a ha,
  rw ←ha,
  simp,
end

end ind_fn

namespace zmod
lemma embedding_coe {n : ℕ} : embedding (coe : (zmod n)ˣ → zmod n) :=
{ induced := (top_eq_iff_cont_inv.2 (begin convert continuous_of_discrete_topology,
    apply discrete_topology_induced,
    change function.injective coe,
    exact units.ext, end)).symm,
  inj := units.ext, }

lemma open_embedding_coe {n : ℕ} : open_embedding (coe : (zmod n)ˣ → zmod n) :=
⟨embedding_coe, (is_open_coe' _).is_open_range⟩
end zmod

namespace ind_fn
lemma helper_is_loc_const {s : set A} (hs : ¬ (0 : A) ∈ s)
  (f : locally_constant (units (zmod d) × units ℤ_[p]) A) : is_open (ind_fn f ⁻¹' s) :=
begin
  have f1 := locally_constant.is_locally_constant f s,
  conv at f1 { congr, rw [to_fun_eq_coe, ind_fn_eq_fun f], },
  rw set.preimage_comp at f1,
  refine (open_embedding.open_iff_preimage_open (open_embedding.prod zmod.open_embedding_coe
      padic_int.open_embedding_coe) (λ z hz, _)).2 f1,
  by_cases h' : is_unit z.1 ∧ is_unit z.2,
  { refine ⟨(is_unit.unit h'.1, is_unit.unit h'.2), prod.ext_iff.2 _⟩,
    simp only [prod.map_mk],
    refine ⟨is_unit.unit_spec _, is_unit.unit_spec _⟩, },
  { exfalso,
    rw [set.mem_preimage, map_ind_fn_eq_zero f h'] at hz,
    refine hs hz, },
end

lemma preimage_zero_of_loc_const (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) A) :
  (ind_fn f)⁻¹' {0} =
  (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p]))'' (f⁻¹' {0}) ∪
  (set.range (prod.map (coe : units (zmod d) → zmod d) (coe : units ℤ_[p] → ℤ_[p])))ᶜ :=
begin
  ext y,
  rw [set.mem_union, set.mem_preimage, set.mem_singleton_iff],
  refine ⟨λ h', _, λ h', _⟩,
  { by_cases h'' : is_unit y.fst ∧ is_unit y.snd,
    { refine or.inl ⟨(is_unit.unit h''.1, is_unit.unit h''.2), _, prod.ext_iff.2
        ⟨is_unit.unit_spec h''.1, is_unit.unit_spec h''.2⟩⟩,
      rw [set.mem_preimage, set.mem_singleton_iff, ←h', map_ind_fn_eq_fn f h''], },
    { right,
      contrapose h'',
      rw [←set.mem_compl_iff, compl_compl, set.mem_range] at h'',
      cases h'' with z hz,
      rw [prod.ext_iff, prod_map] at hz,
      rw [not_not, ←hz.1, ←hz.2],
      refine ⟨units.is_unit z.fst, units.is_unit z.snd⟩, }, },
  { cases h',
    { cases h' with z hz,
      rw [←hz.2, map_ind_fn_eq_fn' f],
      refine hz.1, },
    { apply map_ind_fn_eq_zero,
      refine (λ h, set.not_mem_compl_iff.2 h' _),
      simp only [compl_compl, set.range_prod_map, set.mem_prod, set.mem_range],
      refine ⟨⟨is_unit.unit h.1, is_unit.unit_spec _⟩,
        ⟨is_unit.unit h.2, is_unit.unit_spec _⟩⟩, }, },
end

lemma is_loc_const_ind_fn (f : locally_constant (units (zmod d) × units ℤ_[p]) A) :
  is_locally_constant (ind_fn f) := λ s, begin
  by_cases (0 : A) ∈ s,
  { rw [←set.diff_union_of_subset (set.singleton_subset_iff.2 h), set.preimage_union],
    apply is_open.union,
    { apply helper_is_loc_const _ f,
      simp only [set.mem_diff, set.mem_singleton, not_true, and_false, not_false_iff], },
    { rw preimage_zero_of_loc_const f,
      apply is_open.union ((is_open_map.prod (is_open_coe' _) is_open_coe) _
        (locally_constant.is_locally_constant f _)),
      { rw [is_open_compl_iff, set.range_prod_map],
        refine is_closed.prod (is_closed_discrete (set.range coe)) is_closed_coe, }, }, },
  { apply helper_is_loc_const h f, }, end

lemma add (f1 f2 : (zmod d)ˣ × ℤ_[p]ˣ → R) : ind_fn (f1 + f2) = ind_fn f1 + ind_fn f2 :=
by { rw [ind_fn_def, (add_zero (0 : zmod d × ℤ_[p] → R)).symm, extend_add], }

@[to_additive]
lemma mul (f g : (zmod d)ˣ × ℤ_[p]ˣ → R) : ind_fn (f * g) = ind_fn f * ind_fn g :=
by { rw [ind_fn_def, (mul_zero (0 : zmod d × ℤ_[p] → R)).symm, extend_mul], }

lemma smul (m : R) (f : (zmod d)ˣ × ℤ_[p]ˣ → R) :
  ind_fn (m • f) = m • (ind_fn f) := by { rw [ind_fn_def, (smul_zero m).symm, extend_smul], }
end ind_fn

open ind_fn
/-- The locally constant version of `ind_fn` -/
noncomputable def loc_const_ind_fn (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) A) :
  locally_constant (zmod d × ℤ_[p]) A :=
{ to_fun := ind_fn f,
  is_locally_constant := is_loc_const_ind_fn f }

namespace loc_const_ind_fn
@[simp]
lemma loc_const_ind_fn_def (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R)
  (x : ((zmod d) × ℤ_[p])) : loc_const_ind_fn f x = ind_fn f x := rfl

lemma add (f1 f2 : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  loc_const_ind_fn (f1 + f2) = loc_const_ind_fn f1 + loc_const_ind_fn f2 :=
by { ext, simp [add R f1 f2], }

@[to_additive]
lemma mul (f g : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  loc_const_ind_fn (f * g) = loc_const_ind_fn f * loc_const_ind_fn g :=
by { ext, simp [mul R f g], }

lemma smul (m : R) (f : locally_constant ((zmod d)ˣ × ℤ_[p]ˣ) R) :
  loc_const_ind_fn (m • f) = m • (loc_const_ind_fn f) := by { ext, simp [smul R m f], }
end loc_const_ind_fn

instance {α : Type*} [topological_space α] [discrete_topology α] : discrete_topology αᵐᵒᵖ :=
discrete_topology_induced mul_opposite.unop_injective

instance {k : ℕ} : discrete_topology (zmod k)ˣ :=
discrete_topology_induced (units.embed_product_injective _)

namespace locally_constant
@[to_additive] lemma prod_apply {B C : Type*} [topological_space B] [comm_monoid C]
  (n : ℕ) (f : ℕ → (locally_constant B C)) {x : B} :
  (∏ i in finset.range n, (f i)) x = ∏ i in finset.range n, ((f i) x) :=
begin
  induction n with d hd,
  { simp only [locally_constant.coe_one, finset.range_zero, finset.prod_empty, pi.one_apply], },
  { rw [finset.prod_range_succ, locally_constant.mul_apply, hd, finset.prod_range_succ], },
end

lemma smul_eq_mul' {α β : Type*} [topological_space α] [ring β] (f : locally_constant α β)
  (b : β) : b • f = (locally_constant.const α b) * f := by { ext, simp }
end locally_constant

open discrete_quotient_of_to_zmod_pow clopen_from

lemma loc_const_eq_sum_char_fn [nontrivial R] [fact(0 < d)]
  (f : locally_constant ((zmod d) × ℤ_[p]) R) (hd : d.coprime p) : ∃ n : ℕ,
  f = ∑ a in (finset.range (d * p^n)), f(a) •
  char_fn R (clopen_from.is_clopen (a : zmod (d * p^n))) :=
begin
  set n := (le hd f).some with hn,
  refine ⟨n, locally_constant.ext (λ x, _)⟩,
  set x' := prod_padic_to_zmod n x hd with hx',
  rw [locally_constant.sum_apply,
    finset.sum_eq_single_of_mem x'.val (finset.mem_range.2 (zmod.val_lt _)) (λ b hb h, _)],
  { simp only [nat_cast_val, cast_id', id.def, coe_smul, pi.smul_apply, algebra.id.smul_eq_mul],
    rw [(char_fn_one R _ _).1 (mem_clopen_from_prod_padic_to_zmod _ _ hd), mul_one],
    refine ((le hd f).some_spec _ _ (self_rel_prod_padic_to_zmod _ _ hd)).symm, },
  { rw [locally_constant.smul_apply, (char_fn_zero R _ _).1 (λ h', h _), smul_zero],
    suffices : (b : zmod (d * p^n)) = x',
    { rw ←val_cast_of_lt (finset.mem_range.1 hb),
      refine _root_.congr_arg _ this, },
    { rw [mem_clopen_from, eq_comm] at h',
      rw [←equiv.apply_eq_iff_eq (zmod.chinese_remainder (coprime.pow_right n hd)).to_equiv,
        prod.ext_iff, inv_fst', inv_snd', inv_fst', inv_snd', hx', proj_fst, proj_snd],
      assumption, }, },
end

namespace nat
lemma ne_zero_of_lt' (b : ℕ) {a : ℕ} [fact (b < a)] : a ≠ 0 := @ne_zero_of_lt _ _ b _ (fact.out _)

lemma one_lt_mul_pow_of_ne_one [fact (0 < d)] {k : ℕ} (h : d * p^k ≠ 1) : 1 < d * p^k :=
nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨nat.mul_ne_zero (ne_zero_of_lt' 0)
  (pow_ne_zero _ (nat.prime.ne_zero (fact.out _))), h⟩

lemma mul_pow_eq_one_of_mul_pow_sq_not_one_lt [fact (0 < d)] {n : ℕ} (h : ¬ 1 < d * p^(2 * n)) :
  d * p^n = 1 :=
begin
  rw [not_lt_iff_eq_or_lt, lt_one_iff, nat.mul_eq_zero] at h,
  cases h,
  { have h' := h.symm,
    rw [nat.mul_eq_one_iff, pow_mul', pow_succ, pow_one, nat.mul_eq_one_iff] at h',
    rw [h'.1, h'.2.1, one_mul], },
  { have p2 : p^(2 * n) ≠ 0 := pow_ne_zero _ (nat.prime.ne_zero (fact.out _)),
    simp only [ne_zero_of_lt' 0, p2, or_self] at h,
    exfalso,
    exact h, },
end
end nat

lemma exists_mul_inv_val_eq [fact (0 < d)] (hc' : c.coprime d) (hc : c.coprime p) (k : ℕ) :
  ∃ z : ℕ, c * ((c : zmod (d * p^(2 * k)))⁻¹.val) = dite (1 < d * p^(2 * k))
  (λ h, 1 + z * (d * p^(2 * k))) (λ h, 0) :=
begin
  by_cases eq_one : (d * p^(2 * k)) = 1,
  { have k_zero : ¬ 1 < d * p^(2 * k) := by { rw [eq_one, nat.lt_one_iff], apply nat.one_ne_zero, },
    refine ⟨1, _⟩,
    rw [dif_neg k_zero, eq_one],
    simp only [nat.mul_eq_zero, zmod.val_eq_zero, eq_iff_true_of_subsingleton, or_true], },
  have h : (1 : zmod (d * p^(2 * k))).val = 1,
  { have : ((1 : ℕ) : zmod (d * p^(2 * k))) = 1 := nat.cast_one,
    rw [←this, zmod.val_cast_of_lt (nat.one_lt_mul_pow_of_ne_one eq_one)], },
  simp_rw dif_pos (nat.one_lt_mul_pow_of_ne_one eq_one),
  conv { congr, funext, find 1 {rw ← h}, rw mul_comm z _, },
  apply (nat_coe_zmod_eq_iff (d * p^(2 * k)) _ _).1 _,
  { rw [nat.cast_mul, nat_cast_val, cast_inv (coprime.mul_pow _ hc' hc) dvd_rfl,
      @cast_nat_cast _ (zmod (d * p ^ (2 * k))) _ _ (zmod.char_p _) dvd_rfl c],
    apply coe_mul_inv_eq_one _ (coprime.mul_pow _ hc' hc), },
end
.
open nat
lemma helper_meas_E_c [fact (0 < d)] {n : ℕ} (a : zmod (d * p^n)) (hc' : c.coprime d)
  (hc : c.coprime p) : ∃ z : ℤ, int.fract ((a.val : ℚ) / (↑d * ↑p ^ n)) -
  ↑c * int.fract (↑((c : zmod (d * p^(2 * n)))⁻¹.val) * (a : ℚ) / (↑d * ↑p ^ n)) = z :=
begin
  obtain ⟨z, hz⟩ := int.fract_mul_nat ((↑((c : zmod (d * p^(2 * n)))⁻¹.val) *
    (a : ℚ) / (↑d * ↑p ^ n))) c,
  obtain ⟨z', hz'⟩ := exists_mul_inv_val_eq hc' hc n,
  rw [mul_comm, mul_comm _ (c : ℚ), ←mul_div, ←mul_assoc, ←nat.cast_mul] at hz,
  by_cases pos : 1 < d * p^(2 * n),
  { refine ⟨-z, _⟩,
    rw dif_pos pos at hz',
    rw [hz', nat.cast_add, nat.cast_one, one_add_mul] at hz,
    conv at hz { congr, congr, skip, congr, congr, skip, congr, rw [pow_mul', pow_succ, pow_one], },
    rw [←mul_assoc d (p^n), mul_comm (d * p^n) (p^n), ←mul_assoc z' _ _, nat.cast_mul,
      mul_comm _ (↑(d * p ^ n)), mul_assoc, mul_div (↑(z' * p ^ n)) _ _, ←nat.cast_pow,
      ←nat.cast_mul, mul_div_cancel', ←nat_cast_val, ←nat.cast_mul,
      ←int.cast_coe_nat (z' * p ^ n * a.val), int.fract_add_int] at hz,
    { rw [int.cast_neg, ←hz, neg_sub, nat_cast_val a, nat.cast_mul d _, nat.cast_pow, mul_div], },
    { norm_cast, apply ne_zero_of_lt' 0, apply_instance, }, },
  { simp_rw [←nat.cast_pow, ←nat_cast_val a, ←nat.cast_mul,
      mul_pow_eq_one_of_mul_pow_sq_not_one_lt pos, nat.cast_one, div_one, ←int.cast_coe_nat],
    refine ⟨0, by { simp_rw [int.cast_zero, int.fract_coe, mul_zero, sub_zero] }⟩, },
end

noncomputable instance [fact (0 < d)] : normed_ring (locally_constant (zmod d × ℤ_[p]) R) :=
{ dist_eq := λ x y, dist_eq_norm x y,
  norm_mul := λ a b, begin
    convert_to ∥inclusion _ _ a * inclusion _ _ b∥ ≤ ∥inclusion _ _ a∥ * ∥inclusion _ _ b∥,
    refine norm_mul_le _ _, end }
