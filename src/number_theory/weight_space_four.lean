/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.weight_space_three

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

local attribute [instance] zmod.topological_space

variables (X : Type*) [mul_one_class X] [topological_space X]
variables (A : Type*) [topological_space A] [mul_one_class A] (p : ℕ) [fact p.prime] (d : ℕ)
variables (R : Type*) [normed_comm_ring R] [complete_space R] [char_zero R] (inj : ℤ_[p] → R) (m : ℕ)
  (χ : mul_hom (units (zmod (d*(p^m)))) R) (w : weight_space (units (zmod d) × units (ℤ_[p])) R)
variables {c : ℕ} [fact (0 < d)]
variables [algebra ℚ R] [norm_one_class R]

set_option old_structure_cmd true

open_locale big_operators

open padic_int zmod nat

lemma E_c_sum_equi_class' (x : zmod (d * p^m)) (hc : c.gcd p = 1) (hc' : c.gcd d = 1) :
  ∑ (y : equi_class p d m m.succ (nat.le_succ m) x), (E_c p d hc m.succ y) = (E_c p d hc m x) :=
begin
  rw E_c,
  rw [finset.sum_add_distrib, finset.sum_sub_distrib, sum_fract, ←finset.mul_sum],
  have h1 : d * p ^ m ∣ d * p ^ m.succ,
  { apply mul_dvd_mul_left, rw pow_succ', apply dvd_mul_right, },
  have h2 : ∀ z : ℕ, d * p ^ z ∣ d * p ^ (2 * z),
  { intro z, apply mul_dvd_mul_left, apply pow_dvd_pow, linarith, },
  have h3 : d * p ^ m ∣ d * p ^ (2 * m.succ),
  { apply mul_dvd_mul_left, apply pow_dvd_pow, rw nat.succ_eq_add_one, rw mul_add, linarith, },
  have h4 : ∀ n : ℕ, c.coprime (d * p^n),
  { intro n, apply coprime_mul_iff_right.2 ⟨hc', coprime_pow_spl p c n hc⟩, },
  have h5 : (((c : zmod (d * p^(2 * m.succ)))⁻¹  : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)).val ≤
    (c : zmod (d * p^(2 * m.succ)))⁻¹.val,
  { apply val_le_val', apply mul_le_mul_left', apply pow_le_pow _ _,
    { apply le_of_lt, apply nat.prime.one_lt, apply fact.out, },
    linarith, },
  convert_to ((x.val : ℚ) / (d * p ^ m) + (p - 1) / 2) - (c : ℚ) *
    ∑ (x_1 : (equi_class p d m m.succ (nat.le_succ m)
      ( ((c : zmod (d * p^(2*m.succ)))⁻¹.val) * x))),
    int.fract (((x_1 : zmod (d * p^m.succ)).val : ℚ) / ((d : ℚ) * (p : ℚ)^m.succ)) +
    (∑ (x : (equi_class p d m m.succ _ x)), ((c : ℚ) - 1) / 2) = _ - _ + _,
  { rw [add_right_cancel_iff, sub_right_inj], refine congr_arg _ _,
    apply finset.sum_bij,
    swap 5,
    { rintros, constructor, swap,
      { exact (((c : zmod (d * p^(2*m.succ)))⁻¹).val : zmod (d * p^m.succ)) * a, },
      { rw mem_equi_class,
        have := (mem_equi_class p d m m.succ _ x a).1 a.prop,
        conv_rhs { congr, skip, rw ←this, },
        rw zmod.cast_mul _,
        { rw zmod.cast_nat_cast _ _,
          swap 2, refine zmod.char_p _,
          -- apply congr_arg2,
          -- { simp only [nat_cast_val, cast_id', id.def], rw coe_inv p d m hc hc', },
          -- refl,
          { apply h1, }, }, --congr, rw coe_inv p d m hc hc', },
        swap, { exact zmod.char_p (d * p^m), },
        { apply h1, }, }, },
    { simp, }, --squeeze_simp does not work!
    { rintros, rw int.fract_eq_fract, simp only [subtype.coe_mk],
      rw [div_sub_div_same, zmod.nat_cast_val],
      conv { congr, funext, conv { to_lhs, congr, congr, congr, rw ← zmod.nat_cast_val, skip,
        rw ← zmod.nat_cast_val, }, },
      rw zmod.val_mul, rw ← nat.cast_mul, rw ← nat.cast_sub,
      obtain ⟨z₁, hz₁⟩ := @dvd_sub_mod (d * p^m.succ)
        ((((c : zmod (d * p^(2 * m.succ)))⁻¹ : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)).val * (a : zmod (d * p^m.succ)).val),
      rw zmod.nat_cast_val,
      rw nat.cast_sub,
      rw ← sub_add_sub_cancel _ ((((c : zmod (d * p^(2 * m.succ)))⁻¹ :
        zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)).val * (a : zmod (d * p^m.succ)).val : ℚ) _,
      rw ← nat.cast_mul,
      have f1 : ((((c : zmod (d * p^(2 * m.succ)))⁻¹ : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)).val * (a : zmod (d * p^m.succ)).val) % (d * p^m.succ) ≤ ((((c : zmod (d * p^(2 * m.succ)))⁻¹ : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)).val * (a : zmod (d * p^m.succ)).val),
      { apply mod_le, },
      rw ← nat.cast_sub f1,
      rw hz₁,
      rw ← nat.cast_sub, rw ← nat.mul_sub_right_distrib,
      obtain ⟨z₂, hz₂⟩ := dvd_val_sub_cast_val (d * p^(2 * m.succ)) (d * p^m.succ) (c : zmod (d * p^(2 * m.succ)))⁻¹,
      rw hz₂,
      rw mul_assoc (d * p^(m.succ)) _ _,
      rw nat.cast_mul, rw nat.cast_mul _ z₁, rw ← mul_add,
      rw ← nat.cast_pow, rw ← nat.cast_mul d _, rw mul_comm, rw mul_div_cancel _ _,
      norm_cast,
      refine ⟨((z₂ * (a : zmod (d * p ^ m.succ)).val + z₁ : ℕ) : ℤ), rfl⟩,
      { norm_cast, apply ne_of_gt, apply fact_iff.1, apply imp p d _, },
      { apply mul_le_mul_right' _ _, apply_instance, apply h5, },
      { apply le_trans (mod_le _ _) _, apply mul_le_mul_right' _ _, apply_instance, apply h5, },
      { apply le_trans (mod_le _ _) _, rw nat_cast_val, apply mul_le_mul_right' _ _,
        apply_instance, apply h5, }, },
      --use 0, simp, },
    { simp, rintros a1 ha1 a2 ha2 h, rw is_unit.mul_right_inj at h, assumption,
      { rw is_unit_iff_exists_inv',
        refine ⟨((c : zmod (d * p^(2 * (m.succ)))) : zmod (d * p^(m.succ))), _⟩,
        rw zmod.cast_inv _ _ _ (h4 _) _, apply zmod.mul_inv_of_unit _ (is_unit_mul p d m hc hc'),
        { apply h2, }, }, },
    { simp, rintros a ha, rw mem_equi_class at *,
      use ((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) * a,
      split,
      { rw [mem_equi_class, zmod.cast_mul _],
        { rw ha,
          --have rep : (((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m.succ)) : zmod (d * p^m)) =
            --((c : zmod (d * p^(2 * m.succ))) : zmod (d * p^m)), sorry,
          -- if I remove the above line, the convert below does not work?
          rw ←mul_assoc, convert one_mul x, norm_cast,
          convert zmod.mul_inv_of_unit _ (is_unit_mul' p d m hc hc') using 2, rw rep,
          rw zmod.cast_inv _ _ _ (h4 _) _,
          apply h3, },
           -- using 1,
          --{ apply is_unit_mul' p d m hc hc', }, },
        swap, { refine zmod.char_p _, },
        { apply h1, }, },
      { rw [←mul_assoc, zmod.cast_inv _ _ _ (h4 _) _, zmod.inv_mul_of_unit _ _],
        { rw one_mul a, },
        apply is_unit_mul p d m hc hc',
        { apply h2, }, }, }, },
  rw [sum_fract, fract_eq_self (zero_le_and_lt_one p d m x).1 (zero_le_and_lt_one p d m x).2,
      mul_add, finset.sum_const, card_equi_class],
  simp only [_root_.nsmul_eq_mul],
  rw [sub_add_eq_add_sub, sub_add_eq_add_sub, sub_add_eq_sub_sub, sub_right_comm], congr,
  { rw [add_assoc, add_sub_assoc], congr, linarith, },
  { rw [←nat.cast_pow, ←nat.cast_mul, ←fract_eq_val _ _],
    --apply fract_eq_of_zmod_eq,

    rw ← zmod.nat_cast_val, rw ← zmod.nat_cast_val, --rw ← zmod.nat_cast_val,
    rw ← nat.cast_mul,
    apply fract_eq_of_zmod_eq,
    rw nat.cast_mul,
    rw zmod.nat_cast_val, rw zmod.nat_cast_val, rw zmod.nat_cast_val,
    rw zmod.cast_mul',
    rw zmod.nat_cast_val, rw zmod.cast_id, --rw zmod.nat_cast_val,
    repeat { refine congr_arg _ _, },
    apply _root_.congr_fun, repeat { refine congr_arg _ _, },
    rw zmod.cast_inv _ _ _ (h4 _) _, rw zmod.cast_inv _ _ _ (h4 _) _,
    rw zmod.cast_nat_cast _, rw zmod.cast_nat_cast _,
    -- rw ← zmod.cast_hom_apply (c : zmod (d * p^(2 * m))),
    -- rw ← zmod.cast_hom_apply (c : zmod (d * p^(2 * m.succ))),
    swap 2, { refine zmod.char_p _, },
    swap 3, { refine zmod.char_p _, },
    any_goals { apply h2, },
    any_goals { apply h3, },
    -- apply _root_.congr_fun,
    -- repeat { refine congr_arg _ _, },
    -- repeat { rw zmod.cast_nat_cast _, }, repeat { any_goals { refine zmod.char_p _, }, },
    -- --{ sorry, },
    -- { apply mul_dvd_mul_left, apply pow_dvd_pow, linarith, },
    -- { apply mul_dvd_mul_left, apply pow_dvd_pow, rw ←one_mul m,
    --   apply mul_le_mul, any_goals { linarith, },
    --   { rw one_mul, apply nat.le_succ, }, },
    apply imp p d m, },
end

/-example (n : ℕ) [char_zero R] {s : finset (zmod n)} {f : (zmod n) → ℚ} :
  (((∑ a in s, (f a)) : ℚ) : R) = ∑ a in s, ((f a) : R) :=
begin

end-/

lemma E_c_sum_equi_class (x : zmod (d * p^m)) (hc : c.gcd p = 1) (hc' : c.gcd d = 1) :
∑ (y : zmod (d * p ^ m.succ)) in (λ a : zmod (d * p ^ m), set.to_finset ((equi_class p d m m.succ (nat.le_succ m)) a)) x,
  ((algebra_map ℚ R) (E_c p d hc m.succ y)) = (algebra_map ℚ R) (E_c p d hc m x) :=
begin
  rw ←E_c_sum_equi_class' p d,
  { rw ring_hom.map_sum, simp only,
-- use finset.sum_to_finset_eq_subtype _ (λ y, E_c p d hc m.succ y)?
    apply finset.sum_bij,
    swap 5, { intros a ha, refine ⟨a, set.mem_to_finset.1 ha⟩, },
    { rintros a ha, apply finset.mem_univ, },
    { rintros a ha, simp only [subtype.coe_mk], },
    { rintros a b ha hb h, simp only [subtype.mk_eq_mk] at h, rw h, },
    { rintros b hb, simp only [set.mem_to_finset],
      refine ⟨b.val, _, _⟩,
      { --rw set.mem_to_finset,
        apply b.prop, },
      { rw subtype.ext_iff_val, }, }, },
  any_goals { assumption, },
end
-- why does has_div exist for ℤ and ℕ!?

lemma inter_nonempty_of_not_disjoint {α : Type*} {s t : set α} (h : ¬disjoint s t) :
  ∃ x, x ∈ s ∧ x ∈ t :=
begin
  contrapose h, push_neg at h, rw not_not, rw disjoint_iff, simp [h], ext, split,
  { intro h', rw set.mem_inter_iff at h', specialize h x h'.1, simp, apply h h'.2, },
  { simp, },
end

lemma inter_nonempty_of_not_disjoint' {α : Type*} {s t : finset α} [decidable_eq α]
  (h : ¬disjoint s t) : ∃ x, x ∈ s ∧ x ∈ t :=
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
noncomputable def g (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (hd : 0 < d)
  (f : locally_constant (zmod d × ℤ_[p]) R) (hd' : d.gcd p = 1) : @eventually_constant_seq R :=
{ to_seq := λ (n : ℕ),
    --have hpos : 0 < d * p^n := mul_pos hd (pow_pos (nat.prime.pos (fact_iff.1 _inst_3)) n),
    --by
       --letI : fintype (zmod (d * p^n)) := @zmod.fintype _ ⟨hpos⟩; exact
    ∑ a in (zmod' (d * p^n) (mul_prime_pow_pos p d n)), f(a) • ((algebra_map ℚ R) (E_c p d hc n a)),
  is_eventually_const := ⟨classical.some (factor_F p d R hd' f) + 1,
  begin
  simp, rintros l hl', -- why is the simp needed?
  have hl : classical.some (factor_F p d R hd' f) ≤ l,
  { apply le_trans (nat.le_succ _) hl', },
  set t := λ a : zmod (d * p ^ l), set.to_finset ((equi_class p d l l.succ (nat.le_succ l)) a) with ht,
  rw succ_eq_bUnion_equi_class,
  rw @finset.sum_bUnion _ _ _ _ _ _ (zmod' (d*p^l) (mul_prime_pow_pos p d l)) t _,
  { haveI : fact (0 < l),
    { apply fact_iff.2,
      apply lt_of_lt_of_le (nat.zero_lt_succ _) hl', },
    conv_lhs { apply_congr, skip, conv { apply_congr, skip, rw equi_class_eq p d R l f x hd' hl x_1 H_1, },
    rw [←finset.mul_sum], rw E_c_sum_equi_class p d R l x hc hc', }, },
  { rintros x hx y hy hxy, contrapose hxy, push_neg,
    obtain ⟨z, hz⟩ := inter_nonempty_of_not_disjoint' hxy,
    rw ht at hz, simp at hz, rw mem_equi_class p d l l.succ at hz,
    rw mem_equi_class p d l l.succ at hz, cases hz with h1 h2, rw h1 at h2,
    exact h2, }, end⟩, }

lemma g_def (hc : c.gcd p = 1) (hc' : c.gcd d = 1) (hd : 0 < d)
  (f : locally_constant (zmod d × ℤ_[p]) R) (n : ℕ) (hd' : d.gcd p = 1) :
  (g p d R hc hc' hd f hd').to_seq n =
    ∑ a in (finset.range (d * p^n)),f(a) • ((algebra_map ℚ R) (E_c p d hc n a)) :=
begin
  rw g, simp only,
  apply finset.sum_bij,
  swap 5, { rintros, exact a.val, },
  any_goals { rintros, simp, },
  { apply zmod.val_lt, },
  { rintros a b ha hb h, simp only at h, apply zmod.val_injective _ h, },
  { refine ⟨(b : zmod (d * p^n)), _, _⟩,
    { apply finset.mem_univ, },
    { apply (zmod.val_cast_of_lt (finset.mem_range.1 H)).symm, }, },
end

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
--@[simp] lemma cast_hom_apply' {n : ℕ} (i : zmod n) : cast_hom h R i = i := rfl

-- def G (f : locally_constant ℤ_[p] R) (a : ℤ_[p]) : ℕ := ⨅ n : ℕ, loc_const_const -- is this really needed?
lemma equi_class_clopen (n : ℕ) (a : zmod (d * p^n)) (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  [hd : ∀ n : ℕ, fact (0 < d * p^n)] (h' : d.gcd p = 1) (hd' : 0 < d) (hm : n ≤ m)
  (b : (equi_class p d n m hm a)) : (b.val : zmod d × ℤ_[p]) ∈ (clopen_from p d n a) :=
begin
  have := b.prop,
  rw mem_equi_class at this,
  rw subtype.val_eq_coe,
  rw mem_clopen_from,
  conv { congr, { to_rhs, congr, rw ←this, },
      to_lhs, congr, rw ←this, },
  split,
  { simp only [prod.fst_zmod_cast],
    repeat { rw ←zmod.cast_hom_apply _, },
    any_goals { refine zmod.char_p _, },
    any_goals { apply dvd_mul_right _ _, },
    swap, { apply mul_dvd_mul_left, apply pow_dvd_pow _ _, apply hm, },
    { rw ←ring_hom.comp_apply, apply _root_.congr_fun _,
      congr,
      convert ring_hom.ext_zmod _ _, }, },
  { simp only [prod.snd_zmod_cast],
    convert_to _ = ((b: zmod (d * p^m)) : zmod (p^n)),
    { rw ←zmod.int_cast_cast (b: zmod (d * p^m)),
      conv_rhs { rw ←zmod.int_cast_cast (b: zmod (d * p^m)), },
      change (ring_hom.comp (to_zmod_pow n) (int.cast_ring_hom ℤ_[p])) ((b : zmod (d * p^m)) : ℤ) =
        (int.cast_ring_hom (zmod (p^n))) ((b : zmod (d * p^m)) : ℤ),
      apply _root_.congr_fun _ _, congr,
      convert @ring_hom.ext_zmod 0 _ _ _ _, }, -- good job!
    { repeat { rw ←zmod.cast_hom_apply _, },
      any_goals { refine zmod.char_p _, },
      { rw ←ring_hom.comp_apply, apply _root_.congr_fun _,
      congr,
      convert ring_hom.ext_zmod _ _, },
      any_goals { apply dvd_mul_left _ _, },
      any_goals { apply mul_dvd_mul_left, apply pow_dvd_pow _ _, apply hm, },
      { apply dvd_mul_of_dvd_right _ _, apply pow_dvd_pow _ _, apply hm, }, }, },
end

example {α β : Type*} (h : α ≃ β) : function.injective h.to_fun := equiv.injective h

open locally_constant

lemma g_char_fn (n : ℕ) (a : zmod (d * p^n)) (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  [hd : ∀ n : ℕ, fact (0 < d * p^n)] (h' : d.gcd p = 1) (hd' : 0 < d) (hm : n ≤ m) :
  (g p d R hc hc' hd' (char_fn R (is_clopen_clopen_from p d n a)) h').to_seq m =
  ∑ (y : equi_class p d n m hm a), (algebra_map ℚ R) (E_c p d hc m y) :=
begin
  rw g_def,
  rw char_fn,
  simp only [algebra.id.smul_eq_mul, boole_mul, locally_constant.coe_mk, subtype.val_eq_coe],
  rw finset.sum_ite, simp only [add_zero, finset.sum_const_zero],
  rw finset.sum_bij,
  swap 5,
  { rintros b hb, simp only [finset.mem_filter, finset.mem_range] at hb,
    refine ⟨b, _⟩, rw mem_equi_class, cases hb with h1 h2, --rw ←subtype.val_eq_coe at h2,
    rw mem_clopen_from at h2,
    { apply (function.injective.eq_iff
        (equiv.injective (zmod.chinese_remainder (coprime_pow_spl p d n h')).to_equiv )).1,
      rw prod.ext_iff,
      split,
      { convert h2.1 using 1,
        { --make into separate lemma?
          convert_to _ = ((b : zmod (d * p^n)) : zmod d),
          { simp only [prod.fst_nat_cast], rw zmod.cast_nat_cast _,
            swap, { refine zmod.char_p _, },
            { refine dvd_mul_right _ _, }, },
          --refine (function.injective.eq_iff prod.fst_injective).2 _,
          { change (ring_hom.comp (ring_hom.fst (zmod d) (zmod (p^n)))
            ((zmod.chinese_remainder (coprime_pow_spl p d n h')).to_ring_hom))
              ((b : zmod (d * p^m)) : zmod (d * p^n)) = _,
            symmetry,
            rw ←zmod.cast_hom_apply _,
            { apply congr,
              { congr, convert ring_hom.ext_zmod _ _, },
              { rw zmod.cast_nat_cast _,
                swap, { refine zmod.char_p _, },
                { apply mul_dvd_mul_left, apply pow_dvd_pow _ _, apply hm, }, }, },
            swap, { refine zmod.char_p _, },
            { apply dvd_mul_right _ _, }, }, },
        { change (ring_hom.comp (ring_hom.fst (zmod d) (zmod (p^n)))
            ((zmod.chinese_remainder (coprime_pow_spl p d n h')).to_ring_hom)) a = _,
          symmetry,
          rw ←zmod.cast_hom_apply _,
          { apply congr _ _,
            { congr, convert ring_hom.ext_zmod _ _, },
            { refl, }, },
          swap, { refine zmod.char_p _, },
          { apply dvd_mul_right _ _, },  }, },
      { convert (h2.2).symm,
        { --rw map_nat_cast,
          simp only [map_nat_cast, prod.snd_nat_cast],
          --make into separate lemma?
          convert_to _ = ((b : zmod (d * p^n)) : zmod (p^n)),
          { rw zmod.cast_nat_cast _,
            swap, { refine zmod.char_p _, },
            { refine dvd_mul_left _ _, }, },
          --refine (function.injective.eq_iff prod.fst_injective).2 _,
          { change (ring_hom.comp (ring_hom.snd (zmod d) (zmod (p^n)))
            ((zmod.chinese_remainder (coprime_pow_spl p d n h')).to_ring_hom))
              ((b : zmod (d * p^m)) : zmod (d * p^n)) = _,
            symmetry,
            rw ←zmod.cast_hom_apply _,
            { apply congr,
              { congr, convert ring_hom.ext_zmod _ _, },
              { rw zmod.cast_nat_cast _,
                swap, { refine zmod.char_p _, },
                { apply mul_dvd_mul_left, apply pow_dvd_pow _ _, apply hm, }, }, },
            swap, { refine zmod.char_p _, },
            { apply dvd_mul_left _ _, }, }, },
        { change (ring_hom.comp (ring_hom.snd (zmod d) (zmod (p^n)))
            ((zmod.chinese_remainder (coprime_pow_spl p d n h')).to_ring_hom)) a = _,
          symmetry,
          rw ←zmod.cast_hom_apply _,
          { apply congr _ _,
            { congr, convert ring_hom.ext_zmod _ _, },
            { refl, }, },
          swap, { refine zmod.char_p _, },
          { apply dvd_mul_left _ _, },  },  }, }, }, -- use ring_hom.zmod_ext and ring_hom.comp for all goals above
  { rintros, apply finset.mem_univ, },
  { rintros b hb, simp only [subtype.coe_mk], },
  { rintros b c hb hc h, simp only [subtype.mk_eq_mk] at h,
    simp only [finset.mem_filter, finset.mem_range] at hc,
    simp only [finset.mem_filter, finset.mem_range] at hb,
    rw ←zmod.val_cast_of_lt hb.1,
    rw ←zmod.val_cast_of_lt hc.1,
    rw function.injective.eq_iff (zmod.val_injective _),
    { exact h, },
    { apply hd m, }, },
  { rintros b hb, simp only [finset.mem_filter, finset.mem_range, subtype.val_eq_coe],
    refine ⟨(b.val).val, _, _⟩,
    { simp only [finset.mem_filter, finset.mem_range, subtype.val_eq_coe, zmod.nat_cast_val],
      split,
      { apply zmod.val_lt, },
      { rw ←subtype.val_eq_coe,
        apply equi_class_clopen p d m n a hc hc' h' hd', }, },
    { rw subtype.ext_iff_val, simp only [zmod.cast_id', id.def, zmod.nat_cast_val], }, },
end

lemma seq_lim_g_char_fn (n : ℕ) (a : zmod (d * p^n)) (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  [hd : ∀ n : ℕ, fact (0 < d * p^n)] (h' : d.gcd p = 1) (hd' : 0 < d) :
  sequence_limit_index' (g p d R hc hc' hd' (char_fn R (is_clopen_clopen_from p d n a)) h') ≤ n :=
begin
  apply nat.Inf_le, simp only [set.mem_set_of_eq], rintros m hm,
  repeat { rw g_char_fn, },
  { --have : fact (0 < m), sorry,
    conv_rhs { apply_congr, skip, rw ←E_c_sum_equi_class p d R _ _ _ hc', },
    simp only, rw ←finset.sum_bUnion,
    { apply finset.sum_bij,
      swap 5, { rintros b hb, exact b.val, apply le_trans hm (nat.le_succ m), },
      { rintros b hb,
        simp only [exists_prop, finset.mem_univ, set_coe.exists, finset.mem_bUnion,
          set.mem_to_finset, exists_true_left, subtype.coe_mk, subtype.val_eq_coe],
        refine ⟨b.val, _, _⟩,
        { assumption, },
        { rw mem_equi_class,
          have := b.prop, rw mem_equi_class at this,
          conv_rhs { rw ←this, },
          simp only [subtype.val_eq_coe],
          rw ←zmod.cast_hom_apply ((b : zmod (d * p^m.succ)) : zmod (d * p^m)),
          rw ←zmod.cast_hom_apply (b : zmod (d * p^m.succ)),
          rw ←zmod.cast_hom_apply (b : zmod (d * p^m.succ)),
          rw ←ring_hom.comp_apply, apply _root_.congr_fun _, congr, convert ring_hom.ext_zmod _ _,
          any_goals { refine zmod.char_p _, },
          any_goals { apply mul_dvd_mul_left, apply pow_dvd_pow _ _, },
          { apply le_trans hm (nat.le_succ m), },
          { apply nat.le_succ m, },
          { assumption, }, },
        --{ apply b.prop, trivial, },
        { rw mem_equi_class, rw subtype.val_eq_coe, }, },
      { rintros b hb, simp only, rw subtype.val_eq_coe, },
      { rintros b b' hb hb' h, simp only at h,
        rw subtype.ext_iff_val, assumption, },
      { rintros b hb,
        simp only [exists_prop, finset.mem_univ, set_coe.exists, finset.mem_bUnion,
          set.mem_to_finset, exists_true_left, subtype.coe_mk] at hb,
        rcases hb with ⟨z, h1, h3⟩,
        simp only [exists_prop, finset.mem_univ, set_coe.exists, exists_eq_right',
          exists_true_left, subtype.coe_mk, subtype.val_eq_coe],
        --refine ⟨b, _, trivial, rfl⟩,
        rw mem_equi_class, rw mem_equi_class at h3,
        rw mem_equi_class at h1, rw ←h1, rw ←h3,
        -- stop being lazy and make a lemma from this!
        repeat { rw ←zmod.cast_hom_apply _, },
        rw ←ring_hom.comp_apply, apply _root_.congr_fun _, congr, convert ring_hom.ext_zmod _ _,
        any_goals { refine zmod.char_p _, },
        any_goals { apply mul_dvd_mul_left, apply pow_dvd_pow _ _, },
        { apply nat.le_succ m, },
        { assumption, },
        { apply le_trans hm (nat.le_succ m), }, }, },
    { rintros x hx y hy hxy,
      rw function.on_fun,
      rw finset.disjoint_iff_ne,
      rintros z hz z' hz',
      contrapose hxy, push_neg, push_neg at hxy,
      rw finset.mem_def at *,
      simp only [set.mem_to_finset_val] at hz,
      simp only [set.mem_to_finset_val] at hz',
      rw mem_equi_class at *,
      rw subtype.ext_iff_val, rw subtype.val_eq_coe, rw subtype.val_eq_coe,
      rw ←hz, rw ←hz', rw hxy, }, },
end
-- lemma loc_const_comp (f : locally_constant ℤ_[p] R)

-- can hd be removed?
lemma bernoulli_measure_nonempty (hc : c.gcd p = 1) (hc' : c.gcd d = 1)
  [hd : ∀ n : ℕ, fact (0 < d * p^n)] (h' : d.gcd p = 1) :
  nonempty (@bernoulli_measure p _ d R _ _ _ _ _ _ _ hc) :=
begin
  refine mem_nonempty _,
--  have hd' : 0 < d, sorry,
  refine { to_fun := λ f, sequence_limit (g p d R hc hc' _ f h'),
  map_add' := _,
  map_smul' := _ },
  { rw ←mul_one d, rw ←pow_zero p, apply fact_iff.1, apply hd 0, },
  { rintros,
    have hd' : 0 < d,
    { rw ←mul_one d, rw ←pow_zero p, apply fact_iff.1, apply hd 0, },
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
    have hd' : 0 < d,
    { rw ←mul_one d, rw ←pow_zero p, apply fact_iff.1, apply hd 0, },
    set n := (sequence_limit_index' (g p d R hc hc' hd' x h')) ⊔ (sequence_limit_index' (g p d R hc hc' hd' (m • x) h'))
      with hn,
    repeat { rw sequence_limit_eq (g p d R hc hc' hd' _ h') n _, },
    { repeat { rw g_def p d R hc hc' hd' _ n h', }, simp only [algebra.id.smul_eq_mul, locally_constant.coe_smul, pi.smul_apply], rw finset.mul_sum,
      apply finset.sum_congr, refl,
      rintros, rw mul_assoc, rw ring_hom.id_apply, },
    { rw le_sup_iff, left, apply le_refl, },
    { rw le_sup_iff, right, apply le_refl, }, }, --there has to be a less repetitive way of doing this
  { rw bernoulli_measure, simp only [le_refl, algebra.id.smul_eq_mul, pi.add_apply, locally_constant.coe_add, linear_map.coe_mk, locally_constant.coe_smul,
    subtype.forall, le_sup_iff, set.mem_set_of_eq, pi.smul_apply, subtype.coe_mk, set.singleton_prod, subtype.val_eq_coe],
    intros n a,
    have hd' : 0 < d,
    { rw ←mul_one d, rw ←pow_zero p, apply fact_iff.1, apply hd 0, },
--      have hd' : 0 < d, sorry,
    rw sequence_limit_eq (g p d R hc hc' hd' _ h') n _,
    { rw g_def p d R hc hc' hd' _ n h',
      rw finset.sum_eq_add_sum_diff_singleton, swap 3, exact a.val,
      swap,
      { simp only [finset.mem_range], apply zmod.val_lt _, apply hd n, },
        --apply (@zmod.val_lt (d * p^(n)) (hd n) a),
        rw zmod.nat_cast_val a, rw zmod.nat_cast_val a,
        convert_to (1 • ((algebra_map ℚ R) (E_c p d hc n a))) + _ =
          ((algebra_map ℚ R) (E_c p d hc n a)),
        swap, rw one_smul, rw add_zero,
        congr,
        { simp only [zmod.cast_id', algebra.id.smul_eq_mul, one_mul, id.def, _root_.nsmul_eq_mul, nat.cast_one],
          convert one_mul ((algebra_map ℚ R) (E_c p d hc n a)),
          rw char_fn, simp only [not_exists, set.mem_preimage, set.mem_image, not_and,
          set.mem_singleton_iff, locally_constant.coe_mk, ite_eq_right_iff], rw if_pos,
          rw mem_clopen_from,
          --use (a : ℤ_[p]), --use ((a : zmod (p^n)) : ℤ_[p]),
          split,
          { simp only [prod.fst_zmod_cast],
            /-rw ←zmod.int_cast_cast a, conv_rhs { rw ←zmod.int_cast_cast a, },
            change (ring_hom.comp (to_zmod_pow n) (int.cast_ring_hom (ℤ_[p]))) (a : ℤ) =
              (int.cast_ring_hom (zmod (p^n))) (a : ℤ),
            apply congr_fun _, congr,
            convert @ring_hom.ext_zmod 0 _ _ _ _,-/ },
          { simp only [prod.snd_zmod_cast],
            rw ←zmod.int_cast_cast a, conv_rhs { rw ←zmod.int_cast_cast a, },
            change (int.cast_ring_hom (zmod (p^n))) (a : ℤ) =
              (ring_hom.comp (to_zmod_pow n) (int.cast_ring_hom (ℤ_[p]))) (a : ℤ),
            apply _root_.congr_fun _, congr,
            convert @ring_hom.ext_zmod 0 _ _ _ _,
            /-rw prod.ext_iff,
            simp only [true_and, prod.fst_zmod_cast, prod.snd_zmod_cast, eq_self_iff_true],-/ }, },
        { apply finset.sum_eq_zero, rintros x hx, rw char_fn, simp only [not_exists,
          set.mem_preimage, set.mem_image, not_and, set.mem_singleton_iff, locally_constant.coe_mk,
          ite_eq_right_iff], rw if_neg,
          { rw zero_smul, },
          { --push_neg, rintros y hy h'',
            rintros h'',
            rw mem_clopen_from at h'',
            simp only [finset.mem_sdiff, finset.mem_singleton, finset.mem_range] at hx,
            apply hx.2, /-rw prod.ext_iff at h'',
            simp only [prod.snd_nat_cast, prod.fst_nat_cast] at h'',
            rw h''.2 at hy, -/
            suffices : (x : zmod (p^n)) = (a : zmod (p^n)),
            { rw ←zmod.nat_cast_val a at this,
              rw zmod.nat_coe_eq_nat_coe_iff at this,
              cases h'' with h1 h2,
              rw ←zmod.nat_cast_val a at h1, --simp only [prod.fst_zmod_cast] at h1,
              simp only [prod.fst_nat_cast] at h1,
              rw zmod.nat_coe_eq_nat_coe_iff at h1,
              have h3 := (nat.modeq_and_modeq_iff_modeq_mul (coprime_pow_spl p d n h')).1 ⟨h1, this⟩,
              rw ←zmod.nat_coe_eq_nat_coe_iff at h3,
              have h4 := congr_arg zmod.val h3,
              rw zmod.val_cast_of_lt (hx.1) at h4, rw zmod.val_cast_of_lt (zmod.val_lt a) at h4,
              rw h4, },
            { rw (h''.2), simp only [map_nat_cast, prod.snd_nat_cast], }, }, }, },
    { convert seq_lim_g_char_fn p d R n a hc hc' h' hd', }, },
end

/-{
  to_fun := λ f, sequence_limit (g p d R hc hc' (by {apply fact_iff.1, convert hd 0,
    rw [pow_zero, mul_one], }) f h'),
  map_add' := begin rintros,
    have hd' : 0 < d,
    { rw ←mul_one d, rw ←pow_zero p, apply fact_iff.1, apply hd 0, },
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
    { rw le_sup_iff, left, rw le_sup_iff, left, apply le_refl, }, end,
  map_smul' := sorry,
}-/

/- -- not used, delete?
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
end -/
