/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import number_theory.weight_space_one

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

-- lemma what_to_do (f : locally_constant (zmod d × ℤ_[p]) R) : ∃ (s : finset ℕ)
--   (j : s → R) (i : s → (clopen_basis' p d)), f = ∑ k : s, j(k) • (char_fn (i k)) :=
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

--example (m n : ℕ) (h : m ≤ n.succ) : m ≤ n ∨ m = n.succ := nat.of_le_succ h

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
def equi_class (n m : ℕ) (h : n ≤ m) (a : zmod (d * p^n)) :=
 {b : zmod (d * p^m) | (b : zmod (d * p^n)) = a}
-- change def to a + k*dp^m
-- need h to be n ≤ m, not n < m for g_char_fn

lemma mem_equi_class (n m : ℕ) (h : n ≤ m) (a : zmod (d * p^n)) (b : zmod (d * p^m)) :
  b ∈ equi_class p d n m h a ↔ (b : zmod (d * p^n)) = a :=
⟨λ hb, begin rw equi_class at hb, simp at hb, exact hb, end,
  λ hb, begin rw equi_class, simp, exact hb, end⟩

lemma equi_class_some (n : ℕ) (x : zmod (d * p^n)) (y : equi_class p d n n.succ (nat.le_succ n) x) :
  ∃ k : ℕ, k < p ∧ (y : zmod (d * p^n.succ)).val = x.val + k * d * p^n :=
begin
  have := (mem_equi_class p d n n.succ (nat.le_succ n) x y).1 (y.prop),
  conv { congr, funext, conv { congr, skip, to_rhs, rw ←((mem_equi_class p d n n.succ (nat.le_succ n) x y).1 (y.prop)), }, },
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
def equi_iso_fin (m : ℕ) (a : zmod (d * p^m)) : equi_class p d m m.succ (nat.le_succ m) a ≃ fin p :=
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
      rw ← nat.add_sub_assoc _ _,
      rw nat.add_sub_cancel_left,
      { rw @zmod.nat_cast_val _ _ _ this _, norm_cast, },
      { rw h, apply nat.le_add_right, }, },
    { rw [h, nat.add_sub_cancel_left, mul_assoc], simp, },
  end,
  right_inv := begin
    rintros x,
    simp only [nat.cast_pow],
    rw subtype.ext_iff_val,
    simp only [fin.coe_mk, subtype.val_eq_coe, _root_.coe_coe],
    haveI : fact (0 < d * p ^ m.succ),
    { rw fact_iff at *, apply mul_pos, assumption, apply ((pow_pos (nat.prime.pos _)) m.succ), assumption, },
    have h2 : fact (0 < d * p ^ m),
    { rw fact_iff at *, apply mul_pos, assumption, apply ((pow_pos (nat.prime.pos _)) m), assumption, },
    apply nat.div_eq_of_eq_mul_left,
    { apply fact_iff.1 h2, },
    apply tsub_eq_of_eq_add,
    rw [mul_assoc, zmod.val_nat_cast, nat.mod_eq_of_lt],
    rw add_comm,
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

noncomputable instance (n m : ℕ) (h : n ≤ m) (a : zmod (d * p^n)) :
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
lemma sum_char_fn_dependent_Ec (m : ℕ) (a : zmod (p^m)) (b : zmod d) (hc : c.gcd p = 1) :
  E_c p d hc m a = ∑ x in set.to_finset (equi_class p d m m.succ (nat.le_succ m) a), E_c p d hc m.succ x :=
sorry

lemma loc_const_const (f : locally_constant (zmod d × ℤ_[p]) R) (a : zmod d × ℤ_[p]) : ∃ N : ℕ, ∀ m ≥ N,
  ∀ y ∈ {b : zmod d × ℤ_[p] | (to_zmod_pow m) a.2 = (to_zmod_pow m) b.2}, f y = f a :=
sorry -/
open padic_int

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
def F : ℕ → discrete_quotient (zmod d × ℤ_[p]) := λ n,
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

noncomputable def coe_padic_to_zmod (n : ℕ) (x : zmod d × ℤ_[p]) (hd : d.gcd p = 1) : zmod (d * p^n) :=
--  ((x.1, (to_zmod_pow n)x.2) : zmod (d * p ^ n))
  (zmod.chinese_remainder (nat.coprime.pow_right _ (nat.coprime_iff_gcd_eq_one.1 hd))).inv_fun (x.1, (to_zmod_pow n)x.2)
-- should this be used

/-def bound_set (U : set (zmod d × ℤ_[p])) (hU : is_open U) (hd : gcd d p = 1) :=
  {n : ℕ | ∀ (a : zmod d × ℤ_[p]) (H : a ∈ U), ∃ m : ℕ, n ≤ m ∧
    (clopen_from p d m (coe_padic_to_zmod p d m a hd)).val ⊆ U } -/

def bound_set (U : set (zmod d × ℤ_[p])) (hU : is_open U) (hd : d.gcd p = 1) :=
  {n : ℕ | ∀ (a : zmod d × ℤ_[p]) (H : a ∈ U),
    (clopen_from p d n (coe_padic_to_zmod p d n a hd)) ⊆ U }

noncomputable def bound (U : set (zmod d × ℤ_[p])) (hU : is_open U) (hd : d.gcd p = 1) : ℕ :=
  Inf (bound_set p d U hU hd)
/-noncomputable def bound (U : set (zmod d × ℤ_[p])) (hU : is_open U) := ⨅ (n : ℕ),
  ∃ (a : zmod (d * p^n)), (clopen_from p d n a).val ⊆ U -/

lemma F_rel (x y : zmod d × ℤ_[p]) (n : ℕ) : (F p d n).rel x y ↔
  (to_zmod_pow n) x.snd = (to_zmod_pow n) y.snd ∧ x.fst = y.fst := by { rw F, }

lemma mem_clopen_from (n : ℕ) (a : zmod (d * p^n)) (y : zmod d × ℤ_[p]) :
  y ∈ (clopen_from p d n a) ↔ y.fst = (a : zmod d) ∧
    (a : zmod (p^n)) = (to_zmod_pow n) y.snd :=
begin
  --dsimp [clopen_from],
  simp only [set.mem_preimage, set.mem_singleton_iff, set.mem_prod, and.congr_right_iff],
  --simp only [set.mem_preimage, set.mem_image, set.mem_singleton_iff, set.singleton_prod],
  intro hy,
  rw eq_comm,
  /-split, all_goals { intro h, },
  { rw h,
    /-cases h with x hx, split,
    { rw ←(congr_arg prod.fst hx.2).trans rfl, },
    { rw ←hx.1, apply congr_arg, rw ←(congr_arg prod.snd hx.2).trans rfl, },-/ },
  { refine ⟨y.snd, h.2.symm, _⟩, rw ←h.1, simp only [prod.mk.eta], }, -/
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

example {α β : Type*} (x : α × β) : x = (x.fst, x.snd) := prod.ext rfl rfl

--make `inv_fst`
lemma inv_fst' (n : ℕ) (x : zmod (d * p^n)) (cop : d.coprime (p^n)) :
  (((zmod.chinese_remainder cop).to_equiv) x).fst = (x : zmod d) :=
begin
  rw ←zmod.cast_hom_apply x,
  swap 3, { apply zmod.char_p _, },
  swap, { apply dvd_mul_right, },
  { conv_rhs { rw ←(zmod.chinese_remainder cop).left_inv x, },
    change _ = (zmod.cast_hom _ (zmod d)) ((zmod.chinese_remainder cop).inv_fun
      (((zmod.chinese_remainder cop).to_fun x).fst, ((zmod.chinese_remainder cop).to_fun x).snd)),
    rw proj_fst',
    congr, },
end

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

--make `inv_snd`
lemma inv_snd' (n : ℕ) (x : zmod (d * p^n)) (cop : d.coprime (p^n)) :
  (((zmod.chinese_remainder cop).to_equiv) x).snd = (x : zmod (p^n)) :=
begin
  rw ←zmod.cast_hom_apply x,
  swap 3, { apply zmod.char_p _, },
  swap, { apply dvd_mul_left, },
  { conv_rhs { rw ←(zmod.chinese_remainder cop).left_inv x, },
    change _ = (zmod.cast_hom _ (zmod (p^n))) ((zmod.chinese_remainder cop).inv_fun
      (((zmod.chinese_remainder cop).to_fun x).fst, ((zmod.chinese_remainder cop).to_fun x).snd)),
    rw proj_snd',
    congr, },
end

/-lemma coprime_pow_spl (n : ℕ) (hd : gcd d p = 1) : d.coprime (p^n) :=
  nat.coprime.pow_right _ (nat.coprime_iff_gcd_eq_one.1 hd)-/
open nat

lemma mem_clopen_from' (n : ℕ) (x : zmod d × ℤ_[p]) (y : zmod d × ℤ_[p]) (hd : d.gcd p = 1) :
  y ∈ (clopen_from p d n (coe_padic_to_zmod p d n x hd)) ↔ (F p d n).rel x y :=
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

lemma mem_clopen_from'' (n : ℕ) (x : zmod d × ℤ_[p]) (y : zmod d × ℤ_[p]) (hd : d.gcd p = 1)
  (hy : y ∈ (clopen_from p d n (coe_padic_to_zmod p d n x hd))) :
  (clopen_from p d n (coe_padic_to_zmod p d n x hd)) =
  (clopen_from p d n (coe_padic_to_zmod p d n y hd)) :=
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
  refine congr_arg _ _, exact hn.1,
end

lemma clopen_sub_clopen (k n : ℕ) (h : k ≤ n) (x : zmod d × ℤ_[p]) (hd : d.gcd p = 1) :
  (clopen_from p d n (coe_padic_to_zmod p d n x hd)) ⊆
    (clopen_from p d k (coe_padic_to_zmod p d k x hd)) :=
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

theorem clopen_basis'_topo_basis (hd : d.gcd p = 1) : topological_space.is_topological_basis
  {V | ∃ (U : clopen_basis' p d), V = (U.val)} :=
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
      rw set.singleton_monoid_hom_apply, },
    { --rw clopen_basis,
      rw hU, --rw ←subtype.val_eq_coe at h,
      --have := subtype.ext_iff_val.1 h, simp only [subtype.val_eq_coe] at this,
      repeat { rw subtype.val_eq_coe, }, rw h,
      simp only [and_true, eq_self_iff_true, set.mem_set_of_eq],
      use n,
      { refine ⟨(w : zmod (p^n)), rfl⟩, },
      --refl,
      }, },
  { rcases hy with ⟨x', y', hx, hy, h⟩,
    rw set.mem_range at hx, cases hx with x hx,
    --rw clopen_basis at hy,
    simp only [set.mem_set_of_eq] at hy,
    rcases hy with ⟨n, y, hy⟩,
    set U' : set (zmod d × ℤ_[p]) := ({x} : set (zmod d)) ×ˢ
      (set.preimage (padic_int.to_zmod_pow n) {y}) with hU',
    have hU'' : is_clopen U' := is_clopen_prod (is_clopen_singleton x) (proj_lim_preimage_clopen' p n y),
    set U : clopen_basis' p d := ⟨U', _⟩ with hU,
    any_goals { refine ⟨n, ((zmod.chinese_remainder (coprime_pow_spl p d n hd)).inv_fun (x, y)), _⟩,
      rw hU', congr,
      { convert (proj_fst' _ _ _ _ _).symm, },
      { convert (proj_snd' _ _ _ _ _).symm, }, },
    { refine ⟨U, _⟩,
      rw ←h, rw hU, simp only, congr,
      { rw ←hx, rw set.singleton_monoid_hom_apply, },
      { rw hy, }, }, },
end

--example {U : set (clopen_sets (zmod d × ℤ_[p]))} : set (zmod d × ℤ_[p]) ≃ set (zmod d) × set ℤ_[p] :=

lemma exists_clopen_from {U : set (zmod d × ℤ_[p])} (hU : is_open U) (hd : d.gcd p = 1)
  {x : zmod d × ℤ_[p]} (memU : x ∈ U) : ∃ n : ℕ,
  (clopen_from p d n (coe_padic_to_zmod p d n x hd)) ⊆ U :=
begin
  obtain ⟨V, H, memV, U_sub_V⟩ := topological_space.is_topological_basis.exists_subset_of_mem_open
    (clopen_basis'_topo_basis p d hd) memU hU,
  simp only [exists_prop, subtype.exists, set.mem_set_of_eq] at H,
  rcases H with ⟨W, H⟩, cases H with H hV,
  rcases H with ⟨n, a, H⟩, rw hV at U_sub_V,
  rw hV at memV, rw H at memV, --rw clopen_from at memV,
  /-simp only [set.mem_preimage, set.mem_image, set.mem_singleton_iff,
    set.singleton_prod] at memV, -/
  rw mem_clopen_from at memV,
--  rcases memV with ⟨z', h'1, h'2⟩,
  use n, intros y hy,
  rw mem_clopen_from at hy, rw coe_padic_to_zmod at hy, rw proj_snd at hy, rw proj_fst at hy,
  --rw ←h'2 at hy, simp only at hy,
  apply U_sub_V, rw H, --rw clopen_from,
  simp only [set.mem_preimage, set.mem_singleton_iff, set.mem_prod],
  --simp only [set.mem_preimage, set.mem_image, set.mem_singleton_iff, set.singleton_prod],
  --use y.snd,
  rw ←memV.1, rw memV.2, simp [hy], /-rw hy.2, apply hy,
  simp only [prod.mk.eta, eq_self_iff_true, and_self],-/
end

lemma bound_set_inhabited {U : set (zmod d × ℤ_[p])} (hU : is_clopen U) (hd : d.gcd p = 1)
  (ne : nonempty U) : (bound_set p d U hU.1 hd).nonempty :=
begin
  have com : U ⊆ ⋃ (x : zmod d × ℤ_[p]) (hx : x ∈ U),
  (clopen_from p d (classical.some (exists_clopen_from p d hU.1 hd hx))
  (coe_padic_to_zmod p d (classical.some (exists_clopen_from p d hU.1 hd hx)) x hd)),
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
      (coe_padic_to_zmod p d (classical.some _) z hd)),
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
    intro hi, refine (is_clopen_clopen_from _ _ _ _).1, },
end

lemma bound_mem_bound_set {U : set (zmod d × ℤ_[p])} (hU : is_clopen U) (hd : d.gcd p = 1)
  (ne : nonempty U) : bound p d U hU.1 hd ∈ bound_set p d U hU.1 hd :=
  nat.Inf_mem (bound_set_inhabited _ _ hU _ ne)

lemma le_bound (U : set (zmod d × ℤ_[p])) (hU : is_clopen U) (hd : d.gcd p = 1) (x : zmod d × ℤ_[p])
  (memU : x ∈ U) (n : ℕ) (h : bound p d U hU.1 hd ≤ n) (hd : d.gcd p = 1) (ne : nonempty U) :
  (clopen_from p d n (coe_padic_to_zmod p d n x hd)) ⊆ U :=
begin
  transitivity (clopen_from p d (bound p d U hU.1 hd)
    (coe_padic_to_zmod p d (bound p d U hU.1 hd) x hd)),
  intros y,
  repeat { rw mem_clopen_from', },
  suffices : (F p d n) ≤ (F p d (bound p d U hU.1 hd)),
  { apply this x y, },
  { apply le_F_of_ge p d _ _ h, },
  { apply bound_mem_bound_set p d hU hd ne x memU, },
end

lemma factor_F (hd : d.gcd p = 1) (f : locally_constant (zmod d × ℤ_[p]) R) :
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
    have h1 : y ∈ (clopen_from p d n (coe_padic_to_zmod p d n x hd)),
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
