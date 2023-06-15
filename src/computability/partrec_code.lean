/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import computability.partrec

/-!
# Gödel Numbering for Partial Recursive Functions.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `nat.partrec.code`, an inductive datatype describing code for partial
recursive functions on ℕ. It defines an encoding for these codes, and proves that the constructors
are primitive recursive with respect to the encoding.

It also defines the evalution of these codes as partial functions using `pfun`, and proves that a
function is partially recursive (as defined by `nat.partrec`) if and only if it is the evaluation
of some code.

## Main Definitions

* `nat.partrec.code`: Inductive datatype for partial recursive codes.
* `nat.partrec.code.encode_code`: A (computable) encoding of codes as natural numbers.
* `nat.partrec.code.of_nat_code`: The inverse of this encoding.
* `nat.partrec.code.eval`: The interpretation of a `nat.partrec.code` as a partial function.

## Main Results

* `nat.partrec.code.rec_prim`: Recursion on `nat.partrec.code` is primitive recursive.
* `nat.partrec.code.rec_computable`: Recursion on `nat.partrec.code` is computable.
* `nat.partrec.code.smn`: The $S_n^m$ theorem.
* `nat.partrec.code.exists_code`: Partial recursiveness is equivalent to being the eval of a code.
* `nat.partrec.code.evaln_prim`: `evaln` is primitive recursive.
* `nat.partrec.code.fixed_point`: Roger's fixed point theorem.

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]

-/


open encodable denumerable

namespace nat.partrec
open nat (mkpair)

theorem rfind' {f} (hf : nat.partrec f) : nat.partrec (nat.unpaired (λ a m,
  (nat.rfind (λ n, (λ m, m = 0) <$> f (mkpair a (n + m)))).map (+ m))) :=
partrec₂.unpaired'.2 $
begin
  refine partrec.map
    ((@partrec₂.unpaired' (λ (a b : ℕ),
      nat.rfind (λ n, (λ m, m = 0) <$> f (mkpair a (n + b))))).1 _)
    (primrec.nat_add.comp primrec.snd $
      primrec.snd.comp primrec.fst).to_comp.to₂,
  have := rfind (partrec₂.unpaired'.2 ((partrec.nat_iff.2 hf).comp
    (primrec₂.mkpair.comp
      (primrec.fst.comp $ primrec.unpair.comp primrec.fst)
      (primrec.nat_add.comp primrec.snd
        (primrec.snd.comp $ primrec.unpair.comp primrec.fst))).to_comp).to₂),
  simp at this, exact this
end

/--
Code for partial recursive functions from ℕ to ℕ.
See `nat.partrec.code.eval` for the interpretation of these constructors.
-/
inductive code : Type
| zero : code
| succ : code
| left : code
| right : code
| pair : code → code → code
| comp : code → code → code
| prec : code → code → code
| rfind' : code → code

end nat.partrec

namespace nat.partrec.code
open nat (mkpair unpair)
open nat.partrec (code)

instance : inhabited code := ⟨zero⟩

/-- Returns a code for the constant function outputting a particular natural. -/
protected def const : ℕ → code
| 0     := zero
| (n+1) := comp succ (const n)

theorem const_inj : Π {n₁ n₂}, nat.partrec.code.const n₁ = nat.partrec.code.const n₂ → n₁ = n₂
| 0 0 h := by simp
| (n₁+1) (n₂+1) h := by { dsimp [nat.partrec.code.const] at h,
                          injection h with h₁ h₂,
                          simp only [const_inj h₂] }

/-- A code for the identity function. -/
protected def id : code := pair left right

/--
Given a code `c` taking a pair as input, returns a code using `n` as the first argument to `c`.
-/
def curry (c : code) (n : ℕ) : code :=
comp c (pair (code.const n) code.id)

/-- An encoding of a `nat.partrec.code` as a ℕ. -/
def encode_code : code → ℕ
| zero         := 0
| succ         := 1
| left         := 2
| right        := 3
| (pair cf cg) := bit0 (bit0 $ mkpair (encode_code cf) (encode_code cg)) + 4
| (comp cf cg) := bit0 (bit1 $ mkpair (encode_code cf) (encode_code cg)) + 4
| (prec cf cg) := bit1 (bit0 $ mkpair (encode_code cf) (encode_code cg)) + 4
| (rfind' cf)  := bit1 (bit1 $ encode_code cf) + 4

/--
A decoder for `nat.partrec.code.encode_code`, taking any ℕ to the `nat.partrec.code` it represents.
-/
def of_nat_code : ℕ → code
| 0     := zero
| 1     := succ
| 2     := left
| 3     := right
| (n+4) := let m := n.div2.div2 in
  have hm : m < n + 4, by simp [m, nat.div2_val];
  from lt_of_le_of_lt
    (le_trans (nat.div_le_self _ _) (nat.div_le_self _ _))
    (nat.succ_le_succ (nat.le_add_right _ _)),
  have m1 : m.unpair.1 < n + 4, from lt_of_le_of_lt m.unpair_left_le hm,
  have m2 : m.unpair.2 < n + 4, from lt_of_le_of_lt m.unpair_right_le hm,
  match n.bodd, n.div2.bodd with
  | ff, ff := pair (of_nat_code m.unpair.1) (of_nat_code m.unpair.2)
  | ff, tt := comp (of_nat_code m.unpair.1) (of_nat_code m.unpair.2)
  | tt, ff := prec (of_nat_code m.unpair.1) (of_nat_code m.unpair.2)
  | tt, tt := rfind' (of_nat_code m)
  end

/-- Proof that `nat.partrec.code.of_nat_code` is the inverse of `nat.partrec.code.encode_code`-/
private theorem encode_of_nat_code : ∀ n, encode_code (of_nat_code n) = n
| 0     := by simp [of_nat_code, encode_code]
| 1     := by simp [of_nat_code, encode_code]
| 2     := by simp [of_nat_code, encode_code]
| 3     := by simp [of_nat_code, encode_code]
| (n+4) := let m := n.div2.div2 in
  have hm : m < n + 4, by simp [m, nat.div2_val];
  from lt_of_le_of_lt
    (le_trans (nat.div_le_self _ _) (nat.div_le_self _ _))
    (nat.succ_le_succ (nat.le_add_right _ _)),
  have m1 : m.unpair.1 < n + 4, from lt_of_le_of_lt m.unpair_left_le hm,
  have m2 : m.unpair.2 < n + 4, from lt_of_le_of_lt m.unpair_right_le hm,
  have IH : _ := encode_of_nat_code m,
  have IH1 : _ := encode_of_nat_code m.unpair.1,
  have IH2 : _ := encode_of_nat_code m.unpair.2,
  begin
    transitivity, swap,
    rw [← nat.bit_decomp n, ← nat.bit_decomp n.div2],
    simp [encode_code, of_nat_code, -add_comm],
    cases n.bodd; cases n.div2.bodd;
      simp [encode_code, of_nat_code, -add_comm, IH, IH1, IH2, m, nat.bit]
  end

instance : denumerable code :=
mk' ⟨encode_code, of_nat_code,
  λ c, by induction c; try {refl}; simp [
    encode_code, of_nat_code, -add_comm, *],
  encode_of_nat_code⟩

theorem encode_code_eq : encode = encode_code := rfl
theorem of_nat_code_eq : of_nat code = of_nat_code := rfl

theorem encode_lt_pair (cf cg) :
  encode cf < encode (pair cf cg) ∧
  encode cg < encode (pair cf cg) :=
begin
  simp [encode_code_eq, encode_code, -add_comm],
  have := nat.mul_le_mul_right _ (dec_trivial : 1 ≤ 2*2),
  rw [one_mul, mul_assoc, ← bit0_eq_two_mul, ← bit0_eq_two_mul] at this,
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (dec_trivial:0<4)),
  exact ⟨
    lt_of_le_of_lt (nat.left_le_mkpair _ _) this,
    lt_of_le_of_lt (nat.right_le_mkpair _ _) this⟩
end

theorem encode_lt_comp (cf cg) :
  encode cf < encode (comp cf cg) ∧
  encode cg < encode (comp cf cg) :=
begin
  suffices, exact (encode_lt_pair cf cg).imp
    (λ h, lt_trans h this) (λ h, lt_trans h this),
  change _, simp [encode_code_eq, encode_code]
end

theorem encode_lt_prec (cf cg) :
  encode cf < encode (prec cf cg) ∧
  encode cg < encode (prec cf cg) :=
begin
  suffices, exact (encode_lt_pair cf cg).imp
    (λ h, lt_trans h this) (λ h, lt_trans h this),
  change _, simp [encode_code_eq, encode_code],
end

theorem encode_lt_rfind' (cf) : encode cf < encode (rfind' cf) :=
begin
  simp [encode_code_eq, encode_code, -add_comm],
  have := nat.mul_le_mul_right _ (dec_trivial : 1 ≤ 2*2),
  rw [one_mul, mul_assoc, ← bit0_eq_two_mul, ← bit0_eq_two_mul] at this,
  refine lt_of_le_of_lt (le_trans this _)
    (lt_add_of_pos_right _ (dec_trivial:0<4)),
  exact le_of_lt (nat.bit0_lt_bit1 $ le_of_lt $
    nat.bit0_lt_bit1 $ le_rfl),
end

section
open primrec

theorem pair_prim : primrec₂ pair :=
primrec₂.of_nat_iff.2 $ primrec₂.encode_iff.1 $ nat_add.comp
  (nat_bit0.comp $ nat_bit0.comp $
    primrec₂.mkpair.comp
      (encode_iff.2 $ (primrec.of_nat code).comp fst)
      (encode_iff.2 $ (primrec.of_nat code).comp snd))
  (primrec₂.const 4)

theorem comp_prim : primrec₂ comp :=
primrec₂.of_nat_iff.2 $ primrec₂.encode_iff.1 $ nat_add.comp
  (nat_bit0.comp $ nat_bit1.comp $
    primrec₂.mkpair.comp
      (encode_iff.2 $ (primrec.of_nat code).comp fst)
      (encode_iff.2 $ (primrec.of_nat code).comp snd))
  (primrec₂.const 4)

theorem prec_prim : primrec₂ prec :=
primrec₂.of_nat_iff.2 $ primrec₂.encode_iff.1 $ nat_add.comp
  (nat_bit1.comp $ nat_bit0.comp $
    primrec₂.mkpair.comp
      (encode_iff.2 $ (primrec.of_nat code).comp fst)
      (encode_iff.2 $ (primrec.of_nat code).comp snd))
  (primrec₂.const 4)

theorem rfind_prim : primrec rfind' :=
of_nat_iff.2 $ encode_iff.1 $ nat_add.comp
  (nat_bit1.comp $ nat_bit1.comp $
    encode_iff.2 $ primrec.of_nat code)
  (const 4)

theorem rec_prim' {α σ} [primcodable α] [primcodable σ]
  {c : α → code} (hc : primrec c)
  {z : α → σ} (hz : primrec z)
  {s : α → σ} (hs : primrec s)
  {l : α → σ} (hl : primrec l)
  {r : α → σ} (hr : primrec r)
  {pr : α → code × code × σ × σ → σ} (hpr : primrec₂ pr)
  {co : α → code × code × σ × σ → σ} (hco : primrec₂ co)
  {pc : α → code × code × σ × σ → σ} (hpc : primrec₂ pc)
  {rf : α → code × σ → σ} (hrf : primrec₂ rf) :
let PR (a) := λ cf cg hf hg, pr a (cf, cg, hf, hg),
    CO (a) := λ cf cg hf hg, co a (cf, cg, hf, hg),
    PC (a) := λ cf cg hf hg, pc a (cf, cg, hf, hg),
    RF (a) := λ cf hf, rf a (cf, hf),
    F (a : α) (c : code) : σ := nat.partrec.code.rec_on c
      (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a) in
    primrec (λ a, F a (c a) : α → σ) :=
begin
  intros,
  let G₁ : (α × list σ) × ℕ × ℕ → option σ := λ p,
    let a := p.1.1, IH := p.1.2, n := p.2.1, m := p.2.2 in
    (IH.nth m).bind $ λ s,
    (IH.nth m.unpair.1).bind $ λ s₁,
    (IH.nth m.unpair.2).map $ λ s₂,
    cond n.bodd
      (cond n.div2.bodd
        (rf a (of_nat code m, s))
        (pc a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂)))
      (cond n.div2.bodd
        (co a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂))
        (pr a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂))),
  have : primrec G₁,
  { refine option_bind (list_nth.comp (snd.comp fst) (snd.comp snd)) _,
    refine option_bind ((list_nth.comp (snd.comp fst)
      (fst.comp $ primrec.unpair.comp (snd.comp snd))).comp fst) _,
    refine option_map ((list_nth.comp (snd.comp fst)
      (snd.comp $ primrec.unpair.comp (snd.comp snd))).comp $ fst.comp fst) _,
    have a := fst.comp (fst.comp $ fst.comp $ fst.comp fst),
    have n := fst.comp (snd.comp $ fst.comp $ fst.comp fst),
    have m := snd.comp (snd.comp $ fst.comp $ fst.comp fst),
    have m₁ := fst.comp (primrec.unpair.comp m),
    have m₂ := snd.comp (primrec.unpair.comp m),
    have s := snd.comp (fst.comp fst),
    have s₁ := snd.comp fst,
    have s₂ := snd,
    exact (nat_bodd.comp n).cond
      ((nat_bodd.comp $ nat_div2.comp n).cond
        (hrf.comp a (((primrec.of_nat code).comp m).pair s))
        (hpc.comp a (((primrec.of_nat code).comp m₁).pair $
          ((primrec.of_nat code).comp m₂).pair $ s₁.pair s₂)))
      (primrec.cond (nat_bodd.comp $ nat_div2.comp n)
        (hco.comp a (((primrec.of_nat code).comp m₁).pair $
          ((primrec.of_nat code).comp m₂).pair $ s₁.pair s₂))
        (hpr.comp a (((primrec.of_nat code).comp m₁).pair $
          ((primrec.of_nat code).comp m₂).pair $ s₁.pair s₂))) },
  let G : α → list σ → option σ := λ a IH,
    IH.length.cases (some (z a)) $ λ n,
    n.cases (some (s a)) $ λ n,
    n.cases (some (l a)) $ λ n,
    n.cases (some (r a)) $ λ n,
    G₁ ((a, IH), n, n.div2.div2),
  have : primrec₂ G := (nat_cases
    (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) $
    nat_cases snd (option_some_iff.2 (hs.comp (fst.comp fst))) $
    nat_cases snd (option_some_iff.2 (hl.comp (fst.comp $ fst.comp fst))) $
    nat_cases snd (option_some_iff.2 (hr.comp (fst.comp $ fst.comp $ fst.comp fst)))
    (this.comp $
      ((fst.pair snd).comp $ fst.comp $ fst.comp $ fst.comp $ fst).pair $
      snd.pair $ nat_div2.comp $ nat_div2.comp snd)),
  refine ((nat_strong_rec
    (λ a n, F a (of_nat code n)) this.to₂ $ λ a n, _).comp
    primrec.id $ encode_iff.2 hc).of_eq (λ a, by simp),
  simp,
  iterate 4 {cases n with n, {simp [of_nat_code_eq, of_nat_code]; refl}},
  simp [G], rw [list.length_map, list.length_range],
  let m := n.div2.div2,
  show G₁ ((a, (list.range (n+4)).map (λ n, F a (of_nat code n))), n, m)
    = some (F a (of_nat code (n+4))),
  have hm : m < n + 4, by simp [nat.div2_val, m];
  from lt_of_le_of_lt
    (le_trans (nat.div_le_self _ _) (nat.div_le_self _ _))
    (nat.succ_le_succ (nat.le_add_right _ _)),
  have m1 : m.unpair.1 < n + 4, from lt_of_le_of_lt m.unpair_left_le hm,
  have m2 : m.unpair.2 < n + 4, from lt_of_le_of_lt m.unpair_right_le hm,
  simp [G₁], simp [list.nth_map, list.nth_range, hm, m1, m2],
  change of_nat code (n+4) with of_nat_code (n+4),
  simp [of_nat_code],
  cases n.bodd; cases n.div2.bodd; refl
end

/-- Recursion on `nat.partrec.code` is primitive recursive. -/
theorem rec_prim {α σ} [primcodable α] [primcodable σ]
  {c : α → code} (hc : primrec c)
  {z : α → σ} (hz : primrec z)
  {s : α → σ} (hs : primrec s)
  {l : α → σ} (hl : primrec l)
  {r : α → σ} (hr : primrec r)
  {pr : α → code → code → σ → σ → σ}
  (hpr : primrec (λ a : α × code × code × σ × σ,
    pr a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2))
  {co : α → code → code → σ → σ → σ}
  (hco : primrec (λ a : α × code × code × σ × σ,
    co a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2))
  {pc : α → code → code → σ → σ → σ}
  (hpc : primrec (λ a : α × code × code × σ × σ,
    pc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2))
  {rf : α → code → σ → σ}
  (hrf : primrec (λ a : α × code × σ, rf a.1 a.2.1 a.2.2)) :
let F (a : α) (c : code) : σ := nat.partrec.code.rec_on c
      (z a) (s a) (l a) (r a) (pr a) (co a) (pc a) (rf a) in
    primrec (λ a, F a (c a)) :=
begin
  intros,
  let G₁ : (α × list σ) × ℕ × ℕ → option σ := λ p,
    let a := p.1.1, IH := p.1.2, n := p.2.1, m := p.2.2 in
    (IH.nth m).bind $ λ s,
    (IH.nth m.unpair.1).bind $ λ s₁,
    (IH.nth m.unpair.2).map $ λ s₂,
    cond n.bodd
      (cond n.div2.bodd
        (rf a (of_nat code m) s)
        (pc a (of_nat code m.unpair.1) (of_nat code m.unpair.2) s₁ s₂))
      (cond n.div2.bodd
        (co a (of_nat code m.unpair.1) (of_nat code m.unpair.2) s₁ s₂)
        (pr a (of_nat code m.unpair.1) (of_nat code m.unpair.2) s₁ s₂)),
  have : primrec G₁,
  { refine option_bind (list_nth.comp (snd.comp fst) (snd.comp snd)) _,
    refine option_bind ((list_nth.comp (snd.comp fst)
      (fst.comp $ primrec.unpair.comp (snd.comp snd))).comp fst) _,
    refine option_map ((list_nth.comp (snd.comp fst)
      (snd.comp $ primrec.unpair.comp (snd.comp snd))).comp $ fst.comp fst) _,
    have a := fst.comp (fst.comp $ fst.comp $ fst.comp fst),
    have n := fst.comp (snd.comp $ fst.comp $ fst.comp fst),
    have m := snd.comp (snd.comp $ fst.comp $ fst.comp fst),
    have m₁ := fst.comp (primrec.unpair.comp m),
    have m₂ := snd.comp (primrec.unpair.comp m),
    have s := snd.comp (fst.comp fst),
    have s₁ := snd.comp fst,
    have s₂ := snd,
    exact (nat_bodd.comp n).cond
      ((nat_bodd.comp $ nat_div2.comp n).cond
        (hrf.comp $ a.pair (((primrec.of_nat code).comp m).pair s))
        (hpc.comp $ a.pair (((primrec.of_nat code).comp m₁).pair $
          ((primrec.of_nat code).comp m₂).pair $ s₁.pair s₂)))
      (primrec.cond (nat_bodd.comp $ nat_div2.comp n)
        (hco.comp $ a.pair (((primrec.of_nat code).comp m₁).pair $
          ((primrec.of_nat code).comp m₂).pair $ s₁.pair s₂))
        (hpr.comp $ a.pair (((primrec.of_nat code).comp m₁).pair $
          ((primrec.of_nat code).comp m₂).pair $ s₁.pair s₂))) },
  let G : α → list σ → option σ := λ a IH,
    IH.length.cases (some (z a)) $ λ n,
    n.cases (some (s a)) $ λ n,
    n.cases (some (l a)) $ λ n,
    n.cases (some (r a)) $ λ n,
    G₁ ((a, IH), n, n.div2.div2),
  have : primrec₂ G := (nat_cases
    (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) $
    nat_cases snd (option_some_iff.2 (hs.comp (fst.comp fst))) $
    nat_cases snd (option_some_iff.2 (hl.comp (fst.comp $ fst.comp fst))) $
    nat_cases snd (option_some_iff.2 (hr.comp (fst.comp $ fst.comp $ fst.comp fst)))
    (this.comp $
      ((fst.pair snd).comp $ fst.comp $ fst.comp $ fst.comp $ fst).pair $
      snd.pair $ nat_div2.comp $ nat_div2.comp snd)),
  refine ((nat_strong_rec
    (λ a n, F a (of_nat code n)) this.to₂ $ λ a n, _).comp
    primrec.id $ encode_iff.2 hc).of_eq (λ a, by simp),
  simp,
  iterate 4 {cases n with n, {simp [of_nat_code_eq, of_nat_code]; refl}},
  simp [G], rw [list.length_map, list.length_range],
  let m := n.div2.div2,
  show G₁ ((a, (list.range (n+4)).map (λ n, F a (of_nat code n))), n, m)
    = some (F a (of_nat code (n+4))),
  have hm : m < n + 4, by simp [nat.div2_val, m];
  from lt_of_le_of_lt
    (le_trans (nat.div_le_self _ _) (nat.div_le_self _ _))
    (nat.succ_le_succ (nat.le_add_right _ _)),
  have m1 : m.unpair.1 < n + 4, from lt_of_le_of_lt m.unpair_left_le hm,
  have m2 : m.unpair.2 < n + 4, from lt_of_le_of_lt m.unpair_right_le hm,
  simp [G₁], simp [list.nth_map, list.nth_range, hm, m1, m2],
  change of_nat code (n+4) with of_nat_code (n+4),
  simp [of_nat_code],
  cases n.bodd; cases n.div2.bodd; refl
end

end

section
open computable

/-- Recursion on `nat.partrec.code` is computable. -/
theorem rec_computable {α σ} [primcodable α] [primcodable σ]
  {c : α → code} (hc : computable c)
  {z : α → σ} (hz : computable z)
  {s : α → σ} (hs : computable s)
  {l : α → σ} (hl : computable l)
  {r : α → σ} (hr : computable r)
  {pr : α → code × code × σ × σ → σ} (hpr : computable₂ pr)
  {co : α → code × code × σ × σ → σ} (hco : computable₂ co)
  {pc : α → code × code × σ × σ → σ} (hpc : computable₂ pc)
  {rf : α → code × σ → σ} (hrf : computable₂ rf) :
let PR (a) := λ cf cg hf hg, pr a (cf, cg, hf, hg),
    CO (a) := λ cf cg hf hg, co a (cf, cg, hf, hg),
    PC (a) := λ cf cg hf hg, pc a (cf, cg, hf, hg),
    RF (a) := λ cf hf, rf a (cf, hf),
    F (a : α) (c : code) : σ := nat.partrec.code.rec_on c
      (z a) (s a) (l a) (r a) (PR a) (CO a) (PC a) (RF a) in
    computable (λ a, F a (c a)) :=
begin
  -- TODO(Mario): less copy-paste from previous proof
  intros,
  let G₁ : (α × list σ) × ℕ × ℕ → option σ := λ p,
    let a := p.1.1, IH := p.1.2, n := p.2.1, m := p.2.2 in
    (IH.nth m).bind $ λ s,
    (IH.nth m.unpair.1).bind $ λ s₁,
    (IH.nth m.unpair.2).map $ λ s₂,
    cond n.bodd
      (cond n.div2.bodd
        (rf a (of_nat code m, s))
        (pc a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂)))
      (cond n.div2.bodd
        (co a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂))
        (pr a (of_nat code m.unpair.1, of_nat code m.unpair.2, s₁, s₂))),
  have : computable G₁,
  { refine option_bind (list_nth.comp (snd.comp fst) (snd.comp snd)) _,
    refine option_bind ((list_nth.comp (snd.comp fst)
      (fst.comp $ computable.unpair.comp (snd.comp snd))).comp fst) _,
    refine option_map ((list_nth.comp (snd.comp fst)
      (snd.comp $ computable.unpair.comp (snd.comp snd))).comp $ fst.comp fst) _,
    have a := fst.comp (fst.comp $ fst.comp $ fst.comp fst),
    have n := fst.comp (snd.comp $ fst.comp $ fst.comp fst),
    have m := snd.comp (snd.comp $ fst.comp $ fst.comp fst),
    have m₁ := fst.comp (computable.unpair.comp m),
    have m₂ := snd.comp (computable.unpair.comp m),
    have s := snd.comp (fst.comp fst),
    have s₁ := snd.comp fst,
    have s₂ := snd,
    exact (nat_bodd.comp n).cond
      ((nat_bodd.comp $ nat_div2.comp n).cond
        (hrf.comp a (((computable.of_nat code).comp m).pair s))
        (hpc.comp a (((computable.of_nat code).comp m₁).pair $
          ((computable.of_nat code).comp m₂).pair $ s₁.pair s₂)))
      (computable.cond (nat_bodd.comp $ nat_div2.comp n)
        (hco.comp a (((computable.of_nat code).comp m₁).pair $
          ((computable.of_nat code).comp m₂).pair $ s₁.pair s₂))
        (hpr.comp a (((computable.of_nat code).comp m₁).pair $
          ((computable.of_nat code).comp m₂).pair $ s₁.pair s₂))) },
  let G : α → list σ → option σ := λ a IH,
    IH.length.cases (some (z a)) $ λ n,
    n.cases (some (s a)) $ λ n,
    n.cases (some (l a)) $ λ n,
    n.cases (some (r a)) $ λ n,
    G₁ ((a, IH), n, n.div2.div2),
  have : computable₂ G := (nat_cases
    (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) $
    nat_cases snd (option_some_iff.2 (hs.comp (fst.comp fst))) $
    nat_cases snd (option_some_iff.2 (hl.comp (fst.comp $ fst.comp fst))) $
    nat_cases snd (option_some_iff.2 (hr.comp (fst.comp $ fst.comp $ fst.comp fst)))
    (this.comp $
      ((fst.pair snd).comp $ fst.comp $ fst.comp $ fst.comp $ fst).pair $
      snd.pair $ nat_div2.comp $ nat_div2.comp snd)),
  refine ((nat_strong_rec
    (λ a n, F a (of_nat code n)) this.to₂ $ λ a n, _).comp
    computable.id $ encode_iff.2 hc).of_eq (λ a, by simp),
  simp,
  iterate 4 {cases n with n, {simp [of_nat_code_eq, of_nat_code]; refl}},
  simp [G], rw [list.length_map, list.length_range],
  let m := n.div2.div2,
  show G₁ ((a, (list.range (n+4)).map (λ n, F a (of_nat code n))), n, m)
    = some (F a (of_nat code (n+4))),
  have hm : m < n + 4, by simp [nat.div2_val, m];
  from lt_of_le_of_lt
    (le_trans (nat.div_le_self _ _) (nat.div_le_self _ _))
    (nat.succ_le_succ (nat.le_add_right _ _)),
  have m1 : m.unpair.1 < n + 4, from lt_of_le_of_lt m.unpair_left_le hm,
  have m2 : m.unpair.2 < n + 4, from lt_of_le_of_lt m.unpair_right_le hm,
  simp [G₁], simp [list.nth_map, list.nth_range, hm, m1, m2],
  change of_nat code (n+4) with of_nat_code (n+4),
  simp [of_nat_code],
  cases n.bodd; cases n.div2.bodd; refl
end

end

/--
The interpretation of a `nat.partrec.code` as a partial function.
* `nat.partrec.code.zero`: The constant zero function.
* `nat.partrec.code.succ`: The successor function.
* `nat.partrec.code.left`: Left unpairing of a pair of ℕ (encoded by `nat.mkpair`)
* `nat.partrec.code.right`: Right unpairing of a pair of ℕ (encoded by `nat.mkpair`)
* `nat.partrec.code.pair`: Pairs the outputs of argument codes using `nat.mkpair`.
* `nat.partrec.code.comp`: Composition of two argument codes.
* `nat.partrec.code.prec`: Primitive recursion. Given an argument of the form `nat.mkpair a n`:
  * If `n = 0`, returns `eval cf a`.
  * If `n = succ k`, returns `eval cg (mkpair a (mkpair k (eval (prec cf cg) (mkpair a k))))`
* `nat.partrec.code.rfind'`: Minimization. For `f` an argument of the form `nat.mkpair a m`,
  `rfind' f m` returns the least `a` such that `f a m = 0`, if one exists and `f b m` terminates
  for `b < a`
-/
def eval : code → ℕ →. ℕ
| zero         := pure 0
| succ         := nat.succ
| left         := ↑(λ n : ℕ, n.unpair.1)
| right        := ↑(λ n : ℕ, n.unpair.2)
| (pair cf cg) := λ n, mkpair <$> eval cf n <*> eval cg n
| (comp cf cg) := λ n, eval cg n >>= eval cf
| (prec cf cg) := nat.unpaired (λ a n,
    n.elim (eval cf a) (λ y IH, do i ← IH, eval cg (mkpair a (mkpair y i))))
| (rfind' cf)  := nat.unpaired (λ a m,
    (nat.rfind (λ n, (λ m, m = 0) <$>
      eval cf (mkpair a (n + m)))).map (+ m))

/-- Helper lemma for the evaluation of `prec` in the base case. -/
@[simp] lemma eval_prec_zero (cf cg : code) (a : ℕ) : eval (prec cf cg) (mkpair a 0) = eval cf a :=
by rw [eval, nat.unpaired, nat.unpair_mkpair, nat.elim_zero]

/-- Helper lemma for the evaluation of `prec` in the recursive case. -/
lemma eval_prec_succ (cf cg : code) (a k : ℕ) :
  eval (prec cf cg) (mkpair a (nat.succ k)) =
    do ih <- eval (prec cf cg) (mkpair a k), eval cg (mkpair a (mkpair k ih)) :=
begin
  rw [eval, nat.unpaired, part.bind_eq_bind, nat.unpair_mkpair, nat.elim_succ],
  simp,
end

instance : has_mem (ℕ →. ℕ) code := ⟨λ f c, eval c = f⟩

@[simp] theorem eval_const : ∀ n m, eval (code.const n) m = part.some n
| 0     m := rfl
| (n+1) m := by simp! *

@[simp] theorem eval_id (n) : eval code.id n = part.some n := by simp! [(<*>)]

@[simp] theorem eval_curry (c n x) : eval (curry c n) x = eval c (mkpair n x) :=
by simp! [(<*>)]

theorem const_prim : primrec code.const :=
(primrec.id.nat_iterate (primrec.const zero)
  (comp_prim.comp (primrec.const succ) primrec.snd).to₂).of_eq $
λ n, by simp; induction n; simp [*, code.const, function.iterate_succ']

theorem curry_prim : primrec₂ curry :=
comp_prim.comp primrec.fst $
pair_prim.comp (const_prim.comp primrec.snd) (primrec.const code.id)

theorem curry_inj {c₁ c₂ n₁ n₂} (h : curry c₁ n₁ = curry c₂ n₂) : c₁ = c₂ ∧ n₁ = n₂ :=
⟨by injection h, by { injection h,
                      injection h with h₁ h₂,
                      injection h₂ with h₃ h₄,
                      exact const_inj h₃ }⟩

/--
The $S_n^m$ theorem: There is a computable function, namely `nat.partrec.code.curry`, that takes a
program and a ℕ `n`, and returns a new program using `n` as the first argument.
-/
theorem smn : ∃ f : code → ℕ → code,
  computable₂ f ∧ ∀ c n x, eval (f c n) x = eval c (mkpair n x) :=
⟨curry, primrec₂.to_comp curry_prim, eval_curry⟩

/-- A function is partial recursive if and only if there is a code implementing it. -/
theorem exists_code {f : ℕ →. ℕ} : nat.partrec f ↔ ∃ c : code, eval c = f :=
⟨λ h, begin
  induction h,
  case nat.partrec.zero { exact ⟨zero, rfl⟩ },
  case nat.partrec.succ { exact ⟨succ, rfl⟩ },
  case nat.partrec.left { exact ⟨left, rfl⟩ },
  case nat.partrec.right { exact ⟨right, rfl⟩ },
  case nat.partrec.pair : f g pf pg hf hg
  { rcases hf with ⟨cf, rfl⟩, rcases hg with ⟨cg, rfl⟩,
    exact ⟨pair cf cg, rfl⟩ },
  case nat.partrec.comp : f g pf pg hf hg
  { rcases hf with ⟨cf, rfl⟩, rcases hg with ⟨cg, rfl⟩,
    exact ⟨comp cf cg, rfl⟩ },
  case nat.partrec.prec : f g pf pg hf hg
  { rcases hf with ⟨cf, rfl⟩, rcases hg with ⟨cg, rfl⟩,
    exact ⟨prec cf cg, rfl⟩ },
  case nat.partrec.rfind : f pf hf
  { rcases hf with ⟨cf, rfl⟩,
    refine ⟨comp (rfind' cf) (pair code.id zero), _⟩,
    simp [eval, (<*>), pure, pfun.pure, part.map_id'] },
end, λ h, begin
  rcases h with ⟨c, rfl⟩, induction c,
  case nat.partrec.code.zero { exact nat.partrec.zero },
  case nat.partrec.code.succ { exact nat.partrec.succ },
  case nat.partrec.code.left { exact nat.partrec.left },
  case nat.partrec.code.right { exact nat.partrec.right },
  case nat.partrec.code.pair : cf cg pf pg { exact pf.pair pg },
  case nat.partrec.code.comp : cf cg pf pg { exact pf.comp pg },
  case nat.partrec.code.prec : cf cg pf pg { exact pf.prec pg },
  case nat.partrec.code.rfind' : cf pf { exact pf.rfind' },
end⟩

/--
A modified evaluation for the code which returns an `option ℕ` instead of a `part ℕ`. To avoid
undecidability, `evaln` takes a parameter `k` and fails if it encounters a number ≥ k in the course
of its execution. Other than this, the semantics are the same as in `nat.partrec.code.eval`.
-/
def evaln : ∀ k : ℕ, code → ℕ → option ℕ
| 0     _            := λ m, none
| (k+1) zero         := λ n, guard (n ≤ k) >> pure 0
| (k+1) succ         := λ n, guard (n ≤ k) >> pure (nat.succ n)
| (k+1) left         := λ n, guard (n ≤ k) >> pure n.unpair.1
| (k+1) right        := λ n, guard (n ≤ k) >> pure n.unpair.2
| (k+1) (pair cf cg) := λ n, guard (n ≤ k) >>
  mkpair <$> evaln (k+1) cf n <*> evaln (k+1) cg n
| (k+1) (comp cf cg) := λ n, guard (n ≤ k) >>
  do x ← evaln (k+1) cg n, evaln (k+1) cf x
| (k+1) (prec cf cg) := λ n, guard (n ≤ k) >>
  n.unpaired (λ a n,
  n.cases (evaln (k+1) cf a) $ λ y, do
    i ← evaln k (prec cf cg) (mkpair a y),
    evaln (k+1) cg (mkpair a (mkpair y i)))
| (k+1) (rfind' cf)  := λ n, guard (n ≤ k) >>
  n.unpaired (λ a m, do
  x ← evaln (k+1) cf (mkpair a m),
  if x = 0 then pure m else
  evaln k (rfind' cf) (mkpair a (m+1)))

theorem evaln_bound : ∀ {k c n x}, x ∈ evaln k c n → n < k
| 0     c n x h := by simp [evaln] at h; cases h
| (k+1) c n x h := begin
  suffices : ∀ {o : option ℕ}, x ∈ guard (n ≤ k) >> o → n < k + 1,
  { cases c; rw [evaln] at h; exact this h },
  simpa [(>>)] using nat.lt_succ_of_le
end

theorem evaln_mono : ∀ {k₁ k₂ c n x}, k₁ ≤ k₂ → x ∈ evaln k₁ c n → x ∈ evaln k₂ c n
| 0     k₂     c n x hl h := by simp [evaln] at h; cases h
| (k+1) (k₂+1) c n x hl h := begin
  have hl' := nat.le_of_succ_le_succ hl,
  have : ∀ {k k₂ n x : ℕ} {o₁ o₂ : option ℕ},
    k ≤ k₂ → (x ∈ o₁ → x ∈ o₂) → x ∈ guard (n ≤ k) >> o₁ → x ∈ guard (n ≤ k₂) >> o₂,
  { simp [(>>)], introv h h₁ h₂ h₃, exact ⟨le_trans h₂ h, h₁ h₃⟩ },
  simp at h ⊢,
  induction c with cf cg hf hg cf cg hf hg cf cg hf hg cf hf generalizing x n;
    rw [evaln] at h ⊢; refine this hl' (λ h, _) h,
  iterate 4 {exact h},
  { -- pair cf cg
    simp [(<*>)] at h ⊢,
    exact h.imp (λ a, and.imp (hf _ _) $ Exists.imp $ λ b, and.imp_left (hg _ _)) },
  { -- comp cf cg
    simp at h ⊢,
    exact h.imp (λ a, and.imp (hg _ _) (hf _ _)) },
  { -- prec cf cg
    revert h, simp,
    induction n.unpair.2; simp,
    { apply hf },
    { exact λ y h₁ h₂, ⟨y, evaln_mono hl' h₁, hg _ _ h₂⟩ } },
  { -- rfind' cf
    simp at h ⊢,
    refine h.imp (λ x, and.imp (hf _ _) _),
    by_cases x0 : x = 0; simp [x0],
    exact evaln_mono hl' }
end

theorem evaln_sound : ∀ {k c n x}, x ∈ evaln k c n → x ∈ eval c n
| 0     _ n x h := by simp [evaln] at h; cases h
| (k+1) c n x h := begin
  induction c with cf cg hf hg cf cg hf hg cf cg hf hg cf hf generalizing x n;
    simp [eval, evaln, (>>), (<*>)] at h ⊢; cases h with _ h,
  iterate 4 {simpa [pure, pfun.pure, eq_comm] using h},
  { -- pair cf cg
    rcases h with ⟨y, ef, z, eg, rfl⟩,
    exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩ },
  { --comp hf hg
    rcases h with ⟨y, eg, ef⟩,
    exact ⟨_, hg _ _ eg, hf _ _ ef⟩ },
  { -- prec cf cg
    revert h,
    induction n.unpair.2 with m IH generalizing x; simp,
    { apply hf },
    { refine λ y h₁ h₂, ⟨y, IH _ _, _⟩,
      { have := evaln_mono k.le_succ h₁,
        simp [evaln, (>>)] at this,
        exact this.2 },
      { exact hg _ _ h₂ } } },
  { -- rfind' cf
    rcases h with ⟨m, h₁, h₂⟩,
    by_cases m0 : m = 0; simp [m0] at h₂,
    { exact ⟨0,
       ⟨by simpa [m0] using hf _ _ h₁,
        λ m, (nat.not_lt_zero _).elim⟩,
        by injection h₂ with h₂; simp [h₂]⟩ },
    { have := evaln_sound h₂, simp [eval] at this,
      rcases this with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩,
      refine ⟨ y+1, ⟨by simpa [add_comm, add_left_comm] using hy₁, λ i im, _⟩,
               by simp [add_comm, add_left_comm] ⟩,
      cases i with i,
      { exact ⟨m, by simpa using hf _ _ h₁, m0⟩ },
      { rcases hy₂ (nat.lt_of_succ_lt_succ im) with ⟨z, hz, z0⟩,
        exact ⟨z, by simpa [nat.succ_eq_add_one, add_comm, add_left_comm] using hz, z0⟩ } } }
end

theorem evaln_complete {c n x} : x ∈ eval c n ↔ ∃ k, x ∈ evaln k c n :=
⟨λ h, begin
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ evaln (k+1) c n,
  { exact ⟨k + 1, h⟩ },
  induction c generalizing n x;
    simp [eval, evaln, pure, pfun.pure, (<*>), (>>)] at h ⊢,
  iterate 4 { exact ⟨⟨_, le_rfl⟩, h.symm⟩ },
  case nat.partrec.code.pair : cf cg hf hg
  { rcases h with ⟨x, hx, y, hy, rfl⟩,
    rcases hf hx with ⟨k₁, hk₁⟩, rcases hg hy with ⟨k₂, hk₂⟩,
    refine ⟨max k₁ k₂, _⟩,
    refine ⟨le_max_of_le_left $ nat.le_of_lt_succ $ evaln_bound hk₁,
      _, evaln_mono (nat.succ_le_succ $ le_max_left _ _) hk₁,
      _, evaln_mono (nat.succ_le_succ $ le_max_right _ _) hk₂, rfl⟩ },
  case nat.partrec.code.comp : cf cg hf hg
  { rcases h with ⟨y, hy, hx⟩,
    rcases hg hy with ⟨k₁, hk₁⟩, rcases hf hx with ⟨k₂, hk₂⟩,
    refine ⟨max k₁ k₂, _⟩,
    exact ⟨le_max_of_le_left $ nat.le_of_lt_succ $ evaln_bound hk₁, _,
      evaln_mono (nat.succ_le_succ $ le_max_left _ _) hk₁,
      evaln_mono (nat.succ_le_succ $ le_max_right _ _) hk₂⟩ },
  case nat.partrec.code.prec : cf cg hf hg
  { revert h,
    generalize : n.unpair.1 = n₁, generalize : n.unpair.2 = n₂,
    induction n₂ with m IH generalizing x n; simp,
    { intro, rcases hf h with ⟨k, hk⟩,
      exact ⟨_, le_max_left _ _,
        evaln_mono (nat.succ_le_succ $ le_max_right _ _) hk⟩ },
    { intros y hy hx,
      rcases IH hy with ⟨k₁, nk₁, hk₁⟩, rcases hg hx with ⟨k₂, hk₂⟩,
      refine ⟨(max k₁ k₂).succ, nat.le_succ_of_le $ le_max_of_le_left $
        le_trans (le_max_left _ (mkpair n₁ m)) nk₁, y,
        evaln_mono (nat.succ_le_succ $ le_max_left _ _) _,
        evaln_mono (nat.succ_le_succ $ nat.le_succ_of_le $ le_max_right _ _) hk₂⟩,
      simp [evaln, (>>)],
      exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩ } },
  case nat.partrec.code.rfind' : cf hf
  { rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩,
    suffices : ∃ k, y + n.unpair.2 ∈ evaln (k+1) (rfind' cf)
      (mkpair n.unpair.1 n.unpair.2), {simpa [evaln, (>>)]},
    revert hy₁ hy₂, generalize : n.unpair.2 = m, intros,
    induction y with y IH generalizing m; simp [evaln, (>>)],
    { simp at hy₁, rcases hf hy₁ with ⟨k, hk⟩,
      exact ⟨_, nat.le_of_lt_succ $ evaln_bound hk, _, hk, by simp; refl⟩ },
    { rcases hy₂ (nat.succ_pos _) with ⟨a, ha, a0⟩,
      rcases hf ha with ⟨k₁, hk₁⟩,
      rcases IH m.succ
          (by simpa [nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
          (λ i hi, by simpa [nat.succ_eq_add_one, add_comm, add_left_comm] using
            hy₂ (nat.succ_lt_succ hi))
        with ⟨k₂, hk₂⟩,
      use (max k₁ k₂).succ,
      rw [zero_add] at hk₁,
      use (nat.le_succ_of_le $ le_max_of_le_left $ nat.le_of_lt_succ $ evaln_bound hk₁),
      use a,
      use evaln_mono (nat.succ_le_succ $ nat.le_succ_of_le $ le_max_left _ _) hk₁,
      simpa [nat.succ_eq_add_one, a0, -max_eq_left, -max_eq_right, add_comm, add_left_comm] using
          evaln_mono (nat.succ_le_succ $ le_max_right _ _) hk₂ } }
end, λ ⟨k, h⟩, evaln_sound h⟩

section
open primrec

private def lup (L : list (list (option ℕ))) (p : ℕ × code) (n : ℕ) :=
do l ← L.nth (encode p), o ← l.nth n, o

private lemma hlup : primrec (λ p:_×(_×_)×_, lup p.1 p.2.1 p.2.2) :=
option_bind
  (list_nth.comp fst (primrec.encode.comp $ fst.comp snd))
  (option_bind (list_nth.comp snd $ snd.comp $ snd.comp fst) snd)

private def G (L : list (list (option ℕ))) : option (list (option ℕ)) :=
option.some $
let a := of_nat (ℕ × code) L.length,
    k := a.1, c := a.2 in
(list.range k).map (λ n,
  k.cases none $ λ k',
  nat.partrec.code.rec_on c
    (some 0) -- zero
    (some (nat.succ n))
    (some n.unpair.1)
    (some n.unpair.2)
    (λ cf cg _ _, do
      x ← lup L (k, cf) n,
      y ← lup L (k, cg) n,
      some (mkpair x y))
    (λ cf cg _ _, do
      x ← lup L (k, cg) n,
      lup L (k, cf) x)
    (λ cf cg _ _,
      let z := n.unpair.1 in
      n.unpair.2.cases
        (lup L (k, cf) z)
        (λ y, do
          i ← lup L (k', c) (mkpair z y),
          lup L (k, cg) (mkpair z (mkpair y i))))
    (λ cf _,
      let z := n.unpair.1, m := n.unpair.2 in do
      x ← lup L (k, cf) (mkpair z m),
      x.cases
        (some m)
        (λ _, lup L (k', c) (mkpair z (m+1)))))

private lemma hG : primrec G :=
begin
  have a := (primrec.of_nat (ℕ × code)).comp list_length,
  have k := fst.comp a,
  refine option_some.comp
    (list_map (list_range.comp k) (_ : primrec _)),
  replace k := k.comp fst, have n := snd,
  refine nat_cases k (const none) (_ : primrec _),
  have k := k.comp fst, have n := n.comp fst, have k' := snd,
  have c := snd.comp (a.comp $ fst.comp fst),
  apply rec_prim c
    (const (some 0))
    (option_some.comp (primrec.succ.comp n))
    (option_some.comp (fst.comp $ primrec.unpair.comp n))
    (option_some.comp (snd.comp $ primrec.unpair.comp n)),
  { have L := (fst.comp fst).comp fst,
    have k := k.comp fst, have n := n.comp fst,
    have cf := fst.comp snd,
    have cg := (fst.comp snd).comp snd,
    exact option_bind
      (hlup.comp $ L.pair $ (k.pair cf).pair n)
      (option_map ((hlup.comp $
        L.pair $ (k.pair cg).pair n).comp fst)
        (primrec₂.mkpair.comp (snd.comp fst) snd)) },
  { have L := (fst.comp fst).comp fst,
    have k := k.comp fst, have n := n.comp fst,
    have cf := fst.comp snd,
    have cg := (fst.comp snd).comp snd,
    exact option_bind
      (hlup.comp $ L.pair $ (k.pair cg).pair n)
      (hlup.comp ((L.comp fst).pair $
        ((k.pair cf).comp fst).pair snd)) },
  { have L := (fst.comp fst).comp fst,
    have k := k.comp fst, have n := n.comp fst,
    have cf := fst.comp snd,
    have cg := (fst.comp snd).comp snd,
    have z := fst.comp (primrec.unpair.comp n),
    refine nat_cases
      (snd.comp (primrec.unpair.comp n))
      (hlup.comp $ L.pair $ (k.pair cf).pair z)
      (_ : primrec _),
    have L := L.comp fst, have z := z.comp fst, have y := snd,
    refine option_bind
      (hlup.comp $ L.pair $
        (((k'.pair c).comp fst).comp fst).pair
        (primrec₂.mkpair.comp z y))
      (_ : primrec _),
    have z := z.comp fst, have y := y.comp fst, have i := snd,
    exact hlup.comp ((L.comp fst).pair $
      ((k.pair cg).comp $ fst.comp fst).pair $
      primrec₂.mkpair.comp z $ primrec₂.mkpair.comp y i) },
  { have L := (fst.comp fst).comp fst,
    have k := k.comp fst, have n := n.comp fst,
    have cf := fst.comp snd,
    have z := fst.comp (primrec.unpair.comp n),
    have m := snd.comp (primrec.unpair.comp n),
    refine option_bind
      (hlup.comp $ L.pair $ (k.pair cf).pair (primrec₂.mkpair.comp z m))
      (_ : primrec _),
    have m := m.comp fst,
    exact nat_cases snd (option_some.comp m)
      ((hlup.comp ((L.comp fst).pair $
        ((k'.pair c).comp $ fst.comp fst).pair
        (primrec₂.mkpair.comp (z.comp fst)
          (primrec.succ.comp m)))).comp fst) }
end

private lemma evaln_map (k c n) :
  (((list.range k).nth n).map (evaln k c)).bind (λ b, b) = evaln k c n :=
begin
  by_cases kn : n < k,
  { simp [list.nth_range kn] },
  { rw list.nth_len_le,
    { cases e : evaln k c n, {refl},
      exact kn.elim (evaln_bound e) },
    simpa using kn }
end

/-- The `nat.partrec.code.evaln` function is primitive recursive. -/
theorem evaln_prim : primrec (λ (a : (ℕ × code) × ℕ), evaln a.1.1 a.1.2 a.2) :=
have primrec₂ (λ (_:unit) (n : ℕ),
  let a := of_nat (ℕ × code) n in
  (list.range a.1).map (evaln a.1 a.2)), from
primrec.nat_strong_rec _ (hG.comp snd).to₂ $
  λ _ p, begin
    simp [G],
    rw (_ : (of_nat (ℕ × code) _).snd =
      of_nat code p.unpair.2), swap, {simp},
    apply list.map_congr (λ n, _),
    rw (by simp : list.range p = list.range
      (mkpair p.unpair.1 (encode (of_nat code p.unpair.2)))),
    generalize : p.unpair.1 = k,
    generalize : of_nat code p.unpair.2 = c,
    intro nk,
    cases k with k', {simp [evaln]},
    let k := k'+1, change k'.succ with k,
    simp [nat.lt_succ_iff] at nk,
    have hg : ∀ {k' c' n},
      mkpair k' (encode c') < mkpair k (encode c) →
      lup ((list.range (mkpair k (encode c))).map (λ n,
        (list.range n.unpair.1).map
          (evaln n.unpair.1 (of_nat code n.unpair.2))))
        (k', c') n = evaln k' c' n,
    { intros k₁ c₁ n₁ hl,
      simp [lup, list.nth_range hl, evaln_map, (>>=)] },
    cases c with cf cg cf cg cf cg cf;
      simp [evaln, nk, (>>), (>>=), (<$>), (<*>), pure],
    { cases encode_lt_pair cf cg with lf lg,
      rw [hg (nat.mkpair_lt_mkpair_right _ lf),
          hg (nat.mkpair_lt_mkpair_right _ lg)],
      cases evaln k cf n, {refl},
      cases evaln k cg n; refl },
    { cases encode_lt_comp cf cg with lf lg,
      rw hg (nat.mkpair_lt_mkpair_right _ lg),
      cases evaln k cg n, {refl},
      simp [hg (nat.mkpair_lt_mkpair_right _ lf)] },
    { cases encode_lt_prec cf cg with lf lg,
      rw hg (nat.mkpair_lt_mkpair_right _ lf),
      cases n.unpair.2, {refl},
      simp,
      rw hg (nat.mkpair_lt_mkpair_left _ k'.lt_succ_self),
      cases evaln k' _ _, {refl},
      simp [hg (nat.mkpair_lt_mkpair_right _ lg)] },
    { have lf := encode_lt_rfind' cf,
      rw hg (nat.mkpair_lt_mkpair_right _ lf),
      cases evaln k cf n with x, {refl},
      simp,
      cases x; simp [nat.succ_ne_zero],
      rw hg (nat.mkpair_lt_mkpair_left _ k'.lt_succ_self) }
  end,
(option_bind (list_nth.comp
  (this.comp (const ()) (encode_iff.2 fst)) snd)
  snd.to₂).of_eq $ λ ⟨⟨k, c⟩, n⟩, by simp [evaln_map]

end

section
open partrec computable

theorem eval_eq_rfind_opt (c n) :
  eval c n = nat.rfind_opt (λ k, evaln k c n) :=
part.ext $ λ x, begin
  refine evaln_complete.trans (nat.rfind_opt_mono _).symm,
  intros a m n hl, apply evaln_mono hl,
end

theorem eval_part : partrec₂ eval :=
(rfind_opt (evaln_prim.to_comp.comp
  ((snd.pair (fst.comp fst)).pair (snd.comp fst))).to₂).of_eq $
λ a, by simp [eval_eq_rfind_opt]

/--
Roger's fixed-point theorem: Any total, computable `f` has a fixed point: That is, under the
interpretation given by `nat.partrec.code.eval`, there is a code `c` such that `c` and `f c` have
the same evaluation.
-/
theorem fixed_point
  {f : code → code} (hf : computable f) : ∃ c : code, eval (f c) = eval c :=
let g (x y : ℕ) : part ℕ :=
  eval (of_nat code x) x >>= λ b, eval (of_nat code b) y in
have partrec₂ g :=
  (eval_part.comp ((computable.of_nat _).comp fst) fst).bind
  (eval_part.comp ((computable.of_nat _).comp snd) (snd.comp fst)).to₂,
let ⟨cg, eg⟩ := exists_code.1 this in
have eg' : ∀ a n, eval cg (mkpair a n) = part.map encode (g a n) :=
  by simp [eg],
let F (x : ℕ) : code := f (curry cg x) in
have computable F :=
  hf.comp (curry_prim.comp (primrec.const cg) primrec.id).to_comp,
let ⟨cF, eF⟩ := exists_code.1 this in
have eF' : eval cF (encode cF) = part.some (encode (F (encode cF))),
  by simp [eF],
⟨curry cg (encode cF), funext (λ n,
  show eval (f (curry cg (encode cF))) n = eval (curry cg (encode cF)) n,
  by simp [eg', eF', part.map_id', g])⟩

theorem fixed_point₂
  {f : code → ℕ →. ℕ} (hf : partrec₂ f) : ∃ c : code, eval c = f c :=
let ⟨cf, ef⟩ := exists_code.1 hf in
(fixed_point (curry_prim.comp
  (primrec.const cf) primrec.encode).to_comp).imp $
λ c e, funext $ λ n, by simp [e.symm, ef, part.map_id']

end

end nat.partrec.code
