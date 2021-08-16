/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/
import .decision_nec
import tactic.linarith

/-!
# Decision procedure - sufficient condition and decidability

We give a sufficient condition for a string to be derivable in the MIU language. Together with the
necessary condition, we use this to prove that `derivable` is an instance of `decidable_pred`.

Let `count I st` and `count U st` denote the number of `I`s (respectively `U`s) in `st : miustr`.

We'll show that `st` is derivable if it has the form `M::x` where `x` is a string of `I`s and `U`s
for which `count I x` is congruent to 1 or 2 modulo 3.

To prove this, it suffices to show `derivable M::y` where `y` is any `miustr` consisting only of
`I`s such that the number of `I`s in `y` is `a+3b`, where `a = count I x` and `b = count U x`.
This suffices because Rule 3 permits us to change any string of three consecutive `I`s into a `U`.

As `count I y = (count I x) + 3*(count U x) ≡ (count I x) [MOD 3]`, it suffices to show
`derivable M::z` where `z` is an `miustr` of `I`s such that `count I z` is congruent to
1 or 2 modulo 3.

Let `z` be such an `miustr` and let `c` denote `count I z`, so `c ≡ 1 or 2 [MOD 3]`.
To derive such an `miustr`, it suffices to derive an `miustr` `M::w`, where again w is an
`miustr` of only `I`s with the additional conditions that `count I w` is a power of 2, that
`count I w ≥ c` and that `count I w ≡ c [MOD 3]`.

To see that this suffices, note that we can remove triples of `I`s from the end of `M::w`,
creating `U`s as we go along. Once the number of `I`s equals `m`, we remove `U`s two at a time
until we have no `U`s. The only issue is that we may begin the removal process with an odd number
of `U`s.

Writing `d = count I w`, we see that this happens if and only if `(d-c)/3` is odd.
In this case, we must apply Rule 1 to `z`, prior to removing triples of `I`s. We thereby
introduce an additional `U` and ensure that the final number of `U`s will be even.

## Tags

miu, decision procedure, decidability, decidable_pred, decidable
-/

namespace miu

open miu_atom list nat

/--
We start by showing that an `miustr` `M::w` can be derived, where `w` consists only of `I`s and
where `count I w` is a power of 2.
-/
private lemma der_cons_repeat (n : ℕ) : derivable (M::(repeat I (2^n))) :=
begin
  induction n with k hk,
  { constructor, }, -- base case
  { rw [succ_eq_add_one, pow_add, pow_one 2, mul_two,repeat_add], -- inductive step
    exact derivable.r2 hk, },
end

/-!
## Converting `I`s to `U`s

For any given natural number `c ≡ 1 or 2 [MOD 3]`, we need to show that can derive an `miustr`
`M::w` where `w` consists only of `I`s,  where `d = count I w` is a power of 2, where `d ≥ c` and
where `d ≡ c [MOD 3]`.

Given the above lemmas, the desired result reduces to an arithmetic result, given in the file
`arithmetic.lean`.

We'll use this result to show we can derive an `miustr` of the form `M::z` where `z` is an string
consisting only of `I`s such that `count I z ≡ 1 or 2 [MOD 3]`.

As an intermediate step, we show that derive `z` from `zt`, where `t` is aN `miustr` consisting of
an even number of `U`s and `z` is any `miustr`.
-/

/--
Any number of successive occurrences of `"UU"` can be removed from the end of a `derivable` `miustr`
to produce another `derivable` `miustr`.
-/
lemma der_of_der_append_repeat_U_even {z : miustr} {m : ℕ} (h : derivable (z ++ repeat U (m*2)))
  : derivable z :=
begin
  induction m with k hk,
  { revert h,
    simp only [list.repeat, zero_mul, append_nil, imp_self], },
  { apply hk,
    simp only [succ_mul, repeat_add] at h,
    change repeat U 2 with [U,U] at h,
    rw ←(append_nil (z ++ repeat U (k*2) )),
    apply derivable.r4,
    simp only [append_nil, append_assoc,h], },
end

/-!
In fine-tuning my application of `simp`, I issued the following commend to determine which lemmas
`simp` uses.

`set_option trace.simplify.rewrite true`
-/

/--
We may replace several consecutive occurrences of  `"III"` with the same number of `"U"`s.
In application of the following lemma, `xs` will either be `[]` or `[U]`.
-/
lemma der_cons_repeat_I_repeat_U_append_of_der_cons_repeat_I_append (c k : ℕ)
  (hc : c % 3 = 1 ∨ c % 3 = 2) (xs : miustr) (hder : derivable (M ::(repeat I (c+3*k)) ++ xs)) :
    derivable (M::(repeat I c ++ repeat U k) ++ xs) :=
begin
  revert xs,
  induction k with a ha,
  { simp only [list.repeat, mul_zero, add_zero, append_nil, forall_true_iff, imp_self],},
  { intro xs,
    specialize ha (U::xs),
    intro h₂,
    simp only [succ_eq_add_one, repeat_add], -- We massage the goal
    rw [←append_assoc, ←cons_append],        -- into a form amenable
    change repeat U 1 with [U],             -- to the application of
    rw [append_assoc, singleton_append],     -- ha.
    apply ha,
    apply derivable.r3,
    change [I,I,I] with repeat I 3,
    simp only [cons_append, ←repeat_add],
    convert h₂, },
end

/-!
### Arithmetic

We collect purely arithmetic lemmas: `add_mod2` is used to ensure we have an even number of `U`s
while `le_pow2_and_pow2_eq_mod3` treats the congruence condition modulo 3.
-/
section arithmetic

/--
For every `a`, the number `a + a % 2` is even.
-/
lemma add_mod2 (a : ℕ) : ∃ t, a + a % 2 = t*2 :=
begin
  simp only [mul_comm _ 2], -- write `t*2` as `2*t`
  apply dvd_of_mod_eq_zero, -- it suffices to prove `(a + a % 2) % 2 = 0`
  rw [add_mod, mod_mod, ←two_mul, mul_mod_right],
end

private lemma le_pow2_and_pow2_eq_mod3' (c : ℕ) (x : ℕ) (h : c = 1 ∨ c = 2) :
  ∃ m : ℕ, c + 3*x ≤ 2^m ∧ 2^m % 3 = c % 3 :=
begin
  induction x with k hk,
  { use (c+1),
    cases h with hc hc;
    { rw hc, norm_num }, },
  rcases hk with ⟨g, hkg, hgmod⟩,
  by_cases hp : (c + 3*(k+1) ≤ 2 ^g),
  { use g, exact ⟨hp, hgmod⟩ },
  refine ⟨g + 2, _, _⟩,
  { rw [mul_succ, ←add_assoc, pow_add],
    change 2^2 with (1+3), rw [mul_add (2^g) 1 3, mul_one],
    linarith [hkg, one_le_two_pow g], },
  { rw [pow_add, ←mul_one c],
    exact modeq.mul hgmod rfl }
end

/--
If `a` is 1 or 2 modulo 3, then exists `k` a power of 2 for which `a ≤ k` and `a ≡ k [MOD 3]`.
-/
lemma le_pow2_and_pow2_eq_mod3 (a : ℕ) (h : a % 3 = 1 ∨ a % 3 = 2) :
  ∃ m : ℕ, a ≤ 2^m ∧ 2^m % 3 = a % 3:=
begin
  cases le_pow2_and_pow2_eq_mod3' (a%3) (a/3) h with m hm,
  use m,
  split,
  { convert hm.1, exact (mod_add_div a 3).symm, },
  { rw [hm.2, mod_mod _ 3], },
end

end arithmetic

lemma repeat_pow_minus_append  {m : ℕ} : M :: repeat I (2^m - 1) ++ [I] = M::(repeat I (2^m)) :=
begin
  change [I] with repeat I 1,
  rw [cons_append, ←repeat_add, nat.sub_add_cancel (one_le_pow' m 1)],
end

/--
`der_repeat_I_of_mod3` states that `M::y` is `derivable` if `y` is any `miustr` consisiting just of
`I`s, where `count I y` is 1 or 2 modulo 3.
-/
lemma der_repeat_I_of_mod3 (c : ℕ) (h : c % 3 = 1 ∨ c % 3 = 2):
  derivable (M::(repeat I c)) :=
begin
  -- From `der_cons_repeat`, we can derive the `miustr` `M::w` described in the introduction.
  cases (le_pow2_and_pow2_eq_mod3 c h) with m hm, -- `2^m` will be  the number of `I`s in `M::w`
  have hw₂ : derivable (M::(repeat I (2^m)) ++ repeat U ((2^m -c)/3 % 2)),
  { cases mod_two_eq_zero_or_one ((2^m -c)/3) with h_zero h_one,
    { simp only [der_cons_repeat m, append_nil,list.repeat, h_zero], }, -- `(2^m - c)/3 ≡ 0 [MOD 2]`
    { rw [h_one, ←repeat_pow_minus_append, append_assoc], -- case `(2^m - c)/3 ≡ 1 [MOD 2]`
      apply derivable.r1,
      rw repeat_pow_minus_append,
      exact (der_cons_repeat m), }, },
  have hw₃ : derivable (M::(repeat I c) ++ repeat U ((2^m-c)/3) ++ repeat U ((2^m-c)/3 % 2)),
  { apply der_cons_repeat_I_repeat_U_append_of_der_cons_repeat_I_append c ((2^m-c)/3) h,
    convert hw₂, -- now we must show `c + 3 * ((2 ^ m - c) / 3) = 2 ^ m`
    rw nat.mul_div_cancel',
    { exact nat.add_sub_of_le hm.1 },
    { exact (modeq_iff_dvd' hm.1).mp hm.2.symm } },
  rw [append_assoc, ←repeat_add _ _] at hw₃,
  cases add_mod2 ((2^m-c)/3) with t ht,
  rw ht at hw₃,
  exact der_of_der_append_repeat_U_even hw₃,
end

example (c : ℕ) (h : c % 3 = 1 ∨ c % 3 = 2):
  derivable (M::(repeat I c)) :=
begin
  -- From `der_cons_repeat`, we can derive the `miustr` `M::w` described in the introduction.
  cases (le_pow2_and_pow2_eq_mod3 c h) with m hm, -- `2^m` will be  the number of `I`s in `M::w`
  have hw₂ : derivable (M::(repeat I (2^m)) ++ repeat U ((2^m -c)/3 % 2)),
  { cases mod_two_eq_zero_or_one ((2^m -c)/3) with h_zero h_one,
    { simp only [der_cons_repeat m, append_nil, list.repeat,h_zero], }, -- `(2^m - c)/3 ≡ 0 [MOD 2]`
    { rw [h_one, ←repeat_pow_minus_append, append_assoc], -- case `(2^m - c)/3 ≡ 1 [MOD 2]`
      apply derivable.r1,
      rw repeat_pow_minus_append,
      exact (der_cons_repeat m), }, },
  have hw₃ : derivable (M::(repeat I c) ++ repeat U ((2^m-c)/3) ++ repeat U ((2^m-c)/3 % 2)),
  { apply der_cons_repeat_I_repeat_U_append_of_der_cons_repeat_I_append c ((2^m-c)/3) h,
    convert hw₂, -- now we must show `c + 3 * ((2 ^ m - c) / 3) = 2 ^ m`
    rw nat.mul_div_cancel',
    { exact nat.add_sub_of_le hm.1 },
    { exact (modeq_iff_dvd' hm.1).mp hm.2.symm } },
  rw [append_assoc, ←repeat_add _ _] at hw₃,
  cases add_mod2 ((2^m-c)/3) with t ht,
  rw ht at hw₃,
  exact der_of_der_append_repeat_U_even hw₃,
end

/-!
### `decstr` is a sufficient condition

The remainder of this file sets up the proof that `dectstr en` is sufficent to ensure
`derivable en`. Decidability of `derivable en` is an easy consequence.

The proof proceeds by induction on the `count U` of `en`.

We tackle first the base case of the induction. This requires auxiliary results giving
conditions under which  `count I ys = length ys`.
-/

/--
If an `miustr` has a zero `count U` and contains no `M`, then its `count I` is its length.
-/
lemma count_I_eq_length_of_count_U_zero_and_neg_mem {ys : miustr} (hu : count U ys = 0)
  (hm : M ∉ ys) : count I ys = length ys :=
begin
  induction ys with x xs hxs,
  { refl, },
  { cases x,
    { exfalso, exact hm (mem_cons_self M xs), }, -- case `x = M` gives a contradiction.
    { rw [count_cons, if_pos (rfl), length, succ_eq_add_one, succ_inj'], -- case `x = I`
      apply hxs,
      { simpa only [count], },
      { simp only [mem_cons_iff,false_or] at hm, exact hm, }, },
    { exfalso, simp only [count, countp_cons_of_pos] at hu,  -- case `x = U` gives a contradiction.
      exact succ_ne_zero _ hu, }, },
end

/--
`base_case_suf` is the base case of the sufficiency result.
-/
lemma base_case_suf (en : miustr) (h : decstr en) (hu : count U en = 0) : derivable en :=
begin
  rcases h with ⟨⟨mhead, nmtail⟩, hi ⟩,
  have : en ≠ nil,
  { intro k, simp only [k, count, countp, if_false, zero_mod, zero_ne_one, false_or] at hi,
    contradiction, },
  rcases (exists_cons_of_ne_nil this) with ⟨y,ys,rfl⟩,
  rw head at mhead,
  rw mhead at *,
  suffices  : ∃ c, repeat I c = ys ∧ (c % 3 = 1 ∨ c % 3 = 2),
  { rcases this with ⟨c, hysr, hc⟩,
    rw ←hysr,
    exact der_repeat_I_of_mod3 c hc, },
  { simp only [count] at *,
    use (count I ys),
    refine and.intro _ hi,
    apply repeat_count_eq_of_count_eq_length,
    exact count_I_eq_length_of_count_U_zero_and_neg_mem hu nmtail, },
end

/-!
Before continuing to the proof of the induction step, we need other auxiliary results that
relate to `count U`.
-/
lemma mem_of_count_U_eq_succ {xs : miustr} {k : ℕ} (h : count U xs = succ k) : U ∈ xs :=
begin
  induction xs with z zs hzs,
  { exfalso, rw count at h, contradiction, },
  { simp only [mem_cons_iff],
    cases z,
    repeat -- cases `z = M` and `z=I`
    { right, apply hzs, simp only [count, countp, if_false] at h, rw ←h, refl, },
    { left, refl, }, }, -- case `z = U`
end

lemma eq_append_cons_U_of_count_U_pos {k : ℕ} {zs : miustr} (h : count U zs = succ k) :
∃ (as bs : miustr), (zs = as ++ U :: bs) :=
mem_split (mem_of_count_U_eq_succ h)

/--
`ind_hyp_suf` is the inductive step of the sufficiency result.
 -/
lemma ind_hyp_suf (k : ℕ) (ys : miustr) (hu : count U ys = succ k) (hdec : decstr ys) :
∃ (as bs : miustr), (ys = M::as ++ U:: bs) ∧ (count U (M::as ++ [I,I,I] ++ bs) = k) ∧
  decstr (M::as ++ [I,I,I] ++ bs) :=
begin
  rcases hdec with ⟨⟨mhead,nmtail⟩, hic⟩,
  have : ys ≠ nil,
  { intro k, simp only [k ,count, countp, zero_mod, false_or, zero_ne_one] at hic, contradiction, },
  rcases (exists_cons_of_ne_nil this) with ⟨z,zs,rfl⟩,
  rw head at mhead,
  rw mhead at *,
  simp only [count, countp, cons_append, if_false, countp_append] at *,
  rcases (eq_append_cons_U_of_count_U_pos hu) with ⟨as,bs,hab⟩,
  rw hab at *,
  simp only [countp, cons_append, if_pos, if_false, countp_append] at *,
  use [as,bs],
  apply and.intro rfl (and.intro (succ.inj hu) _),
  split,
  { apply and.intro rfl,
    simp only [tail, mem_append, mem_cons_iff, false_or, not_mem_nil, or_false] at *,
    exact nmtail, },
  { simp only [count, countp, cons_append, if_false, countp_append, if_pos],
    rw [add_right_comm, add_mod_right], exact hic, },
end

/--
`der_of_decstr` states that `derivable en` follows from `decstr en`.
-/
theorem der_of_decstr {en : miustr} (h : decstr en) : derivable en :=
begin
/- The next three lines have the effect of introducing `count U en` as a variable that can be used
 for induction -/
  have hu : ∃ n, count U en = n := exists_eq',
  cases hu with n hu,
  revert en, /- Crucially, we need the induction hypothesis to quantify over `en` -/
  induction n with k hk,
  { exact base_case_suf, },
  { intros ys hdec hus,
    rcases ind_hyp_suf k ys hus hdec with ⟨as, bs, hyab, habuc, hdecab⟩,
    have h₂ : derivable (M::as ++ [I,I,I] ++ bs) := hk hdecab habuc,
    rw hyab,
    exact derivable.r3 h₂, },
end

/-!
### Decidability of `derivable`
-/

/--
Finally, we have the main result, namely that `derivable` is a decidable predicate.
-/
instance : decidable_pred derivable :=
λ en, decidable_of_iff _ ⟨der_of_decstr, decstr_of_der⟩

/-!
By decidability, we can automatically determine whether any given `miustr` is `derivable`.
-/

example : ¬(derivable "MU") :=
dec_trivial

example : derivable "MUIUIUIIIIIUUUIUII" :=
dec_trivial

end miu
