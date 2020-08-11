/-
Copyright (c) 2020 Gihan Marasingha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gihan Marasingha
-/
import .decision_nec
import tactic.linarith
import .arithmetic

/-!
# Decision procedure - sufficient condition

We give a sufficient condition for a string to be derivable in the MIU language.

Let `icount st` and `ucount st` denote the number of `I`s (respectively `U`s) in `st : miustr`.

We'll show that an MIU string is `derivable` if it has the form `M::x` where `x` is a string of `I`s
and `U`s where `icount x` is congruent to 1 or 2 modulo 3.

To prove this, it suffices to be able to show that one can derive an `miustr` `M::y` where `y` is
an `miustr` consisting only of `I`s and where the number of `I`s in `y` is `a+3b` where
`a = icount x` and `b = ucount x`.
This suffices because Rule 3 permits us to change any string of three consecutive `I`s into a `U`.

Note `icount y = (icount x) + 3(ucount x) ≡ icount x [MOD 3]`. Thus, it suffices to show we can
generate any `miustr` `M::z` where `z` is an `miustr` of `I`s such that `icount z` is congruent to
1 or 2 modulo 3.

Let `z` be such an `miustr` and let `c` denote `icount z`, so `c ≡ 1 or 2 [MOD 3]`.
To derive such an `miustr`, it suffices to derive an `miustr` `M::w`, where again w is an
`miustr` of only `I`s with the additional conditions that `icount w` is a power of 2, that
`icount w ≥ c` and that `icount w ≡ c [MOD 3]`.

To see that this suffices, note that we can remove triples of `I`s from the end of `M::w`,
creating `U`s as we go along. Once the number of `I`s equals `m`, we just remove `U`s two at a time
until we have no `U`s. The only issue is that we may not have an even number of `U`s!
Writing `d = icount w`, we see that this happens if and only if `(d-c)/3` is odd.
To avoid this, we apply Rule 1 to `z` in this case, prior to removing triples of `I`s.
By applying Rule 1, we add an additional `U` so the final number of `U`s will be even.
-/

namespace miu

open miu_atom
open list
open nat

/--
We start by showing that an `miustr` `M::w` can be derived, where `w` consists only of `I`s and
where `icount w` is a power of 2.
-/
private lemma pow2str (n : ℕ) : derivable (M::(repeat I (2^n))) :=
begin
  induction n with k hk, {
    constructor, /- base case -/
  }, { /- Start of induction step -/
    have : repeat I (2^k.succ) = repeat I (2^k) ++ repeat I (2^k),
    calc repeat I (2^k.succ) = repeat I (2^k*2) : by congr' 1
                         ... = repeat I (2^k) ++ repeat I (2^k) : by simp only [repeat_add,mul_two],
    rw this,
    exact derivable.r2 hk,
  }
end


/-!
## Converting `I`s to `U`s

For any given natural number `c ≡ 1 or 2 [MOD 3]`, we need to show that can derive an `miustr`
`M::w` where `w` consists only of `I`s,  where `d = icount w` is a power of 2, where `d ≥ c` and
where `d ≡ c [MOD 3]`.

Given the above lemmas, the desired result reduces to an arithmetic result, given in the file
`arithmetic.lean`.

We'll use this result to show we can derive an `miustr` of the form `M::z` where `z` is an string
consisting only of `I`s such that `icount z ≡ 1 or 2 [MOD 3]`.

As an intermediate step, we show that derive `z` from `zt`, where `t` is aN `miustr` consisting of
an even number of `U`s and `z` is any `miustr`.
-/

/--
Any number of successive occurrences of `"UU"` can be removed from the end of a `derivable` `miustr`
to produce another `derivable` `miustr`.
-/
lemma remove_UUs {z : miustr} {m : ℕ} (h : derivable (z ++ repeat U (m*2)))
  : derivable z :=
begin
  induction m with k hk, { /- base case for induction on `m` -/
    revert h,
    simp only [list.repeat,zero_mul,append_nil, imp_self], -- or simp by itself!
  }, { /- inductive step -/
    apply hk,
    simp only [succ_mul,repeat_add] at h,
    change repeat U 2 with [U,U] at h,
    rw ←(append_nil (z ++ repeat U (k*2) )),
    apply derivable.r4,
    simp only [append_nil,append_assoc,h],
  }
end


/-!
The following option is incredibly useful for determining which lemmas are used by simp.

set_option trace.simplify.rewrite true
-/


/--
We may replace several consecutive occurrences of  `"III"` with the same number of `"U"`s.
In application of the following lemma, `xs` will either be `[]` or `[U]`.
-/
lemma i_to_u (c k : ℕ) (hc : c % 3 = 1 ∨ c % 3 = 2)
  (xs : miustr) (hder : derivable (M ::(repeat I (c+3*k)) ++ xs)) :
    derivable (M::(repeat I c ++ repeat U k) ++ xs) :=
begin
  revert xs,
  induction k with a ha, {
    simp only [list.repeat,mul_zero,add_zero,append_nil, forall_true_iff,imp_self],
  }, {
    intro xs,
    specialize ha (U::xs),
    intro h₂,
    simp only [succ_eq_add_one,repeat_add], -- We massage the goal
    rw [←append_assoc,←cons_append],        -- into a form amenable
    change repeat U 1 with [U],             -- to the application of
    rw [append_assoc,singleton_append],     -- ha.
    apply ha,
    apply derivable.r3,
    change [I,I,I] with repeat I 3,
    simp only [cons_append,←repeat_add],
    convert h₂,
  }
end


/--
A simple arithmetic result.
-/
lemma add_mod2 (a : ℕ) : ∃ t, a + a % 2 = t*2 :=
begin
  simp only [mul_comm _ 2], -- write `t*2` as `2*t`
  apply dvd_of_mod_eq_zero, -- it suffices to prove `(a + a % 2) % 2 = 0`
  rw [add_mod,mod_mod,←two_mul,mul_mod_right],
end



lemma rep_pow_minus_append  {m : ℕ} : M:: repeat I (2^m - 1) ++ [I] = M::(repeat I (2^m)) :=
begin
  calc
    M:: repeat I (2^m-1) ++ [I] = M::repeat I (2^m-1) ++ repeat I 1 : by simp
                        ... = M::repeat I ( (2^m-1) + 1) : by simp [repeat_add]
                        ... = M::repeat I (2^m) : by rw nat.sub_add_cancel (one_le_pow' m 1)
end


/--
`der_rep_I_of_mod3` states that `M::y` is `derivable` if `y` is any `miustr` consisiting just of
`I`s, where `icount y` is 1 or 2 modulo 3.
-/
lemma der_rep_I_of_mod3 (c : ℕ) (h : c % 3 = 1 ∨ c % 3 = 2):
  derivable (M::(repeat I c)) :=
begin
  -- From pow2str, we can derive the `miustr` `M::w` described in the introduction.
  cases (mod12pow c h) with m hm, -- `2^m` will be  the number of `I`s in the string `M::w`
  have hw₂ : derivable (M::(repeat I (2^m)) ++ repeat U ((2^m -c)/3 % 2)),
    cases mod_two_eq_zero_or_one ((2^m -c)/3) with h_zero h_one, {
      simp only [pow2str m,append_nil,list.repeat,h_zero] }, -- case `(2^m - c)/3 ≡ 0 [MOD 2]`
      rw [h_one,←rep_pow_minus_append, append_assoc], -- case `(2^m - c)/3 ≡ 1 [MOD 2]`
      apply derivable.r1,
      rw rep_pow_minus_append,
      exact (pow2str m),
  have hw₃ : derivable (M::(repeat I c) ++ repeat U ((2^m-c)/3) ++ repeat U ((2^m-c)/3 % 2)),
    apply i_to_u c ((2^m-c)/3),
      exact h, /- `c` is 1 or 2 (mod 3) -/
      convert hw₂, -- now we must show `c + 3 * ((2 ^ m - c) / 3) = 2 ^ m`
      rw nat.mul_div_cancel',
      exact add_sub_of_le hm.1,
      exact (modeq.modeq_iff_dvd' hm.1).mp hm.2.symm,
  rw [append_assoc, ←repeat_add _ _] at hw₃,
  cases add_mod2 ((2^m-c)/3) with t ht,
  rw ht at hw₃,
  exact remove_UUs hw₃,
end


/--
`ucount st` is the number of `U`s in `st : miustr`/
-/
def ucount : miustr → ℕ
| [] := 0
| (U::cs) := 1 + ucount cs
| (_::cs) := ucount cs

/--
`ucount` is additive with respect to `append`.
-/
lemma ucountappend (a b : miustr) :
  ucount (a ++ b) = ucount a + ucount b :=
begin
  induction a with ha hax haxs,
    simp only [ucount,nil_append,zero_add],
    cases ha;
      simp only [ucount, haxs, add_assoc,cons_append],
end


/-!
### The main result

The remainder of this file sets up the proof that `derivable en` follows from `decstr en`.

The proof proceeds by induction on the `ucount` of `en`.

We tackle first the base case of the induction. This requires auxiliary results: one is a proof of
`icount ys ≤ length ys`. Two others give conditions under which  `icount ys = length ys`.
-/

/--
The `icount` of an `miustr` is at most its length.
-/
lemma icount_lt {ys : miustr} : icount ys ≤ length ys :=
begin
  induction ys with x xs hxs, {
    simp only [icount,length],
  }, {
    cases x;
      {simp only [icount,length], linarith}
  }
end

/--
If the `icount` of `ys : miustr` equals its length, then `ys` consists entirely of `I`s
-/
lemma eq_of_icount_eq_length  {ys : miustr} (h : icount ys = length ys) :
  ys = repeat I (icount ys) :=
begin
  induction ys with x xs hxs, {
    simp only [icount,list.repeat],
  } , {
    have : icount xs ≤ length xs := icount_lt,
    cases x, swap, { -- swap bring case `x = I` to the fore
      rw h,
      have : icount xs = xs.length,
        rw [icount,length,add_comm] at h,
        exact add_right_cancel h,
      rw hxs this,
      simp,
    }, repeat  { /- cases where `x = M` or `x = U` -/
      rw [icount,length] at h,
      exfalso,
      linarith,
    }
  }
end

/--
If an `miustr` has a zero `ucount` and contains no `M`, then its `icount` is its length.
-/
lemma icount_eq_length_of_ucount_zero_and_neg_mem {ys : miustr} (hu : ucount ys = 0) (hm : M ∉ ys) :
  icount ys = length ys :=
begin
  induction ys with x xs hxs, {
    simp [icount],
  }, {
    cases x, { /- case `x = M` gives a contradiction -/
      exfalso, exact hm (mem_cons_self M xs),
    }, { /- case `x = I` -/
      rw [icount,length,add_comm],
      rw succ_inj',
      apply hxs,
        { rwa ucount at hu },
        exact not_mem_of_not_mem_cons hm,
    }, { /- case `x = U` gives a (different) contradiction -/
      exfalso,
      rw ucount at hu, linarith,
    },
  }
end


/--
`base_case_suf` is the base case of our main result.
-/
lemma base_case_suf (en : miustr) (h : decstr en) (hu : ucount en = 0) : derivable en :=
begin
  cases h with hm hi, /- `hm : goodm en, hi` : congruence condition in `icount` -/
  rcases hm with ⟨ys, hys, hnm⟩, /- `hys : en = M :: ys`, `hnm :  M ∉ ys` -/
  suffices  : ∃ c, ys = repeat I c ∧ (c % 3 = 1 ∨ c % 3 = 2), {
    rcases this with ⟨c, hysr, hc⟩,
    rw [hys, hysr],
    exact der_rep_I_of_mod3  c hc,
  },
  simp only [ucount,hys] at hu, -- gives `ucount = 0`
  use (icount ys),
  split, {
    apply eq_of_icount_eq_length,
    exact icount_eq_length_of_ucount_zero_and_neg_mem hu hnm, -- show `icount ys = length ys`
  },
  rw hys at hi, -- replace `en` with `M::ys` in `hi`
  simp only [icount] at hi,
  exact hi,
end


/-!
Before continuing to the proof of the induction step, we need other auxiliary results that
relate to `ucount`.
-/


lemma in_of_ucount_eq_succ {xs : miustr} {k : ℕ} (h : ucount xs = succ k) : U ∈ xs :=
begin
  induction xs with z zs hzs, {
    exfalso, rw ucount at h, contradiction, -- base case
  }, { -- induction step
    simp only [mem_cons_iff],
    cases z, repeat { -- deal equally with the cases `z = M` and `z = I`
      rw ucount at h,
      right,
      exact hzs h,
    }, {  -- the case `z = U`
      left, refl,
    }
  }
end


lemma split_at_first_U {k : ℕ} {ys : miustr} (hm : goodm ys) (h : ucount ys = succ k) :
∃ (as bs : miustr), (ys = M:: as ++ U :: bs) :=
begin
  rcases hm with ⟨xs, hm, _⟩,
  rw hm,
  simp only [cons_inj,cons_append], -- it suffices to prove `xs = as ++ U :: bs`
  have : ucount ys = ucount xs,
    rw [hm,ucount],
  rw this at h,
  apply mem_split,
  exact in_of_ucount_eq_succ h,
end


/--
`ind_hyp_suf` is the inductive step of our main theorem.
 -/
lemma ind_hyp_suf (k : ℕ) (ys : miustr) (hu : ucount ys = succ k) (hdec : decstr ys) :
∃ (as bs : miustr), (ys = M::as ++ U:: bs) ∧ (ucount (M::as ++ [I,I,I] ++ bs) = k) ∧
  decstr (M::as ++ [I,I,I] ++ bs) :=
begin
  rcases hdec with ⟨hm,hic⟩,
  rcases split_at_first_U hm hu with ⟨as,bs,hab⟩,
  use as, use bs,
  split,
    { exact hab, },
    split, -- show `ucount (M::as ++ [I,I,I] ++ bs) = k`
      rw hab at hu,
      rw [ucountappend,ucountappend] at *, simp [ucount] at *,
      apply succ.inj, rw [←hu], simp only [succ_eq_add_one,add_comm,add_assoc],
    rcases hm with ⟨zs,hzs,hmnze⟩,
    simp only [cons_inj,cons_append,hzs] at hab, -- `zs = as ++ U :: bs`
    simp only [hab,mem_append,mem_cons_iff,false_or] at hmnze,
    push_neg at hmnze, -- we have `M ∉ as ∧ M ∉ bs`.
    -- split `decstr (M::as ++ [I,I,I] ++ bs)`
    split, { -- first split `goodm (M::as ++ [I,I,I] ++ bs)`
      constructor, simp [cons_inj],
      split,
        refl, -- now we prove `M ∉ as ++ [I,I,I] ++ bs`
      apply not_mem_append, exact hmnze.left,
      simp only [mem_cons_iff,false_or], exact hmnze.right,
    }, { -- now demonstrate the `icount` is correct.
      rw hab at hzs, rw hzs at hic,
      suffices : icount (M::as ++ [I,I,I] ++ bs) = icount (M::as ++ [U]++bs) + 3, {
        rw this, simp only [hic,cons_append,nil_append,add_mod_right,append_assoc],
      },
      rw hzs at hu,
      repeat {rw icountappend at *}, simp [icount] at *,
      norm_num, simp only [add_comm,add_assoc],
    }
end


/--
`der_of_decstr` is our main result. It shows `derivable en` follows from  `decstr en`.
-/
theorem der_of_decstr  (en : miustr) (h : decstr en) : derivable en :=
begin
/- The next three lines have the effect of introducing `ucount en` as a variable that can be used
 for induction -/
  have hu : ∃ n, ucount en = n := exists_eq',
  cases hu with n hu,
  revert en, /- Crucially, we need the induction hypothesis to quantify over `en` -/
  induction n with k hk, {
    apply base_case_suf; assumption
  }, {
  intros ys hdec hus,
  rcases ind_hyp_suf k ys hus hdec with ⟨as,bs,hyab,habuc,hdecab⟩,
  have h₂ : derivable (M::as ++ [I,I,I] ++ bs) :=
    hk (M::as ++ [I,I,I] ++ bs) hdecab habuc,
  rw hyab,
  exact derivable.r3 h₂,
}
end

example  (en : miustr) (h : decstr en) : derivable en :=
begin
/- The next three lines have the effect of introducing `ucount en` as a variable that can be used
 for induction -/
  have hu : ∃ n, ucount en = n := exists_eq',
  cases hu with n hu,
  revert en, /- Crucially, we need the induction hypothesis to quantify over `en` -/
  induction n with k hk, {
    apply base_case_suf; assumption
  }, {
  intros ys hdec hus,
  rcases ind_hyp_suf k ys hus hdec with ⟨as,bs,hyab,habuc,hdecab⟩,
  have h₂ : derivable (M::as ++ [I,I,I] ++ bs) :=
    hk (M::as ++ [I,I,I] ++ bs) hdecab habuc,
  rw hyab,
  exact derivable.r3 h₂,
}
end



end miu
