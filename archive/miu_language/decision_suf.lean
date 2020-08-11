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

Let `count I st` and `count U st` denote the number of `I`s (respectively `U`s) in `st : miustr`.

We'll show that an MIU string is `derivable` if it has the form `M::x` where `x` is a string of `I`s
and `U`s where `count I x` is congruent to 1 or 2 modulo 3.

To prove this, it suffices to be able to show that one can derive an `miustr` `M::y` where `y` is
an `miustr` consisting only of `I`s and where the number of `I`s in `y` is `a+3b` where
`a = count I x` and `b = count U x`.
This suffices because Rule 3 permits us to change any string of three consecutive `I`s into a `U`.

Note `count I y = (count I x) + 3(count U x) ≡ count I x [MOD 3]`. Thus, it suffices to show we can
generate any `miustr` `M::z` where `z` is an `miustr` of `I`s such that `count I z` is congruent to
1 or 2 modulo 3.

Let `z` be such an `miustr` and let `c` denote `count I z`, so `c ≡ 1 or 2 [MOD 3]`.
To derive such an `miustr`, it suffices to derive an `miustr` `M::w`, where again w is an
`miustr` of only `I`s with the additional conditions that `count I w` is a power of 2, that
`count I w ≥ c` and that `count I w ≡ c [MOD 3]`.

To see that this suffices, note that we can remove triples of `I`s from the end of `M::w`,
creating `U`s as we go along. Once the number of `I`s equals `m`, we just remove `U`s two at a time
until we have no `U`s. The only issue is that we may not have an even number of `U`s!
Writing `d = count I w`, we see that this happens if and only if `(d-c)/3` is odd.
To avoid this, we apply Rule 1 to `z` in this case, prior to removing triples of `I`s.
By applying Rule 1, we add an additional `U` so the final number of `U`s will be even.
-/

namespace miu

open miu_atom
open list
open nat

/--
We start by showing that an `miustr` `M::w` can be derived, where `w` consists only of `I`s and
where `count I w` is a power of 2.
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
`I`s, where `count I y` is 1 or 2 modulo 3.
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



/-!
### The main result

The remainder of this file sets up the proof that `derivable en` follows from `decstr en`.

The proof proceeds by induction on the `count U` of `en`.

We tackle first the base case of the induction. This requires auxiliary results that give
conditions under which  `count I ys = length ys`.
-/


/--
If the `count I` of `ys : miustr` equals its length, then `ys` consists entirely of `I`s
-/
lemma eq_of_countI_eq_length  {ys : miustr} (h : count I ys = length ys) :
  ys = repeat I (count I ys) :=
begin
  have h₂ : repeat I (count I ys) <+ ys,
    exact le_count_iff_repeat_sublist.mp (le_refl _),
  have h₃ : length (repeat I (count I ys)) = length ys,
    rwa length_repeat,
  exact (eq_of_sublist_of_length_eq h₂ h₃).symm,
end


/--
If an `miustr` has a zero `count U` and contains no `M`, then its `count I` is its length.
-/
lemma countI_eq_length_of_countU_zero_and_neg_mem {ys : miustr} (hu : count U ys = 0)
  (hm : M ∉ ys) : count I ys = length ys :=
begin
  induction ys with x xs hxs, {
    refl,
  }, {
    cases x, { -- case `x = M` gives a contradiction.
      exfalso, exact hm (mem_cons_self M xs),
    }, { -- case `x = I`.
      rw [count_cons, if_pos (rfl),length,succ_eq_add_one,succ_inj'],
      apply hxs, {
        simpa only [count],
      },
      simp only [mem_cons_iff,false_or] at hm,
      exact hm,
    }, -- case `x = U` gives a (different) contradiction.
    exfalso, simp only [count,countp_cons_of_pos] at hu,
    exact succ_ne_zero _ hu,
  }
end

/--
`base_case_suf` is the base case of our main result.
-/
lemma base_case_suf (en : miustr) (h : decstr en) (hu : count U en = 0) : derivable en :=
begin
  cases h with hm hi, /- `hm : goodm en, hi` : congruence condition in `count I` -/
  rcases hm with ⟨ys, hys, hnm⟩, /- `hys : en = M :: ys`, `hnm :  M ∉ ys` -/
  suffices  : ∃ c, ys = repeat I c ∧ (c % 3 = 1 ∨ c % 3 = 2), {
    rcases this with ⟨c, hysr, hc⟩,
    rw [hys, hysr],
    exact der_rep_I_of_mod3  c hc,
  },
  simp only [count U,hys] at hu, -- gives `count U = 0`
  use (count I ys),
  split, {
    apply eq_of_countI_eq_length,
    exact countI_eq_length_of_countU_zero_and_neg_mem hu hnm, -- show `count I ys = length ys`
  },
  rw hys at hi, -- replace `en` with `M::ys` in `hi`
  simp only [count] at hi,
  exact hi,
end


/-!
Before continuing to the proof of the induction step, we need other auxiliary results that
relate to `count U`.
-/


lemma mem_of_countU_eq_succ {xs : miustr} {k : ℕ} (h : count U xs = succ k) : U ∈ xs :=
begin
  induction xs with z zs hzs, {
    exfalso, rw count at h, contradiction,
  },
  simp only [mem_cons_iff],
  cases z, repeat { -- cases `z = M` and `z=I`
    right, apply hzs, simp only [count,countp,if_false] at h, rw ←h, refl,
  },
  left, refl, -- case `z = U`
end



lemma split_at_first_U {k : ℕ} {ys : miustr} (hm : goodm ys) (h : count U ys = succ k) :
∃ (as bs : miustr), (ys = M:: as ++ U :: bs) :=
begin
  rcases hm with ⟨xs, hm, _⟩,
  simp only [hm,cons_inj,cons_append], -- it suffices to prove `xs = as ++ U :: bs`
  apply mem_split,
  apply mem_of_countU_eq_succ,
    simp only [hm,count,countp,if_false] at h, rw ←h, refl,
end


/--
`ind_hyp_suf` is the inductive step of our main theorem.
 -/
lemma ind_hyp_suf (k : ℕ) (ys : miustr) (hu : count U ys = succ k) (hdec : decstr ys) :
∃ (as bs : miustr), (ys = M::as ++ U:: bs) ∧ (count U (M::as ++ [I,I,I] ++ bs) = k) ∧
  decstr (M::as ++ [I,I,I] ++ bs) :=
begin
  rcases hdec with ⟨hm,hic⟩,
  rcases split_at_first_U hm hu with ⟨as,bs,hab⟩,
  use as, use bs,
  split,
    { exact hab, },
    split, { -- show `count U (M::as ++ [I,I,I] ++ bs) = k`
      rw hab at hu,
      rw [count_append,count_append] at *, simp [count U] at *,
      apply succ.inj, rw [←hu],
    },
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
    }, { -- now demonstrate the `count I` is correct.
      rw hab at hzs, rw hzs at hic,
      suffices : count I (M::as ++ [I,I,I] ++ bs) = count I (M::as ++ [U]++bs) + 3, {
        rw this, simp only [hic,cons_append,nil_append,add_mod_right,append_assoc],
      },
      rw hzs at hu,
      repeat {rw count_append at *}, simp [count] at *,
      norm_num, rw [add_assoc,add_assoc], congr' 1, rw add_comm,
    }
end

/--
`der_of_decstr` is our main result. It shows `derivable en` follows from  `decstr en`.
-/
theorem der_of_decstr  (en : miustr) (h : decstr en) : derivable en :=
begin
/- The next three lines have the effect of introducing `count U en` as a variable that can be used
 for induction -/
  have hu : ∃ n, count U en = n := exists_eq',
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
