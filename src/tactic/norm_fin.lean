/-
Copyright (c) 2021 Yakov Pechersky All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Mario Carneiro
-/

import tactic.norm_num

/-!
# `norm_fin`

This file defines functions for dealing with `fin n` numbers as expressions.

## Main definitions

* `fin.mk_numeral` embeds a `fin n` as a numeral expression into a type supporting the needed
  operations. It does not need a tactic state.
* `fin.reflect` specializes `fin.mk_numeral` to `fin (n + 1)`.
* `expr.of_fin` behaves like `fin.mk_numeral`, but uses the tactic state to infer the needed
  structure on the target type.

* `expr.to_fin` evaluates a normal numeral expression as a `fin n`.
* `expr.eval_fin` evaluates a numeral expression with arithmetic operations as a `fin n`.

* 'norm_fin.eval' is a `norm_num` plugin for normalizing `k` where `k` are numerals,
optionally preceded by `fin.succ` or `fin.cast_succ`.

-/

namespace tactic
namespace norm_fin
open norm_num

def normalize_fin (n : ℕ) (a : fin n) (b : ℕ) := a.1 = b % n
def normalize_fin_lt (n : ℕ) (a : fin n) (b : ℕ) := a.1 = b

theorem normalize_fin_lt.coe {n} {a : fin n} {b : ℕ} (h : normalize_fin_lt n a b) : ↑a = b := h

theorem normalize_fin_iff {n} [fact (0 < n)] {a b} :
  normalize_fin n a b ↔ a = fin.of_nat' b :=
iff.symm (fin.eq_iff_veq _ _)

theorem normalize_fin_lt.mk {n a b n'} (hn : n = n')
  (h : normalize_fin n a b) (h2 : b < n') : normalize_fin_lt n a b :=
h.trans $ nat.mod_eq_of_lt $ by rw hn; exact h2

theorem normalize_fin_lt.lt {n a b} (h : normalize_fin_lt n a b) : b < n :=
by rw ← h.coe; exact a.2

theorem normalize_fin_lt.of {n a b} (h : normalize_fin_lt n a b) : normalize_fin n a b :=
h.trans $ eq.symm $ nat.mod_eq_of_lt h.lt

theorem normalize_fin.zero (n) : normalize_fin (n+1) 0 0 := refl _
theorem normalize_fin_lt.zero (n) : normalize_fin_lt (n+1) 0 0 := refl _
theorem normalize_fin.one (n) : normalize_fin (n+1) 1 1 := refl _
theorem normalize_fin.add {n} {a b : fin n} {a' b' c' : ℕ}
  (ha : normalize_fin n a a') (hb : normalize_fin n b b')
  (h : a' + b' = c') : normalize_fin n (a + b) c' :=
by simp only [normalize_fin, ← h] at *; rw [nat.add_mod, ← ha, ← hb, fin.add_def]
theorem normalize_fin.mul {n} {a b : fin n} {a' b' c' : ℕ}
  (ha : normalize_fin n a a') (hb : normalize_fin n b b')
  (h : a' * b' = c') : normalize_fin n (a * b) c' :=
by simp only [normalize_fin, ← h] at *; rw [nat.mul_mod, ← ha, ← hb, fin.mul_def]
theorem normalize_fin.bit0 {n} {a : fin n} {a' : ℕ}
  (h : normalize_fin n a a') : normalize_fin n (bit0 a) (bit0 a') := h.add h rfl
theorem normalize_fin.bit1 {n} {a : fin (n+1)} {a' : ℕ}
  (h : normalize_fin (n+1) a a') : normalize_fin (n+1) (bit1 a) (bit1 a') :=
h.bit0.add (normalize_fin.one _) rfl

theorem normalize_fin_lt.succ {n} {a : fin n} {a' b : ℕ}
  (h : normalize_fin_lt n a a') (e : a' + 1 = b) : normalize_fin_lt n.succ (fin.succ a) b :=
by simpa [normalize_fin_lt, ← e] using h

theorem normalize_fin_lt.cast_lt {n m} {a : fin m} {ha} {a' : ℕ}
  (h : normalize_fin_lt m a a') : normalize_fin_lt n (fin.cast_lt a ha) a' :=
by simpa [normalize_fin_lt] using h

theorem normalize_fin_lt.cast_le {n m} {nm} {a : fin m} {a' : ℕ}
  (h : normalize_fin_lt m a a') : normalize_fin_lt n (fin.cast_le nm a) a' :=
by simpa [normalize_fin_lt] using h

theorem normalize_fin_lt.cast {n m} {nm} {a : fin m} {a' : ℕ}
  (h : normalize_fin_lt m a a') : normalize_fin_lt n (fin.cast nm a) a' :=
by simpa [normalize_fin_lt] using h

theorem normalize_fin.cast {n m} {nm} {a : fin m} {a' : ℕ}
  (h : normalize_fin m a a') : normalize_fin n (fin.cast nm a) a' :=
by convert ← normalize_fin_lt.cast h

theorem normalize_fin_lt.cast_add {n m} {a : fin n} {a' : ℕ}
  (h : normalize_fin_lt n a a') : normalize_fin_lt (n + m) (fin.cast_add m a) a' :=
by simpa [normalize_fin_lt] using h

theorem normalize_fin_lt.cast_succ {n} {a : fin n} {a' : ℕ}
  (h : normalize_fin_lt n a a') : normalize_fin_lt (n+1) (fin.cast_succ a) a' :=
normalize_fin_lt.cast_add h

theorem normalize_fin_lt.add_nat {n m m'} (hm : m = m') {a : fin n} {a' b : ℕ}
  (h : normalize_fin_lt n a a') (e : a' + m' = b) :
  normalize_fin_lt (n+m) (@fin.add_nat n m a) b :=
by simpa [normalize_fin_lt, ← e, ← hm] using h

theorem normalize_fin_lt.nat_add {n m n'} (hn : n = n') {a : fin m} {a' b : ℕ}
  (h : normalize_fin_lt m a a') (e : n' + a' = b) :
  normalize_fin_lt (n+m) (@fin.nat_add n m a) b :=
by simpa [normalize_fin_lt, ← e, ← hn] using h

theorem normalize_fin.reduce {n} {a : fin n} {n' a' b k nk : ℕ}
  (hn : n = n') (h : normalize_fin n a a') (e1 : n' * k = nk) (e2 : nk + b = a') :
  normalize_fin n a b :=
by rwa [← e2, ← e1, ← hn, normalize_fin, add_comm, nat.add_mul_mod_self_left] at h

theorem normalize_fin_lt.reduce {n} {a : fin n} {n' a' b k nk : ℕ}
  (hn : n = n') (h : normalize_fin n a a') (e1 : n' * k = nk) (e2 : nk + b = a') (hl : b < n') :
  normalize_fin_lt n a b :=
normalize_fin_lt.mk hn (h.reduce hn e1 e2) hl

theorem normalize_fin.eq {n} {a b : fin n} {c : ℕ}
  (ha : normalize_fin n a c) (hb : normalize_fin n b c) : a = b := fin.eq_of_veq $ ha.trans hb.symm
theorem normalize_fin.lt {n} {a b : fin n} {a' b' : ℕ}
  (ha : normalize_fin n a a') (hb : normalize_fin_lt n b b') (h : a' < b') : a < b :=
by have ha' := normalize_fin_lt.mk rfl ha (h.trans hb.lt); rwa [← hb.coe, ← ha'.coe] at h
theorem normalize_fin.le {n} {a b : fin n} {a' b' : ℕ}
  (ha : normalize_fin n a a') (hb : normalize_fin_lt n b b') (h : a' ≤ b') : a ≤ b :=
by have ha' := normalize_fin_lt.mk rfl ha (h.trans_lt hb.lt); rwa [← hb.coe, ← ha'.coe] at h

meta inductive fin_result | new | fail | evaled (nn : ℕ) (n' : expr) (p : expr)

meta def fin_result.get (n : expr) : fin_result → tactic (ℕ × expr × expr)
| fin_result.new := do
  (n', p) ← or_refl_conv norm_num.derive n,
  nn ← n'.to_nat,
  pure (nn, n', p)
| fin_result.fail := failed
| (fin_result.evaled nn n' p) := pure (nn, n', p)

meta def fin_result.mk : option (ℕ × expr × expr) → fin_result
| none := fin_result.fail
| (some (nn, n', p)) := fin_result.evaled nn n' p

@[derive [monad, alternative]]
meta def eval_fin_m (α : Type) : Type :=
state_t (instance_cache × fin_result) tactic α

@[inline] meta def eval_fin_m.lift {α} (m : tactic α) : eval_fin_m α :=
⟨λ ⟨ic, r⟩, do a ← m, pure (a, ic, r)⟩

meta instance {α} : has_coe (tactic α) (eval_fin_m α) := ⟨eval_fin_m.lift⟩

@[inline] meta def eval_fin_m.lift_ic {α}
  (m : instance_cache → tactic (instance_cache × α)) : eval_fin_m α :=
⟨λ ⟨ic, r⟩, do (ic, a) ← m ic, pure (a, ic, r)⟩

@[inline] meta def eval_fin_m.reset {α} (m : eval_fin_m α) : eval_fin_m (fin_result × α) :=
⟨λ ⟨ic, r'⟩, do (a, ic, r) ← m.run ⟨ic, fin_result.new⟩, pure ((r, a), ic, r')⟩

@[inline] meta def eval_fin_m.eval_n (n : expr) : eval_fin_m (ℕ × expr × expr) :=
⟨λ ⟨ic, r⟩, do np@(nn, n', p) ← fin_result.get n r, pure (np, ic, fin_result.evaled nn n' p)⟩

@[inline] meta def eval_fin_m.try_eval_n (n : expr) : eval_fin_m (option (ℕ × expr × expr)) :=
⟨λ ⟨ic, r⟩, do o ← try_core (fin_result.get n r), pure (o, ic, fin_result.mk o)⟩

@[inline] meta def eval_fin_m.run {α} (m : eval_fin_m α) : tactic α :=
do ic ← mk_instance_cache `(ℕ), (a, _) ← state_t.run m (ic, fin_result.new), pure a

meta inductive match_fin_result
| zero (n : expr)
| one (n : expr)
| add (n a b : expr)
| mul (n a b : expr)
| bit0 (n a : expr)
| bit1 (n a : expr)
| succ (n a : expr)
| cast_lt (n m a h : expr)
| cast_le (n m h a : expr)
| cast (n m h a : expr)
| cast_add (n m a : expr)
| cast_succ (n a : expr)
| add_nat (n m a : expr)
| nat_add (n m a : expr)

section
open match_fin_result
meta def match_fin_coe_fn (a : expr) : expr → option match_fin_result
| `(@fin.cast_le %%n %%m %%h) := some (cast_le n m h a)
| `(@fin.cast %%m %%n %%h) := some (cast n m h a)
| `(@fin.cast_add %%n %%m) := some (cast_add n m a)
| `(@fin.cast_succ %%n) := some (cast_succ n a)
| `(@fin.add_nat %%n %%m) := some (add_nat n m a)
| `(@fin.nat_add %%n %%m) := some (nat_add n m a)
| _ := none

meta def match_fin : expr → option match_fin_result
| `(@has_zero.zero ._ (@fin.has_zero %%n)) := some (zero n)
| `(@has_one.one ._ (@fin.has_one %%n)) := some (one n)
| `(@has_add.add (fin %%n) ._ %%a %%b) := some (add n a b)
| `(@has_mul.mul (fin %%n) ._ %%a %%b) := some (mul n a b)
| `(@_root_.bit0 (fin %%n) ._ %%a) := some (bit0 n a)
| `(@_root_.bit1 ._ (@fin.has_one %%n) ._ %%a) := some (bit1 n a)
| `(@fin.succ %%n %%a) := some (succ n a)
| `(@fin.cast_lt %%n %%m %%a %%h) := some (cast_lt n m a h)
| (expr.app `(@coe_fn ._ ._ %%f) a) := match_fin_coe_fn a f
| _ := none
end

meta def reduce_fin' : bool → expr → expr → expr × expr → eval_fin_m (expr × expr)
| lt n a (a', pa) := do
  (nn, n', pn) ← eval_fin_m.eval_n n,
  na ← expr.to_nat a',
  if na < nn then
    if lt then do
      p ← eval_fin_m.lift_ic (λ ic, prove_lt_nat ic a' n'),
      pure (a', `(@normalize_fin_lt.mk).mk_app [n, a, a', n', pn, pa, p])
    else pure (a', pa)
  else
    let nb := na % nn, nk := (na - nb) / nn in
    eval_fin_m.lift_ic $ λ ic, do
      (ic, k) ← ic.of_nat nk,
      (ic, b) ← ic.of_nat nb,
      (ic, nk, pe1) ← prove_mul_nat ic n' k,
      (ic, pe2) ← prove_add_nat ic nk b a',
      if lt then do
        (ic, p) ← prove_lt_nat ic b n',
        pure (ic, b,
          `(@normalize_fin_lt.reduce).mk_app [n, a, n', a', b, k, nk, pn, pa, pe1, pe2, p])
      else pure (ic, b,
          `(@normalize_fin.reduce).mk_app [n, a, n', a', b, k, nk, pn, pa, pe1, pe2])

meta def eval_fin_lt' (eval_fin : expr → eval_fin_m (expr × expr)) :
  expr → expr → eval_fin_m (expr × expr)
| n a := do
  e ← match_fin a,
  match e with
  | match_fin_result.succ n a := do
    (_, a', pa) ← (eval_fin_lt' n a).reset,
    (b, pb) ← eval_fin_m.lift_ic (λ ic, prove_succ' ic a'),
    pure (b, `(@normalize_fin_lt.succ).mk_app [n, a, a', b, pa, pb])
  | match_fin_result.cast_lt _ m a h := do
    (_, a', pa) ← (eval_fin_lt' m a).reset,
    pure (a', `(@normalize_fin_lt.cast_lt).mk_app [n, m, a, h, a', pa])
  | match_fin_result.cast_le _ m nm a := do
    (_, a', pa) ← (eval_fin_lt' m a).reset,
    pure (a', `(@normalize_fin_lt.cast_le).mk_app [n, m, nm, a, a', pa])
  | match_fin_result.cast m _ nm a := do
    (_, a', pa) ← (eval_fin_lt' m a).reset,
    pure (a', `(@normalize_fin_lt.cast).mk_app [n, m, nm, a, a', pa])
  | match_fin_result.cast_add n m a := do
    (_, a', pa) ← (eval_fin_lt' m a).reset,
    pure (a', `(@normalize_fin_lt.cast_add).mk_app [n, m, a, a', pa])
  | match_fin_result.cast_succ n a := do
    (_, a', pa) ← (eval_fin_lt' n a).reset,
    pure (a', `(@normalize_fin_lt.cast_succ).mk_app [n, a, a', pa])
  | match_fin_result.add_nat n m a := do
    (_, a', pa) ← (eval_fin_lt' n a).reset,
    (m', pm) ← or_refl_conv norm_num.derive m,
    (b, pb) ← eval_fin_m.lift_ic (λ ic, prove_add_nat' ic a' m'),
    pure (b, `(@normalize_fin_lt.add_nat).mk_app [n, m, m', pm, a, a', b, pa, pb])
  | match_fin_result.nat_add n m a := do
    (_, a', pa) ← (eval_fin_lt' m a).reset,
    (n', pn) ← or_refl_conv norm_num.derive n,
    (b, pb) ← eval_fin_m.lift_ic (λ ic, prove_add_nat' ic n' a'),
    pure (b, `(@normalize_fin_lt.nat_add).mk_app [n, m, n', pn, a, a', b, pa, pb])
  | _ := do
    (_, n', pn) ← eval_fin_m.eval_n n,
    (a', pa) ← eval_fin a >>= reduce_fin' tt n a,
    p ← eval_fin_m.lift_ic (λ ic, prove_lt_nat ic a' n'),
    pure (a', `(@normalize_fin_lt.mk).mk_app [n, a, a', n', pn, pa, p])
  end

meta def get_fin_type (a : expr) : tactic expr :=
do `(fin %%n) ← infer_type a, pure n

meta def eval_fin : expr → eval_fin_m (expr × expr)
| a := do
  m ← match_fin a,
  match m with
  | match_fin_result.zero n := pure (`(0 : ℕ), `(normalize_fin.zero).mk_app [n])
  | match_fin_result.one n := pure (`(1 : ℕ), `(normalize_fin.one).mk_app [n])
  | match_fin_result.add n a b := do
    (a', pa) ← eval_fin a,
    (b', pb) ← eval_fin b,
    (c, pc) ← eval_fin_m.lift_ic (λ ic, prove_add_nat' ic a' b'),
    pure (c, `(@normalize_fin.add).mk_app [n, a, b, a', b', c, pa, pb, pc])
  | match_fin_result.mul n a b := do
    (a', pa) ← eval_fin a,
    (b', pb) ← eval_fin b,
    (c, pc) ← eval_fin_m.lift_ic (λ ic, prove_mul_nat ic a' b'),
    pure (c, `(@normalize_fin.mul).mk_app [n, a, b, a', b', c, pa, pb, pc])
  | match_fin_result.bit0 n a := do
    (a', pa) ← eval_fin a,
    pure (`(@bit0 ℕ _).mk_app [a'], `(@normalize_fin.bit0).mk_app [n, a, a', pa])
  | match_fin_result.bit1 n a := do
    (a', pa) ← eval_fin a,
    pure (`(@bit1 ℕ _ _).mk_app [a'], `(@normalize_fin.bit1).mk_app [n, a, a', pa])
  | match_fin_result.cast m n nm a := do
    (_, a', pa) ← (eval_fin a).reset,
    pure (a', `(@normalize_fin.cast).mk_app [n, m, nm, a, a', pa])
  | _ := do
    n ← get_fin_type a,
    (a', pa) ← eval_fin_lt' eval_fin n a,
    pure (a', `(@normalize_fin_lt.of).mk_app [n, a, a', pa])
  end

meta def eval_fin_lt : expr → expr → eval_fin_m (expr × expr) := eval_fin_lt' eval_fin

meta def reduce_fin (lt : bool) (n a : expr) : eval_fin_m (expr × expr) :=
eval_fin a >>= reduce_fin' lt n a

meta def prove_lt_fin' : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr
| n a b a' b' := do
  (a', pa) ← reduce_fin' ff n a a',
  (b', pb) ← reduce_fin' tt n b b',
  p ← eval_fin_m.lift_ic (λ ic, prove_lt_nat ic a' b'),
  pure (`(@normalize_fin.lt).mk_app [n, a, b, a', b', pa, pb, p])

meta def prove_le_fin' : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr
| n a b a' b' := do
  (a', pa) ← reduce_fin' ff n a a',
  (b', pb) ← reduce_fin' tt n b b',
  p ← eval_fin_m.lift_ic (λ ic, prove_le_nat ic a' b'),
  pure (`(@normalize_fin.le).mk_app [n, a, b, a', b', pa, pb, p])

meta def prove_eq_fin' : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr
| n a b (a', pa) (b', pb) :=
  if a' =ₐ b' then do
    pure (`(@normalize_fin.eq).mk_app [n, a, b, a', pa, pb])
  else do
    (a', pa) ← reduce_fin' ff n a (a', pa),
    (b', pb) ← reduce_fin' ff n b (b', pb),
    guard (a' =ₐ b'),
    pure (`(@normalize_fin.eq).mk_app [n, a, b, a', pa, pb])

meta def eval_prove_fin
  (f : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr)
  (a b : expr) : tactic expr :=
do n ← get_fin_type a, eval_fin_m.run $ eval_fin a >>= λ a', eval_fin b >>= f n a b a'

meta def prove_eq_fin : expr → expr → tactic expr := eval_prove_fin prove_eq_fin'
meta def prove_lt_fin : expr → expr → tactic expr := eval_prove_fin prove_lt_fin'
meta def prove_le_fin : expr → expr → tactic expr := eval_prove_fin prove_le_fin'

section
open norm_num.match_numeral_result

/-- Given expressions `n` and `m` such that `n` is definitionally equal to `m.succ`, and
a natural numeral `a`, proves `(b, ⊢ normalize_fin n b a)`, where `n` and `m` are both used
in the construction of the numeral `b : fin n`. -/
meta def mk_fin_numeral (n m : expr) : expr → option (expr × expr)
| a := match match_numeral a with
  | zero := some (
    expr.app `(@has_zero.zero (fin %%n)) `(@fin.has_zero %%m),
    expr.app `(normalize_fin.zero) m)
  | one := some (
    expr.app `(@has_one.one (fin %%n)) `(@fin.has_one %%m),
    expr.app `(normalize_fin.one) m)
  | bit0 a := do
    (a', p) ← mk_fin_numeral a,
    some (`(bit0 %%a' : fin %%n), `(@normalize_fin.bit0).mk_app [n, a', a, p])
  | bit1 a := do
    (a', p) ← mk_fin_numeral a,
    some (
      `(@_root_.bit1 (fin %%n)).mk_app [`(@fin.has_one %%m), `(@fin.has_add %%n), a'],
      `(@normalize_fin.bit1).mk_app [m, a', a, p])
  | _ := none
  end
end

meta def eval_rel {α} (a b : expr)
  (f : expr → expr × expr → expr × expr → ℕ → ℕ → eval_fin_m α) :
  tactic α :=
do n ← get_fin_type a,
  eval_fin_m.run $ do
    (nn, n', pn) ← eval_fin_m.eval_n n,
    (a', pa) ← eval_fin a,
    (b', pb) ← eval_fin b,
    na ← eval_fin_m.lift a'.to_nat,
    nb ← eval_fin_m.lift b'.to_nat,
    f n (a', pa) (b', pb) (na % nn) (nb % nn)

@[norm_num] meta def eval_ineq : expr → tactic (expr × expr)
| `(%%a < %%b) := eval_rel a b $ λ n a' b' na nb,
  if na < nb then do
    p ← prove_lt_fin' n a b a' b',
    true_intro p
  else do
    p ← prove_le_fin' n b a b' a',
    eval_fin_m.lift_ic $ λ ic, do
      (ic, p) ← ic.mk_app ``not_lt_of_ge [a, b, p],
      p ← false_intro p,
      pure (ic, p)
| `(%%a ≤ %%b) := eval_rel a b $ λ n a' b' na nb,
  if na ≤ nb then do
    p ← prove_le_fin' n a b a' b',
    true_intro p
  else do
    p ← prove_lt_fin' n b a b' a',
    eval_fin_m.lift_ic $ λ ic, do
      (ic, p) ← ic.mk_app ``not_le_of_gt [a, b, p],
      p ← false_intro p,
      pure (ic, p)
| `(%%a = %%b) := eval_rel a b $ λ n a' b' na nb,
  if na = nb then do
    p ← prove_eq_fin' n a b a' b',
    true_intro p
  else do
    p ← (if na < nb then do
      p ← prove_lt_fin' n a b a' b',
      eval_fin_m.lift_ic $ λ ic, ic.mk_app ``ne_of_lt [a, b, p]
    else do
      p ← prove_lt_fin' n b a b' a',
      eval_fin_m.lift_ic $ λ ic, ic.mk_app ``ne_of_gt [a, b, p]),
    false_intro p
| `(%%a > %%b) := mk_app ``has_lt.lt [b, a] >>= eval_ineq
| `(%%a ≥ %%b) := mk_app ``has_le.le [b, a] >>= eval_ineq
| `(%%a ≠ %%b) := eval_rel a b $ λ n a' b' na nb,
  if na = nb then do
    p ← prove_eq_fin' n a b a' b',
    ↑(mk_app ``not_not_intro [p] >>= false_intro)
  else do
    p ← (if na < nb then do
      p ← prove_lt_fin' n a b a' b',
      eval_fin_m.lift_ic $ λ ic, ic.mk_app ``ne_of_lt [a, b, p]
    else do
      p ← prove_lt_fin' n b a b' a',
      eval_fin_m.lift_ic $ λ ic, ic.mk_app ``ne_of_gt [a, b, p]),
    true_intro p
| _ := failed

meta def as_numeral (n e : expr) : eval_fin_m (option ℕ) :=
match e.to_nat with
| none := pure none
| some ne := do
  o ← eval_fin_m.try_eval_n n,
  pure $ match o with
  | none := some ne
  | some (nn, _) := if ne < nn then some ne else none
  end
end

/--
A `norm_num` plugin for normalizing `(k : fin n)` where `k` is numeral.
It also handles `fin.succ k` and `fin.cast_succ k`.

```
example : (5 : fin 7) = fin.succ (fin.succ 3) := by norm_num
```
-/
meta def eval_fin_num (a : expr) : tactic (expr × expr) :=
do n ← get_fin_type a,
  eval_fin_m.run $ do
    as_numeral n a >>= (λ o, guardb o.is_none),
    (a', pa) ← eval_fin a,
    (a', pa) ← reduce_fin' ff n a (a', pa) <|> pure (a', pa),
    (nm + 1, _) ← eval_fin_m.eval_n n | failure,
    m' ← eval_fin_m.lift_ic (λ ic, ic.of_nat nm),
    n' ← eval_fin_m.lift_ic (λ ic, ic.of_nat (nm+1)),
    (b, pb) ← mk_fin_numeral n' m' a',
    pure (b, `(@normalize_fin.eq).mk_app [n, a, b, a', pa, pb])

end norm_fin


namespace interactive
open interactive interactive.types

meta def norm_fin (hs : parse simp_arg_list) : tactic unit :=
try (simp_top_down tactic.norm_fin.eval_fin_num) >> try (norm_num hs (loc.ns [none]))

end interactive
end tactic
