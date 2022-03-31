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

* `tactic.norm_fin.eval_ineq` is a `norm_num` plugin for normalizing equalities and inequalities of
  type `fin n`.

* `tactic.interactive.norm_fin` is a standalone tactic like `norm_num` for normalizing `fin n`
  expressions anywhere in the goal.

-/

namespace tactic
namespace norm_fin
open norm_num

/-- `normalize_fin n a b` means that `a : fin n` is equivalent to `b : ℕ` in the modular sense -
that is, `↑a ≡ b (mod n)`. This is used for translating the algebraic operations: addition,
multiplication, zero and one, which use modulo for reduction. -/
def normalize_fin (n : ℕ) (a : fin n) (b : ℕ) := a.1 = b % n

/-- `normalize_fin_lt n a b` means that `a : fin n` is equivalent to `b : ℕ` in the embedding
sense - that is, `↑a = b`. This is used for operations that treat `fin n` as the subset
`{0, ..., n-1}` of `ℕ`. For example, `fin.succ : fin n → fin (n+1)` is thought of as the successor
function, but it does not lift to a map `zmod n → zmod (n+1)`; this addition only makes sense if
the input is strictly less than `n`.

`normalize_fin_lt n a b` is equivalent to `normalize_fin n a b ∧ b < n`. -/
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

theorem normalize_fin.zero (n) : normalize_fin (n+1) 0 0 := by { rw normalize_fin, norm_num }
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

/-- The monad for the `norm_fin` internal tactics. The state consists of an instance cache for `ℕ`,
and a tuple `(nn, n', p)` where `p` is a proof of `n = n'` and `nn` is `n` evaluated to a natural
number. (`n` itself is implicit.)  It is in an `option` because it is lazily initialized - for many
`n` we will never need this information, and indeed eagerly computing it would make some reductions
fail spuriously if `n` is not a numeral. -/
@[derive [monad, alternative]]
meta def eval_fin_m (α : Type) : Type :=
state_t (instance_cache × option (ℕ × expr × expr)) tactic α

/-- Lifts a tactic into the `eval_fin_m` monad. -/
@[inline] meta def eval_fin_m.lift {α} (m : tactic α) : eval_fin_m α :=
⟨λ ⟨ic, r⟩, do a ← m, pure (a, ic, r)⟩

meta instance {α} : has_coe (tactic α) (eval_fin_m α) := ⟨eval_fin_m.lift⟩

/-- Lifts an `instance_cache` tactic into the `eval_fin_m` monad. -/
@[inline] meta def eval_fin_m.lift_ic {α}
  (m : instance_cache → tactic (instance_cache × α)) : eval_fin_m α :=
⟨λ ⟨ic, r⟩, do (ic, a) ← m ic, pure (a, ic, r)⟩

/-- Evaluates a monadic action with a fresh `n` cache, and restore the old cache on completion of
the action. This is used when evaluating a tactic in the context of a different `n` than the parent
context. For example if we are evaluating `fin.succ a`, then `a : fin n` and
`fin.succ a : fin (n+1)`, so the parent cache will be about `n+1` and we need a separate cache for
`n`. -/
@[inline] meta def eval_fin_m.reset {α} (m : eval_fin_m α) : eval_fin_m α :=
⟨λ ⟨ic, r⟩, do (a, ic, _) ← m.run ⟨ic, none⟩, pure (a, ic, r)⟩

/-- Given `n`, returns a tuple `(nn, n', p)` where `p` is a proof of `n = n'` and `nn` is `n`
evaluated to a natural number. The result of the evaluation is cached for future references.
Future calls to this function must use the same value of `n`, unless it is in a sub-context
created by `eval_fin_m.reset`. -/
meta def eval_fin_m.eval_n (n : expr) : eval_fin_m (ℕ × expr × expr) :=
⟨λ ⟨ic, r⟩, match r with
  | none := do
    (n', p) ← or_refl_conv norm_num.derive n,
    nn ← n'.to_nat,
    let np := (nn, n', p),
    pure (np, ic, some np)
  | some np := pure (np, ic, some np)
  end⟩

/-- Run an `eval_fin_m` action with a new cache and discard the cache after evaluation. -/
@[inline] meta def eval_fin_m.run {α} (m : eval_fin_m α) : tactic α :=
do ic ← mk_instance_cache `(ℕ), (a, _) ← state_t.run m (ic, none), pure a

/-- The expression constructors recognized by the `eval_fin` evaluator. This is used instead of a
direct expr pattern match because expr pattern matches generate very large terms under the
hood so going via an intermediate inductive type like this is more efficient. -/
meta inductive match_fin_result
| zero (n : expr)            -- `(0 : fin (n+1))`
| one (n : expr)             -- `(1 : fin (n+1))`
| add (n a b : expr)         -- `(a + b : fin n)`
| mul (n a b : expr)         -- `(a * b : fin n)`
| bit0 (n a : expr)          -- `(bit0 a : fin n)`
| bit1 (n a : expr)          -- `(bit1 a : fin (n+1))`
| succ (n a : expr)          -- `(fin.succ a : fin n.succ)`
| cast_lt (n m i h : expr)   -- `(fin.cast_lt (i : fin m) (h : i.val < n) : fin n)`
| cast_le (n m h a : expr)   -- `(fin.cast_le (h : n ≤ m) (a : fin n) : fin m)`
| cast (n m h a : expr)      -- `(fin.cast_le (h : n = m) (a : fin n) : fin m)`
| cast_add (n m a : expr)    -- `(fin.cast_add m (a : fin n) : fin (n + m))`
| cast_succ (n a : expr)     -- `(fin.cast_succ (a : fin n) : fin (n + 1))`
| add_nat (n m a : expr)     -- `(fin.add_nat m (a : fin n) : fin (n + m))`
| nat_add (n m a : expr)     -- `(fin.nat_add n (a : fin m) : fin (n + m))`

section
open match_fin_result
/-- Match a fin expression of the form `(coe_fn f a)` where `f` is some fin function. Several fin
functions are written this way: for example `cast_le : n ≤ m → fin n ↪o fin m` is not actually a
function but rather an order embedding with a coercion to a function. -/
meta def match_fin_coe_fn (a : expr) : expr → option match_fin_result
| `(@fin.cast_le %%n %%m %%h) := some (cast_le n m h a)
| `(@fin.cast %%m %%n %%h) := some (cast n m h a)
| `(@fin.cast_add %%n %%m) := some (cast_add n m a)
| `(@fin.cast_succ %%n) := some (cast_succ n a)
| `(@fin.add_nat %%n %%m) := some (add_nat n m a)
| `(@fin.nat_add %%n %%m) := some (nat_add n m a)
| _ := none

/-- Match a fin expression to a `match_fin_result`, for easier pattern matching in the
evaluator. -/
meta def match_fin : expr → option match_fin_result
| `(@has_zero.zero ._ (@fin.has_zero %%n)) := some (zero n)
| `(@has_one.one ._ (@fin.has_one %%n)) := some (one n)
| `(@has_add.add (fin %%n) ._ %%a %%b) := some (add n a b)
| `(@has_mul.mul (fin %%n) ._ %%a %%b) := some (mul n a b)
| `(@_root_.bit0 (fin %%n) ._ %%a) := some (bit0 n a)
| `(@_root_.bit1 ._ (@fin.has_one %%n) ._ %%a) := some (bit1 n a)
| `(@fin.succ %%n %%a) := some (succ n a)
| `(@fin.cast_lt %%n %%m %%a %%h) := some (cast_lt n m a h)
| (expr.app `(@coe_fn ._ ._ ._ %%f) a) := match_fin_coe_fn a f
| _ := none
end

/-- `reduce_fin lt n a (a', pa)` expects that `pa : normalize_fin n a a'` where `a'`
is a natural numeral, and produces `(b, pb)` where `pb : normalize_fin n a b` if `lt` is false, or
`pb : normalize_fin_lt n a b` if `lt` is true. In either case, `b` will be chosen to be less than
`n`, but if `lt` is true then we also prove it. This requires that `n` can be evaluated to a
numeral. -/
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

/-- `eval_fin_lt' eval_fin n a` expects that `a : fin n`, and produces `(b, p)` where
`p : normalize_fin_lt n a b`. (It is mutually recursive with `eval_fin` which is why it takes the
function as an argument.) -/
meta def eval_fin_lt' (eval_fin : expr → eval_fin_m (expr × expr)) :
  expr → expr → eval_fin_m (expr × expr)
| n a := do
  e ← match_fin a,
  match e with
  | match_fin_result.succ n a := do
    (a', pa) ← (eval_fin_lt' n a).reset,
    (b, pb) ← eval_fin_m.lift_ic (λ ic, prove_succ' ic a'),
    pure (b, `(@normalize_fin_lt.succ).mk_app [n, a, a', b, pa, pb])
  | match_fin_result.cast_lt _ m a h := do
    (a', pa) ← (eval_fin_lt' m a).reset,
    pure (a', `(@normalize_fin_lt.cast_lt).mk_app [n, m, a, h, a', pa])
  | match_fin_result.cast_le _ m nm a := do
    (a', pa) ← (eval_fin_lt' m a).reset,
    pure (a', `(@normalize_fin_lt.cast_le).mk_app [n, m, nm, a, a', pa])
  | match_fin_result.cast m _ nm a := do
    (a', pa) ← (eval_fin_lt' m a).reset,
    pure (a', `(@normalize_fin_lt.cast).mk_app [n, m, nm, a, a', pa])
  | match_fin_result.cast_add n m a := do
    (a', pa) ← (eval_fin_lt' m a).reset,
    pure (a', `(@normalize_fin_lt.cast_add).mk_app [n, m, a, a', pa])
  | match_fin_result.cast_succ n a := do
    (a', pa) ← (eval_fin_lt' n a).reset,
    pure (a', `(@normalize_fin_lt.cast_succ).mk_app [n, a, a', pa])
  | match_fin_result.add_nat n m a := do
    (a', pa) ← (eval_fin_lt' n a).reset,
    (m', pm) ← or_refl_conv norm_num.derive m,
    (b, pb) ← eval_fin_m.lift_ic (λ ic, prove_add_nat' ic a' m'),
    pure (b, `(@normalize_fin_lt.add_nat).mk_app [n, m, m', pm, a, a', b, pa, pb])
  | match_fin_result.nat_add n m a := do
    (a', pa) ← (eval_fin_lt' m a).reset,
    (n', pn) ← or_refl_conv norm_num.derive n,
    (b, pb) ← eval_fin_m.lift_ic (λ ic, prove_add_nat' ic n' a'),
    pure (b, `(@normalize_fin_lt.nat_add).mk_app [n, m, n', pn, a, a', b, pa, pb])
  | _ := do
    (_, n', pn) ← eval_fin_m.eval_n n,
    (a', pa) ← eval_fin a >>= reduce_fin' tt n a,
    p ← eval_fin_m.lift_ic (λ ic, prove_lt_nat ic a' n'),
    pure (a', `(@normalize_fin_lt.mk).mk_app [n, a, a', n', pn, pa, p])
  end

/-- Get `n` such that `a : fin n`. -/
meta def get_fin_type (a : expr) : tactic expr := do `(fin %%n) ← infer_type a, pure n

/-- Given `a : fin n`, `eval_fin a` returns `(b, p)` where `p : normalize_fin n a b`. This function
does no reduction of the numeral `b`; for example `eval_fin (5 + 5 : fin 6)` returns `10`. It works
even if `n` is a variable, for example `eval_fin (5 + 5 : fin (n+1))` also returns `10`. -/
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
    (a', pa) ← (eval_fin a).reset,
    pure (a', `(@normalize_fin.cast).mk_app [n, m, nm, a, a', pa])
  | _ := do
    n ← get_fin_type a,
    (a', pa) ← eval_fin_lt' eval_fin n a,
    pure (a', `(@normalize_fin_lt.of).mk_app [n, a, a', pa])
  end

/-- `eval_fin_lt n a` expects that `a : fin n`, and produces `(b, p)` where
`p : normalize_fin_lt n a b`. -/
meta def eval_fin_lt : expr → expr → eval_fin_m (expr × expr) := eval_fin_lt' eval_fin

/-- Given `a : fin n`, `eval_fin ff n a` returns `(b, p)` where `p : normalize_fin n a b`, and
`eval_fin tt n a` returns `p : normalize_fin_lt n a b`. Unlike `eval_fin`, this also does reduction
of the numeral `b`; for example `reduce_fin ff 6 (5 + 5 : fin 6)` returns `4`. As a result, it
fails if `n` is a variable, for example `reduce_fin ff (n+1) (5 + 5 : fin (n+1))` fails. -/
meta def reduce_fin (lt : bool) (n a : expr) : eval_fin_m (expr × expr) :=
eval_fin a >>= reduce_fin' lt n a

/-- If `a b : fin n` and `a'` and `b'` are as returned by `eval_fin`,
then `prove_lt_fin' n a b a' b'` proves `a < b`. -/
meta def prove_lt_fin' : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr
| n a b a' b' := do
  (a', pa) ← reduce_fin' ff n a a',
  (b', pb) ← reduce_fin' tt n b b',
  p ← eval_fin_m.lift_ic (λ ic, prove_lt_nat ic a' b'),
  pure (`(@normalize_fin.lt).mk_app [n, a, b, a', b', pa, pb, p])

/-- If `a b : fin n` and `a'` and `b'` are as returned by `eval_fin`,
then `prove_le_fin' n a b a' b'` proves `a ≤ b`. -/
meta def prove_le_fin' : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr
| n a b a' b' := do
  (a', pa) ← reduce_fin' ff n a a',
  (b', pb) ← reduce_fin' tt n b b',
  p ← eval_fin_m.lift_ic (λ ic, prove_le_nat ic a' b'),
  pure (`(@normalize_fin.le).mk_app [n, a, b, a', b', pa, pb, p])

/-- If `a b : fin n` and `a'` and `b'` are as returned by `eval_fin`,
then `prove_eq_fin' n a b a' b'` proves `a = b`. -/
meta def prove_eq_fin' : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr
| n a b (a', pa) (b', pb) :=
  if a' =ₐ b' then do
    pure (`(@normalize_fin.eq).mk_app [n, a, b, a', pa, pb])
  else do
    (a', pa) ← reduce_fin' ff n a (a', pa),
    (b', pb) ← reduce_fin' ff n b (b', pb),
    guard (a' =ₐ b'),
    pure (`(@normalize_fin.eq).mk_app [n, a, b, a', pa, pb])

/-- Given a function with the type of `prove_eq_fin'`, evaluates it with the given `a` and `b`. -/
meta def eval_prove_fin
  (f : expr → expr → expr → expr × expr → expr × expr → eval_fin_m expr)
  (a b : expr) : tactic expr :=
do n ← get_fin_type a, eval_fin_m.run $ eval_fin a >>= λ a', eval_fin b >>= f n a b a'

/-- If `a b : fin n`, then `prove_eq_fin a b` proves `a = b`. -/
meta def prove_eq_fin : expr → expr → tactic expr := eval_prove_fin prove_eq_fin'
/-- If `a b : fin n`, then `prove_lt_fin a b` proves `a < b`. -/
meta def prove_lt_fin : expr → expr → tactic expr := eval_prove_fin prove_lt_fin'
/-- If `a b : fin n`, then `prove_le_fin a b` proves `a ≤ b`. -/
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

/-- The common prep work for the cases in `eval_ineq`. Given inputs `a b : fin n`, it calls
`f n a' b' na nb` where `a'` and `b'` are the result of `eval_fin` and `na` and `nb` are
`a' % n` and `b' % n` as natural numbers. -/
meta def eval_rel {α} (a b : expr)
  (f : expr → expr × expr → expr × expr → ℕ → ℕ → eval_fin_m α) : tactic α :=
do n ← get_fin_type a,
  eval_fin_m.run $ do
    (nn, n', pn) ← eval_fin_m.eval_n n,
    (a', pa) ← eval_fin a,
    (b', pb) ← eval_fin b,
    na ← eval_fin_m.lift a'.to_nat,
    nb ← eval_fin_m.lift b'.to_nat,
    f n (a', pa) (b', pb) (na % nn) (nb % nn)

/-- Given `a b : fin n`, proves either `(n, tt, p)` where `p : a < b` or
`(n, ff, p)` where `p : b ≤ a`. -/
meta def prove_lt_ge_fin : expr → expr → tactic (expr × bool × expr)
| a b := eval_rel a b $ λ n a' b' na nb,
  if na < nb then prod.mk n <$> prod.mk tt <$> prove_lt_fin' n a b a' b'
  else prod.mk n <$> prod.mk ff <$> prove_le_fin' n b a b' a'

/-- Given `a b : fin n`, proves either `(n, tt, p)` where `p : a = b` or
`(n, ff, p)` where `p : a ≠ b`. -/
meta def prove_eq_ne_fin : expr → expr → tactic (expr × bool × expr)
| a b := eval_rel a b $ λ n a' b' na nb,
  if na = nb then prod.mk n <$> prod.mk tt <$> prove_eq_fin' n a b a' b'
  else if na < nb then do
    p ← prove_lt_fin' n a b a' b',
    pure (n, ff, `(@ne_of_lt (fin %%n) _).mk_app [a, b, p])
  else do
    p ← prove_lt_fin' n b a b' a',
    pure (n, ff, `(@ne_of_gt (fin %%n) _).mk_app [a, b, p])

/-- A `norm_num` extension that evaluates equalities and inequalities on the type `fin n`.

```
example : (5 : fin 7) = fin.succ (fin.succ 3) := by norm_num
```
-/
@[norm_num] meta def eval_ineq : expr → tactic (expr × expr)
| `(%%a < %%b) := do
  (n, lt, p) ← prove_lt_ge_fin a b,
  if lt then true_intro p else false_intro (`(@not_lt_of_ge (fin %%n) _).mk_app [a, b, p])
| `(%%a ≤ %%b) := do
  (n, lt, p) ← prove_lt_ge_fin b a,
  if lt then false_intro (`(@not_le_of_gt (fin %%n) _).mk_app [a, b, p]) else true_intro p
| `(%%a = %%b) := do
  (n, eq, p) ← prove_eq_ne_fin a b,
  if eq then true_intro p else false_intro p
| `(%%a > %%b) := mk_app ``has_lt.lt [b, a] >>= eval_ineq
| `(%%a ≥ %%b) := mk_app ``has_le.le [b, a] >>= eval_ineq
| `(%%a ≠ %%b) := do
  (n, eq, p) ← prove_eq_ne_fin a b,
  if eq then false_intro `(not_not_intro (%%p : (%%a : fin %%n) = %%b)) else true_intro p
| _ := failed

/-- Evaluates `e : fin n` to a natural number less than `n`. Returns `none` if it is not a natural
number or greater than `n`. -/
meta def as_numeral (n e : expr) : eval_fin_m (option ℕ) :=
match e.to_nat with
| none := pure none
| some ne := do
  (nn, _) ← eval_fin_m.eval_n n,
  pure $ if ne < nn then some ne else none
end

/-- Given `a : fin n`, returns `(b, ⊢ a = b)` where `b` is a normalized fin numeral. Fails if `a`
is already normalized. -/
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

setup_tactic_parser

/-- Rewrites occurrences of fin expressions to normal form anywhere in the goal.
The `norm_num` extension will only rewrite fin expressions if they appear in equalities and
inequalities. For example if the goal is `P (2 + 2 : fin 3)` then `norm_num` will not do anything
but `norm_fin` will reduce the goal to `P 1`.

(The reason this is not part of `norm_num` is because evaluation of fin numerals uses a top down
evaluation strategy while `norm_num` works bottom up; also determining whether a normalization
will work is expensive, meaning that unrelated uses of `norm_num` would be slowed down with this
as a plugin.) -/
meta def norm_fin (hs : parse simp_arg_list) : tactic unit :=
try (simp_top_down tactic.norm_fin.eval_fin_num) >> try (norm_num hs (loc.ns [none]))

/--
Rewrites occurrences of fin expressions to normal form anywhere in the goal.
The `norm_num` extension will only rewrite fin expressions if they appear in equalities and
inequalities. For example if the goal is `P (2 + 2 : fin 3)` then `norm_num` will not do anything
but `norm_fin` will reduce the goal to `P 1`.

```lean
example : (5 : fin 7) = fin.succ (fin.succ 3) := by norm_num
example (P : fin 7 → Prop) (h : P 5) : P (fin.succ (fin.succ 3)) := by norm_fin; exact h
```
-/
add_tactic_doc
{ name        := "norm_fin",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.norm_fin],
  tags        := ["arithmetic", "decision procedure"] }

end interactive
end tactic
