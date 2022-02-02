/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import data.vector.basic
import computability.tm_to_partrec
import data.nat.log


/-!
# TODO
-/

/-- μ-recursive algorithms for functions from ℕ^k to ℕ. Similar to `nat.partrec.code`, but with
arity. -/
@[derive inhabited]
inductive μ_recursive : ℕ -> Type
| const {k : ℕ} {n : ℕ} : μ_recursive k
| succ : μ_recursive 1
| proj {i k : ℕ} (h : i < k) : μ_recursive k
| comp {m k : ℕ} (h : μ_recursive m) (g : fin m -> μ_recursive k) : μ_recursive k
| ρ {k : ℕ} (g : μ_recursive k) (h : μ_recursive (k + 2)) : μ_recursive (k + 1)
| μ {k : ℕ} (f : μ_recursive (k + 1)) : μ_recursive k


-- Note that we use the code type defined in turing.to_partrec, since this is over lists.
-- A type of codes that works over naturals will not let us compute without exponential slowdowns.
open turing.to_partrec

def time : turing.to_partrec.code → list ℕ →. ℕ
| code.zero'       := pure 1
| code.succ        := pure 1
| code.tail        := pure 1
| (code.cons f fs) := λ l, time f l + time fs l + pure 1
| (code.comp f g)  := λ l, time g l + ((code.eval g l) >>= time f) + pure 1
| (code.case f g)  := λ l, l.head.elim (time f l.tail) (λ y _, time g (y :: l.tail)) + pure 1
| (code.fix f)     := λ l, ((@pfun.fix ((list ℕ) × ℕ) (ℕ) $
  λ ⟨v, n⟩,
  if v.head = 0
    then ((time f v.tail).map sum.inl)
    else (prod.mk <$> f.eval v.tail <*> (time f v.tail) + pure n).map sum.inr
) ⟨l, 0⟩)
