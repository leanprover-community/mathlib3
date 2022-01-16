/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import data.vector.basic
import computability.partrec_code
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


open nat.partrec.code

def time : nat.partrec.code → ℕ →. ℕ
| zero         := pure 0
| succ         := nat.log 2
| left         := nat.log 2
| right        := nat.log 2
| (pair cf cg) := λ n, ((nat.log 2) <$> (eval cf n)) + ((nat.log 2) <$> (eval cg n)) + time cf n + time cg n
| (comp cf cg) := λ n, time cg n + ((eval cg n) >>= time cf)
| (prec cf cg) := λ n, sorry -- todo, when depaired to 0 is time of f, otherwise recurse
| (rfind' cf)  := λ n, sorry


end nat.partrec
