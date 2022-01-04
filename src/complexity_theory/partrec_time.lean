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

-- inductive code_time_bound : code -> (ℕ -> ℕ) -> Prop
-- | bound_zero : code_time_bound code.zero (λ n, 1)
-- | bound_succ : code_time_bound code.succ (λ n, n)
-- | bound_left : code_time_bound code.left (λ n, n)
-- | bound_right : code_time_bound code.right (λ n, n)
-- | bound_right : code_time_bound code.right (λ n, n)


def my_swap {α : Type*} {β : Type*} {γ : Type*} (f : α -> β -> γ) := λ a b, f b a

instance {α : Type*} [has_add α] : has_add (part α) := {add := bind ((λ f a b, f b a) (λ a, part.map (λ b, a + b)))}


def time : nat.partrec.code → ℕ →. ℕ
| zero         := pure 0
| succ         := nat.log 2
| left         := nat.log 2
| right        := nat.log 2
| (pair cf cg) := λ n, ((nat.log 2) <$> (eval cf n)) + ((nat.log 2) <$> (eval cg n)) + time cf n + time cg n
| (comp cf cg) := λ n, sorry
| (prec cf cg) := sorry
| (rfind' cf)  := sorry


end nat.partrec
