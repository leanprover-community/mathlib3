/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.derive_fintype

@[derive fintype]
inductive alphabet
| a | b | c | d | e | f | g | h | i | j | k | l | m
| n | o | p | q | r | s | t | u | v | w | x | y | z
| A | B | C | D | E | F | G | H | I | J | K | L | M
| N | O | P | Q | R | S | T | U | V | W | X | Y | Z

@[derive fintype]
inductive foo
| A (x : bool)
| B (y : unit)
| C (z : fin 37)

@[derive fintype]
inductive foo2 (α : Type)
| A : α → foo2
| B : α → α → foo2
| C : α × α → foo2
| D : foo2

-- @[derive fintype] -- won't work because missing decidable instance
inductive foo3 (α β : Type) (n : ℕ)
| A : (α → β) → foo3
| B : fin n → foo3

instance (α β : Type) [decidable_eq α] [fintype α] [fintype β] (n : ℕ) : fintype (foo3 α β n) :=
by tactic.mk_fintype_instance

@[derive fintype]
structure foo4 {m n : Type} (b : m → ℕ) :=
(x : m × n)
(y : m × n)
(h : b x.1 = b y.1)

class my_class (M : Type*) :=
(one : M)
(eq_one : ∀ x : M, x = one)

instance {M : Type*} [fintype M] [decidable_eq M] : fintype (my_class M) :=
by tactic.mk_fintype_instance
