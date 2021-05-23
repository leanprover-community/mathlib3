/-
Copyright (c) 2020 Dany Fabian. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
import tactic.unfold_cases

open tactic

variable {α : Type*}

inductive color
| red
| black

inductive node (α)
| leaf {} : node
| tree {} (color : color) (left : node) (val : α) (right : node) : node

/-- this function creates 122 cases as opposed to the 5 we see here. -/
def balance_eqn_compiler {α} : color → node α → α → node α → node α
| color.black (node.tree color.red (node.tree color.red a x b) y c) z d :=
    node.tree color.red (node.tree color.black a x b) y (node.tree color.black c z d)
| color.black (node.tree color.red a x (node.tree color.red b y c)) z d :=
    node.tree color.red (node.tree color.black a x b) y (node.tree color.black c z d)
| color.black a x (node.tree color.red (node.tree color.red b y c) z d) :=
    node.tree color.red (node.tree color.black a x b) y (node.tree color.black c z d)
| color.black a x (node.tree color.red b y (node.tree color.red c z d)) :=
    node.tree color.red (node.tree color.black a x b) y (node.tree color.black c z d)
| color a x b := node.tree color a x b

example : ∀ a (x:α) b y c z d, balance_eqn_compiler color.black (node.tree color.red (node.tree color.red a x b) y c) z d =
    node.tree color.red (node.tree color.black a x b) y (node.tree color.black c z d) :=
begin
  unfold_cases { refl },
end

/-- this function creates 122 cases as opposed to the 5 we see here. -/
def balance_match {α}  (c:color) (l:node α) (v:α) (r:node α) : node α :=
match c, l, v, r with
| color.black, node.tree color.red (node.tree color.red a x b) y c, z, d :=
    node.tree color.red (node.tree color.black a x b) y (node.tree color.black c z d)
| color.black, node.tree color.red a x (node.tree color.red b y c), z, d :=
    node.tree color.red (node.tree color.black a x b) y (node.tree color.black c z d)
| color.black, a, x, node.tree color.red (node.tree color.red b y c) z d :=
    node.tree color.red (node.tree color.black a x b) y (node.tree color.black c z d)
| color.black, a, x, node.tree color.red b y (node.tree color.red c z d) :=
     node.tree color.red (node.tree color.black a x b) y (node.tree color.black c z d)
| color, a, x, b := node.tree color a x b
end

example : ∀ a (x:α) b y c z d, balance_match color.black (node.tree color.red (node.tree color.red a x b) y c) z d =
    node.tree color.red (node.tree color.black a x b) y (node.tree color.black c z d) :=
begin
  unfold_cases { refl },
end

def foo : ℕ → ℕ → ℕ
| 0 0 := 17
| (n+2) 17 := 17
| 1 0 := 23
| 0 (n+18) := 15
| 0 17 := 17
| 1 17 := 17
| _ (n+18) := 27
| _ _ := 15

example : ∀ x, foo x 17 = 17 :=
begin
  unfold_cases { refl },
end

def bar : ℕ → ℕ
| 17 := 17
| 9 := 17
| n := 17

example : ∀ x, bar x = 17 :=
begin
  unfold_cases { refl }
end

def baz : ℕ → ℕ → Prop
| 0 0 := false
| 0 n := true
| n 0 := false
| n m := n < m

example : ∀ x, baz x 0 = false :=
begin
  unfold_cases { refl },
end
