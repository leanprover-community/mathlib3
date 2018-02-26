/-
Copyright (c) 2017 Simon Hudon All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

Basic machinery for defining general coinductive types

Examples for coinductive types
-/

import data.coinductive

-- taken from
-- https://github.com/leanprover/lean/wiki/Coinductive-Types

namespace examples

-- coinductive l_two_tree (A : Type) : Type :=
-- | nil {}      : l_two_tree A
-- | cons        : A → l_two_tree A → l_two_tree A
-- | cons₂       : A → l_two_tree → l_two_tree A → l_two_tree A

inductive l_two_tree_node (A : Type) : Type
| nil {}      : l_two_tree_node
| cons        : A → l_two_tree_node
| cons₂       : A → l_two_tree_node
open l_two_tree_node

def branch (A : Type) : l_two_tree_node A → Type
 | nil := empty
 | (cons _) := unit
 | (cons₂ _) := bool

def l_two_tree_intl (A : Type) := cofix (branch A)

inductive l_two_tree (A : Type) : Type
| nil {}      : l_two_tree
| cons        : A → l_two_tree_intl A → l_two_tree
| cons₂       : A → l_two_tree_intl A → l_two_tree_intl A → l_two_tree

def to_intl {A : Type} : l_two_tree A → l_two_tree_intl A
| l_two_tree.nil := cofix.mk nil empty.elim
| (l_two_tree.cons x t) := cofix.mk (cons x) (λ _, t)
| (l_two_tree.cons₂ x t₀ t₁) := cofix.mk (cons₂ x) (λ i : bool, if i then t₀ else t₁)

def of_intl {A : Type} : l_two_tree_intl A → l_two_tree A :=
cofix.cases $ λ i,
match i with
| nil := λ ch, l_two_tree.nil
| (cons x) := λ ch, l_two_tree.cons x (ch ())
| (cons₂ x) := λ ch, l_two_tree.cons₂ x (ch tt) (ch ff)
end

def l_two_equiv (A : Type) : l_two_tree A ≃ l_two_tree_intl A :=
{ to_fun := to_intl
, inv_fun := of_intl
, left_inv := by { assume x, cases x ; simp [to_intl,of_intl], }
, right_inv := by { assume x, apply cofix.cases _ x, intros,
                    dsimp [of_intl],
                    cases i ; simp [of_intl._match_1,to_intl] ;
                    congr ; funext x ; cases x ; simp } }

-- construct one infinite tree and print part of it
def mk_tree : ℕ → l_two_tree_intl ℕ :=
cofix.corec $ λ n,
if n % 2 = 0 then
⟨ cons₂ n , λ i : bool, if i then n+1 else n+2 ⟩
else
⟨ cons n , λ _, n+1 ⟩

open nat
def to_bin_tree : l_two_tree_intl ℕ → ℕ → bin_tree ℕ
 | t (succ n) :=
match of_intl t with
 | l_two_tree.nil := bin_tree.empty
 | (l_two_tree.cons x t') := bin_tree.node (bin_tree.leaf x) (to_bin_tree t' n)
 | (l_two_tree.cons₂ x t₀ t₁) := bin_tree.node (bin_tree.leaf x)
                                               (bin_tree.node (to_bin_tree t₀ n)
                                                              (to_bin_tree t₁ n))
end
 | _ 0 := bin_tree.empty

#reduce to_bin_tree (mk_tree 0) 3
/-
bin_tree.node (bin_tree.leaf 0)
  (bin_tree.node
     (bin_tree.node (bin_tree.leaf 1) (bin_tree.node (bin_tree.leaf 2) (bin_tree.node bin_tree.empty bin_tree.empty)))
     (bin_tree.node (bin_tree.leaf 2)
        (bin_tree.node (bin_tree.node (bin_tree.leaf 3) bin_tree.empty)
           (bin_tree.node (bin_tree.leaf 4) (bin_tree.node bin_tree.empty bin_tree.empty)))))

-/
#eval bin_tree.to_list $ to_bin_tree (mk_tree 0) 3
-- [0, 1, 2, 2, 3, 4]

-- recursion

end examples
