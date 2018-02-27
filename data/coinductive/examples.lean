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

inductive l_two_tree' (A X : Type) : Type
| nil {}      : l_two_tree'
| cons        : A → X → l_two_tree'
| cons₂       : A → X → X → l_two_tree'

def  l_two_tree (A : Type) := l_two_tree' A (l_two_tree_intl A)

def to_intl {A : Type} : l_two_tree A → l_two_tree_intl A
| l_two_tree'.nil := cofix.mk nil empty.elim
| (l_two_tree'.cons x t) := cofix.mk (cons x) (λ _, t)
| (l_two_tree'.cons₂ x t₀ t₁) := cofix.mk (cons₂ x) (λ i : bool, if i then t₀ else t₁)

def of_intl {A : Type} : l_two_tree_intl A → l_two_tree A :=
cofix.cases $ λ i,
match i with
| nil := λ ch, l_two_tree'.nil
| (cons x) := λ ch, l_two_tree'.cons x (ch ())
| (cons₂ x) := λ ch, l_two_tree'.cons₂ x (ch tt) (ch ff)
end

def l_two_equiv (A : Type) : l_two_tree A ≃ l_two_tree_intl A :=
{ to_fun := to_intl
, inv_fun := of_intl
, left_inv := by { assume x, cases x ; simp [to_intl,of_intl], }
, right_inv := by { assume x, apply cofix.cases _ x, intros,
                    dsimp [of_intl],
                    cases i ; simp [of_intl._match_1,to_intl] ;
                    congr ; funext x ; cases x ; simp } }

-- corecursion
def l_two_tree.corec {A} {X : Sort*}
  (f : Π z, X → (X → z) → l_two_tree' A z)
  (x₀ : X)
: l_two_tree A :=
of_intl $
  cofix.corec (λ x,
    match f X x id with
     | l_two_tree'.nil := ⟨ nil, empty.elim ⟩
     | (l_two_tree'.cons x t) := ⟨ cons x, λ _, t ⟩
     | (l_two_tree'.cons₂ x t₀ t₁) := ⟨ cons₂ x, λ i : bool, if i then t₀ else t₁ ⟩
    end)
    x₀

def mk_tree : ℕ → l_two_tree ℕ :=
l_two_tree.corec $ λ z n mk_tree,
if n % 10 = 0 then
  l_two_tree'.cons n (mk_tree $ n+1)
else if n % 10 = 7 then
  l_two_tree'.nil
else
  l_two_tree'.cons₂ n (mk_tree $ n+1) (mk_tree $ n+2)

def l_two_tree.corec' {A} {X : Sort*}
  (f : Π z, X → (X → z) → l_two_tree' A (l_two_tree' A z))
  (s₀ : X)
: l_two_tree A :=
of_intl $
  cofix.corec
  (λ s : X ⊕ l_two_tree' A X,
        match s with
         | (sum.inl s') :=
           match f X s' id with
            | l_two_tree'.nil := ⟨ l_two_tree_node.nil, empty.elim ⟩
            | (l_two_tree'.cons x t) := ⟨ l_two_tree_node.cons x, λ _, sum.inr t ⟩
            | (l_two_tree'.cons₂ x t₀ t₁) := ⟨ l_two_tree_node.cons₂ x, λ b : bool, sum.inr (if b then t₀ else t₁) ⟩
           end
         | (sum.inr s) :=
           match s with
            | l_two_tree'.nil := ⟨ l_two_tree_node.nil, empty.elim ⟩
            | (l_two_tree'.cons x t) := ⟨ l_two_tree_node.cons x, λ _, sum.inl t ⟩
            | (l_two_tree'.cons₂ x t₀ t₁) := ⟨ l_two_tree_node.cons₂ x, λ b : bool, sum.inl (if b then t₀ else t₁) ⟩
           end
        end )
  (sum.inl s₀ : X ⊕ l_two_tree' A X)

def mk_tree' : ℕ → l_two_tree ℕ :=
l_two_tree.corec' $ λ z n mk_tree,
l_two_tree'.cons₂ n (l_two_tree'.cons (n+1) (mk_tree $ n+1)) (l_two_tree'.cons (n+2) (mk_tree $ n+2))


open nat
def to_bin_tree_aux : l_two_tree_intl ℕ → ℕ → bin_tree ℕ
 | t (succ n) :=
match of_intl t with
 | l_two_tree'.nil := bin_tree.empty
 | (l_two_tree'.cons x t') := bin_tree.node (bin_tree.leaf x) (to_bin_tree_aux t' n)
 | (l_two_tree'.cons₂ x t₀ t₁) := bin_tree.node (bin_tree.leaf x)
                                               (bin_tree.node (to_bin_tree_aux t₀ n)
                                                              (to_bin_tree_aux t₁ n))
end
 | _ 0 := bin_tree.empty

def to_bin_tree (t : l_two_tree ℕ) : ℕ → bin_tree ℕ :=
to_bin_tree_aux (to_intl t)

#reduce to_bin_tree (mk_tree 0) 3
/-
bin_tree.node (bin_tree.leaf 0)
  (bin_tree.node (bin_tree.leaf 1)
     (bin_tree.node (bin_tree.node (bin_tree.leaf 2) (bin_tree.node bin_tree.empty bin_tree.empty))
        (bin_tree.node (bin_tree.leaf 3) (bin_tree.node bin_tree.empty bin_tree.empty))))
-/
#eval bin_tree.to_list $ to_bin_tree (mk_tree 0) 5
-- [0, 1, 2, 3, 4, 5, 4, 5, 6, 3, 4, 5, 6, 5, 6]

#eval bin_tree.to_list $ to_bin_tree (mk_tree' 0) 7
-- [0, 1, 1, 2, 2, 3, 3, 4, 4, 3, 3, 4, 4, 5, 5, 2, 2, 3, 3, 4, 4, 5, 5, 4, 4, 5, 5, 6, 6]

end examples
