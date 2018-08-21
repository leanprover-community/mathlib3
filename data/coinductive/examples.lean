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

open function (const)

@[reducible]
def cofix' {α : Type*} (β : α → Type*) := @cofix unit (λ _, α) (λ _ i, β i) (λ x _ _, ()) ()
def cofix'.corec {α : Type*} {β : α → Type*} {X : Type*}
    (f : X → Σ y : α, Π a: β y, X) (x₀ : X) : cofix' β :=
@cofix.corec unit (λ _, α) (λ _, β) (λ x _ _, ()) (λ _, X) (λ _, f) () x₀

#check @cofix.cases
  -- Π {ι : Type u_2} {α : ι → Type u_1} {β : Π (i : ι), α i → Type u_3}
  -- {γ : Π (i : ι) (a : α i), β i a → ι} {i : ι} {r : Π {i : ι}, cofix γ i → Sort u_4},
  --   (Π {i : ι} (x : α i) (c : Π (b : β i x), cofix γ (γ i x b)), r (cofix.mk x c)) → Π (x : cofix γ i), r x

-- set_option pp.implicit true
def cofix'.cases {α : Sort*} {β : α → Sort*}
    -- (C) (f)
    {C : cofix' β → Sort*}
    (f : Π (x : α) (c : Π (b : β x), cofix' β), C (cofix.mk x c))
    (x : cofix' β) : C x :=
@cofix.cases unit (λ _, α) (λ _, β) (λ x _ _, ()) ()
(λ _ x, C $ cast (by congr) x)
(λ (_ : unit) (x : α) c, cast (by casesm* unit;refl) $ f x c)
x

def cofix'.cases_on {α : Sort*} {β : α → Sort*}
    {C : cofix' β → Sort*}
    (x : cofix' β)
    (f : Π (x : α) (c : Π (b : β x), cofix' β), C (cofix.mk x c)) : C x :=
cofix'.cases f x

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

def l_two_tree_intl (A : Type) := cofix' (branch A)

mutual inductive l_two_tree', l_leaf' (A X : Type)
with l_two_tree' : Type
| nil {}      : l_two_tree'
| cons        : A → l_leaf' → l_two_tree'
| cons₂       : A → l_leaf' → l_leaf' → l_two_tree'
with l_leaf' : Type
| hole {} : X → l_leaf'
| more : l_two_tree' → l_leaf'

@[reducible]
def  l_two_tree (A : Type) := l_two_tree' A (l_two_tree_intl A)
@[reducible]
def l_leaf (A : Type) := l_leaf' A (l_two_tree_intl A)

-- inductive tree (A :
#check l_two_tree_intl.

mutual def to_intl', to_intl {A : Type}
with to_intl' : l_leaf A → l_two_tree_intl A
| (l_leaf'.hole t) := t
| (l_leaf'.more t) := to_intl t
with to_intl : l_two_tree A → l_two_tree_intl A
| l_two_tree'.nil := cofix.mk nil empty.elim
| (l_two_tree'.cons x t) := cofix.mk (cons x) (λ _, to_intl' t)
| (l_two_tree'.cons₂ x t₀ t₁) := cofix.mk (cons₂ x) (λ i : bool, if i then to_intl' t₀ else to_intl' t₁)
#check cofix'.cases
-- def of_intl {A : Type} (x : l_two_tree_intl A) : l_two_tree A :=
-- -- cofix'.cases _ _
-- cofix'.cases_on x (λ y : l_two_tree_node A,
-- match y with
-- | nil := λ ch : branch A nil → l_two_tree A, l_two_tree'.nil
-- | (cons xx) := λ ch : branch A (cons xx) → l_two_tree A, l_two_tree'.cons xx (l_leaf'.hole $ ch ())
-- | (cons₂ xx) := λ ch : branch A (cons₂ xx) → l_two_tree A, l_two_tree'.cons₂ xx (l_leaf'.hole $ ch tt) (l_leaf'.hole $ ch ff)
-- end)
-- begin
--   apply cofix'.cases (λ y : l_two_tree_node A, _) x,
--   cases y; intro ch,
--   case nil { exact l_two_tree'.nil },
--   case cons : x  { exact l_two_tree'.cons x (l_leaf'.hole $ ch ()) },
--   case cons₂ : x { exact l_two_tree'.cons₂ x (l_leaf'.hole $ ch tt) (l_leaf'.hole $ ch ff) },
-- end

-- def l_two_equiv (A : Type) : l_two_tree A ≃ l_two_tree_intl A :=
-- { to_fun := to_intl
-- , inv_fun := of_intl
-- , left_inv := by { assume x, cases x ; simp [to_intl,of_intl] ; admit }
-- , right_inv := by { assume x, apply cofix.cases _ x, intros,
--                     dsimp [of_intl],
--                     cases i ; simp [of_intl._match_1,to_intl] ;
--                     congr ; funext x ; cases x ; admit } }

-- corecursion
def corec_next_state {A X} : Π x : l_two_tree' A X, Σ n, branch A n → l_leaf' A X
     | l_two_tree'.nil := ⟨ nil, empty.elim ⟩
     | (l_two_tree'.cons x t) := ⟨ cons x, λ _, t ⟩
     | (l_two_tree'.cons₂ x t₀ t₁) := ⟨ cons₂ x, λ i : bool, if i then t₀ else t₁ ⟩

-- def l_two_tree.corec {A} {X : Sort*}
--   (f : Π z, X → (X → l_leaf' A z) → l_two_tree' A z)
--   (x₀ : X)
-- : l_two_tree A :=
-- of_intl $
--   cofix.corec (λ x : l_leaf' A X,
--     match x with
--      | (l_leaf'.hole x') :=
--         corec_next_state $ f _ x' l_leaf'.hole
--      | (l_leaf'.more t) := corec_next_state t
--     end)
--     (l_leaf'.hole x₀)

open l_leaf' (more)

-- def mk_tree : ℕ → l_two_tree ℕ :=
-- l_two_tree.corec $ λ z n mk_tree,
-- if n % 10 = 0 then
--   l_two_tree'.cons n (mk_tree $ n+1)
-- else if n % 10 = 7 then
--   l_two_tree'.nil
-- else
--   l_two_tree'.cons₂ n (mk_tree $ n+1) (mk_tree $ n+2)

-- def mk_tree' : ℕ → l_two_tree ℕ :=
-- l_two_tree.corec $ λ z n mk_tree,
-- l_two_tree'.cons₂ n (more $ l_two_tree'.cons (n+1) (mk_tree $ n+1))
--                     (more $ l_two_tree'.cons (n+2) (mk_tree $ n+2))


open nat
-- mutual def to_bin_tree_aux, to_bin_tree
-- with to_bin_tree_aux : ℕ → l_leaf ℕ → bin_tree ℕ
--  | (succ n) :=
-- have n < succ n, from lt_succ_self _,
-- λ t,
-- match t with
--  | (more t) := to_bin_tree n t
--  | (l_leaf'.hole x) := to_bin_tree n (of_intl x)
-- end
--  | 0 := λ _, bin_tree.empty
-- with to_bin_tree : ℕ → l_two_tree ℕ → bin_tree ℕ
--  | (succ n) :=
-- have n < succ n, from lt_succ_self _,
-- λ t,
-- match t with
--  | l_two_tree'.nil := bin_tree.empty
--  | (l_two_tree'.cons x t') := bin_tree.node (bin_tree.leaf x) (to_bin_tree_aux n t')
--  | (l_two_tree'.cons₂ x t₀ t₁) := bin_tree.node (bin_tree.leaf x)
--                                                (bin_tree.node (to_bin_tree_aux n t₀)
--                                                               (to_bin_tree_aux n t₁))
-- end
--  | 0 := λ _, bin_tree.empty

def bin_tree.repr {α} [has_repr α] : bin_tree α → string
 | bin_tree.empty := "⊥"
 | (bin_tree.leaf x) := repr x
 | (bin_tree.node t₀ t₁) := "(node " ++ bin_tree.repr t₀ ++ " " ++ bin_tree.repr t₁ ++ ")"

instance {α} [has_repr α] : has_repr (bin_tree α) :=
{ repr := bin_tree.repr }

-- #eval to_bin_tree 3 (mk_tree 0)
/- (node 0 (node 1 (node ⊥ ⊥))) -/
-- #eval to_bin_tree 5 (mk_tree 0)
-- (node 0 (node 1 (node (node 2 (node ⊥ ⊥)) (node 3 (node ⊥ ⊥)))))

-- #eval to_bin_tree 7 (mk_tree' 0)
/-
(node 0 (node (node 1 (node 1 (node (node 2 ⊥) (node 3 ⊥))))
              (node 2 (node 2 (node (node 3 ⊥) (node 4 ⊥))))))
-/

-- example {A} (p q : l_two_tree_intl A) : p = q :=
-- begin
--   co_cases p,
--   admit
-- end

end examples
