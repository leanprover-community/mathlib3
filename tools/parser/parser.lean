/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Monadic parsing, following Graham Hutton and Erik Meijer, "Monadic Parsing in Haskell," 1998.
-/

/- auxiliary -/

@[simp]
lemma {u v} pair_eta {α : Type u} {β : Type v} : ∀{p : α × β}, (p.1, p.2) = p
| (a, b) := rfl

lemma {u} list.join_append {α : Type u} :
  ∀xs ys : list (list α), list.join (xs ++ ys) = list.join xs ++ list.join ys
| [] ys      := by simp [list.join]
| (x::xs) ys := by simp [list.join, list.join_append]

@[simp]
lemma {u v} list.bind_nil {α : Type u} {β : Type v} {f : α → list β} : list.bind [] f = [] :=
rfl

@[simp]
lemma {u v} list.bind_cons {α : Type u} {β : Type v} {f : α → list β} {x : α} {xs : list α} :
  list.bind (x :: xs) f = f x ++ list.bind xs f :=
rfl

@[simp]
lemma {u v} list.bind_append {α : Type u} {β : Type v} {f : α → list β} :
  ∀xs ys : list α, list.bind (xs ++ ys) f = list.bind xs f ++ list.bind ys f
| [] _ := by simp
| (x::xs) _ := by simp [list.bind_append xs]

lemma {u v w} list.bind_assoc {α : Type u} {β : Type v} {γ : Type w} {f : α → list β} {g : β → list γ} :
  ∀xs, list.bind (list.bind xs f) g = list.bind xs (λx, list.bind (f x) g)
| []      := by simp [list.map, list.join, list.bind]
| (x::xs) := by simp [list.join_append, list.bind_assoc xs]

lemma {u v} list.bind_singleton {α : Type u} {β : Type v} {f : α → β} :
  ∀xs, list.bind xs (λx, [f x]) = list.map f xs
| [] := by simp
| (x :: xs) := by simp [list.bind_singleton xs]

/-
  The parsing monad.
-/

variables {α β : Type}

def parser (α : Type) : Type := list char → list (α × list char)

@[inline] def parser_fmap (f : α → β) (a : parser α) : parser β :=
λ s, list.map (λ p : α × list char, (f p.1, p.2)) (a s)

@[inline] def parser_pure (a : α) : parser α := λ s, [(a, s)]

@[inline] def parser_bind (a : parser α) (b : α → parser β) : parser β :=
λ s, list.bind (a s) (λ p, b p.1 p.2)

instance monad_parser : monad parser :=
{ map                   := @parser_fmap,
  pure                  := @parser_pure,
  bind                  := @parser_bind,
  id_map                := assume α p, funext $ assume s,
    by simp [parser_fmap]; exact list.map_id _,
  pure_bind             := assume α β a f, funext $ assume s,
    by simp [parser_bind, parser_pure],
  bind_assoc            := assume α β γ p f g, funext $ assume s,
    by simp [parser_bind, list.bind_assoc],
  bind_pure_comp_eq_map := assume α β f p, funext $ assume s,
    by simp [parser_bind, parser_pure, parser_fmap, list.bind_singleton, function.comp] }

def list.deterministic_or : list α → list α → list α
| [] []      := []
| [] (x::xs) := [x]
| (x::xs) _  := [x]

instance : alternative parser :=
{ monad_parser with
  failure := λ a s, [],
  orelse := λ a p₁ p₂ s, list.deterministic_or (p₁ s) (p₂ s) }

namespace parser

def parser_bignum := 1000

def parse (p : parser α) (s : string) : option α :=
match p (s.to_list) with
| []            := none
| ((a, s) :: l) := some a
end

def item : parser char
| []      := []
| (c::cs) := [(c, cs)]

section an_example
  private def my_parser : parser (char × char) :=
  do a ← item,
     b ← item,
     c ← item,
     return (a, c)

  -- vm_eval parse my_parser "abcde"  -- output : (some (#"a", #"c"))
end an_example

def sat (p : char → Prop) [decidable_pred p] : parser char :=
do c ← item, if p c then return c else failure

def take_char (c : char) : parser char := sat (λ x, x = c)

def take_string_aux : list char → parser unit
| []      := return ()
| (c::cs) := do take_char c, take_string_aux cs, return ()

def take_string (s : list char) : parser (list char) :=
do take_string_aux s >> return s

def many_aux (p : parser α) : ℕ → parser (list α)
| 0     := return []
| (n+1) := (do a ← p, l ← many_aux n, return (a :: l)) <|> return []

def many (p : parser α) : parser (list α) :=
many_aux p parser_bignum

def many1 (p : parser α) : parser (list α) :=
do a ← p, l ← many p, return (a :: l)

def sepby1 {α β : Type} (p : parser α) (sep : parser β) : parser (list α) :=
do a ← p, l ← many (do sep, p), return (a::l)

def sepby {α β : Type} (p : parser α) (sep : parser β) : parser (list α) :=
sepby1 p sep <|> return []

def chainl1_rest (p : parser α) (op : parser (α → α → α)) : ℕ → α → parser α
| 0     := λ a, return a
| (n+1) := λ a, (do f ← op, b ← p, chainl1_rest n (f a b)) <|> return a

def chainl1 (p : parser α) (op : parser (α → α → α)) : parser α :=
do a ← p, chainl1_rest p op parser_bignum a

def chainl (p : parser α) (op : parser (α → α → α)) (a : α) : parser α :=
chainl1 p op <|> return a

def chainr1_rest (p : parser α) (op : parser (α → α → α)) (a : α) : ℕ → parser α
| 0     := return a
| (n+1) := do f ← op, b ← chainr1_rest n, return (f a b) <|> return a

def chainr1 (p : parser α) (op : parser (α → α → α)) : parser α :=
do a ← p, chainr1_rest p op a parser_bignum

def chainr (p : parser α) (op : parser (α → α → α)) (a : α) : parser α :=
chainr1 p op <|> return a

/-- consume whitespace -/
def space : parser (list char) := many (sat char.is_whitespace)

/-- parse with p, and then consume whitespace -/
def token (p : parser α) : parser α := do a ← p, space, return a

/-- consume s -/
def symb (s : list char) : parser (list char) := token (take_string s)

/-- consume leading whitespace, and then apply p -/
def apply (p : parser α) : parser α := do space, p

end parser
