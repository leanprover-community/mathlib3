/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

A sample parser for modal logic.
-/
import .parser

/-
namespace modal

def varname := string

inductive form
| var : varname → form
| bot : form
| conj : form → form → form
| disj : form → form → form
| impl : form → form → form
| neg : form → form
| box : form → form
| diam : form → form

open form

def size : form → ℕ
| (var s)    := 1
| bot        := 1
| (conj s t) := size s + size t + 1
| (disj s t) := size s + size t + 1
| (impl s t) := size s + size t + 1
| (neg s)    := size s + 1
| (box s)    := size s + 1
| (diam s)   := size s + 1

def num_atoms : form → ℕ
| (var s)    := 1
| bot        := 1
| (conj s t) := num_atoms s + num_atoms t
| (disj s t) := num_atoms s + num_atoms t
| (impl s t) := num_atoms s + num_atoms t
| (neg s)    := num_atoms s
| (box s)    := num_atoms s
| (diam s)   := num_atoms s

end modal

section some_examples
open modal.form

private def my_form :=
  impl (conj (box (var "p1")) (box (impl (var "p1") (var "p2")))) (box (var "p2"))

example : modal.size my_form = 10 := rfl
example : modal.num_atoms my_form = 4 := rfl

end some_examples

namespace modal

meta instance : has_quote varname := string.has_quote

namespace form

meta def quote : form → pexpr
| (var s)    := ``(var %%(has_quote.quote s))
| bot        := ``(bot)
| (conj s t) := ``(conj %%(quote s) %%(quote t))
| (disj s t) := ``(disj %%(quote s) %%(quote t))
| (impl s t) := ``(impl %%(quote s) %%(quote t))
| (neg s)    := ``(neg %%(quote s))
| (box s)    := ``(box %%(quote s))
| (diam s)   := ``(diam %%(quote s))

meta instance : has_quote form := ⟨quote⟩

end form

namespace parse
open parser

def varname : parser string :=
token (do c ← sat char.is_alpha,
          cs ← many (sat char.is_alphanum),
          return (list.reverse (c :: cs)))

def atom : parser modal.form :=
(do vn ← varname, return (modal.form.var vn)) <|>
(do symb "⊥", return (modal.form.bot))

def unary_op : parser (modal.form → modal.form) :=
(do symb "¬", return (λ f, modal.form.neg f)) <|>
(do symb "◾", return (λ f, modal.form.box f)) <|>
(do symb "◆", return (λ f, modal.form.diam f))

def binary_op : parser (modal.form → modal.form → modal.form) :=
(do symb "∧", return (λ f₁ f₂, modal.form.conj f₁ f₂)) <|>
(do symb "∨", return (λ f₁ f₂, modal.form.disj f₁ f₂)) <|>
(do symb "→", return (λ f₁ f₂, modal.form.impl f₁ f₂))

def strong_form_aux (p : parser modal.form) : ℕ → parser modal.form
| 0     := failure
| (n+1) := atom <|>
           (do op ← unary_op, f ← strong_form_aux n, return (op f)) <|>
           (do symb "(", f ← p, symb ")", return f)

/--- parse a formula that is tightly bound -/
def strong_form (p : parser modal.form) : parser modal.form :=
strong_form_aux p parser_bignum

def form_aux : ℕ → parser modal.form
| 0     := failure
| (n+1) := chainl1 (strong_form (form_aux n)) binary_op

def form : parser modal.form := form_aux parser_bignum

/-- parse a string, and return some formula or none -/
def form_of_string (s : string) : option modal.form :=
parse (apply form) s

meta def build_form_from_string (s : string) : tactic unit :=
match form_of_string s with
| some f := tactic.to_expr (quote f) >>= tactic.exact
| none   := tactic.fail ("failed to parse " ++ s)
end

end parse

end modal

prefix `[modal]`:100 := modal.parse.build_form_from_string

section some_examples
open modal
open modal.form

check (by [modal] "p ∧ q → p")
check (by [modal] "◾ p1 ∧ q")
check (by [modal] "◾ (p1 ∧ ◾ (p1 → p2)) → ◾ ◾ (p1 ∧ p2)")

example : num_atoms (by [modal] "◾ (p1 ∧ ◾ (p1 → p2)) → ◾ ◾ (p1 ∧ p2)") = 5 := rfl

example : (by [modal] "p ∧ q → p") = impl (conj (var "p") (var "q")) (var "p") := rfl

end some_examples
-/
