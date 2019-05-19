/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Parse proof output from SPASS.
-/

import data.buffer.parser
import tactic.spass.recipe

universe u

open list parser tactic

inductive rule
| inp : rule
| obv (c l : nat) : rule
| fac (k rf1 rf2 : nat) : rule
| con (c l : nat) : rule
| res (c1 l1 c2 l2 : nat) : rule
| unc (c1 l1 c2 l2 : nat) : rule
| ems : list (nat × nat) → rule

namespace rule

def repr : rule → string
| rule.inp := "Inp"
| (rule.obv k m) := "Obv:" ++ k.repr ++ "." ++ m.repr
| (rule.con k m) := "Con:" ++ k.repr ++ "." ++ m.repr
| (rule.fac ln rf1 rf2) := "Fac:" ++ ln.repr ++ "." ++
  rf1.repr ++ "," ++
  ln.repr ++ "." ++
  rf2.repr
| (rule.res c1 l1 c2 l2) := "Res:" ++ c1.repr ++ "." ++
  l1.repr ++ "," ++
  c2.repr ++ "." ++
  l2.repr
| (rule.unc c1 l1 c2 l2) := "UnC:" ++ c1.repr ++ "." ++
  l1.repr ++ "," ++
  c2.repr ++ "." ++
  l2.repr
| (rule.ems l) := "EmS:" ++ l.repr

instance has_repr : has_repr rule := ⟨repr⟩
meta instance has_to_format : has_to_format rule := ⟨λ x, repr x⟩

end rule

structure line :=
(n : nat)
(r : rule)
(c : cla)

namespace line

def repr : line → string
| ⟨n, r, c⟩ := n.repr ++ " " ++ r.repr ++ " " ++ c.repr

instance has_repr : has_repr line := ⟨repr⟩
meta instance has_to_format : has_to_format line := ⟨λ x, repr x⟩

end line

inductive preterm : Type
| sym : nat  → preterm
| var : nat  → preterm
| app : preterm → preterm → preterm

def digits : list char :=
[ '0', '1', '2', '3', '4', '5', '6', '7', '8', '9' ]

def unpunctuate_core : list char → list char
| []        := []
| [c]       := if c = '.' then [] else [c]
| (c :: cs) := c :: unpunctuate_core cs

def unpunctuate (s : string) : string :=
⟨unpunctuate_core s.data⟩

def string.filter (p : char → Prop) [decidable_pred p] (s : string) : string :=
⟨s.data.filter p⟩

def lex_core : list char → bool → list (list char) → list (list char)
| []        _ ts := (ts.map reverse).reverse
| (c :: cs) _ [] :=
  if c = ' '
  then lex_core cs ff []
  else lex_core cs tt [[c]]
| (c :: cs) b (t :: ts) :=
  if c = ' '
  then lex_core cs ff (t :: ts)
  else if b
       then lex_core cs tt ((c :: t) :: ts)
       else lex_core cs tt ([c] :: t :: ts)

def lex (s : string) : list string :=
(lex_core s.data ff []).map string_imp.mk

namespace parse

meta def to_tactic {α : Type u} : (string ⊕ α) → tactic α
| (sum.inl s) := fail s
| (sum.inr a) := return a

def digits : parser string := many_char (one_of digits)

def nat : parser nat :=
digits >>= (return ∘ string.to_nat)

def character : parser char := sat (λ x, x ≠ '\n')

def linestring_core : parser string := many_char character <* many (ch '\n')

meta def linestrings_core (s : string) : tactic (list string) :=
to_tactic $ run_string (many linestring_core) (s ++ "\n")

meta def is_linestring (s : string) : tactic bool :=
match s.data with
| []       := return ff
| (c :: _) := return (c ∈ _root_.digits)
end

meta def linestrings (s : string) : tactic (list string) :=
linestrings_core s >>= monad.filter is_linestring

meta def reference : parser (_root_.nat × _root_.nat) :=
do k ← nat,
   ch '.',
	 m ← nat,
	 pure (k, m)

meta def rule_core : parser _root_.rule :=
(str "Inp" >> pure _root_.rule.inp) <|>
(do str "Obv",
    ch ':',
    (k, m) ← reference,
		pure (_root_.rule.obv k m)) <|>
(do str "Con",
    ch ':',
    (k, m) ← reference,
		pure (_root_.rule.con k m)) <|>
(do (str "Fac"),
    ch ':',
    cn ← nat, ch '.',
    rf1 ← nat, ch ',',
    _ ← nat, ch '.',
    rf2 ← nat,
		pure (_root_.rule.fac cn rf1 rf2)) <|>
(do (str "Res"),
    ch ':',
    c1 ← nat, ch '.',
    l1 ← nat, ch ',',
    c2 ← nat, ch '.',
    l2 ← nat,
		pure (_root_.rule.res c1 l1 c2 l2)) <|>
(do (str "UnC"),
    ch ':',
    c1 ← nat, ch '.',
    l1 ← nat, ch ',',
    c2 ← nat, ch '.',
    l2 ← nat,
		pure (_root_.rule.unc c1 l1 c2 l2)) <|>
(do (str "EmS" <|> str "MRR" <|> str "SSi" <|> str "SoR"),
    ch ':',
    l ← sep_by1 (ch ',') reference,
		pure (_root_.rule.ems l))

meta def rule : parser _root_.rule :=
do ch '[', nat, ch ':',
   r ← rule_core, ch ']', pure r

meta def number_rule' : parser (_root_.nat × _root_.rule) :=
do n ← nat,
   r ← rule,
	 pure (n, r)

meta def number_rule (s : string) : tactic (_root_.nat × _root_.rule) :=
to_tactic (run_string number_rule' s)

def split_clastrings_core : list string → list string → list string × list string
| ns []        := (ns, [])
| ns (s :: ss) :=
  if s = "->" then (ns, ss) else split_clastrings_core (ns ++ [s]) ss

def split_clastrings (ss : list string) : list string × list string :=
split_clastrings_core [] ss

meta def var_index : parser _root_.nat :=
(ch 'u' >> pure 0) <|>
(ch 'v' >> pure 1) <|>
(ch 'w' >> pure 2) <|>
(ch 'y' >> pure 4) <|>
(ch 'z' >> pure 5) <|>
(do ch 'x',
    ((eof >> pure 3) <|>
		 (do n ← nat, pure (n + 5))))

meta def preterm : parser preterm :=
(do ch 's',
    n ← nat,
		((do ch '(',
		     pts ← sep_by1 (ch ',') preterm,
		     ch ')',
			   pure (list.foldl _root_.preterm.app (_root_.preterm.sym n) pts)) <|>
			(pure (_root_.preterm.sym n)))) <|>
(do n ← var_index, pure $ _root_.preterm.var n)

meta def preterm_to_term : _root_.preterm → tactic term
| (_root_.preterm.sym k)   := return $ term.sym k
| (_root_.preterm.app pt $ _root_.preterm.var k) :=
  do t ← preterm_to_term pt,
	   return (term.vpp t k)
| (_root_.preterm.app pt $ ps) :=
  do t ← preterm_to_term pt,
     s ← preterm_to_term ps,
		 return (term.app t s)
| (_root_.preterm.var k) := fail "Ill-formed term"

meta def term (s : string) : tactic term :=
match run_string preterm s with
| (sum.inl s)  := fail s
| (sum.inr pt) := preterm_to_term pt
end

meta def line (s : string) : tactic line :=
match lex ((unpunctuate s).filter (λ c, ¬ c ∈ ['*', '+', '|'])) with
| []          := failed
| (tk :: tks) :=
  do (k, r) ← number_rule tk,
	   let (ntks, ptks) := split_clastrings tks,
	   nts ← monad.mapm term ntks,
	   pts ← monad.mapm term ptks,
		 return ⟨k, r, (nts, pts)⟩
end

meta def lines (s : string) : tactic (list $ _root_.line) :=
do ss ← linestrings s,
   monad.mapm line ss

end parse
