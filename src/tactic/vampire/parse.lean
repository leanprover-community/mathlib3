/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek

  Parse proof output from Vampire.
-/

import data.buffer.parser
import tactic.vampire.proof

universe u

open list parser tactic

namespace vampire

inductive preterm : Type
| sym : nat  → preterm
| var : nat  → preterm
| app : preterm → preterm → preterm

namespace preterm

def repr : preterm → string
| (preterm.sym k)   := "& " ++ k.repr
| (preterm.var k)   := "# " ++ k.repr
| (preterm.app t s) := "(" ++ t.repr ++ " & " ++ s.repr ++ ")"

instance has_repr : has_repr preterm := ⟨repr⟩

meta instance has_to_format : has_to_format preterm := ⟨λ x, repr x⟩

def to_term : preterm → option term
| (preterm.sym k) := return $ term.sym k
| (preterm.app pt $ preterm.var k) :=
  do t ← pt.to_term,
	   return (term.vpp t k)
| (preterm.app pt $ ps) :=
  do t ← pt.to_term,
     s ← ps.to_term,
		 return (term.app t s)
| (preterm.var k) := none

end preterm

inductive rule
| inp             : rule
| map (k : nat)   : rule
| res (k m : nat) : rule

namespace rule

def repr : rule → string
| rule.inp        := "Inp"
| (rule.map k)    := "Map"  ++ ":" ++ k.repr
| (rule.res k m)  := "Res"  ++ ":" ++ k.repr ++ "," ++ m.repr

instance has_repr : has_repr rule := ⟨repr⟩

meta instance has_to_format : has_to_format rule := ⟨λ x, repr x⟩

end rule

structure line :=
(n : nat)
(c : cla)
(r : rule)

namespace line

def repr : line → string
| ⟨n, c, r⟩ := n.repr ++ ". " ++ c.repr ++ " " ++ r.repr

instance has_repr : has_repr line := ⟨repr⟩

meta instance has_to_format : has_to_format line := ⟨λ x, repr x⟩

end line

def digits : list char :=
[ '0', '1', '2', '3', '4', '5', '6', '7', '8', '9' ]

namespace parse

meta def to_tactic {α : Type u} : (string ⊕ α) → tactic α
| (sum.inl s) := fail s
| (sum.inr a) := return a

def is_proof_line_string (s : string) : parser bool :=
match s.data with
| []       := pure ff
| (c :: _) := pure (c ∈ digits)
end

def digits : parser string := many_char (one_of digits)

def nat : parser nat :=
digits >>= (return ∘ string.to_nat)

def character : parser char := sat (λ x, x ≠ '\n')

def output_line_string : parser string :=
many_char character <* (ch '\n' <|> eps)

meta def proof_line_strings : parser (list string) :=
many output_line_string >>=
monad.filter is_proof_line_string

def ws : parser unit := many' (ch ' ')

def rule : parser rule :=
( do (str "factoring" <|> str "duplicate literal removal") <* ws,
     k ← nat, pure (rule.map k) ) <|>
( do (str "resolution" <|> str "subsumption resolution") <* ws,
     k ← (nat <* ch ','),
     m ← nat,
     pure (rule.res k m) ) <|>
( do str "input", pure rule.inp )

meta def preterm : parser preterm :=
( do n ← ch 's' *> nat,
     ( ( do pts ← ch '(' *> (sep_by1 (ch ',') preterm) <* ch ')',
     		    pure (list.foldl _root_.vampire.preterm.app
              (_root_.vampire.preterm.sym n) pts) ) <|>
       ( pure (_root_.vampire.preterm.sym n) ) )) <|>
( do n ← ch 'X' *> nat,
     pure $ _root_.vampire.preterm.var n)

meta def term : parser term :=
do pt ← preterm,
   match pt.to_term with
   | none := parser.fail "Ill-formed term"
   | (some t) := pure t
   end

meta def lit : parser lit :=
( do t ← ch '~' *> term,
     pure (ff, t) ) <|>
( do t ← term, pure (tt, t) )

meta def line_core : parser (cla × _root_.vampire.rule) :=
ws *>
( ( do l ← lit <* ws,
       (ch '|' <|> eps),
       (c, r) ← line_core,
       pure (l :: c, r) )  <|>
  ( do ((str "$false" >> ws) <|> eps),
       r ← (ch '[' *> rule <* ch ']'),
       (ch '\n' <|> eps),
       pure ([], r) ) )

meta def proof_line : parser line :=
do n ← nat, ch '.',
   (c, r) ← line_core,
   return ⟨n, c, r⟩

end parse

meta def proof_line (s : string) : tactic line :=
match run_string parse.proof_line s with
| (sum.inl str) := fail str
| (sum.inr l)   := return l
end

meta def proof_line_strings (s : string) : tactic (list string) :=
match run_string parse.proof_line_strings s with
| (sum.inl str) := fail str
| (sum.inr ss)  := return ss
end

end vampire
