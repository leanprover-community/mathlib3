import .term .parse

open list parser tactic

namespace vampire

@[derive decidable_eq]
inductive inf : Type
| n : nat → inf
| h : inf
| r : inf
| t : inf
| s : inf
| c : inf
| e : inf
| m : inf
| y : inf
| a : inf
| v : inf

namespace inf

def repr : inf → string
| (n k) := k.repr
| h := "h"
| r := "r"
| t := "t"
| s := "s"
| c := "c"
| e := "e"
| m := "m"
| y := "y"
| a := "a"
| v := "v"

instance has_repr : has_repr inf := ⟨repr⟩

meta instance has_to_format : has_to_format inf := ⟨λ x, repr x⟩

end inf

@[reducible] def infs : Type := list inf

def infs.repr : infs → string
| [] := ""
| [i] := i.repr
| (i :: is) := i.repr ++ " " ++ infs.repr is

def term.to_infs : term → infs
| (term.sym k)   := [inf.n k, inf.y]
| (term.app t s) := t.to_infs ++ s.to_infs ++ [inf.a]
| (term.vpp t k) := t.to_infs ++ [inf.n k, inf.v]

def term.to_rr : term → string := infs.repr ∘ term.to_infs

def lit.to_rr : lit → string
| (tt, t) := t.to_rr ++ " ps"
| (ff, t) := t.to_rr ++ " ng"

def cla.to_rr : cla → string
| []       := "nl"
| (l :: c) := cla.to_rr c ++ " " ++ l.to_rr ++ " cs"

def mat.to_rr : mat → string
| []       := "nl"
| (c :: m) := mat.to_rr m ++ " " ++ c.to_rr ++ " cs"

def mapping.to_infs : mapping → infs
| (k, sum.inl m) := [inf.n k, inf.n m]
| (k, sum.inr t) := inf.n k :: t.to_infs

def mappings.to_infs : mappings → infs
| []       := [inf.e]
| (m :: μ) := mappings.to_infs μ ++ m.to_infs ++ [inf.m]

meta def parse_inf_core : parser inf :=
(do k ← parse.nat, pure $ inf.n k) <|>
(ch 'h' >> pure inf.h) <|>
(ch 'r' >> pure inf.r) <|>
(ch 't' >> pure inf.t) <|>
(ch 's' >> pure inf.s) <|>
(ch 'c' >> pure inf.c) <|>
(ch 'e' >> pure inf.e) <|>
(ch 'm' >> pure inf.m) <|>
(ch 'y' >> pure inf.y) <|>
(ch 'a' >> pure inf.a) <|>
(ch 'v' >> pure inf.v)

meta def parse_inf : parser inf :=
parse_inf_core <* many (ch ' ')

meta def parse_infs : parser infs :=
many parse_inf

end vampire
