/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.fintype.card

/-!
# Numeral parsers

This file expands on the existing `nat : parser ℕ` to provide parsers into any type `α` that
can be represented by a numeral, which relies on `α` having a 0, 1, and addition operation.
There are also convenience parsers that ensure that the numeral parsed in is not larger than
the cardinality of the type `α` , if it is known that `fintype α`. Additionally, there are
convenience parsers that parse in starting from "1", which can be useful for positive ordinals;
or parser from a given character or character range.

## Main definitions

* 'numeral` : The parser which uses `nat.cast` to map the result of `parser.nat` to the desired `α`
* `numeral.of_fintype` :  The parser which `guard`s to make sure the parsed numeral is within the
  cardinality of the target `fintype` type `α`.

## Implementation details

When the `numeral` or related parsers are invoked, the desired type is provided explicitly. In many
cases, it can be inferred, so one can write, for example
```lean
def get_fin : string → fin 5 :=
sum.elim (λ _, 0) id ∘ parser.run_string (parser.numeral.of_fintype _)
```

In the definitions of the parsers (except for `numeral`), there is an implicit `nat.cast` in
the final `pure` statement.
-/

open parser parse_result

namespace parser

variables (α : Type) [has_zero α] [has_one α] [has_add α]

def numeral : parser α :=
nat.cast <$> nat

def numeral.of_fintype [fintype α] : parser α :=
do
  c ← nat,
  guard (c < fintype.card α),
  pure c

def numeral.from_one : parser α :=
do
  c ← nat,
  guard (0 < c),
  pure $ ((c - 1) : ℕ)

def numeral.from_one.of_fintype [fintype α] : parser α :=
do
  c ← nat,
  guard (0 < c ∧ c ≤ fintype.card α),
  pure $ ((c - 1) : ℕ)

def numeral.char (fromc toc : char) : parser α :=
do
  c ← sat (λ c, fromc ≤ c ∧ c ≤ toc),
  pure $ ((c.to_nat - fromc.to_nat) : ℕ)

def numeral.char.of_fintype [fintype α] (fromc : char) : parser α :=
do
  c ← sat (λ c, fromc ≤ c ∧ c.to_nat - fintype.card α < fromc.to_nat),
  pure $ ((c.to_nat - fromc.to_nat) : ℕ)

end parser
