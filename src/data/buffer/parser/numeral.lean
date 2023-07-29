/-
Copyright (c) 2020 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.buffer.parser.basic

/-!
# Numeral parsers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file expands on the existing `nat : parser ℕ` to provide parsers into any type `α` that
can be represented by a numeral, which relies on `α` having a 0, 1, and addition operation.
There are also convenience parsers that ensure that the numeral parsed in is not larger than
the cardinality of the type `α` , if it is known that `fintype α`. Additionally, there are
convenience parsers that parse in starting from "1", which can be useful for positive ordinals;
or parser from a given character or character range.

## Main definitions

* `parser.numeral` : The parser which uses `nat.cast`
  to map the result of `parser.nat` to the desired `α`
* `parser.numeral.of_fintype` :  The parser which `guard`s to make sure the parsed
  numeral is within the cardinality of the target `fintype` type `α`.

## Implementation details

When the `parser.numeral` or related parsers are invoked, the desired type is provided explicitly.
In many cases, it can be inferred, so one can write, for example
```lean
def get_fin : string → fin 5 :=
sum.elim (λ _, 0) id ∘ parser.run_string (parser.numeral.of_fintype _)
```

In the definitions of the parsers (except for `parser.numeral`), there is an
explicit `nat.bin_cast` instead an explicit or implicit `nat.cast`.
-/

open parser parse_result

namespace parser

variables (α : Type) [has_zero α] [has_one α] [has_add α]

/--
Parse a string of digits as a numeral while casting it to target type `α`.
-/
@[derive [mono, bounded, prog]]
def numeral : parser α :=
nat.bin_cast <$> nat

/--
Parse a string of digits as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint. The parser ensures that the numeral parsed in
is within the cardinality of the type `α`.
-/
@[derive [mono, bounded, prog]]
def numeral.of_fintype [fintype α] : parser α :=
do
  c ← nat,
  decorate_error (sformat!"<numeral less than {to_string (fintype.card α)}>")
    (guard (c < fintype.card α)),
  pure $ nat.bin_cast c

/--
Parse a string of digits as a numeral while casting it to target type `α`. The parsing starts
at "1", so `"1"` is parsed in as `nat.cast 0`. Providing `"0"` to the parser causes a failure.
-/
@[derive [mono, bounded, prog]]
def numeral.from_one : parser α :=
do
  c ← nat,
  decorate_error ("<positive numeral>")
    (guard (0 < c)),
  pure $ nat.bin_cast (c - 1)

/--
Parse a string of digits as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint. The parser ensures that the numeral parsed in
is within the cardinality of the type `α`. The parsing starts
at "1", so `"1"` is parsed in as `nat.cast 0`. Providing `"0"` to the parser causes a failure.
-/
@[derive [mono, bounded, prog]]
def numeral.from_one.of_fintype [fintype α] : parser α :=
do
  c ← nat,
  decorate_error (sformat!"<positive numeral less than or equal to {to_string (fintype.card α)}>")
    (guard (0 < c ∧ c ≤ fintype.card α)),
  pure $ nat.bin_cast (c - 1)

/--
Parse a character as a numeral while casting it to target type `α`,
The parser ensures that the character parsed in is within the bounds set by `fromc` and `toc`,
and subtracts the value of `fromc` from the parsed in character.
-/
@[derive [mono, bounded, err_static, step]]
def numeral.char (fromc toc : char) : parser α :=
do
  c ← decorate_error
    (sformat!"<char between '{fromc.to_string}' to '{toc.to_string}' inclusively>")
    (sat (λ c, fromc ≤ c ∧ c ≤ toc)),
  pure $ nat.bin_cast (c.to_nat - fromc.to_nat)

/--
Parse a character as a numeral while casting it to target type `α`,
which has a `[fintype α]` constraint.
The parser ensures that the character parsed in is greater or equal to `fromc` and
and subtracts the value of `fromc` from the parsed in character. There is also a check
that the resulting value is within the cardinality of the type `α`.
-/
@[derive [mono, bounded, err_static, step]]
def numeral.char.of_fintype [fintype α] (fromc : char) : parser α :=
do
  c ← decorate_error
    (sformat!"<char from '{fromc.to_string}' to '
    { (char.of_nat (fromc.to_nat + fintype.card α - 1)).to_string}' inclusively>")
    (sat (λ c, fromc ≤ c ∧ c.to_nat - fintype.card α < fromc.to_nat)),
  pure $ nat.bin_cast (c.to_nat - fromc.to_nat)

/-! ## Specific numeral types -/

/--
Matches an integer, like `43` or `-2`.
Large numbers may cause performance issues, so don't run this parser on untrusted input.
-/
def int : parser int :=
(coe <$> nat) <|> (ch '-' >> has_neg.neg <$> coe <$> nat)

/--
Matches an rational number, like `43/1` or `-2/3`.
Requires that the negation is in the numerator,
and that both a numerator and denominator are provided (e.g. will not match `43`).
Large numbers may cause performance issues, so don't run this parser on untrusted input.
-/
def rat : parser rat :=
(λ x y, ↑x / ↑y) <$> int <*> (ch '/' >> nat)

end parser
