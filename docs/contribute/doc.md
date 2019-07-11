# Documentation style

We are in the process of implementing new documentation requirements for mathlib. All future pull requests must meet the following standards.

## Header comment

Explain the header fields here.

Replace the example below with a better one?

```
/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

# p-adic norm

This file defines the p-adic valuation and the p-adic norm on ℚ.

The p-adic valuation on ℚ is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on p.

The valuation induces a norm on ℚ. This norm is a nonarchimedean absolute value.
It takes values in {0} ∪ {1/p^k | k ∈ ℤ}.

## Notations

This file uses the local notation `/.` for `rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking (prime p) as a type class argument.

## References

Tags: p-adic, p adic, padic, norm, valuation

-/
```

## Docstrings

Every definition and major theorem is required to have a doc string.

Explain more here.

## Examples

The following files are maintained as examples of good documentation style:

* where?
* where?
