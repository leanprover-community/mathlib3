# Library Style Guidelines #
Author: [Jeremy Avigad](http://www.andrew.cmu.edu/user/avigad)

In addition to the [naming conventions](naming.md),
files in the Lean library generally adhere to the following guidelines
and conventions. Having a uniform style makes it easier to browse the
library and read the contents, but these are meant to be guidelines
rather than rigid rules.

### Variable conventions ###

- `u`, `v`, `w`, ... for universes
- `α`, `β`, `γ`, ... for types
- `a`, `b`, `c`, ... for propositions
- `x`, `y`, `z`, ... for elements of a generic type
- `h`, `h₁`, ...     for assumptions
- `p`, `q`, `r`, ... for predicates and relations
- `s`, `t`, ...      for lists
- `s`, `t`, ...      for sets
- `m`, `n`, `k`, ... for natural numbers
- `i`, `j`, `k`, ... for integers



### Line length ###

Lines should not be longer than 100 characters. This makes files
easier to read, especially on a small screen or in a small window.

### Header and imports ###

The file header should contain copyright information, a list of all
the authors who have worked on the file, and a description of the
contents. Do all `import`s right after the header, without a line
break. You can also open namespaces in the same block.

```lean
/-
Copyright (c) 2015 Joe Cool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Joe Cool.

A theory of everything.
-/
import data.nat algebra.group
open nat eq.ops
```

### Structuring definitions and theorems ###

Use spaces around ":" and ":=". Put them before a line break rather
than at the beginning of the next line.

Use two spaces to indent. You can use an extra indent when a long line
forces a break to suggest the the break is artificial rather than
structural, as in the statement of theorem:

```lean
open nat
theorem two_step_induction_on {P : nat → Prop} (a : nat) (H1 : P 0) (H2 : P (succ 0))
    (H3 : ∀ (n : nat) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) : P a :=
sorry
```

If you want to indent to make parameters line up, that is o.k. too:
```lean
open nat
theorem two_step_induction_on {P : nat → Prop} (a : nat) (H1 : P 0) (H2 : P (succ 0))
                              (H3 : ∀ (n : nat) (IH1 : P n) (IH2 : P (succ n)), P (succ (succ n))) :
  P a :=
sorry
```

After stating the theorem, we generally do not indent the first line
of a proof, so that the proof is "flush left" in the file.
```lean
open nat
theorem nat_case {P : nat → Prop} (n : nat) (H1: P 0) (H2 : ∀m, P (succ m)) : P n :=
nat.induction_on n H1 (take m IH, H2 m)
```

When a proof rule takes multiple arguments, it is sometimes clearer, and often
necessary, to put some of the arguments on subsequent lines. In that case,
indent each argument.
```lean
open nat
axiom zero_or_succ (n : nat) : n = zero ∨ n = succ (pred n)
theorem nat_discriminate {B : Prop} {n : nat} (H1: n = 0 → B)
    (H2 : ∀m, n = succ m → B) : B :=
or.elim (zero_or_succ n)
  (take H3 : n = zero, H1 H3)
  (take H3 : n = succ (pred n), H2 (pred n) H3)
```
Don't orphan parentheses; keep them with their arguments.

Here is a longer example.
```lean
import data.list
open list eq.ops
variable {T : Type}
local attribute mem [reducible]
local attribute append [reducible]
theorem mem_split {x : T} {l : list T} : x ∈ l → ∃s t : list T, l ` s ++ (x::t) :`
list.induction_on l
  (take H : x ∈ [], false.elim (iff.elim_left !mem_nil_iff H))
  (take y l,
    assume IH : x ∈ l → ∃s t : list T, l = s ++ (x::t),
    assume H : x ∈ y::l,
    or.elim (eq_or_mem_of_mem_cons H)
      (assume H1 : x = y,
        exists.intro [] (!exists.intro (H1 ▸ rfl)))
      (assume H1 : x ∈ l,
        obtain s (H2 : ∃t : list T, l = s ++ (x::t)), from IH H1,
        obtain t (H3 : l = s ++ (x::t)), from H2,
        have H4 : y :: l = (y::s) ++ (x::t), from H3 ▸ rfl,
        !exists.intro (!exists.intro H4)))
```

A short definition can be written on a single line:
```lean
open nat
definition square (x : nat) : nat := x * x
```
For longer definitions, use conventions like those for theorems.

A "have" / "from" pair can be put on the same line.
```lean
have H2 : n ≠ succ k, from subst (ne_symm (succ_ne_zero k)) (symm H),
[...]
```
You can also put it on the next line, if the justification is long.
```lean
have H2 : n ≠ succ k,
  from subst (ne_symm (succ_ne_zero k)) (symm H),
[...]
```
If the justification takes more than a single line, keep the "from" on the same
line as the "have", and then begin the justification indented on the next line.
```lean
have n ≠ succ k, from
  not_intro
    (take H4 : n = succ k,
      have H5 : succ l = succ k, from trans (symm H) H4,
      have H6 : l = k, from succ_inj H5,
      absurd H6 H2)))),
[...]
```

When the arguments themselves are long enough to require line breaks, use
an additional indent for every line after the first, as in the following
example:
```lean
import data.nat
open nat eq algebra
theorem add_right_inj {n m k : nat} : n + m ` n + k → m = k :`
nat.induction_on n
  (take H : 0 + m = 0 + k,
    calc
        m = 0 + m : symm (zero_add m)
      ... = 0 + k : H
      ... = k     : zero_add)
  (take (n : nat) (IH : n + m ` n + k → m = k) (H : succ n + m ` succ n + k),
    have H2 : succ (n + m) = succ (n + k), from
      calc
        succ (n + m) = succ n + m   : symm (succ_add n m)
                 ... = succ n + k   : H
                 ... = succ (n + k) : succ_add n k,
    have H3 : n + m = n + k, from succ.inj H2,
    IH H3)
```

### Binders ###

Use a space after binders:
or this:
```lean
example : ∀ α : Type, ∀ x : α, ∃ y, (λ u, u) x ` y :`
take (α : Type) (x : α), exists.intro x rfl
```

### Calculations ###

There is some flexibility in how you write calculational proofs. In
general, it looks nice when the comparisons and justifications line up
neatly:
```lean
import data.list
open list
variable {α : Type}

theorem reverse_reverse : ∀ (l : list α), reverse (reverse l) = l
| []       := rfl
| (a :: l) := calc
    reverse (reverse (a :: l)) = reverse (concat a (reverse l))     : rfl
                           ... = reverse (reverse l ++ [a])         : concat_eq_append
                           ... = reverse [a] ++ reverse (reverse l) : reverse_append
                           ... = reverse [a] ++ l                   : reverse_reverse
                           ... = a :: l                             : rfl
```

To be more compact, for example, you may do this only after the first line:

```lean
import data.list
open list
variable {α : Type}

theorem reverse_reverse : ∀ (l : list α), reverse (reverse l) = l
| []       := rfl
| (a :: l) := calc
    reverse (reverse (a :: l))
          = reverse (concat a (reverse l))     : rfl
      ... = reverse (reverse l ++ [a])         : concat_eq_append
      ... = reverse [a] ++ reverse (reverse l) : reverse_append
      ... = reverse [a] ++ l                   : reverse_reverse
      ... = a :: l                             : rfl
```

### Sections ###

Within a section, you can indent definitions and theorems to make the
scope salient:
```lean
section my_section
  variable α : Type
  variable P : Prop

  definition foo (x : α) : α := x

  theorem bar (H : P) : P := H
end my_section
```
If the section is long, however, you can omit the indents.

We generally use a blank line to separate theorems and definitions,
but this can be omitted, for example, to group together a number of
short definitions, or to group together a definition and notation.

## Comments

Use comment delimeters `/-- -/` to provide section headers and
separators, and for long comments. Use `--` for short or in-line
comments.

------
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
