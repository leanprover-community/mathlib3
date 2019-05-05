# The conversion tactic mode

Inside a tactic block, one can use the keyword `conv` to enter conversion
mode. This mode allows to travel inside assumptions and goals, even
inside `λ` binders in them, to apply rewriting or simplifying steps.

This is similar to the conversion tacticals (tactic combinators) found in
other theorem provers like HOL4, HOL Light or Isabelle.

### Basic navigation and rewriting

As a first example, let us prove
`example (a b c : ℕ) : a * (b * c) = a * (c * b)` (examples in this file
are somewhat artificial since the `ring` tactic from
`tactic.ring` could finish them immediately). The naive first attempt is
to enter tactic mode and try `rw mul_comm`. But this transforms the goal
into `b * c * a = a * (c * b)`, after commuting the very first
multiplication appearing in the term. There are several ways to fix this
issue, and one way is to use a more precise tool : the
conversion mode.  The following code block shows the current target after
each line. Note that the target is prefixed by `|` where normal mode
shows a goal prefixed by `⊢` (these targets are still called "goals"
though).

```lean
example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
begin
  conv
  begin          -- | a * (b * c) = a * (c * b)
    to_lhs,      -- | a * (b * c)
    congr,       -- 2 goals : | a and | b * c
    skip,        -- | b * c
    rw mul_comm, -- | c * b
  end
end
```

The above snippet show three navigation commands:
* `to_lhs` navigates to the left hand side of a relation (here
  equality), there is also a `to_rhs` navigating to the right hand side.
* `congr` creates as many targets as there are arguments to the current
  head function (here the head function is multiplication)
* `skip` goes to the next target

Once arrived at the relevant target, we can use `rw` as in normal mode.
Note that Lean tries to solves the current goal if it became `x = x` (in
the strict syntactical sense, definitional equality is not enough: one
needs to conclude by `refl` or `trivial` in this case).

The second main reason to use conversion mode is to rewrite under
binders. Suppose we want to prove `example (λ x : ℕ, 0+x) = (λ x, x)`.
The naive first attempt is to enter tactic mode and try `rw zero_add`.
But this fails with a frustrating
```
rewrite tactic failed, did not find
instance of the pattern in the target expression 0 + ?m_3
state:
⊢ (λ (x : ℕ), 0 + x) = λ (x : ℕ), x
```

The solution is:
```lean
example : (λ x : ℕ, 0 + x) = (λ x, x) :=
begin
  conv
  begin           -- | (λ (x : ℕ), 0 + x) = λ (x : ℕ), x
    to_lhs,       -- | λ (x : ℕ), 0 + x
    funext,       -- | 0 + x
    rw zero_add,  -- | x
  end
end
```
where `funext` is the navigation command entering inside the `λ` binder.
Note that this example is somewhat artificial, one could also do:
```lean
example : (λ x : ℕ, 0+x) = (λ x, x) :=
by funext ; rw zero_add
```

All this is also available to rewrite an hypothesis `H` from the local context
using `conv at H`.

### Pattern matching

Navigation using the above commands can be tedious. One can shortcut it
using pattern matching as follows:

```lean
example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
begin
conv in (b*c)
begin          -- | b * c
  rw mul_comm, -- | c * b
end
end
```

As usual, `begin` and `end` can be replaced by curly brackets to
delimit conversion mode and a single tactic invocation can be introduced
by `by` to get the one liner:

```lean
example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
by conv in (b*c) { rw mul_comm }
```

Beware that a well known bug makes Lean printing: "find converter
failed, pattern was not found" when the tactics inside conversion mode
fail, even if the pattern was actually found.

Of course wild-cards are allowed:

```lean
example (a b c : ℕ) : a + (b * c) = a + (c * b) :=
by conv in (_ * c) { rw mul_comm }
```

In all those cases, only the first match is affected.
A more sophisticated version of pattern matching is available inside
conversion mode using the `for` command. The following performs rewriting
only for the second and third occurrences of `b * c`:

```lean
example (a b c : ℕ) : (b * c) * (b * c) * (b * c) = (b * c) * (c * b)  * (c * b):=
by conv { for (b * c) [2, 3] { rw mul_comm } }
```

### Other tactics inside conversion mode

Besides rewriting using `rw`, one can use `simp`, `dsimp`, `change` and `whnf`.
`change` is a useful tool -- it allows changing a term to something
definitionally equal, rather like the `show` command in tactic mode.
The `whnf` command means "reduces to weak head normal form" and will eventually
be explained in [Programming in Lean](https://leanprover.github.io/programming_in_lean/#08_Writing_Tactics.html) section 8.4.

Extensions to `conv` provided by mathlib, such as `ring` and `norm_num`, can be
found at [docs/tactics.md#conv](../tactics.md#conv).
