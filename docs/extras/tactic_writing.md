# Tactics writing in Lean tutorial

## Monadology

Tactics are programs that act on the proof state.  But Lean is a
functional programming language. It means all you can do is
define and evaluate functions. Each function takes input with a
predefined type, and gives output with a predefined type. It seems to
prevent having a global state (like the current assumptions and goals),
and having output type depending on the input value (for instance a
tactic can succeed or fail), or outputting messages. These issues are
resolved by three layers of tricks (the following brief descriptions
will hopefully become clearer later):
* using complicated types carrying the proof state and tactic running
  state around
* using clever notations that hide most of the complicated type
  bookkeeping and composition
* using interactive tactic blocks, introduced by `by` or delimited by
  `begin`/`end`

The first two points are collectively known as monadic programming (of
course there is a more precise definition, but we will try to ignore it).

The type of a function that can inspect the proof state, modify it, and
potentially return something of type `α` (or fail) is called `tactic α`. In
particular `tactic unit` is only about manipulating proof state, without
trying to return anything (technically it will return something of type
`unit`, which is the type having exactly one term, denoted by `()`).
Such functions are either called by other
tactics---those are typically in the `tactic` namespace---or called
interactively by users inside tactic blocks---those must be in the
`tactic.interactive` namespace (this is not quite necessary for very simple
tactics, but weird things will happen in general when ignoring this rule). A
shortcut which is sometimes convenient is: one can copy definitions with name
`my_tac1`, `my_tac2`, `my_tac3`, into the `tactic.interactive` namespace using
`` run_cmd add_interactive [`my_tac1,`my_tac2, `my_tac3] ``.
These functions will be used to generate Lean proofs, but we will not prove
anything about these functions themselves, nor will the constants `my_tac1`,
`my_tac2`, etc. appear in the proofs
that they generate. By prefacing them with the keyword `meta`, we tell Lean that
they are for "evaluation purposes only," which disables some of the checks that
non-`meta` declarations must pass.
This is enough knowledge to write a first tactic.

```lean
meta def my_first_tactic : tactic unit := tactic.trace "Hello, World."

example : true :=
begin
  my_first_tactic,
  trivial
end
```

In the example, `my_first_tactic` is underlined in green (in VScode) and
moving the cursor on that line will display our message in the Lean
messages buffer.

Next we need to learn how to chain several actions. Deep down, this is
all about composing functions, but the monadic notations hide this and
emulate imperative programming. We need to use the `and_then`
combinator. The first way is to use the infix notation `>>`, as in:

```lean
meta def my_second_tactic : tactic unit :=
tactic.trace "Hello," >> tactic.trace "World."
```
which now prints our message in two pieces. Alternatively, one can use
the `do` syntax, which has other goodies. This introduces a
comma-separated list of instructions to perform in sequence.
```lean
meta def my_second_tactic' : tactic unit :=
do
  tactic.trace "Hello,",
  tactic.trace "World."
```

Besides displaying messages, the next thing tactics can do is to fail,
potentially with some explanation.
```lean
meta def my_failing_tactic  : tactic unit := tactic.failed

meta def my_failing_tactic' : tactic unit :=
tactic.fail "This tactic failed, we apologize for the inconvenience."
```

When chaining instructions, the first failure interrupts the process.
However the `orelse` combinator, denoted by an infix `<|>` allows to try
its right-hand side if its left-hand side failed. The following will
successfully deliver its message.
```lean
meta def my_orelse_tactic : tactic unit :=
my_failing_tactic <|> my_first_tactic
```

The next composite thing to do is to use some function that, after
reading or altering the proof state, actually tries to return
something. For instance the built-in `tactic.target` (tries to) return
the current goal. This goal has type `expr` (more on that type later).
The type of `tactic.target` is thus `tactic expr`. Say we want to trace
the current goal. A naive attempt would be:
```lean
meta def broken_trace_goal : tactic unit :=
tactic.trace tactic.target    -- WRONG!
```
This cannot be correct because `tactic.target` could fail (there could
be no more goal) and `tactic.trace` cannot take that failure as an
input. We need the bind combinator, with infix notation `>>=`, sending
the output of its left-hand side to its right-hand side in case of
success and failing otherwise.
```lean
meta def trace_goal : tactic unit :=
 tactic.target >>= tactic.trace
```
Alternatively, especially if the output of `tactic.target` could be used
several times, one can use the `do` blocks assignments using `←` (the
same arrow as in the rewrite syntax). This emulation of imperative
variable assignment will of course fail (as the failing tactics above)
if the right-hand side of the assignment fails.
```lean
meta def trace_goal' : tactic unit :=
do
 goal ← tactic.target,
 tactic.trace goal
```
Beware that this kind of assignment is only trying to extract data of type
`α` from something of type `tactic α`. It cannot be used to store
regular stuff. The following doesn't work.
```lean
meta def broken_assignment : tactic unit :=
do
 message ← "Hello, World.",  -- WRONG!
 tactic.trace message
```
However, one can use `let` in `do` blocks, as in:
```lean
meta def let_example : tactic unit :=
do
 let message := "Hello, World.",
 tactic.trace message
```
Next, we want to write tactics returning something, as `tactic.target`
is doing. The only extra ingredient is the `return` function. The
following function tries to return `tt` is there is no more goal, `ff`
otherwise. The next one can be used interactively and traces the result
(note that using the first one interactively won't have any visible
effect since interactive use ignores the returned value).
```lean
meta def is_done : tactic bool :=
(tactic.target >> return ff) <|> return tt

meta def trace_is_done : tactic unit :=
is_done >>= tactic.trace
```
The last thing we will need about monadic assignment is pattern-matching
assignment. The following tactic tries to define expressions `l` and `r` as
the left and right hand sides of the current goal. It also uses the
`to_string` function which is very convenient in combination with `trace`
in order to debug tactics, and works on any type which is an instance of `has_to_string`.
```lean
meta def trace_goal_is_eq : tactic unit :=
(do  `(%%l = %%r) ← tactic.target,
     tactic.trace $ "Goal is equality between " ++ (to_string l) ++ " and " ++ (to_string r) )
   <|> tactic.trace "Goal is not an equality"
```
The parenthesis in the above code don't look very nice. One could use
instead curly brackets which allow to delimit a `do` block, as in:
```lean
meta def trace_goal_is_eq : tactic unit :=
do { `(%%l = %%r) ← tactic.target,
     tactic.trace $ "Goal is equality between " ++ (to_string l) ++ " and " ++ (to_string r) }
   <|> tactic.trace "Goal is not an equality"
```
## A first real world tactic

We have studied enough monadology to understand our first useful tactic:
the `assumption` tactic, which searches the local context for an
assumption which closes the current goal. It uses a couple more builtin
tactics, both declared and briefly documented in the core library in
[init/meta/tactic.lean](https://github.com/leanprover/lean/blob/master/library/init/meta/tactic.lean) but actually implemented in C++.
First `infer_type : expr → tactic expr`
tries to determine the type of an expression (since it returns a
`tactic expr`, it must be chained with either `>>=` or `←`, as explained
above).
Next `tactic.unify` which, modulo a couple of optional parameters, takes
two expressions and succeeds if and only if they are definitionaly equal.
The first piece of the assumption tactic is a helper function searching
an expression sharing the type of some expression `e` in a list of
expressions, returning the first match (or failing if nothing matches).
```lean
meta def find_matching_type (e : expr) : list expr → tactic expr
| []         := tactic.failed
| (H :: Hs)  := do t ← tactic.infer_type H,
                   (tactic.unify e t >> return H) <|> find_matching_type Hs
```
Make sure you really understand the control flow in the above code using
the previous section. The basic pattern is classical recursive find in a
list. Notice the expression `e` is left of colon, hence it will be passed
unchanged to the recursive call `find_matching_type Hs`. The choice of
name `H` stands for `hypothesis`, while `Hs`, following Haskell's naming
conventions, stands for several hypotheses. The imperative analogue of
what happens for non-empty lists would read something like the following
imperative pseudo-code
```
if unify(e, infer_type(H)) then return H else find_matching_type(e, HS)
```
We can now use this function for our interactive tactic. We first need
to grab the local context using `local_context`, which returns a list of
expressions that we can pass to our `find_matching_type`. If that
function succeeds, its output is passed to the builtin tactic
`tactic.exact`. Here we need to use the fully qualified name because of
possible confusion with the interactive version of `exact` (which takes
different parameters, so it's not an exact copy of the non-interactive
one). This is good opportunity to point out that the beginning of this
tutorial uses fully qualified names everywhere for clarity, but of
course the real world workflow is to open the `tactic` namespace.
```lean
meta def my_assumption : tactic unit :=
do { ctx ← tactic.local_context,
     t   ← tactic.target,
     find_matching_type t ctx >>= tactic.exact }
<|> tactic.fail "my_assumption tactic failed"
```
Bonus question: what if we remove the brackets? Will it still
type-check? If yes, will the resulting tactic be the same?


##  Monadic loops

A crucial tool of imperative programming is loops, so monads must
emulate this. We already know from usual Lean that `list.map` and
`list.foldr`/`list.foldl` allow to loop on elements of list. But we need
version that interacts nicely with the monad world (consuming and
returning terms of type `tactic stuff`). Those versions are prefixed with
"m" for monad, as in `list.mmap`, `list.mfoldr` etc. Our tactic is then:
```lean
meta def list_types : tactic unit :=
do
  l ← tactic.local_context,
  l.mmap (λ h, tactic.infer_type h >>= tactic.trace),
  return ()
```
The last line is a bit silly, it's there because what we get from the
previous line has type `list (tactic unit)`, so it cannot be the final
piece of our do block. Hence we add `return ()` where `()` is the
only term of type `unit`. One can also use the tactic `skip` to achieve
the same goal. This special case is so common that we actually have a
variant `list.mmap'` of `list.mmap` which discards the result of
the function applied to elements of the list, and returns `()` when it's
done traversing the list.

## Manipulating the local context

Our next goal is to be able to use and create assumptions in the local context.
We will write a tactic that produces a new assumption by adding two known
equalities (or failing miserably if this operation doesn't make sense). At
first the names of thoses two equalities will be stupidly hardwired in our
tactic. So we want a tactic performing the first line in the following proof.
```lean
example (a b j k : ℤ) (h₁ : a = b) (h₂ : j = k) :
  a + j = b + k :=
begin
  have := congr (congr_arg has_add.add h₁) h₂,
  exact this
end
```

The first new concept we need is that of a name. In order to allow for
namespace management, names in Lean are actually defined as an inductive
type, in core library [meta/name.lean](https://github.com/leanprover/lean/blob/master/library/init/meta/name.lean). Manpulating its constructors is not
convenient, so we use instead the backtick notation (this is the first of
many uses of backticks in tactic writing). Actually we already did that when
discussing the `add_interactive` command at the very beginning. Accessing an
item of the local context by its name is done by `tactic.get_local`. The next
new piece we need is `tactic.interactive.«have»` which will create our new
context item. Its weird name works around the fact that `have` is a keyword,
hence not a valid name. It takes two optional arguments that we ignore for
now, and a pre-expression which is a proof of our new item. Such a
pre-expression is constructed using the double-backtick-parenthesis notation:
``` ``(...) ```. Inside such a construction, previously assigned expressions
are accessed using the anti-quotation prefix `%%`. This syntax is very close to the pattern matching syntax we saw above (but different).

```lean
open tactic.interactive («have»)
open tactic (get_local infer_type)

meta def tactic.interactive.add_eq_h₁_h₂ : tactic unit :=
do e1 ← get_local `h₁,
   e2 ← get_local `h₂,
   «have» none none ``(_root_.congr (congr_arg has_add.add %%e1) %%e2)

example (a b j k : ℤ) (h₁ : a = b) (h₂ : j = k) :
  a + j = b + k :=
begin
  add_eq_h₁_h₂,
  exact this
end
```
A last remark about the above tactic: the names `` `h₁ `` and `` `h₂ `` are resolved when the tactic is executed. In order to trigger name resolution when
the tactic is parsed, one should use double-backtick, as in ``` ``h₁ ```. Of course
in the above context, that would trigger an error since nothing named `h₁` is
in sight at tactic parsing time. But it can be useful in other cases.

## Tactic arguments parsing

### Parsing identifiers

Obviously the previous tactic is useless if the assumption names are hardwired. So we replace it by:
```lean
open interactive (parse)
open lean.parser (ident)

meta def tactic.interactive.add_eq (h1 : parse ident) (h2 : parse ident) : tactic unit :=
do e1 ← get_local h1,
   e2 ← get_local h2,
   «have» none none ``(_root_.congr (congr_arg has_add.add %%e1) %%e2)
```
The arguments `h1` and `h2` tell lean to parse identifiers. There is quite a
bit of trickery going one here. The Lean parser sees `parse` left of colon,
so it knows it must do some argument parsing, but then the resulting type is
nothing but a name, as demonstrated below.
```lean
meta example : (parse ident) = name := rfl
```

### Parsing optional arguments and using tokens

The next improvement to this tactic offers the opportunity to name the new
local assumption (which is currently named `this`). Such names are
traditionaly introduced by the token `with`, followed by the desired identifier.
The "followed by" is expressed by the `seq_right` combinator (there is again
a monad lurking here), with notation `*>`. Parsing a token is introduced by
`lean.parser.tk` followed by a string which must be taken from a
predetermined list (the initial value of this list can be found in
Lean source code, in [frontends/lean/token_table.cpp](https://github.com/leanprover/lean/blob/master/src/frontends/lean/token_table.cpp), elements are added to this list when literals are used in `notation`, `infix`, or `precedence`). And then the
combination is wrapped into `optional` to make it optional. The term `h` we
get below has then type `option name` and can be passed as the first argument
of `«have»`, which will use it if provided, and otherwise use the name `this`.
```lean
open lean.parser (tk)
meta def tactic.interactive.add_eq' (h1 : parse ident) (h2 : parse ident)
  (h : parse (optional (tk "with" *> ident))) : tactic unit :=
do e1 ← get_local h1,
   e2 ← get_local h2,
   «have» h none ``(_root_.congr (congr_arg has_add.add %%e1) %%e2)

example (m a b c j k : ℤ) (Hj : a = b) (Hk : j = k) :
  a + j = b + k :=
begin
  add_eq' Hj Hk with new,
  exact new
end
```

### Parsing locations and expressions

Our next tactic multiplies from the left an equality by a given expression
(or fails if this operation wouldn't make sense). We want to mechanize the following proof.
```lean
example (a b c : ℤ) (hyp : a = b) : c*a = c*b :=
begin
  replace hyp := congr_arg (λ x, c*x) hyp,
  exact hyp
end
```

The main new skills here consist in indicating at what location we want to
act, using the traditional token `at`, and passing an expression to the
tactic. Locations are defined in the core library [meta/interactive_base.lean](https://github.com/leanprover/lean/blob/master/library/init/meta/interactive_base.lean) as
an inductive type having two constructors: `wildcard` which indicates all
locations, and `loc.ns` which takes a `list (option name)`, where `none` in
the `option name` means the current goal, whereas `some n` means the thing
named `n` in the local context. In our case we will pattern-match on the
parsed location and reject everything except specifying a single name from
the local context. The second new piece is how to parse a user-provided
expression. The relevant parser is `interactive.types.texpr`, whose result is
converted to an actual expression using `tactic.i_to_expr`. This is also the
opportunity for our first serious use of pattern matching assignment, and
for using the second optional argument of `«have»` which is the expected type
(otherwise we would get unapplied multiplication, with an explicit lambda, try it!).
```lean
open interactive (loc.ns)
open interactive.types (texpr location)
meta def mul_left (q : parse texpr) : parse location → tactic unit
| (loc.ns [some h]) := do
   e ← tactic.i_to_expr q,
   H ← get_local h,
   `(%%l = %%r) ← infer_type H,
   «have» h ``(%%e*%%l = %%e*%%r) ``(congr_arg (λ x, %%e*x) %%H),
   tactic.clear H
| _ := tactic.fail "mul_left takes exactly one location"

example (a b c : ℤ) (hyp : a = b) : c*a = c*b :=
begin
  mul_left c at hyp,
  exact hyp
end
```

As a last refinement, let us make a version of this tactic which names the
multiplied equality by appending `.mul`, and optionally removes the original
one if the tactic name is followed by `!`. This is the opportunity to use
`when` which is the monadic version of `ite` (with else branch doing nothing).
See [category/combinators.lean](https://github.com/leanprover/lean/blob/master/library/init/category/combinators.lean) in core library for other variations on this idea.
```lean
meta def mul_left_bis (clear_hyp : parse (optional $ tk "!")) (q : parse texpr) :
parse location → tactic unit
| (loc.ns [some h]) := do
   e ← tactic.i_to_expr q,
   H ← get_local h,
   `(%%l = %%r) ← infer_type H,
   «have» (H.local_pp_name ++ "mul" : name) ``(%%e*%%l = %%e*%%r) ``(congr_arg (λ x, %%e*x) %%H),
   when clear_hyp.is_some (tactic.clear H)
| _ := tactic.fail "mul_left_bis takes exactly one location"
```

## What to read now?

This is the end of this tutorial (although there are two cheat sheets below).
If you want to learn more, you can read the definitions of tactics in either
the core library or mathlib, see what you can understand, and ask specific
questions on Zulip. For more theory, especially a proper explanation of monads, you can read
[Programming in Lean](https://github.com/leanprover/programming_in_lean), but the actual tactic writing part is not up to date. The official documentation of the tactic framework is
the paper [A Metaprogramming Framework for Formal Verification](https://leanprover.github.io/papers/tactic.pdf).

## Mario's backtick cheat sheet

This section is a direct compilation of messages from Mario on Zulip.

* `` `my.name `` is the way to refer to a name. It is essentially a form of string quoting; no checks are done besides parsing dots into namespaced names

* ``` ``some ``` does name resolution at parse time, so this example expands to  `` `option.some `` and will error if the given name doesn't exist
* `` `(my expr) `` constructs an expression at parse time, resolving what it can in the current (of the tactic) namespace
* ``` ``(my pexpr) ``` constructs a pre-expression at parse time, resolving in the current (of the tactic) namespace
* ```` ```(my pexpr) ```` constructs a pexpr, but defers resolution to run time (of the tactic), meaning that any references will be resolved in the namespace of the begin end block of the user, rather than the tactic itself
* `%%`: This is called anti-quotation, and is supported in all the expr and pexpr quoting expressions `` `(expr) ``, ``` ``(pexpr) ```, ```` ```(pexpr) ````, as well as `` `[tacs] ``. Wherever an expression is expected inside one of these quoting constructs, you can use `%%e` instead, where `e` has type `expr` in the outer context of the tactic, and it will be spliced into the constructed expr/pexpr/etc. For example, if `a b : expr` then  `` `(%%a + %%b) `` is of type `expr`
* The `reflect` function turns a term `t : T` into an `expr` that reflects `t`, if Lean can infer an instance `reflected t`. This can be used, for example, to refer to local variables from a tactic definition inside a quotation, using `%%(reflect n)`. As an example, we could write
    ```
    meta def assert_ge_zero (n : ℕ) : tactic unit :=
    do v ← to_expr ``(nat.zero_le %%(reflect n)),
       t ← infer_type v,
       assertv `h t v,
       skip
    ```
    If you just wrote `n` directly here you'd get a "unexpected local in quotation expression" error.
* `` `[tac...] `` is exactly the same as `begin tac... end` in the sense that it parses tac... using the interactive mode parser, but instead of evaluating the tactic to produce a term, it just wraps up the list of tactics as a single tactic of type tactic unit. This is useful for writing "macros" or light-weight tactic writing


Also worth mentioning are `expr` pattern matches, which have the same syntax
like `` `(%%a + %%b) ``. These can be used in the pattern position of a match or on
the left side of a `←` in do notation, and will destruct an expression and
bind the antiquoted variables.
For example, if `e` is an expression then `` do `(%%a = %%b) ← return e, ... `` will check that `e` is an equality, and bind the LHS and RHS to `a` and `b` (of type `expr`), and if it is not an equality the tactic will fail.

(It's worth noting that this sort of pattern matching works at a syntactic level. Sometimes
it is more flexible to use unification, instead.)

## Mario's monadic symbols cheat sheet

All functions and notations from the list below apply to more general monads than `tactic`, so they are listed in a generic form but, for the purposes
of this tutorial `m` is always `tactic` (or `lean.parser`). Although
everything can be done with the symbols introduced in this tutorials, more
esoteric symbols allow to compress code, and understanding them is useful for
reading available tactics.

* `return`: produce a value in the monad (type: `A → m A`)
* `ma >>= f`: get the value of type `A` from `ma : m A` and pass it to `f : A → m B`. Alternate syntax: `do a ← ma, f a`
* `f <$> ma`: apply the function `f : A → B` to the value in `ma : m A` to get a `m B`. Same as `do a ← ma, return (f a)`
* `ma >> mb`: same as `do a ← ma, mb`; here the return value of `ma` is ignored and then `mb` is called. Alternate syntax: `do ma, mb`
* `mf <*> ma`: same as `do f ← mf, f <$> ma`, or `do f ← mf, a ← ma, return (f a)`.
* `ma <* mb`: same as `do a ← ma, mb, return a`
* `ma *> mb`: same as `do ma, mb`, or `ma >> mb`. Why two notations for the same thing? Historical reasons
* `pure`: same as `return`. Again, historical reasons
* `failure`: failed value (specific monads usually have a more useful form of this, like `fail` and `failed` for tactics)
* `ma <|> ma'` recover from failure: runs `ma` and if it fails then runs `ma'`.
* `a $> mb`: same as `do mb, return a`
* `ma <$ b`: same as `do ma, return b`
