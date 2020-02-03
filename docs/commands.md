# Commands

Commands provide a way to interact with and modify a Lean environment outside of the context of a proof.
Familiar commands from core Lean include `#check`, `#eval`, and `run_cmd`.

Mathlib provides a number of commands that offer customized behavior. These commands fall into two
categories:

* *Transient* commands are used to query the environment for information, but do not modify it,
  and have no effect on the following proofs. These are useful as a user to get information from Lean.
  They should not appear in "finished" files.
  Transient commands typically begin with the symbol `#`.
  `#check` is a standard example of a transient command.

* *Permanent* commands modify the environment. Removing a permanent command from a file may affect
  the following proofs. `set_option class.instance_max_depth 500` is a standard example of a
  permanent command.

User-defined commands can have unintuitive interactions with the parser. For the most part, this is
not something to worry about. However, you may occasionally see strange error messages when using
mathlib commands: for instance, running these commands immediately after `import file.name` will
produce an error. An easy solution is to run a built-in no-op command in between, for example:

```
import data.nat.basic

run_cmd tactic.skip -- this serves as a "barrier" between `import` and `#find`

#find _ + _ = _ + _
```

## find

The `find` command from `tactic.find` allows to find definitions lemmas using
pattern matching on the type. For instance:

```lean
import tactic.find

#find _ + _ = _ + _
#find (_ : ℕ) + _ = _ + _
#find ℕ → ℕ
```

The tactic `library_search` is an alternate way to find lemmas in the library.

## Localized notation

This consists of two user-commands which allow you to declare notation and commands localized to a namespace.

* Declare notation which is localized to a namespace using:
```
localized "infix ` ⊹ `:60 := my_add" in my.add
```
* After this command it will be available in the same section/namespace/file, just as if you wrote `local infix ` ⊹ `:60 := my_add`
* You can open it in other places. The following command will declare the notation again as local notation in that section/namespace/files:
```
open_locale my.add
```
* More generally, the following will declare all localized notation in the specified namespaces.
```
open_locale namespace1 namespace2 ...
```
* You can also declare other localized commands, like local attributes
```
localized "attribute [simp] le_refl" in le
```
* Warning 1: as a limitation on user commands, you cannot put `open_locale` directly after your imports. You have to write another command first (e.g. `open`, `namespace`, `universe variables`, `noncomputable theory`, `run_cmd tactic.skip`, ...).
* Warning 2: You have to fully specify the names used in localized notation, so that the localized notation also works when the appropriate namespaces are not opened.

## reassoc_axiom

When declaring a class of categories, the axioms can be reformulated to be more amenable
to manipulation in right associated expressions:

```lean
class some_class (C : Type) [category C] :=
(foo : Π X : C, X ⟶ X)
(bar : ∀ {X Y : C} (f : X ⟶ Y), foo X ≫ f = f ≫ foo Y)

reassoc_axiom some_class.bar
```

The above will produce:

```lean
lemma some_class.bar_assoc {Z : C} (g : Y ⟶ Z) :
  foo X ≫ f ≫ g = f ≫ foo Y ≫ g := ...
```

Here too, the `reassoc` attribute can be used instead. It works well when combined with
`simp`:

```lean
attribute [simp, reassoc] some_class.bar
```

## lint
User commands to spot common mistakes in the code

* `#lint`: check all declarations in the current file
* `#lint_mathlib`: check all declarations in mathlib (so excluding core or other projects,
  and also excluding the current file)
* `#lint_all`: check all declarations in the environment (the current file and all
  imported files)

The following linters are run by default:
1. `unused_arguments` checks for unused arguments in declarations.
2. `def_lemma` checks whether a declaration is incorrectly marked as a def/lemma.
3. `dup_namespce` checks whether a namespace is duplicated in the name of a declaration.
4. `ge_or_gt` checks whether ≥/> is used in the declaration.
5. `instance_priority` checks that instances that always apply have priority below default.
6. `doc_blame` checks for missing doc strings on definitions and constants.
7.  `has_inhabited_instance` checks whether every type has an associated `inhabited` instance.
8.  `impossible_instance` checks for instances that can never fire.
9.  `incorrect_type_class_argument` checks for arguments in [square brackets] that are not classes.
10. `dangerous_instance` checks for instances that generate type-class problems with metavariables.

Another linter, `doc_blame_thm`, checks for missing doc strings on lemmas and theorems.
This is not run by default.

The command `#list_linters` prints a list of the names of all available linters.

You can append a `*` to any command (e.g. `#lint_mathlib*`) to omit the slow tests (4).

You can append a `-` to any command (e.g. `#lint_mathlib-`) to run a silent lint
that suppresses the output of passing checks.
A silent lint will fail if any test fails.

You can append a sequence of linter names to any command to run extra tests, in addition to the
default ones. e.g. `#lint doc_blame_thm` will run all default tests and `doc_blame_thm`.

You can append `only name1 name2 ...` to any command to run a subset of linters, e.g.
`#lint only unused_arguments`

You can add custom linters by defining a term of type `linter` in the `linter` namespace.
A linter defined with the name `linter.my_new_check` can be run with `#lint my_new_check`
or `lint only my_new_check`.
If you add the attribute `@[linter]` to `linter.my_new_check` it will run by default.

Adding the attribute `@[nolint]` to a declaration omits it from all linter checks.

## mk_simp_attribute

The command `mk_simp_attribute simp_name "description"` creates a simp set with name `simp_name`.
Lemmas tagged with `@[simp_name]` will be included when `simp with simp_name` is called.
`mk_simp_attribute simp_name none` will use a default description.

Appending the command with `with attr1 attr2 ...` will include all declarations tagged with
`attr1`, `attr2`, ... in the new simp set.

This command is preferred to using ``run_cmd mk_simp_attr `simp_name`` since it adds a doc string
to the attribute that is defined. If you need to create a simp set in a file where this command is not
available, you should use
```lean
run_cmd mk_simp_attr `simp_name
run_cmd add_doc_string `simp_attr.simp_name "Description of the simp set here"
```

## library_note

At various places in mathlib, we leave implementation notes that are referenced from many other
files. To keep track of these notes, we use the command `library_note`. This makes it easy to
retrieve a list of all notes, e.g. for documentation output.

These notes can be referenced in mathlib with the syntax `Note [note id]`.
Often, these references will be made in code comments (`--`) that won't be displayed in docs.
If such a reference is made in a doc string or module doc, it will be linked to the corresponding
note in the doc display.

Syntax:
```
library_note "note id" "note message"
```

An example from `meta.expr`:

```
library_note "open expressions"
"Some declarations work with open expressions, i.e. an expr that has free variables.
Terms will free variables are not well-typed, and one should not use them in tactics like
`infer_type` or `unify`. You can still do syntactic analysis/manipulation on them.
The reason for working with open types is for performance: instantiating variables requires
iterating through the expression. In one performance test `pi_binders` was more than 6x
quicker than `mk_local_pis` (when applied to the type of all imported declarations 100x)."
```

This note can be referenced near a usage of `pi_binders`:


```
-- See Note [open expressions]
/-- behavior of f -/
def f := pi_binders ...
```

## alias

The `alias` can be used to create copies
of a theorem or definition with different names.

Syntax:

```
/-- doc string -/
alias my_theorem ← alias1 alias2 ...
```

This produces defs or theorems of the form:

```
/-- doc string -/
@[alias] theorem alias1 : <type of my_theorem> := my_theorem

/-- doc string -/
@[alias] theorem alias2 : <type of my_theorem> := my_theorem
```

Iff alias syntax:

```
alias A_iff_B ↔ B_of_A A_of_B
alias A_iff_B ↔ ..
```

This gets an existing biconditional theorem `A_iff_B` and produces
the one-way implications `B_of_A` and `A_of_B` (with no change in
implicit arguments). A blank `_` can be used to avoid generating one direction.
The `..` notation attempts to generate the 'of'-names automatically when the
input theorem has the form `A_iff_B` or `A_iff_B_left` etc.

## setup_tactic_parser

`setup_tactic_parser_cmd` is a user command that opens the namespaces used in writing
interactive tactics, and declares the local postfix notation `?` for `optional` and `*` for `many`.
It does *not* use the `namespace` command, so it will typically be used after
`namespace tactic.interactive`.

## import_private

`import_private foo from bar` finds a private declaration `foo` in the same file as `bar`
and creates a local notation to refer to it.

`import_private foo`, looks for `foo` in all imported files.

## explode

`#explode decl_name` displays a proof term in a line by line format somewhat akin to a Fitch style
proof or the Metamath proof style.

`#explode iff_true_intro` produces

```
iff_true_intro : ∀ {a : Prop}, a → (a ↔ true)
0│   │ a         ├ Prop
1│   │ h         ├ a
2│   │ hl        │ ┌ a
3│   │ trivial   │ │ true
4│2,3│ ∀I        │ a → true
5│   │ hr        │ ┌ true
6│5,1│ ∀I        │ true → a
7│4,6│ iff.intro │ a ↔ true
8│1,7│ ∀I        │ a → (a ↔ true)
9│0,8│ ∀I        │ ∀ {a : Prop}, a → (a ↔ true)

```

## where

When working in a Lean file with namespaces, parameters, and variables,
it can be confusing to identify what the current "parser context" is.
The command `#where` tries to identify and print information about the current location,
including the active namespace, open namespaces, and declared variables.

This information is not "officially" accessible in the metaprogramming environment;
`#where` retrieves it via a number of hacks that are not always reliable.
While it is very useful as a quick reference, users should not assume its output is correct.
