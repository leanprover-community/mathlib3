/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import tactic.core

/-!
# A tactic for type-based naming of variables

When we name hypotheses or variables, we often do so in a type-directed fashion:
a hypothesis of type `ℕ` is called `n` or `m`; a hypothesis of type `list ℕ` is
called `ns`; etc. This module provides a tactic,
`tactic.typical_variable_names`, which looks up typical variable names for a
given type.

Typical variable names are registered by giving an instance of the type class
`has_variable_names`. This file provides `has_variable_names` instances for many
of the core Lean types. If you want to override these, you can declare a
high-priority instance (perhaps localised) of `has_variable_names`. E.g. to
change the names given to natural numbers:

```lean
def foo : has_variable_names ℕ :=
⟨[`i, `j, `k]⟩

local attribute [instance, priority 1000] foo
```
-/

universes u v

/--
Type class for associating a type `α` with typical variable names for elements
of `α`. See `tactic.typical_variable_names`.
-/
class has_variable_names (α : Sort u) : Type :=
(names : list name)
(names_nonempty : 0 < names.length . tactic.exact_dec_trivial)


namespace tactic

/--
`typical_variable_names t` obtains typical names for variables of type `t`.
The returned list is guaranteed to be nonempty. Fails if there is no instance
`has_typical_variable_names t`.

```
typical_variable_names `(ℕ) = [`n, `m, `o]
```
-/
meta def typical_variable_names (t : expr) : tactic (list name) :=
(do
  names ← to_expr ``(has_variable_names.names %%t),
  eval_expr (list name) names)
<|> fail! "typical_variable_names: unable to get typical variable names for type {t}"

end tactic


namespace has_variable_names

/--
`@make_listlike_instance α _ β` creates an instance `has_variable_names β` from
an instance `has_variable_names α`. If `α` has associated names `a`, `b`, ...,
the generated instance for `β` has names `as`, `bs`, ... This can be used to
create instances for 'containers' such as lists or sets.
-/
def make_listlike_instance (α : Sort u) [has_variable_names α]
  {β : Sort v} : has_variable_names β :=
⟨ (names α).map $ λ n, n.append_suffix "s",
  by simp [names_nonempty] ⟩

/--
`@make_inheriting_instance α _ β` creates an instance `has_variable_names β`
from an instance `has_variable_names α`. The generated instance contains the
same variable names as that of `α`. This can be used to create instances for
'wrapper' types like `option` and `subtype`.
-/
def make_inheriting_instance (α : Sort u) [has_variable_names α]
  {β : Sort v} : has_variable_names β :=
⟨names α, names_nonempty⟩

end has_variable_names

open has_variable_names


instance {n α} [has_variable_names α] : has_variable_names (d_array n (λ _, α)) :=
make_listlike_instance α

instance : has_variable_names bool :=
⟨[`b]⟩

instance : has_variable_names char :=
⟨[`c]⟩

instance {n} : has_variable_names (fin n):=
⟨[`n, `m, `o]⟩

instance : has_variable_names ℤ :=
⟨[`n, `m, `o]⟩

instance {α} [has_variable_names α] : has_variable_names (list α) :=
make_listlike_instance α

instance : has_variable_names ℕ :=
⟨[`n, `m, `o]⟩

instance Prop.has_variable_names : has_variable_names Prop :=
⟨[`P, `Q, `R]⟩

instance {α} [has_variable_names α] : has_variable_names (thunk α) :=
make_inheriting_instance α

instance {α β} : has_variable_names (prod α β) :=
⟨[`p]⟩

instance {α β} : has_variable_names (pprod α β) :=
⟨[`p]⟩

instance {α} {β : α → Type*} : has_variable_names (sigma β) :=
⟨[`p]⟩

instance {α} {β : α → Sort*} : has_variable_names (psigma β) :=
⟨[`p]⟩

instance {α} [has_variable_names α] {p : α → Prop} : has_variable_names (subtype p) :=
make_inheriting_instance α

instance {α} [has_variable_names α] : has_variable_names (option α) :=
make_inheriting_instance α

instance {α} : has_variable_names (bin_tree α) :=
⟨[`t]⟩

instance {α} [has_variable_names α] {lt : α → α → Prop} :
  has_variable_names (rbtree α lt) :=
make_listlike_instance α

meta instance {α} [has_variable_names α] : has_variable_names (native.rb_set α) :=
make_listlike_instance α

instance {α} [has_variable_names α] : has_variable_names (set α) :=
make_listlike_instance α

instance : has_variable_names string :=
⟨[`s]⟩

instance : has_variable_names unsigned :=
⟨[`n, `m, `o]⟩

instance {α} {β : α → Sort*} : has_variable_names (Π a : α, β a) :=
⟨[`f, `g, `h]⟩

instance : has_variable_names name :=
⟨[`n]⟩

meta instance {α} : has_variable_names (tactic α) :=
⟨[`t]⟩

meta instance : has_variable_names expr :=
⟨[`e]⟩

meta instance : has_variable_names pexpr :=
⟨[`e]⟩

meta instance : has_variable_names level :=
⟨[`u, `v, `w]⟩

instance : has_variable_names binder_info :=
⟨[`bi]⟩
