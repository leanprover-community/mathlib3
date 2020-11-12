/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jannis Limperg
-/

import tactic.core

/-!
# A tactic for type-based naming of variables

When we name hypotheses or variables, we often do so in a type-directed fashion:
a hypothesis of type `ℕ` is called `n` or `m`; a hypothesis of type `list ℕ` is
called `ns`; etc. This module provides a tactic,
`tactic.typical_variable_names`, which looks up typical variable names for a
given type. Typical variable names are registered by giving an instance of the
type class `has_variable_names`.
-/

universes u v

/--
Type class for associating a type `α` with typical variable names for elements
of `α`. See `tactic.typical_variable_names`.
-/
meta class has_variable_names (α : Sort u) : Type :=
(first_name : name)
(other_names : list name)


namespace has_variable_names

/--
`names α` returns the names associated with the type `α`. The returned list is
guaranteed to be nonempty.
-/
meta def names {α} [has_variable_names α] : list name :=
first_name α :: other_names α

end has_variable_names


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
meta def make_listlike_instance (α : Sort u) [has_variable_names α]
  {β : Sort v} : has_variable_names β :=
⟨ (first_name α).append_suffix "s",
  (other_names α).map $ λ n, n.append_suffix "s" ⟩

/--
`@make_inheriting_instance α _ β` creates an instance `has_variable_names β`
from an instance `has_variable_names α`. The generated instance contains the
same variable names as that of `α`. This can be used to create instances for
'wrapper' types like `option` and `subtype`.
-/
meta def make_inheriting_instance (α : Sort u) [has_variable_names α]
  {β : Sort v} : has_variable_names β :=
⟨ first_name α, other_names α ⟩

end has_variable_names

open has_variable_names


meta instance {n α} [has_variable_names α] : has_variable_names (d_array n (λ _, α)) :=
make_listlike_instance α

meta instance : has_variable_names bool :=
⟨`b, []⟩

meta instance : has_variable_names char :=
⟨`c, []⟩

meta instance {n} : has_variable_names (fin n):=
⟨`n, [`m, `o]⟩

meta instance : has_variable_names ℤ :=
⟨`n, [`m, `o]⟩

meta instance {α} [has_variable_names α] : has_variable_names (list α) :=
make_listlike_instance α

meta instance : has_variable_names ℕ :=
⟨`n, [`m, `o]⟩

meta instance : has_variable_names Prop :=
⟨`P, [`Q, `R]⟩

meta instance {α} [has_variable_names α] : has_variable_names (thunk α) :=
make_inheriting_instance α

meta instance {α β} : has_variable_names (prod α β) :=
⟨`p, []⟩

meta instance {α β} : has_variable_names (pprod α β) :=
⟨`p, []⟩

meta instance {α} {β : α → Type*} : has_variable_names (sigma β) :=
⟨`p, []⟩

meta instance {α} {β : α → Sort*} : has_variable_names (psigma β) :=
⟨`p, []⟩

meta instance {α} [has_variable_names α] {p : α → Prop} : has_variable_names (subtype p) :=
make_inheriting_instance α

meta instance {α} [has_variable_names α] : has_variable_names (option α) :=
make_inheriting_instance α

meta instance {α} : has_variable_names (bin_tree α) :=
⟨`t, []⟩

meta instance {α} [has_variable_names α] {lt : α → α → Prop} :
  has_variable_names (rbtree α lt) :=
make_listlike_instance α

meta instance {α} [has_variable_names α] : has_variable_names (native.rb_set α) :=
make_listlike_instance α

meta instance {α} [has_variable_names α] : has_variable_names (set α) :=
make_listlike_instance α

meta instance : has_variable_names string :=
⟨`s, []⟩

meta instance : has_variable_names unsigned :=
⟨`n, [`m, `o]⟩

meta instance {α} {β : α → Sort*} : has_variable_names (Π a : α, β a) :=
⟨`f, [`g, `h]⟩

meta instance : has_variable_names name :=
⟨`n, []⟩

meta instance {α} : has_variable_names (tactic α) :=
⟨`t, []⟩

meta instance : has_variable_names expr :=
⟨`e, []⟩

meta instance : has_variable_names pexpr :=
⟨`e, []⟩

meta instance : has_variable_names level :=
⟨`u, [`v, `w]⟩

meta instance : has_variable_names binder_info :=
⟨`bi, []⟩
