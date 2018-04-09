# Structures and classes tips and tricks

These notes start where the chapters 9 and 10 of 
[TPIL](https://leanprover.github.io/theorem_proving_in_lean/structures_and_records.html) ends. 
It assumes some familiarity with those chapters.


### Record update new notation ###

One preliminary remark is the notation
`{ record-obj with (<field-name> := <expr>)* }` covered in 
[Section 9.2](https://leanprover.github.io/theorem_proving_in_lean/structures_and_records.html#objects)
is deprecated. We now use `{fields, ..s}` for the structure update
instead of `{s with fields}`. One can specify several sources, which are
tried in order. For instance, the example 

```lean
structure point (α : Type) :=
mk :: (x : α) (y : α)

def p : point nat :=
{x := 1, y := 2}

#reduce {p with y := 3}
#reduce {p with x := 3}
```

now reads:

```lean
structure point (α : Type) :=
mk :: (x : α) (y : α)

def p : point nat :=
{x := 1, y := 2}

#reduce {y := 3, ..p}
#reduce {x := 3, ..p}
```

### About the namespace shortcut ###

As explained in TPIL, "every structure declaration introduces a namespace with the same name" and, still using the `point` structure example, "Given p : point nat, the notation p.x is shorthand for point.x p. This provides a convenient way of accessing the fields of a structure".

But actually this trick has a wider scope. For every function `f` in the
`point` namespace, `p.f` is `f` where the first explicit argument is
replaced by `p`. For instance:

```lean
structure point (α : Type) := (x : α) (y : α)

namespace point
def sum {α : Type} [has_add α] (p : point α) := p.x + p.y

def diff_x {α : Type} [has_sub α] (p q : point α) := p.x - q.x
end point

variables (α : Type) [has_add α] [has_sub α] (p : point α)
#reduce p.sum      -- p.x + p.y
#reduce p.diff_x   -- λ (q : point α), p.x - q.x
```

Note that those example wouldn't work if `α` was an explicit argument.
Also note that in `p.diff_x`, `p` becomes the first argument of
`point.diff_x`.


### The rebinding pattern ###

Especially when bundling data and properties, the default argument types
(explicit, implicit, inferred by type class resolution) may not be
suitable. For instance, consider the following bundled version of group
homomorphisms.

```lean
structure group_hom (α β) [group α] [group β]:=
(map : α → β)
(mul : ∀ a b : α, map (a * b) = map a * map b)

variable f : group_hom α β 
#check f.mul  -- f.mul : ∀ (a b : α), f.map (a * b) = f.map a * f.map b
```

We see that `a` and `b` are explicit arguments to `f.mul`. The following 
is only restating that condition with different binders.

```lean
lemma group_hom.mul' (f : group_hom α β) {a b : α} : f.map (a*b) = (f.map a)*(f.map b) :=
f.mul _ _
```

Compare the two versions in the following (which uses 
`theorem mul_self_iff_eq_one : a * a = a ↔ a = 1` from mathlib
`algebra.group`):

```lean
lemma one (f : group_hom α β) : f.map 1 = 1 :=
mul_self_iff_eq_one.1 $ calc
(f.map 1)*(f.map 1) =  f.map (1*1) : (f.mul _ _).symm
                ... = f.map 1 : by simp
      
lemma one' (f : group_hom α β) : f.map 1 = 1 :=
mul_self_iff_eq_one.1 $ calc
(f.map 1)*(f.map 1) =  f.map (1*1) : f.mul'.symm
                ... = f.map 1 : by simp
```
