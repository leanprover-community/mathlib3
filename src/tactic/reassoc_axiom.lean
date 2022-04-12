/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import category_theory.category.basic

/-!
# Tools to reformulate category-theoretic axioms in a more associativity-friendly way

## The `reassoc` attribute

The `reassoc` attribute can be applied to a lemma

```lean
@[reassoc]
lemma some_lemma : foo ≫ bar = baz := ...
```

and produce

```lean
lemma some_lemma_assoc {Y : C} (f : X ⟶ Y) : foo ≫ bar ≫ f = baz ≫ f := ...
```

The name of the produced lemma can be specified with `@[reassoc other_lemma_name]`. If
`simp` is added first, the generated lemma will also have the `simp` attribute.

## The `reassoc_axiom` command

When declaring a class of categories, the axioms can be reformulated to be more amenable
to manipulation in right associated expressions:

```lean
class some_class (C : Type) [category C] :=
(foo : Π X : C, X ⟶ X)
(bar : ∀ {X Y : C} (f : X ⟶ Y), foo X ≫ f = f ≫ foo Y)

reassoc_axiom some_class.bar
```

Here too, the `reassoc` attribute can be used instead. It works well when combined with
`simp`:

```lean
attribute [simp, reassoc] some_class.bar
```
-/

namespace tactic

open category_theory

/-- From an expression `f ≫ g`, extract the expression representing the category instance. -/
meta def get_cat_inst : expr → tactic expr
| `(@category_struct.comp _ %%struct_inst _ _ _ _ _) := pure struct_inst
| _ := failed

/-- (internals for `@[reassoc]`)
Given a lemma of the form `∀ ..., f ≫ g = h`, proves a new lemma of the form
`h : ∀ ... {W} (k), f ≫ (g ≫ k) = h ≫ k`, and returns the type and proof of this lemma.
-/
meta def prove_reassoc (h : expr) : tactic (expr × expr) :=
do
   (vs,t) ← infer_type h >>= open_pis,
   (lhs,rhs) ← match_eq t,
   struct_inst ← get_cat_inst lhs <|> get_cat_inst rhs <|> fail "no composition found in statement",
   `(@quiver.hom _ %%hom_inst %%X %%Y) ← infer_type lhs,
   C ← infer_type X,
   X' ← mk_local' `X' binder_info.implicit C,
   ft ← to_expr ``(@quiver.hom _ %%hom_inst %%Y %%X'),
   f' ← mk_local_def `f' ft,
   t' ← to_expr ``(@category_struct.comp _ %%struct_inst _ _ _%%lhs %%f' =
                     @category_struct.comp _ %%struct_inst _ _ _ %%rhs %%f'),
   let c' := h.mk_app vs,
   (_,pr) ← solve_aux t' (rewrite_target c'; reflexivity),
   pr ← instantiate_mvars pr,
   let s := simp_lemmas.mk,
   s ← s.add_simp ``category.assoc,
   s ← s.add_simp ``category.id_comp,
   s ← s.add_simp ``category.comp_id,
   (t'', pr', _) ← simplify s [] t',
   pr' ← mk_eq_mp pr' pr,
   t'' ← pis (vs ++ [X',f']) t'',
   pr' ← lambdas (vs ++ [X',f']) pr',
   pure (t'',pr')

/-- (implementation for `@[reassoc]`)
Given a declaration named `n` of the form `∀ ..., f ≫ g = h`, proves a new lemma named `n'`
of the form `∀ ... {W} (k), f ≫ (g ≫ k) = h ≫ k`.
-/
meta def reassoc_axiom (n : name) (n' : name := n.append_suffix "_assoc") : tactic unit :=
do d ← get_decl n,
   let ls := d.univ_params.map level.param,
   let c := @expr.const tt n ls,
   (t'',pr') ← prove_reassoc c,
   add_decl $ declaration.thm n' d.univ_params t'' (pure pr'),
   copy_attribute `simp n n'

setup_tactic_parser

/--
The `reassoc` attribute can be applied to a lemma

```lean
@[reassoc]
lemma some_lemma : foo ≫ bar = baz := ...
```

to produce

```lean
lemma some_lemma_assoc {Y : C} (f : X ⟶ Y) : foo ≫ bar ≫ f = baz ≫ f := ...
```

The name of the produced lemma can be specified with `@[reassoc other_lemma_name]`. If
`simp` is added first, the generated lemma will also have the `simp` attribute.
-/
@[user_attribute]
meta def reassoc_attr : user_attribute unit (option name) :=
{ name := `reassoc,
  descr := "create a companion lemma for associativity-aware rewriting",
  parser := optional ident,
  after_set := some (λ n _ _,
    do some n' ← reassoc_attr.get_param n | reassoc_axiom n (n.append_suffix "_assoc"),
       reassoc_axiom n $ n.get_prefix ++ n' ) }

add_tactic_doc
{ name                     := "reassoc",
  category                 := doc_category.attr,
  decl_names               := [`tactic.reassoc_attr],
  tags                     := ["category theory"] }

/--
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
-/
@[user_command]
meta def reassoc_cmd (_ : parse $ tk "reassoc_axiom") : lean.parser unit :=
do n ← ident,
   of_tactic $
   do n ← resolve_constant n,
      reassoc_axiom n

add_tactic_doc
{ name                     := "reassoc_axiom",
  category                 := doc_category.cmd,
  decl_names               := [`tactic.reassoc_cmd],
  tags                     := ["category theory"] }

namespace interactive

setup_tactic_parser

/-- `reassoc h`, for assumption `h : x ≫ y = z`, creates a new assumption
`h : ∀ {W} (f : Z ⟶ W), x ≫ y ≫ f = z ≫ f`.
`reassoc! h`, does the same but deletes the initial `h` assumption.
(You can also add the attribute `@[reassoc]` to lemmas to generate new declarations generalized
in this way.)
-/
meta def reassoc (del : parse (tk "!")?) (ns : parse ident*) : tactic unit :=
do ns.mmap' (λ n,
   do h ← get_local n,
      (t,pr) ← prove_reassoc h,
      assertv n t pr,
      when del.is_some (tactic.clear h) )

end interactive

def calculated_Prop {α} (β : Prop) (hh : α) := β

meta def derive_reassoc_proof : tactic unit :=
do `(calculated_Prop %%v %%h) ← target,
   (t,pr) ← prove_reassoc h,
   unify v t,
   exact pr

end tactic

/-- With `h : x ≫ y ≫ z = x` (with universal quantifiers tolerated),
`reassoc_of h : ∀ {X'} (f : W ⟶ X'), x ≫ y ≫ z ≫ f = x ≫ f`.

The type and proof of `reassoc_of h` is generated by `tactic.derive_reassoc_proof`
which make `reassoc_of` meta-programming adjacent. It is not called as a tactic but as
an expression. The goal is to avoid creating assumptions that are dismissed after one use:

```lean
example (X Y Z W : C) (x : X ⟶ Y) (y : Y ⟶ Z) (z z' : Z ⟶ W) (w : X ⟶ Z)
  (h : x ≫ y = w)
  (h' : y ≫ z = y ≫ z') :
  x ≫ y ≫ z = w ≫ z' :=
begin
  rw [h',reassoc_of h],
end
```
-/
theorem category_theory.reassoc_of {α} (hh : α) {β}
  (x : tactic.calculated_Prop β hh . tactic.derive_reassoc_proof) : β := x

/--
`reassoc_of h` takes local assumption `h` and add a ` ≫ f` term on the right of
both sides of the equality. Instead of creating a new assumption from the result, `reassoc_of h`
stands for the proof of that reassociated statement. This keeps complicated assumptions that are
used only once or twice from polluting the local context.

In the following, assumption `h` is needed in a reassociated form. Instead of proving it as a new
goal and adding it as an assumption, we use `reassoc_of h` as a rewrite rule which works just as
well.

```lean
example (X Y Z W : C) (x : X ⟶ Y) (y : Y ⟶ Z) (z z' : Z ⟶ W) (w : X ⟶ Z)
  (h : x ≫ y = w)
  (h' : y ≫ z = y ≫ z') :
  x ≫ y ≫ z = w ≫ z' :=
begin
  -- reassoc_of h : ∀ {X' : C} (f : W ⟶ X'), x ≫ y ≫ f = w ≫ f
  rw [h',reassoc_of h],
end
```

Although `reassoc_of` is not a tactic or a meta program, its type is generated
through meta-programming to make it usable inside normal expressions.
-/
add_tactic_doc
{ name                     := "category_theory.reassoc_of",
  category                 := doc_category.tactic,
  decl_names               := [`category_theory.reassoc_of],
  tags                     := ["category theory"] }
