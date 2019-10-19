/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import category_theory.category

/-!
Reformulate category-theoretic axioms in a more associativity-friendly way.

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

```
class some_class (C : Type) [category C] :=
(foo : Π X : C, X ⟶ X)
(bar : ∀ {X Y : C} (f : X ⟶ Y), foo X ≫ f = f ≫ foo Y)

reassoc_axiom some_class.bar
```

Here too, the `reassoc` attribute can be used instead. It works well when combined with
`simp`:

```
attribute [simp, reassoc] some_class.bar
```
-/

namespace tactic

open interactive lean.parser category_theory

/-- From an expression `f ≫ g`, extract the expression representing the category instance. -/
meta def get_cat_inst : expr → tactic expr
| `(@category_struct.comp _ %%struct_inst _ _ _ _ _) := pure struct_inst
| _ := failed

/-- (internals for `@[reassoc]`)
Given a lemma of the form `f ≫ g = h`, proves a new lemma of the form `h : ∀ {W} (k), f ≫ (g ≫ k) = h ≫ k`,
and returns the type and proof of this lemma.
-/
meta def prove_reassoc (h : expr) : tactic (expr × expr) :=
do
   (vs,t) ← infer_type h >>= mk_local_pis,
   (vs',t) ← whnf t >>= mk_local_pis,
   let vs := vs ++ vs',
   (lhs,rhs) ← match_eq t,
   struct_inst ← get_cat_inst lhs <|> get_cat_inst rhs <|> fail "no composition found in statement",
   `(@has_hom.hom _ %%hom_inst %%X %%Y) ← infer_type lhs,
   C ← infer_type X,
   X' ← mk_local' `X' binder_info.implicit C,
   ft ← to_expr ``(@has_hom.hom _ %%hom_inst %%Y %%X'),
   f' ← mk_local_def `f' ft,
   t' ← to_expr ``(@category_struct.comp _ %%struct_inst _ _ _%%lhs %%f' = @category_struct.comp _ %%struct_inst _ _ _ %%rhs %%f'),
   let c' := h.mk_app vs,
   (_,pr) ← solve_aux t' (rewrite_target c'; reflexivity),
   pr ← instantiate_mvars pr,
   let s := simp_lemmas.mk,
   s ← s.add_simp ``category.assoc,
   s ← s.add_simp ``category.id_comp,
   s ← s.add_simp ``category.comp_id,
   (t'',pr') ← simplify s [] t',
   pr' ← mk_eq_mp pr' pr,
   t'' ← pis (vs ++ [X',f']) t'',
   pr' ← lambdas (vs ++ [X',f']) pr',
   pure (t'',pr')

/-- (implementation for `@[reassoc]`)
Given a declaration named `n` of the form `f ≫ g = h`, proves a new lemma named `n'` of the form `∀ {W} (k), f ≫ (g ≫ k) = h ≫ k`.
-/
meta def reassoc_axiom (n : name) (n' : name := n.append_suffix "_assoc") : tactic unit :=
do d ← get_decl n,
   let ls := d.univ_params.map level.param,
   let c := @expr.const tt n ls,
   (t'',pr') ← prove_reassoc c,
   add_decl $ declaration.thm n' d.univ_params t'' (pure pr'),
   copy_attribute `simp n tt n'

/--
On the following lemma:
```
@[reassoc]
lemma foo_bar : foo ≫ bar = foo := ...
```
generates

```
lemma foo_bar_assoc {Z} {x : Y ⟶ Z} : foo ≫ bar ≫ x = foo ≫ x := ...
```

The name of `foo_bar_assoc` can also be selected with @[reassoc new_name]
-/
@[user_attribute]
meta def reassoc_attr : user_attribute unit (option name) :=
{ name := `reassoc,
  descr := "create a companion lemma for associativity-aware rewriting",
  parser := optional ident,
  after_set := some (λ n _ _,
    do some n' ← reassoc_attr.get_param n | reassoc_axiom n (n.append_suffix "_assoc"),
       reassoc_axiom n $ n.get_prefix ++ n' ) }

/--
```
reassoc_axiom my_axiom
```

produces the lemma `my_axiom_assoc` which transforms a statement of the
form `x ≫ y = z` into `x ≫ y ≫ k = z ≫ k`.
-/
@[user_command]
meta def reassoc_cmd (_ : parse $ tk "reassoc_axiom") : lean.parser unit :=
do n ← ident,
   of_tactic' $
   do n ← resolve_constant n,
      reassoc_axiom n

namespace interactive

setup_tactic_parser

/-- `reassoc h`, for assumption `h : x ≫ y = z ≫ x`, creates a new assumption `h : ∀ {W} (f : Z ⟶ W), x ≫ y ≫ f = z ≫ x ≫ f`.
    `reassoc! h`, does the same but deletes the initial `h` assumption.
(You can also add the attribute `@[reassoc]` to lemmas to generate new declarations generalized in this way.)
-/
meta def reassoc (del : parse (tk "!")?) (ns : parse ident*) : tactic unit :=
do ns.mmap' (λ n,
   do h ← get_local n,
      (t,pr) ← prove_reassoc h,
      assertv n t pr,
      when del.is_some (tactic.clear h) )

end interactive


end tactic
