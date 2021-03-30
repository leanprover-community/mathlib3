/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.concrete_category

/-!
# Tools to reformulate category-theoretic lemmas in concrete categories

## The `elementwise` attribute

The `elementwise` attribute can be applied to a lemma

```lean
@[elementwise]
lemma some_lemma {C : Type*} [category C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : ...) : f ≫ g = h := ...
```

and will produce

```lean
lemma some_lemma_apply {C : Type*} [category C] [concrete_category C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : ...) (x : X) : g (f x) = h x := ...
```

(Here `X` is being coerced to a type via `concrete_category.has_coe_to_sort` and
`f`, `g`, and `h` are being coerced to functions via `concrete_category.has_coe_to_fun`.)

The name of the produced lemma can be specified with `@[elementwise other_lemma_name]`.
If `simp` is added first, the generated lemma will also have the `simp` attribute.

## Implementation

This closely follows the implementation of the `@[reassoc]` attribute, due to Simon Hudon.
Thanks to Gabriel Ebner for help diagnosing universe issues.

-/

namespace tactic

open interactive lean.parser category_theory

/--
From an expression `f = g`,
where `f g : X ⟶ Y` for some objects `X Y : V` with `[S : category V]`,
extract the expression for `S`.
-/
meta def extract_category : expr → tactic expr
| `(@eq (@has_hom.hom ._ (@category_struct.to_has_hom _
     (@category.to_category_struct _ %%S)) _ _) _ _) := pure S
| _ := failed

/-- (internals for `@[elementwise]`)
Given a lemma of the form `f = g`, where `f g : X ⟶ Y` and `X Y : V`,
proves a new lemma of the form
`∀ [concrete_category.{w} V] (x : X), f x = g x`,
and returns the type and proof of this lemma,
along with the new universe parameter `w`.
-/
-- This is closely modelled on `reassoc_axiom`.
meta def prove_elementwise (h : expr) : tactic (expr × expr × name) :=
do
   (vs,t) ← infer_type h >>= open_pis,
   (vs',t) ← whnf t >>= open_pis,
   let vs := vs ++ vs',
   (f, g) ← match_eq t,
   S ← extract_category t <|> fail "no morphism equation found in statement",
   `(@has_hom.hom _ %%H %%X %%Y) ← infer_type f,
   C ← infer_type X,
   CC_type ← to_expr ``(@concrete_category %%C %%S),
   CC ← mk_local' `I binder_info.inst_implicit CC_type,
   x_type ← to_expr ``(@coe_sort %%C
     (@category_theory.concrete_category.has_coe_to_sort %%C %%S %%CC) %%X),
   x ← mk_local_def `x x_type,
   t' ← to_expr ``(@coe_fn (@category_theory.has_hom.hom %%C %%H %%X %%Y)
     (@category_theory.concrete_category.has_coe_to_fun %%C %%S %%CC %%X %%Y) %%f %%x =
       @coe_fn (@category_theory.has_hom.hom %%C %%H %%X %%Y)
         (@category_theory.concrete_category.has_coe_to_fun %%C %%S %%CC %%X %%Y) %%g %%x),
   let c' := h.mk_app vs,
   (_,pr) ← solve_aux t' (rewrite_target c'; reflexivity),
   -- There will be a universe metavariable lurking here,
   -- because we summoned a `concrete_category`, which (!?) has an unconstrained universe level.
   [u] ← pure t'.list_univ_meta_vars,
   -- We unify that with a fresh universe parameter.
   n ← mk_fresh_name,
   unify (expr.sort (level.param n)) (expr.sort (level.mvar u)),
   t' ← instantiate_mvars t',
   CC ← instantiate_mvars CC,
   x ← instantiate_mvars x,
   -- Now the key step: replace morphism composition with function composition,
   -- and identity morphisms with nothing.
   let s := simp_lemmas.mk,
   s ← s.add_simp ``coe_id,
   s ← s.add_simp ``coe_comp,
   (t'', pr', _) ← simplify s [] t',
   pr' ← mk_eq_mp pr' pr,
   t'' ← pis (vs ++ [CC,x]) t'',
   pr' ← lambdas (vs ++ [CC,x]) pr',
   pure (t'',pr',n)

/-- (implementation for `@[elementwise]`)
Given a declaration named `n` of the form `∀ ..., f = g`, proves a new lemma named `n'`
of the form `∀ ... [concrete_category V] (x : X), f x = g x`.
-/
meta def elementwise_lemma (n : name) (n' : name := n.append_suffix "_apply") : tactic unit :=
do d ← get_decl n,
   let c := @expr.const tt n d.univ_levels,
   (t'',pr',l') ← prove_elementwise c,
   add_decl $ declaration.thm n' (l' :: d.univ_params) t'' (pure pr'),
   copy_attribute `simp n n'

/--
The `elementwise` attribute can be applied to a lemma

```lean
@[elementwise]
lemma some_lemma {C : Type*} [category C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : ...) : f ≫ g = h := ...
```

and will produce

```lean
lemma some_lemma_apply {C : Type*} [category C] [concrete_category C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (w : ...) (x : X) : g (f x) = h x := ...
```

(Here `X` is being coerced to a type via `concrete_category.has_coe_to_sort` and
`f`, `g`, and `h` are being coerced to functions via `concrete_category.has_coe_to_fun`.)

The name of the produced lemma can be specified with `@[elementwise other_lemma_name]`.
If `simp` is added first, the generated lemma will also have the `simp` attribute.
-/
@[user_attribute]
meta def elementwise_attr : user_attribute unit (option name) :=
{ name := `elementwise,
  descr := "create a companion lemma for a morphism equation applied to an element",
  parser := optional ident,
  after_set := some (λ n _ _,
    do some n' ← elementwise_attr.get_param n | elementwise_lemma n (n.append_suffix "_apply"),
       elementwise_lemma n $ n.get_prefix ++ n' ) }

add_tactic_doc
{ name                     := "elementwise",
  category                 := doc_category.attr,
  decl_names               := [`tactic.elementwise_attr],
  tags                     := ["category theory"] }

end tactic
