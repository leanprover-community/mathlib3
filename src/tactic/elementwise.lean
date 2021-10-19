/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.fresh_names
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

Here `X` is being coerced to a type via `concrete_category.has_coe_to_sort` and
`f`, `g`, and `h` are being coerced to functions via `concrete_category.has_coe_to_fun`.
Further, we simplify the type using `concrete_category.coe_id : ((𝟙 X) : X → X) x = x` and
`concrete_category.coe_comp : (f ≫ g) x = g (f x)`,
replacing morphism composition with function composition.

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
| `(@eq (@quiver.hom ._ (@category_struct.to_quiver _
     (@category.to_category_struct _ %%S)) _ _) _ _) := pure S
| _ := failed

/-- (internals for `@[elementwise]`)
Given a lemma of the form `f = g`, where `f g : X ⟶ Y` and `X Y : V`,
proves a new lemma of the form
`∀ (x : X), f x = g x`
if we are already in a concrete category, or
`∀ [concrete_category.{w} V] (x : X), f x = g x`
otherwise.

Returns the type and proof of this lemma,
and the universe parameter `w` for the `concrete_category` instance, if it was not synthesized.
-/
-- This is closely modelled on `reassoc_axiom`.
meta def prove_elementwise (h : expr) : tactic (expr × expr × option name) :=
do
   (vs,t) ← infer_type h >>= open_pis,
   (f, g) ← match_eq t,
   S ← extract_category t <|> fail "no morphism equation found in statement",
   `(@quiver.hom _ %%H %%X %%Y) ← infer_type f,
   C ← infer_type X,
   CC_type ← to_expr ``(@concrete_category %%C %%S),
   (CC, CC_found) ← (do CC ← mk_instance CC_type, pure (CC, tt)) <|>
     (do CC ← mk_local' `I binder_info.inst_implicit CC_type, pure (CC, ff)),
   -- This is need to fill in universe levels fixed by `mk_instance`:
   CC_type ← instantiate_mvars CC_type,
   x_type ← to_expr ``(@coe_sort %%C
     (@category_theory.concrete_category.has_coe_to_sort %%C %%S %%CC) %%X),
   x ← mk_local_def `x x_type,
   t' ← to_expr ``(@coe_fn (@quiver.hom %%C %%H %%X %%Y)
     (@category_theory.concrete_category.has_coe_to_fun %%C %%S %%CC %%X %%Y) %%f %%x =
       @coe_fn (@quiver.hom %%C %%H %%X %%Y)
         (@category_theory.concrete_category.has_coe_to_fun %%C %%S %%CC %%X %%Y) %%g %%x),
   let c' := h.mk_app vs,
   (_,pr) ← solve_aux t' (rewrite_target c'; reflexivity),
   -- The codomain of forget lives in a new universe, which may be now a universe metavariable
   -- if we didn't synthesize an instance:
   [w, _, _] ← pure CC_type.get_app_fn.univ_levels,
   -- We unify that with a fresh universe parameter.
   n ← match w with
   | level.mvar _ := (do
      n ← get_unused_name_reserved [`w] mk_name_set,
      unify (expr.sort (level.param n)) (expr.sort w),
      pure (option.some n))
   | _ := pure option.none
   end,
   t' ← instantiate_mvars t',
   CC ← instantiate_mvars CC,
   x ← instantiate_mvars x,
   -- Now the key step: replace morphism composition with function composition,
   -- and identity morphisms with nothing.
   let s := simp_lemmas.mk,
   s ← s.add_simp ``id_apply,
   s ← s.add_simp ``comp_apply,
   (t'', pr', _) ← simplify s [] t' {fail_if_unchanged := ff},
   pr' ← mk_eq_mp pr' pr,
   -- Further, if we're in `Type`, get rid of the coercions entirely.
   let s := simp_lemmas.mk,
   s ← s.add_simp ``concrete_category.has_coe_to_fun_Type,
   (t'', pr'', _) ← simplify s [] t'' {fail_if_unchanged := ff},
   pr'' ← mk_eq_mp pr'' pr',
   t'' ← pis (vs ++ (if CC_found then [x] else [CC, x])) t'',
   pr'' ← lambdas (vs ++ (if CC_found then [x] else [CC, x])) pr'',
   pure (t'', pr'', n)

/-- (implementation for `@[elementwise]`)
Given a declaration named `n` of the form `∀ ..., f = g`, proves a new lemma named `n'`
of the form `∀ ... [concrete_category V] (x : X), f x = g x`.
-/
meta def elementwise_lemma (n : name) (n' : name := n.append_suffix "_apply") : tactic unit :=
do d ← get_decl n,
   let c := @expr.const tt n d.univ_levels,
   (t'',pr',l') ← prove_elementwise c,
   let params := l'.to_list ++ d.univ_params,
   add_decl $ declaration.thm n' params t'' (pure pr'),
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

Here `X` is being coerced to a type via `concrete_category.has_coe_to_sort` and
`f`, `g`, and `h` are being coerced to functions via `concrete_category.has_coe_to_fun`.
Further, we simplify the type using `concrete_category.coe_id : ((𝟙 X) : X → X) x = x` and
`concrete_category.coe_comp : (f ≫ g) x = g (f x)`,
replacing morphism composition with function composition.

The `[concrete_category C]` argument will be omitted if it is possible to synthesize an instance.

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

namespace interactive

setup_tactic_parser

/--
`elementwise h`, for assumption `w : ∀ ..., f ≫ g = h`, creates a new assumption
`w : ∀ ... (x : X), g (f x) = h x`.

`elementwise! h`, does the same but deletes the initial `h` assumption.
(You can also add the attribute `@[elementwise]` to lemmas to generate new declarations generalized
in this way.)
-/
meta def elementwise (del : parse (tk "!")?) (ns : parse ident*) : tactic unit :=
do ns.mmap' (λ n,
   do h ← get_local n,
      (t,pr,u) ← prove_elementwise h,
      assertv n t pr,
      when del.is_some (tactic.clear h) )

end interactive

/-- Auxiliary definition for `category_theory.elementwise_of`. -/
meta def derive_elementwise_proof : tactic unit :=
do `(calculated_Prop %%v %%h) ← target,
   (t,pr,n) ← prove_elementwise h,
   unify v t,
   exact pr

end tactic

/--
With `w : ∀ ..., f ≫ g = h` (with universal quantifiers tolerated),
`elementwise_of w : ∀ ... (x : X), g (f x) = h x`.

The type and proof of `elementwise_of h` is generated by `tactic.derive_elementwise_proof`
which makes `elementwise_of` meta-programming adjacent. It is not called as a tactic but as
an expression. The goal is to avoid creating assumptions that are dismissed after one use:

```lean
example (M N K : Mon.{u}) (f : M ⟶ N) (g : N ⟶ K) (h : M ⟶ K) (w : f ≫ g = h) (m : M) :
  g (f m) = h m :=
begin
  rw elementwise_of w,
end
```
-/
theorem category_theory.elementwise_of {α} (hh : α) {β}
  (x : tactic.calculated_Prop β hh . tactic.derive_elementwise_proof) : β := x

/--
With `w : ∀ ..., f ≫ g = h` (with universal quantifiers tolerated),
`elementwise_of w : ∀ ... (x : X), g (f x) = h x`.

Although `elementwise_of` is not a tactic or a meta program, its type is generated
through meta-programming to make it usable inside normal expressions.
-/
add_tactic_doc
{ name                     := "category_theory.elementwise_of",
  category                 := doc_category.tactic,
  decl_names               := [`category_theory.elementwise_of],
  tags                     := ["category theory"] }
