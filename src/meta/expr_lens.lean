/-
Copyright (c) 2020 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Keeley Hoek, Scott Morrison
-/
import meta.expr
/-!
# A lens for zooming into nested `expr` applications

A "lens" for looking into the subterms of an expression, tracking where we've been, so that
when we "zoom out" after making a change we know exactly which order of `congr_fun`s and
`congr_arg`s we need to make things work.

This file defines the `expr_lens` inductive type, defines basic operations this type, and defines a
useful map-like function `expr.app_map` on `expr`s which maps over applications.

This file is for non-tactics.

## Tags

expr, expr_lens, congr, environment, meta, metaprogramming, tactic
-/

/-! ### Declarations about `expr_lens` -/

/-- You're supposed to think of an `expr_lens` as a big set of nested applications with a single
hole which needs to be filled, either in a function spot or argument spot. `expr_lens.fill` can
fill this hole and turn your lens back into a real `expr`. -/
meta inductive expr_lens
| app_fun : expr_lens → expr → expr_lens
| app_arg : expr_lens → expr → expr_lens
| entire  : expr_lens

namespace expr_lens

/-- Inductive type with two constructors `F` and `A`,
that represent the function-part `f` and arg-part `a` of an application `f a`. They specify the
directions in which an `expr_lens` should zoom into an `expr`.

This type is used in the development of rewriting tactics such as `nth_rewrite` and
`rewrite_search`. -/
@[derive [decidable_eq, inhabited]]
inductive dir
| F
| A

/-- String representation of `dir`. -/
def dir.to_string : dir → string
| dir.F := "F"
| dir.A := "A"

instance : has_to_string dir := ⟨dir.to_string⟩

open tactic

/-- Fill the function or argument hole in this lens with the given `expr`. -/
meta def fill : expr_lens → expr → expr
| entire        e := e
| (app_fun l f) x := l.fill (expr.app f x)
| (app_arg l x) f := l.fill (expr.app f x)

/-- Zoom into `e : expr` given the context of an `expr_lens`, popping out an `expr` and a new
zoomed `expr_lens`, if this is possible (`e` has to be an application). -/
meta def zoom : expr_lens → list dir → expr → option (expr_lens × expr)
| l [] e := (l, e)
| l (dir.F :: rest) (expr.app f x) := (expr_lens.app_arg l x).zoom rest f
| l (dir.A :: rest) (expr.app f x) := (expr_lens.app_fun l f).zoom rest x
| _ _ _ := none

/-- Convert an `expr_lens` into a list of instructions needed to build it; repeatedly inspecting a
function or its argument a finite number of times. -/
meta def to_dirs : expr_lens → list dir
| expr_lens.entire        := []
| (expr_lens.app_fun l _) := l.to_dirs.concat dir.A
| (expr_lens.app_arg l _) := l.to_dirs.concat dir.F

/-- Sometimes `mk_congr_arg` fails, when the function is 'superficially dependent'.
Try to `dsimp` the function first before building the `congr_arg` expression. -/
meta def mk_congr_arg_using_dsimp (G W : expr) (u : list name) : tactic expr :=
do s ← simp_lemmas.mk_default,
   t ← infer_type G,
   t' ← s.dsimplify u t { fail_if_unchanged := ff },
   to_expr ```(congr_arg (show %%t', from %%G) %%W)

private meta def trace_congr_error (f : expr) (x_eq : expr) : tactic unit :=
do pp_f ← pp f,
   pp_f_t ← (infer_type f >>= λ t, pp t),
   pp_x_eq ← pp x_eq,
   pp_x_eq_t ← (infer_type x_eq >>= λ t, pp t),
   trace format!"expr_lens.congr failed on \n{pp_f} : {pp_f_t}\n{pp_x_eq} : {pp_x_eq_t}"

/-- Turn an `e : expr_lens` and a proof that `a = b` into a series of `congr_arg` or `congr_fun`
applications showing that the expressions obtained from `e.fill a` and `e.fill b` are equal. -/
meta def congr : expr_lens → expr → tactic expr
| entire e_eq        := pure e_eq
| (app_fun l f) x_eq := do fx_eq ← try_core $ do {
                             mk_congr_arg f x_eq
                             <|> mk_congr_arg_using_dsimp f x_eq [`has_coe_to_fun.F] },
                           match fx_eq with
                           | (some fx_eq) := l.congr fx_eq
                           | none         := trace_congr_error f x_eq >> failed
                           end
| (app_arg l x) f_eq := mk_congr_fun f_eq x >>= l.congr

/-- Pretty print a lens. -/
meta def to_tactic_string : expr_lens → tactic string
| entire := return "(entire)"
| (app_fun l f) := do pp ← pp f,
                      rest ← l.to_tactic_string,
                      return sformat!"(fun \"{pp}\" {rest})"
| (app_arg l x) := do pp ← pp x,
                      rest ← l.to_tactic_string,
                      return sformat!"(arg \"{pp}\" {rest})"

end expr_lens

namespace expr

/-- The private internal function used by `app_map`, which "does the work". -/
private meta def app_map_aux {α} (F : expr_lens → expr → tactic (list α)) :
  option (expr_lens × expr) → tactic (list α)
| (some (l, e)) := list.join <$> monad.sequence [
    F l e,
    app_map_aux $ l.zoom [expr_lens.dir.F] e,
    app_map_aux $ l.zoom [expr_lens.dir.A] e
  ] <|> pure []
| none := pure []

/-- `app_map F e` maps a function `F` which understands `expr_lens`es
over the given `e : expr` in the natural way;
that is, make holes in `e` everywhere where that is possible
(generating `expr_lens`es in the process),
and at each stage call the function `F` passing
both the `expr_lens` generated and the `expr` which was removed to make the hole.

At each stage `F` returns a list of some type, and `app_map` collects these lists together and
returns a concatenation of them all. -/
meta def app_map {α} (F : expr_lens → expr → tactic (list α)) (e : expr) : tactic (list α) :=
app_map_aux F (expr_lens.entire, e)

end expr
