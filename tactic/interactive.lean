/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.dlist tactic.basic tactic.rcases tactic.generalize_proofs meta.expr

open lean
open lean.parser

local postfix `?`:9001 := optional
local postfix *:9001 := many

namespace tactic
namespace interactive
open interactive interactive.types expr

meta def rcases_parse : parser (list rcases_patt) :=
with_desc "patt" $ let p :=
  (rcases_patt.one <$> ident_) <|>
  (rcases_patt.many <$> brackets "⟨" "⟩" (sep_by (tk ",") rcases_parse)) in
list.cons <$> p <*> (tk "|" *> p)*

meta def rcases_parse.invert : list rcases_patt → list (list rcases_patt) :=
let invert' (l : list rcases_patt) : rcases_patt := match l with
| [k] := k
| _ := rcases_patt.many (rcases_parse.invert l)
end in
list.map $ λ p, match p with
| rcases_patt.one n := [rcases_patt.one n]
| rcases_patt.many l := invert' <$> l
end

/--
The `rcases` tactic is the same as `cases`, but with more flexibility in the
`with` pattern syntax to allow for recursive case splitting. The pattern syntax
uses the following recursive grammar:

```
patt ::= (patt_list "|")* patt_list
patt_list ::= id | "_" | "⟨" (patt ",")* patt "⟩"
```

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive datatype,
naming the first three parameters of the first constructor as `a,b,c` and the
first two of the second constructor `d,e`. If the list is not as long as the
number of arguments to the constructor or the number of constructors, the
remaining variables will be automatically named. If there are nested brackets
such as `⟨⟨a⟩, b | c⟩ | d` then these will cause more case splits as necessary.
If there are too many arguments, such as `⟨a, b, c⟩` for splitting on
`∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last
parameter as necessary.
-/
meta def rcases (p : parse texpr) (ids : parse (tk "with" *> rcases_parse)?) : tactic unit :=
tactic.rcases p $ rcases_parse.invert $ ids.get_or_else [default _]

/--
This is a "finishing" tactic modification of `simp`. The tactic `simpa [rules, ...] using e`
will simplify the hypothesis `e` using `rules`, then simplify the goal using `rules`, and
try to close the goal using `assumption`. If `e` is a term instead of a local constant,
it is first added to the local context using `have`.
-/
meta def simpa (use_iota_eqn : parse $ (tk "!")?) (no_dflt : parse only_flag)
  (hs : parse simp_arg_list) (attr_names : parse with_ident_list)
  (tgt : parse (tk "using" *> texpr)?) (cfg : simp_config_ext := {}) : tactic unit :=
let simp_at (lc) := simp use_iota_eqn no_dflt hs attr_names (loc.ns lc) cfg >> try (assumption <|> trivial) in
match tgt with
| none := get_local `this >> simp_at [some `this, none] <|> simp_at [none]
| some e :=
  (do e ← i_to_expr e,
    match e with
    | local_const _ lc _ _ := simp_at [some lc, none]
    | e := do
      t ← infer_type e,
      assertv `this t e >> simp_at [some `this, none]
    end) <|> (do
      simp_at [none],
      ty ← target,
      e ← i_to_expr_strict ``(%%e : %%ty), -- for positional error messages, don't care about the result
      pty ← pp ty, ptgt ← pp e,
      -- Fail deliberately, to advise regarding `simp; exact` usage
      fail ("simpa failed, 'using' expression type not directly " ++
        "inferrable. Try:\n\nsimpa ... using\nshow " ++
        to_fmt pty ++ ",\nfrom " ++ ptgt : format))
end

/-- `try_for n { tac }` executes `tac` for `n` ticks, otherwise uses `sorry` to close the goal.
  Never fails. Useful for debugging. -/
meta def try_for (max : parse parser.pexpr) (tac : itactic) : tactic unit :=
do max ← i_to_expr_strict max >>= tactic.eval_expr nat,
   tactic.try_for max tac <|>
     (tactic.trace "try_for timeout, using sorry" >> admit)

/-- Multiple subst. `substs x y z` is the same as `subst x, subst y, subst z`. -/
meta def substs (l : parse ident*) : tactic unit :=
l.mmap' (λ h, get_local h >>= tactic.subst)

/-- Unfold coercion-related definitions -/
meta def unfold_coes (loc : parse location) : tactic unit :=
unfold [``coe,``lift_t,``has_lift_t.lift,``coe_t,``has_coe_t.coe,``coe_b,``has_coe.coe,
        ``coe_fn, ``has_coe_to_fun.coe, ``coe_sort, ``has_coe_to_sort.coe] loc

/-- For debugging only. This tactic checks the current state for any
  missing dropped goals and restores them. Useful when there are no
  goals to solve but "result contains meta-variables". -/
meta def recover : tactic unit :=
do r ← tactic.result,
   tactic.set_goals $ r.fold [] $ λ e _ l,
     match e with
     | expr.mvar _ _ _ := insert e l
     | _ := l
     end

/-- Like `try { tac }`, but in the case of failure it continues
  from the failure state instead of reverting to the original state. -/
meta def continue (tac : itactic) : tactic unit :=
λ s, result.cases_on (tac s)
 (λ a, result.success ())
 (λ e ref, result.success ())

/-- Move goal `n` to the front. -/
meta def swap (n := 2) : tactic unit :=
if n = 2 then tactic.swap else tactic.rotate (n-1)

/-- Generalize proofs in the goal, naming them with the provided list. -/
meta def generalize_proofs : parse ident_* → tactic unit :=
tactic.generalize_proofs

/-- Clear all hypotheses starting with `_`, like `_match` and `_let_match`. -/
meta def clear_ : tactic unit := tactic.repeat $ do
  l ← local_context,
  l.reverse.mfirst $ λ h, do
    name.mk_string s p ← return $ local_pp_name h,
    guard (s.front = '_'),
    cl ← infer_type h >>= is_class, guard (¬ cl),
    tactic.clear h

/-- Same as the `congr` tactic, but only works up to depth `n`. This
  is useful when the `congr` tactic is too aggressive in breaking
  down the goal. For example, given `⊢ f (g (x + y)) = f (g (y + x))`,
  `congr` produces the goals `⊢ x = y` and `⊢ y = x`, while
  `congr_n 2` produces the intended `⊢ x + y = y + x`. -/
meta def congr_n : nat → tactic unit
| 0     := failed
| (n+1) := focus1 (try assumption >> congr_core >>
  all_goals (try reflexivity >> try (congr_n n)))

/-- Acts like `have`, but removes a hypothesis with the same name as
  this one. For example if the state is `h : p ⊢ goal` and `f : p → q`,
  then after `replace h := f h` the goal will be `h : q ⊢ goal`,
  where `have h := f h` would result in the state `h : p, h : q ⊢ goal`.
  This can be used to simulate the `specialize` and `apply at` tactics
  of Coq. -/
meta def replace (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : tactic unit :=
do let h := h.get_or_else `this,
  old ← try_core (get_local h),
  «have» h q₁ q₂,
  match old, q₂ with
  | none,   _      := skip
  | some o, some _ := tactic.clear o
  | some o, none   := swap >> tactic.clear o >> swap
  end

/-- Unfreeze local instances, which allows us to revert
  instances in the context. -/
meta def unfreezeI := tactic.unfreeze_local_instances

/-- Reset the instance cache. This allows any new instances
  added to the context to be used in typeclass inference. -/
meta def resetI := reset_instance_cache

/-- Like `intro`, but uses the introduced variable
  in typeclass inference. -/
meta def introI (p : parse ident_?) : tactic unit :=
intro p >> reset_instance_cache

/-- Like `intros`, but uses the introduced variable(s)
  in typeclass inference. -/
meta def introsI (p : parse ident_*) : tactic unit :=
intros p >> reset_instance_cache

/-- Used to add typeclasses to the context so that they can
  be used in typeclass inference. The syntax is the same as `have`,
  but the proof-omitted version is not supported. For
  this one must write `have : t, { <proof> }, resetI, <proof>`. -/
meta def haveI (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse (tk ":=" *> texpr)) : tactic unit :=
do h ← match h with
  | none   := get_unused_name "_inst"
  | some a := return a
  end,
  «have» (some h) q₁ (some q₂),
  match q₁ with
  | none    := swap >> reset_instance_cache >> swap
  | some p₂ := reset_instance_cache
  end

/-- Used to add typeclasses to the context so that they can
  be used in typeclass inference. The syntax is the same as `let`. -/
meta def letI (h : parse ident?) (q₁ : parse (tk ":" *> texpr)?) (q₂ : parse $ (tk ":=" *> texpr)?) : tactic unit :=
do h ← match h with
  | none   := get_unused_name "_inst"
  | some a := return a
  end,
  «let» (some h) q₁ q₂,
  match q₁ with
  | none    := swap >> reset_instance_cache >> swap
  | some p₂ := reset_instance_cache
  end

/-- Like `exact`, but uses all variables in the context
  for typeclass inference. -/
meta def exactI (q : parse texpr) : tactic unit :=
reset_instance_cache >> exact q

/--
  `apply_assumption` looks for an assumption of the form `... → ∀ _, ... → head`
  where `head` matches the current goal.

  alternatively, when encountering an assumption of the form `sg₀ → ¬ sg₁`,
  after the main approach failed, the goal is dismissed and `sg₀` and `sg₁`
  are made into the new goal.

  optional arguments:
  - asms: list of rules to consider instead of the local constants
  - tac:  a tactic to run on each subgoals after applying an assumption; if
          this tactic fails, the corresponding assumption will be rejected and
          the next one will be attempted.
 -/
meta def apply_assumption
  (asms : option (list expr) := none)
  (tac : tactic unit := return ()) : tactic unit :=
do { ctx ← asms.to_monad <|> local_context,
     t   ← target,
     hs   ← find_matching_head t ctx,
     hs.any_of (λ H, () <$ tactic.apply H ; tac) } <|>
do { exfalso,
     ctx ← asms.to_monad <|> local_context,
     t   ← target,
     hs   ← find_matching_head t ctx,
     hs.any_of (λ H, () <$ tactic.apply H ; tac) }
<|> fail "assumption tactic failed"

open nat

/--
  `solve_by_elim` calls `apply_assumption` on the main goal to find an assumption whose head matches
  and repeated calls `apply_assumption` on the generated subgoals until no subgoals remains
  or up to `depth` times.

  `solve_by_elim` discharges the current goal or fails

  `solve_by_elim` does some back-tracking if `apply_assumption` chooses an unproductive assumption

  optional arguments:
  - discharger: a subsidiary tactic to try at each step (`cc` is often helpful)
  - asms: list of assumptions / rules to consider instead of local constants
  - depth: number of attempts at discharging generated sub-goals
  -/
meta def solve_by_elim (discharger : tactic unit := done) (asms : option (list expr) := none)  : opt_param ℕ 3 → tactic unit
| 0 := done
| (succ n) := discharger <|> (apply_assumption asms $ solve_by_elim n)

/--
  `tautology` breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
  and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
  using `reflexivity` or `solve_by_elim`
-/
meta def tautology : tactic unit :=
repeat (do
  gs ← get_goals,
  () <$ tactic.intros ;
  casesm (some ()) [``(_ ∧ _),``(_ ∨ _),``(Exists _)] ;
  constructor_matching (some ()) [``(_ ∧ _),``(_ ↔ _)],
  gs' ← get_goals,
  guard (gs ≠ gs') ) ;
repeat
(reflexivity <|> solve_by_elim <|> constructor_matching none [``(_ ∧ _),``(_ ↔ _),``(Exists _)]) ;
done

/-- Shorter name for the tactic `tautology`. -/
meta def tauto := tautology

/-- `wlog h : i ≤ j using i j`: without loss of generality, let us assume `h : i ≤ j`
    If `using i j` is omitted, the last two free variables found in `i ≤ j` will be used.

    `wlog : R x y` (synonymous with `wlog : R x y using x y`) adds `R x y` to the
    assumptions and the goal `⊢ R x y ∨ R y x`.

    A special case is made for total order relations `≤` where `⊢ R x y ∨ R y x`
    is discharged automatically.

    TODO(Simon): Generalize to multiple pairs of variables
  -/
meta def wlog (h : parse ident?)
              (p : parse (tk ":" *> texpr))
              (xy : parse (tk "using" *> monad.sequence [ident,ident])?)
: tactic unit :=
do p' ← to_expr p,
   (x :: y :: _) ← xy.to_monad >>= mmap get_local <|> pure p'.list_local_const,
   n ← tactic.revert_lst [x,y],
   x ← intro1, y ← intro1,
   p ← to_expr p,
   when (¬ x.occurs p ∨ ¬ x.occurs p) (do
     p ← pp p,
     fail format!"{p} should reference {x} and {y}"),
   let p' := subst_locals [(x,y),(y,x)] p,
   t ← target,
   let g := p.imp t,
   g ← tactic.pis [x,y] g,
   this ← assert `this (set_binder g [binder_info.default,binder_info.default]),
   tactic.clear x, tactic.clear y,
   intron 2,
   intro $ h.get_or_else `a, intron (n-2), tactic.swap,
   let h := h.get_or_else `this,
   h' ← to_expr ``(%%p ∨ %%p') >>= assert h,
   tactic.clear this,
   assumption <|> `[exact le_total _ _] <|> tactic.swap,
   (() <$ tactic.cases h' [`h,`h])
   ; specialize ```(%%this _ _ h)
   ; intron (n-2) ; try (solve_by_elim <|> tauto <|> (tactic.intros >> cc)),
   return ()

end interactive
end tactic
