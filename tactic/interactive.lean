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

local notation `listΣ` := list_Sigma
local notation `listΠ` := list_Pi

/--
This parser uses the "inverted" meaning for the `many` constructor:
rather than representing a sum of products, here it represents a
product of sums. We fix this by applying `invert`, defined below, to
the result.
-/
@[reducible] def rcases_patt_inverted := rcases_patt

meta def rcases_parse : parser (listΣ rcases_patt_inverted) :=
with_desc "patt" $ let p :=
  (rcases_patt.one <$> ident_) <|>
  (rcases_patt.many <$> brackets "⟨" "⟩" (sep_by (tk ",") rcases_parse)) in
list.cons <$> p <*> (tk "|" *> p)*

meta def rcases_parse.invert : listΣ rcases_patt_inverted → listΣ (listΠ rcases_patt) :=
let invert' (l : listΣ rcases_patt_inverted) : rcases_patt := match l with
| [rcases_patt.one n] := rcases_patt.one n
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

/-- Same as the `congr` tactic, but takes an optional argument which gives
  the depth of recursive applications. This is useful when `congr`
  is too aggressive in breaking down the goal. For example, given
  `⊢ f (g (x + y)) = f (g (y + x))`, `congr'` produces the goals `⊢ x = y`
  and `⊢ y = x`, while `congr' 2` produces the intended `⊢ x + y = y + x`. -/
meta def congr' : parse (with_desc "n" small_nat)? → tactic unit
| (some 0) := failed
| o        := focus1 (assumption <|> (congr_core >>
  all_goals (reflexivity <|> try (congr' (nat.pred <$> o)))))

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

meta def solve_by_elim_aux (discharger : tactic unit) (asms : option (list expr))  : ℕ → tactic unit
| 0 := done
| (succ n) := discharger <|> (apply_assumption asms $ solve_by_elim_aux n)

meta structure by_elim_opt :=
  (discharger : tactic unit := done)
  (restr_hyp_set : option (list expr) := none)
  (max_rep : ℕ := 3)

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
meta def solve_by_elim (opt : by_elim_opt := { }) : tactic unit :=
solve_by_elim_aux opt.discharger opt.restr_hyp_set opt.max_rep

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

/--
 Tag lemmas of the form:

 ```
 lemma my_collection.ext (a b : my_collection)
   (h : ∀ x, a.lookup x = b.lookup y) :
   a = b := ...
 ```
 -/
@[user_attribute]
meta def extensional_attribute : user_attribute :=
{ name := `extensionality,
  descr := "lemmas usable by `ext` tactic" }

attribute [extensionality] funext array.ext

/--
  `ext1 id` selects and apply one extensionality lemma (with attribute
  `extensionality`), using `id`, if provided, to name a local constant
  introduced by the lemma. If `id` is omitted, the local constant is
  named automatically, as per `intro`.
 -/
meta def ext1 (x : parse ident_ ?) : tactic unit :=
do ls ← attribute.get_instances `extensionality,
   ls.any_of (λ l, applyc l) <|> fail "no applicable extensionality rule found",
   interactive.intro x

/--
  - `ext` applies as many extensionality lemmas as possible;
  - `ext ids`, with `ids` a list of identifiers, finds extentionality and applies them
    until it runs out of identifiers in `ids` to name the local constants.

  When trying to prove:

  ```
  α β : Type,
  f g : α → set β
  ⊢ f = g
  ```

  applying `ext x y` yields:

  ```
  α β : Type,
  f g : α → set β,
  x : α,
  y : β
  ⊢ y ∈ f x ↔ y ∈ f x
  ```

  by applying functional extensionality and set extensionality.
  -/
meta def ext : parse ident_ * → tactic unit
 | [] := repeat (ext1 none)
 | xs := xs.mmap' (ext1 ∘ some)

private meta def generalize_arg_p_aux : pexpr → parser (pexpr × name)
| (app (app (macro _ [const `eq _ ]) h) (local_const x _ _ _)) := pure (h, x)
| _ := fail "parse error"


private meta def generalize_arg_p : parser (pexpr × name) :=
with_desc "expr = id" $ parser.pexpr 0 >>= generalize_arg_p_aux

lemma {u} generalize_a_aux {α : Sort u}
  (h : ∀ x : Sort u, (α → x) → x) : α := h α id

/--
  Like `generalize` but also considers assumptions
  specified by the user. The user can also specify to
  omit the goal.
  -/
meta def generalize_hyp  (h : parse ident?) (_ : parse $ tk ":")
  (p : parse generalize_arg_p)
  (l : parse location) :
  tactic unit :=
do h' ← get_unused_name `h,
   x' ← get_unused_name `x,
   g ← if ¬ l.include_goal then
       do refine ``(generalize_a_aux _),
          some <$> (prod.mk <$> tactic.intro x' <*> tactic.intro h')
   else pure none,
   n ← l.get_locals >>= tactic.revert_lst,
   generalize h () p,
   intron n,
   match g with
     | some (x',h') :=
        do tactic.apply h',
           tactic.clear h',
           tactic.clear x'
     | none := return ()
   end

/--
  Similar to `refine` but generates equality proof obligations
  for every discrepancy between the goal and the type of the rule.
  -/
meta def convert (sym : parse (with_desc "←" (tk "<-")?)) (r : parse texpr) (n : parse (tk "using" *> small_nat)?) : tactic unit :=
do v ← mk_mvar,
   if sym.is_some
     then refine ``(eq.mp %%v %%r)
     else refine ``(eq.mpr %%v %%r),
   gs ← get_goals,
   set_goals [v],
   congr' n,
   gs' ← get_goals,
   set_goals $ gs' ++ gs

meta def clean_ids : list name :=
[``id, ``id_rhs, ``id_delta]

/-- Remove identity functions from a term. These are normally
  automatically generated with terms like `show t, from p` or
  `(p : t)` which translate to some variant on `@id t p` in
  order to retain the type. -/
meta def clean (q : parse texpr) : tactic unit :=
do tgt : expr ← target,
   e ← i_to_expr_strict ``(%%q : %%tgt),
   tactic.exact $ e.replace (λ e n,
     match e with
     | (app (app (const n _) _) e') :=
       if n ∈ clean_ids then some e' else none
     | (app (lam _ _ _ (var 0)) e') := some e'
     | _ := none
     end)

end interactive
end tactic
