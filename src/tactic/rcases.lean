/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.dlist
import tactic.core

open lean lean.parser

namespace tactic

/-
These synonyms for `list` are used to clarify the meanings of the many
usages of lists in this module.

- `listΣ` is used where a list represents a disjunction, such as the
  list of possible constructors of an inductive type.

- `listΠ` is used where a list represents a conjunction, such as the
  list of arguments of an individual constructor.

These are merely type synonyms, and so are not checked for consistency
by the compiler.

The `def`/`local notation` combination makes Lean retain these
annotations in reported types.
-/
@[reducible] def list_Sigma := list
@[reducible] def list_Pi := list
local notation `listΣ` := list_Sigma
local notation `listΠ` := list_Pi

@[reducible] meta def goals := list expr

/--
An `rcases` pattern can be one of the following, in a nested combination:

* A name like `foo`
* The special keyword `rfl` (for pattern matching on equality using `subst`)
* A type ascription like `pat : ty` (parentheses are optional)
* A tuple constructor like `⟨p1, p2, p3⟩`
* An alternation / variant pattern `p1 | p2 | p3`

Parentheses can be used for grouping; alternation is higher precedence than type ascription, so
`p1 | p2 | p3 : ty` means `(p1 | p2 | p3) : ty`.

N-ary alternations are treated as a group, so `p1 | p2 | p3` is not the same as `p1 | (p2 | p3)`,
and similarly for tuples. However, note that an n-ary alternation or tuple can match an n-ary
conjunction or disjunction, because if the number of patterns exceeds the number of constructors in
the type being destructed, the extra patterns will match on the last element, meaning that
`p1 | p2 | p3` will act like `p1 | (p2 | p3)` when matching `a1 ∨ a2 ∨ a3`. If matching against a
type with 3 constructors,  `p1 | (p2 | p3)` will act like `p1 | (p2 | p3) | _` instead.
-/
meta inductive rcases_patt : Type
| one : name → rcases_patt
| typed : rcases_patt → pexpr → rcases_patt
| tuple : listΠ rcases_patt → rcases_patt
| alts : listΣ rcases_patt → rcases_patt

meta instance rcases_patt.inhabited : inhabited rcases_patt :=
⟨rcases_patt.one `_⟩

meta def rcases_patt.name : rcases_patt → option name
| (rcases_patt.one n) := some n
| (rcases_patt.typed p _) := p.name
| (rcases_patt.alts [p]) := p.name
| _ := none

meta def rcases_patt.as_tuple : rcases_patt → listΠ rcases_patt
| (rcases_patt.tuple ps) := ps
| p := [p]

meta def rcases_patt.as_alts : rcases_patt → listΣ rcases_patt
| (rcases_patt.alts ps) := ps
| p := [p]

meta def rcases_patt.tuple' : listΠ rcases_patt → rcases_patt
| [p] := p
| ps := rcases_patt.tuple ps

meta def rcases_patt.alts' : listΣ rcases_patt → rcases_patt
| [p] := p
| ps := rcases_patt.alts ps

meta def rcases_patt.tuple₁_core : listΠ rcases_patt → listΠ rcases_patt
| [] := []
| [rcases_patt.tuple []] := [rcases_patt.tuple []]
| [rcases_patt.tuple ps] := ps
| (p :: ps) := p :: rcases_patt.tuple₁_core ps

meta def rcases_patt.tuple₁ : listΠ rcases_patt → rcases_patt
| [] := default _
| [rcases_patt.one n] := rcases_patt.one n
| ps := rcases_patt.tuple (rcases_patt.tuple₁_core ps)

meta def rcases_patt.alts₁_core : listΣ (listΠ rcases_patt) → listΣ rcases_patt
| [] := []
| [[rcases_patt.alts ps]] := ps
| (p :: ps) := rcases_patt.tuple₁ p :: rcases_patt.alts₁_core ps

meta def rcases_patt.alts₁ : listΣ (listΠ rcases_patt) → rcases_patt
| [[]] := rcases_patt.tuple []
| [[rcases_patt.alts ps]] := rcases_patt.tuple [rcases_patt.alts ps]
| ps := rcases_patt.alts' (rcases_patt.alts₁_core ps)

meta instance rcases_patt.has_reflect : has_reflect rcases_patt
| (rcases_patt.one n) := `(_)
| (rcases_patt.typed l e) :=
  (`(rcases_patt.typed).subst (rcases_patt.has_reflect l)).subst (reflect e)
| (rcases_patt.tuple l) := `(λ l, rcases_patt.tuple l).subst $
  by haveI := rcases_patt.has_reflect; exact list.reflect l
| (rcases_patt.alts l) := `(λ l, rcases_patt.alts l).subst $
  by haveI := rcases_patt.has_reflect; exact list.reflect l

meta def rcases_patt.format : bool → rcases_patt → tactic format
| _ (rcases_patt.one n) := pure $ to_fmt n
| _ (rcases_patt.tuple []) := pure "⟨⟩"
| _ (rcases_patt.tuple ls) := do
  fs ← ls.mmap $ rcases_patt.format ff,
  pure $ "⟨" ++ format.group (format.nest 1 $
    format.join $ list.intersperse ("," ++ format.line) fs) ++ "⟩"
| br (rcases_patt.alts ls) := do
  fs ← ls.mmap $ rcases_patt.format tt,
  let fmt := format.join $ list.intersperse (↑" |" ++ format.space) fs,
  pure $ if br then format.bracket "(" ")" fmt else fmt
| br (rcases_patt.typed p e) := do
  fp ← rcases_patt.format ff p,
  fe ← pp e,
  let fmt := fp ++ " : " ++ fe,
  pure $ if br then format.bracket "(" ")" fmt else fmt

meta instance rcases_patt.has_to_tactic_format : has_to_tactic_format rcases_patt :=
⟨λ e, rcases_patt.format ff e⟩

/--
Takes the number of fields of a single constructor and patterns to
match its fields against (not necessarily the same number). The
returned lists each contain one element per field of the
constructor. The `name` is the name which will be used in the
top-level `cases` tactic, and the `rcases_patt` is the pattern which
the field will be matched against by subsequent `cases` tactics.
-/

meta def rcases.process_constructor :
  nat → listΠ rcases_patt → listΠ name × listΠ rcases_patt
| 0     ids  := ([], [])
| 1     []   := ([`_], [default _])
| 1     [id] := ([id.name.get_or_else `_], [id])

-- The interesting case: we matched the last field against multiple
-- patterns, so split off the remaining patterns into a subsequent
-- match. This handles matching `α × β × γ` against `⟨a, b, c⟩`.
| 1     ids  := ([`_], [rcases_patt.tuple ids])

| (n+1) ids  :=
  let (ns, ps) := rcases.process_constructor n ids.tail,
      p := ids.head in
  (p.name.get_or_else `_ :: ns, p :: ps)

meta def rcases.process_constructors (params : nat) :
  listΣ name → listΣ rcases_patt →
  tactic (dlist name × listΣ (name × listΠ rcases_patt))
| []      ids := pure (dlist.empty, [])
| (c::cs) ids := do
  n ← mk_const c >>= get_arity,
  let (h, t) := (match cs, ids.tail with
  -- We matched the last constructor against multiple patterns,
  -- so split off the remaining constructors. This handles matching
  -- `α ⊕ β ⊕ γ` against `a|b|c`.
  | [], _::_ := ([rcases_patt.alts ids], [])
  | _, _ := (ids.head.as_tuple, ids.tail)
  end : _),
  let (ns, ps) := rcases.process_constructor (n - params) h,
  (l, r) ← rcases.process_constructors cs t,
  pure (dlist.of_list ns ++ l, (c, ps) :: r)

private def align {α β} (p : α → β → Prop) [∀ a b, decidable (p a b)] :
  list α → list β → list (α × β)
| (a::as) (b::bs) :=
  if p a b then (a, b) :: align as bs else align as (b::bs)
| _ _ := []

private meta def get_local_and_type (e : expr) : tactic (expr × expr) :=
(do t ← infer_type e, pure (t, e)) <|> (do
    e ← get_local e.local_pp_name,
    t ← infer_type e, pure (t, e))

meta mutual def rcases_core, rcases.continue
with rcases_core : rcases_patt → expr → tactic goals
| (rcases_patt.one `rfl) e := do
  (t, e) ← get_local_and_type e,
  subst e,
  get_goals
-- If the pattern is any other name, we already bound the name in the
-- top-level `cases` tactic, so there is no more work to do for it.
| (rcases_patt.one _) _ := get_goals
| (rcases_patt.typed p ty) e := do
  (t, e) ← get_local_and_type e,
  ty ← i_to_expr_no_subgoals ``(%%ty : Sort*),
  unify t ty,
  t ← instantiate_mvars t,
  ty ← instantiate_mvars ty,
  e ← if t =ₐ ty then pure e else
    change_core ty (some e) >> get_local e.local_pp_name,
  rcases_core p e
| (rcases_patt.alts [p]) e := rcases_core p e
| pat e := do
  (t, e) ← get_local_and_type e,
  t ← whnf t,
  env ← get_env,
  let I := t.get_app_fn.const_name,
  let pat := pat.as_alts,
  (ids, r, l) ← (if I ≠ `quot
  then do
    when (¬env.is_inductive I) $
      fail format!"rcases tactic failed: {e} : {I} is not an inductive datatype",
    let params := env.inductive_num_params I,
    let c := env.constructors_of I,
    (ids, r) ← rcases.process_constructors params c pat,
    l ← cases_core e ids.to_list,
    pure (ids, r, l)
  else do
    (ids, r) ← rcases.process_constructors 2 [`quot.mk] pat,
    [(_, d)] ← induction e ids.to_list `quot.induction_on |
      fail format!"quotient induction on {e} failed. Maybe goal is not in Prop?",
    -- the result from `induction` is missing the information that the original constructor was
    -- `quot.mk` so we fix this up:
    pure (ids, r, [(`quot.mk, d)])),
  gs ← get_goals,
  -- `cases_core` may not generate a new goal for every constructor,
  -- as some constructors may be impossible for type reasons. (See its
  -- documentation.) Match up the new goals with our remaining work
  -- by constructor name.
  list.join <$> (align (λ (a : name × _) (b : _ × name × _), a.1 = b.2.1) r (gs.zip l)).mmap
    (λ⟨⟨_, ps⟩, g, _, hs, _⟩,
      set_goals [g] >> rcases.continue (ps.zip hs))

with rcases.continue : listΠ (rcases_patt × expr) → tactic goals
| [] := get_goals
| ((pat, e) :: l) := do
  gs ← rcases_core pat e,
  list.join <$> gs.mmap (λ g, set_goals [g] >> rcases.continue l)

/-- `rcases h e pat` performs case distinction on `e` using `pat` to
name the arising new variables and assumptions. If `h` is `some` name,
a new assumption `h : e = pat` will relate the expression `e` with the
current pattern. -/
meta def rcases (h : option name) (p : pexpr) (pat : rcases_patt) : tactic unit := do
  let p := match pat with
  | rcases_patt.typed _ ty := ``(%%p : %%ty)
  | _ := p
  end,
  e ← match h with
    | some h := do
      x ← get_unused_name $ pat.name.get_or_else `this,
      interactive.generalize h () (p, x),
      get_local x
    | none := i_to_expr p
    end,
  if e.is_local_constant then
    focus1 (rcases_core pat e >>= set_goals)
  else do
    x ← pat.name.elim mk_fresh_name pure,
    n ← revert_kdependencies e semireducible,
    tactic.generalize e x <|> (do
      t ← infer_type e,
      tactic.assertv x t e,
      get_local x >>= tactic.revert,
      pure ()),
    h ← tactic.intro1,
    focus1 (rcases_core pat h >>= set_goals)

meta def rintro (ids : listΠ rcases_patt) : tactic unit :=
do l ← ids.mmap (λ id, do
    e ← intro $ id.name.get_or_else `_,
    pure (id, e)),
  focus1 (rcases.continue l >>= set_goals)

def merge_list {α} (m : α → α → α) : list α → list α → list α
| [] l₂ := l₂
| l₁ [] := l₁
| (a :: l₁) (b :: l₂) := m a b :: merge_list l₁ l₂

meta def rcases_patt.merge : rcases_patt → rcases_patt → rcases_patt
| (rcases_patt.alts p₁) p₂ := rcases_patt.alts (merge_list rcases_patt.merge p₁ p₂.as_alts)
| p₁ (rcases_patt.alts p₂) := rcases_patt.alts (merge_list rcases_patt.merge p₁.as_alts p₂)
| (rcases_patt.tuple p₁) p₂ := rcases_patt.tuple (merge_list rcases_patt.merge p₁ p₂.as_tuple)
| p₁ (rcases_patt.tuple p₂) := rcases_patt.tuple (merge_list rcases_patt.merge p₁.as_tuple p₂)
| (rcases_patt.typed p₁ e) p₂ := rcases_patt.typed (p₁.merge p₂) e
| p₁ (rcases_patt.typed p₂ e) := rcases_patt.typed (p₁.merge p₂) e
| (rcases_patt.one `rfl) (rcases_patt.one `rfl) := rcases_patt.one `rfl
| (rcases_patt.one `_) p := p
| p (rcases_patt.one `_) := p
| (rcases_patt.one n) _ := rcases_patt.one n

meta mutual def rcases_hint_core, rcases_hint.process_constructors, rcases_hint.continue
with rcases_hint_core : ℕ → expr → tactic (rcases_patt × goals)
| depth e := do
  (t, e) ← get_local_and_type e,
  t ← whnf t,
  env ← get_env,
  let I := t.get_app_fn.const_name,
  (do guard (I = ``eq),
    subst e,
    prod.mk (rcases_patt.one `rfl) <$> get_goals) <|>
  (do
    let c := env.constructors_of I,
    some l ← try_core (guard (depth ≠ 0) >> cases_core e) |
      prod.mk (rcases_patt.one e.local_pp_name) <$> get_goals,
    gs ← get_goals,
    (ps, gs') ← rcases_hint.process_constructors (depth - 1) c (gs.zip l),
    pure (rcases_patt.alts₁ ps, gs'))

with rcases_hint.process_constructors : ℕ → listΣ name →
  list (expr × name × listΠ expr × list (name × expr)) →
  tactic (listΣ (listΠ rcases_patt) × goals)
| depth [] _  := pure ([], [])
| depth cs [] := pure (cs.map (λ _, []), [])
| depth (c::cs) ((g, c', hs, _) :: l) :=
  if c ≠ c' then do
    (ps, gs) ← rcases_hint.process_constructors depth cs l,
    pure (default _ :: ps, gs)
  else do
    (p, gs) ← set_goals [g] >> rcases_hint.continue depth hs,
    (ps, gs') ← rcases_hint.process_constructors depth cs l,
    pure (p :: ps, gs ++ gs')

with rcases_hint.continue : ℕ → listΠ expr → tactic (listΠ rcases_patt × goals)
| depth [] := prod.mk [] <$> get_goals
| depth (e :: l) := do
  (p, gs) ← rcases_hint_core depth e,
  (ps, gs') ← gs.mfoldl (λ (r : listΠ rcases_patt × goals) g,
    do (ps, gs') ← set_goals [g] >> rcases_hint.continue depth l,
      pure (merge_list rcases_patt.merge r.1 ps, r.2 ++ gs')) ([], []),
  pure (p :: ps, gs')

meta def rcases_hint (p : pexpr) (depth : nat) : tactic rcases_patt :=
do e ← i_to_expr p,
  if e.is_local_constant then
    focus1 $ do (p, gs) ← rcases_hint_core depth e, set_goals gs, pure p
  else do
    x ← mk_fresh_name,
    n ← revert_kdependencies e semireducible,
    tactic.generalize e x <|> (do
      t ← infer_type e,
      tactic.assertv x t e,
      get_local x >>= tactic.revert,
      pure ()),
    h ← tactic.intro1,
    focus1 $ do (p, gs) ← rcases_hint_core depth h, set_goals gs, pure p

meta def rintro_hint (depth : nat) : tactic (listΠ rcases_patt) :=
do l ← intros,
  focus1 $ do
    (p, gs) ← rcases_hint.continue depth l,
    set_goals gs,
    pure p

setup_tactic_parser

local notation `listΣ` := list_Sigma
local notation `listΠ` := list_Pi

meta mutual def rcases_patt_parse, rcases_patt_parse_list
with rcases_patt_parse : bool → parser rcases_patt
| tt := with_desc "patt" $
  (brackets "(" ")" (rcases_patt_parse ff)) <|>
  (rcases_patt.tuple <$> brackets "⟨" "⟩" (sep_by (tk ",") (rcases_patt_parse ff))) <|>
  (rcases_patt.one <$> ident_)
| ff := with_desc "patt" $ do
  pat ← rcases_patt.alts' <$> rcases_patt_parse_list,
  (tk ":" *> pat.typed <$> texpr) <|> pure pat

with rcases_patt_parse_list : parser (listΣ rcases_patt)
| x := (with_desc "patt_list" $ do
  pat ← rcases_patt_parse tt,
  (tk "|" *> list.cons pat <$> rcases_patt_parse_list) <|>
  pure [pat]) x

meta def rcases_parse_depth : parser nat :=
do o ← (tk ":" *> small_nat)?, pure $ o.get_or_else 5

precedence `?`:max

/-- syntax for a `rcases` pattern: `('?' expr (: n)?) | ((h :)? expr (with patt_list)?)`  -/
meta def rcases_parse : parser (pexpr × ((option name × rcases_patt) ⊕ nat)) :=
with_desc "('?' expr (: n)?) | ((h :)? expr (with patt_list)?)" $ do
  hint ← (tk "?")?,
  p ← texpr,
  match hint with
  | none := do
    (h, p) ←
    (do expr.local_const h _ _ _ ← pure p, tk ":" *> prod.mk (some h) <$> texpr) <|>
      pure (none, p),
    ids ← (tk "with" *> rcases_patt_parse ff)?,
    pure (p, sum.inl (h, ids.get_or_else (rcases_patt.tuple [])))
  | some _ := do depth ← rcases_parse_depth, pure (p, sum.inr depth)
  end

meta def rintro_parse : parser (listΠ rcases_patt ⊕ nat) :=
with_desc "('?' (: n)?) | patt_list" $
(tk "?" >> sum.inr <$> rcases_parse_depth) <|>
sum.inl <$> (rcases_patt_parse tt)*

meta def ext_patt := listΠ rcases_patt

meta def ext_parse : parser ext_patt := (rcases_patt_parse tt)*

namespace interactive
open interactive interactive.types expr

/--
The `rcases` tactic is the same as `cases`, but with more flexibility in the
`with` pattern syntax to allow for recursive case splitting. The pattern syntax
uses the following recursive grammar:

```lean
patt ::= (patt_list "|")* patt_list
patt_list ::= id | "rfl" | "_" | "⟨" (patt ",")* patt "⟩"
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

If `rcases` results in an expression of the form `x = a`, then using `rfl`
in the pattern will have the same effect as writing `h` and then
following the `rcases` with a `subst h`.

`rcases` also has special support for quotient types: quotient induction into Prop works like
matching on the constructor `quot.mk`.

`rcases h : e with PAT` will do the same as `rcases e with PAT` with the exception that an assumption
`h : e = PAT` will be added to the context.

`rcases? e` will perform case splits on `e` in the same way as `rcases e`,
but rather than accepting a pattern, it does a maximal cases and prints the
pattern that would produce this case splitting. The default maximum depth is 5,
but this can be modified with `rcases? e : n`.
-/
meta def rcases : parse rcases_parse → tactic unit
| (p, sum.inl (h, ids)) := tactic.rcases h p ids
| (p, sum.inr depth) := do
  patt ← tactic.rcases_hint p depth,
  pe ← pp p,
  ppat ← pp patt,
  trace $ ↑"Try this: rcases " ++ pe ++ " with " ++ ppat

add_tactic_doc
{ name       := "rcases",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.rcases],
  tags       := ["induction"] }

/--
The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintro (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.

`rintro?` will introduce and case split on variables in the same way as
`rintro`, but will also print the `rintro` invocation that would have the same
result. Like `rcases?`, `rintro? : n` allows for modifying the
depth of splitting; the default is 5.

`rintros` is an alias for `rintro`.
-/
meta def rintro : parse rintro_parse → tactic unit
| (sum.inl []) := intros []
| (sum.inl l)  := tactic.rintro l
| (sum.inr depth) := do
  ps ← tactic.rintro_hint depth,
  fs ← ps.mmap (λ p, do
    f ← pp $ p.format tt,
    pure $ format.space ++ format.group f),
  trace $ ↑"Try this: rintro" ++ format.join fs

/-- Alias for `rintro`. -/
meta def rintros := rintro

add_tactic_doc
{ name       := "rintro",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.rintro, `tactic.interactive.rintros],
  tags       := ["induction"],
  inherit_description_from := `tactic.interactive.rintro }

setup_tactic_parser

meta def obtain_parse : parser (option rcases_patt × option pexpr) :=
with_desc "patt_list? (: expr)?" $
  (do pat ← rcases_patt_parse ff,
    pure $ match pat with
    | rcases_patt.typed pat tp := (some pat, some tp)
    | _ := (some pat, none)
    end) <|>
  prod.mk none <$> (tk ":" >> texpr)?

/--
The `obtain` tactic is a combination of `have` and `rcases`.

```lean
obtain ⟨patt⟩ : type,
{ ... }
```
is equivalent to
```lean
have h : type,
{ ... },
rcases h with ⟨patt⟩
```

The syntax `obtain ⟨patt⟩ : type := proof` is also supported.

If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

If `type` is omitted, `:= proof` is required.
-/
meta def obtain : parse obtain_parse → parse (tk ":=" >> texpr)? → tactic unit
| (pat, none) (some val) := tactic.rcases none val (pat.get_or_else (default _))
| (pat, some tp) (some val) := tactic.rcases none val $ (pat.get_or_else (default _)).typed tp
| (pat, some tp) none := do
  nm ← mk_fresh_name,
  e ← to_expr tp >>= assert nm,
  (g :: gs) ← get_goals,
  set_goals gs,
  tactic.rcases none ``(%%e) (pat.get_or_else (rcases_patt.one `this)),
  gs ← get_goals,
  set_goals (g::gs)
| (pat, none) none :=
  fail $ "`obtain` requires either an expected type or a value.\n" ++
         "usage: `obtain ⟨patt⟩? : type (:= val)?` or `obtain ⟨patt⟩? (: type)? := val`"

add_tactic_doc
{ name       := "obtain",
  category   := doc_category.tactic,
  decl_names := [`tactic.interactive.obtain],
  tags       := ["induction"] }

end interactive
end tactic
