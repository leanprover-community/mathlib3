/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/

import tactic.rewrite_search.types
import tactic.converter.interactive -- Required for us to emit more compact `conv` invocations

/-!
# Tools to extract valid Lean code from a path found by rewrite search.
-/

open interactive interactive.types expr tactic

namespace tactic.rewrite_search

universes u

/--
A `dir_pair` is a pair of items designed to be accessed according to
`dir`, a "direction" defined in the `expr_lens` library.
-/
@[derive inhabited]
structure dir_pair (α : Type u) :=
(l r : α)

namespace dir_pair
open expr_lens

variables {α β : Type} (p : dir_pair α)

/-- Get one side of the pair, picking the side according to the direction. -/
def get : dir → α
| dir.F := p.l
| dir.A := p.r

/-- Set one side of the pair, picking the side according to the direction. -/
def set : dir → α → dir_pair α
| dir.F v := ⟨v, p.r⟩
| dir.A v := ⟨p.l, v⟩

/-- Convert the pair to a list of its elements. -/
def to_list : list α := [p.l, p.r]

/-- Convert the pair to a readable string format. -/
def to_string [has_to_string α] (p : dir_pair α) : string :=
to_string p.l ++ "-" ++ to_string p.r

instance has_to_string [has_to_string α] : has_to_string (dir_pair α) := ⟨to_string⟩

end dir_pair

/-- Helper for getting the nth item in a list of rules -/
private meta def nth_rule (rs : list (expr × bool)) (i : ℕ) : expr × bool := (rs.nth i).iget

/-- Convert a rule into the string of Lean code used to refer to this rule. -/
private meta def pp_rule (r : expr × bool) : tactic string :=
do pp ← pp r.1, return $ (if r.2 then "←" else "") ++ to_string pp

private meta def how.to_rewrite (rs : list (expr × bool)) : how → option (expr × bool)
| h := nth_rule rs h.rule_index

/-- Explain a single rewrite using `nth_rewrite`. -/
private meta def explain_using_location (rs : list (expr × bool)) (s : side) :
  how → tactic (option string)
| h := do
  rule ← pp_rule $ nth_rule rs h.rule_index,
  return $ some ("nth_rewrite_" ++ s.to_xhs ++ " " ++ to_string h.location ++ " " ++ rule)

/-- Explain a list of rewrites using `nth_rewrite`. -/
private meta def using_location.explain_rewrites (rs : list (expr × bool)) (s : side)
  (steps : list how) : tactic string :=
do rules ← steps.mmap $ λ h : how, option.to_list <$> explain_using_location rs s h,
  return $ string.intercalate ",\n  " rules.join

namespace using_conv

/-- `app_addr` represents a tree structure that `conv` tactics use for a rewrite. -/
inductive app_addr
| node (children : dir_pair (option app_addr)) : app_addr
| rw : list ℕ → app_addr

open app_addr

private meta def app_addr.to_string : app_addr → string
| (node c) := "(node " ++ ((c.to_list.filter_map id).map app_addr.to_string).to_string ++ ")"
| (rw rws) := "(rw " ++ rws.to_string ++ ")"

/--
A data structure for the result of a splice operation.
obstructed:  There was more of the addr to be added left, but we hit a rw
contained:   The added addr was already contained, and did not terminate at an existing rw
new:         The added addr terminated at an existing rw or we could create a new one for it
-/
@[derive inhabited]
inductive splice_result
| obstructed
| contained
| new (addr : app_addr)

open splice_result

private meta def pack_splice_result (s : expr_lens.dir) :
  splice_result → dir_pair (option app_addr) → splice_result
| (new addr) c := new $ app_addr.node $ c.set s (some addr)
| sr _ := sr

private meta def splice_in_aux (new_rws : list ℕ) :
  option app_addr → list expr_lens.dir → splice_result
| (some $ node _) [] := contained
| (some $ node c) (s :: rest) := pack_splice_result s (splice_in_aux (c.get s) rest) c
| (some $ rw _) (_ :: _) := obstructed
| (some $ rw rws) [] := new $ rw (rws ++ new_rws)
| none [] := new $ rw new_rws
| none l := splice_in_aux (some $ node ⟨none, none⟩) l

open expr_lens

private meta def to_congr_form : list expr_lens.dir → tactic (list expr_lens.dir)
| [] := return []
| (dir.F :: (dir.A :: rest)) := do
  r ← to_congr_form rest,
  return (dir.F :: r)
| (dir.A :: rest) := do
  r ← to_congr_form rest,
  return (dir.A :: r)
| [dir.F] := fail "app list ends in side.L!"
| (dir.F :: (dir.F :: _)) := fail "app list has repeated side.L!"

/-- Attempt to add new rewrites into the `app_addr` tree. -/
private meta def splice_in (a : option app_addr) (rws : list ℕ) (s : list expr_lens.dir) :
  tactic splice_result :=
splice_in_aux rws a <$> to_congr_form s

/-- Construct a single `erw` tactic for the given rules. -/
private meta def build_rw_tactic (rs : list (expr × bool)) (hs : list ℕ) : tactic string :=
do rws ← (hs.map $ nth_rule rs).mmap pp_rule,
  return $ "erw [" ++ (string.intercalate ", " rws) ++ "]"

private meta def explain_tree_aux (rs : list (expr × bool)) :
app_addr → tactic (option (list string))
| (app_addr.rw rws) := (λ a, some [a]) <$> build_rw_tactic rs rws
| (app_addr.node ⟨func, arg⟩) := do
  sf ← match func with | none := pure none | some func := explain_tree_aux func end,
  sa ← match arg  with | none := pure none | some arg  := explain_tree_aux arg  end,
  return $ match (sf, sa) with
  | (none, none) := none
  | (some sf, none) := ["congr"].append sf
  | (none, some sa) := ["congr", "skip"].append sa
  | (some sf, some sa) := (["congr"].append sf).append (["skip"].append sf)
  end

/-- Construct a string of Lean code that does a rewrite for the provided tree. -/
private meta def explain_tree (rs : list (expr × bool)) (tree : app_addr) :
  tactic (list string) :=
list.join <$> option.to_list <$> explain_tree_aux rs tree

/--
Gather all rewrites into trees, then generate a line of code for each tree.
The return value has one `conv_x` tactic on each line.
-/
private meta def explanation_lines (rs : list (expr × bool)) (s : side) :
option app_addr → list how → tactic (list string)
| none [] := return []
| (some tree) [] := do
  tacs ← explain_tree rs tree,
  return $ if tacs.length = 0 then []
  else ["conv_" ++ s.to_xhs ++ " { " ++ string.intercalate ", " tacs ++ " }"]
| tree (h :: rest) := do
  (new_tree, rest_if_fail) ← match h.addr with
  | (some addr) := do
    new_tree ← splice_in tree [h.rule_index] addr,
    return (some new_tree, list.cons h rest)
  | none := do
    return (none, rest)
  end,
  match new_tree with
  | some (new new_tree) := explanation_lines new_tree rest
  | _ := do
    line ← explanation_lines tree [],
    lines ← explanation_lines none rest_if_fail,
    return $ line ++ lines
  end

/-- Explain a list of rewrites using `conv_x` tactics. -/
meta def explain_rewrites (rs : list (expr × bool)) (s : side) (hows : list how) :
  tactic string :=
string.intercalate ",\n  " <$> explanation_lines rs s none hows

end using_conv

private meta def explain_rewrites_concisely (steps : list (expr × bool)) (needs_refl : bool) :
  tactic string :=
do rules ← string.intercalate ", " <$> steps.mmap pp_rule,
  return $ "erw [" ++ rules ++ "]" ++ (if needs_refl then ", refl" else "")

/--
Fails if we can't just use rewrite.
Otherwise, returns 'tt' if we need a `refl` at the end.
-/
private meta def check_if_simple_rewrite_succeeds (rewrites : list (expr × bool)) (goal : expr) :
  tactic bool :=
lock_tactic_state $ do
  m ← mk_meta_var goal,
  set_goals [m],
  rewrites.mmap' $ λ q, rewrite_target q.1 {symm := q.2, md := semireducible},
  (reflexivity reducible >> return ff) <|> (reflexivity >> return tt)

/-- Construct a list of rewrites from a proof unit. -/
meta def proof_unit.rewrites (u : proof_unit) (rs : list (expr × bool)) : list (expr × bool) :=
u.steps.filter_map $ how.to_rewrite rs

/-- Construct an explanation string from a proof unit. -/
meta def proof_unit.explain (u : proof_unit) (rs : list (expr × bool))
  (explain_using_conv : bool) : tactic string :=
if explain_using_conv then
  using_conv.explain_rewrites rs u.side u.steps
else
  using_location.explain_rewrites rs u.side u.steps

private meta def explain_proof_full (rs : list (expr × bool)) (explain_using_conv : bool) :
list proof_unit → tactic string
| [] := return ""
| (u :: rest) := do
  -- Don't use transitivity for the last unit, since it must be redundant.
  head ← if rest.length = 0 ∨ u.side = side.L then pure [] else (do
    n ← infer_type u.proof >>= (λ e, prod.snd <$> (match_eq e <|> match_iff e)) >>= pp,
    pure $ ["transitivity " ++ to_string n]),
  unit_expl ← u.explain rs explain_using_conv,
  rest_expl ← explain_proof_full rest,
  let expls := (head ++ [unit_expl, rest_expl]).filter $ λ t, ¬(t.length = 0),
  return $ string.intercalate ",\n  " expls

private meta def explain_proof_concisely (rules : list (expr × bool)) (proof : expr)
  (l : list proof_unit) : tactic string :=
do let rws : list (expr × bool) := list.join $ l.map (λ u, do
    (r, s) ← u.rewrites rules,
    return (r, if u.side = side.L then s else ¬s)),
  goal ← infer_type proof,
  needs_refl ← check_if_simple_rewrite_succeeds rws goal,
  explain_rewrites_concisely rws needs_refl

/--
Trace a human-readable explanation in Lean code of a proof generated by rewrite search.
Emit it as "Try this: <code>" with each successive line of code indented.
-/
meta def explain_search_result (cfg : config) (rules : list (expr × bool)) (proof : expr)
  (units : list proof_unit) : tactic unit :=
if units.empty then trace "Try this: exact rfl" else do
  explanation ← explain_proof_concisely rules proof units <|>
                explain_proof_full rules cfg.explain_using_conv units,
  trace $ "Try this: " ++ explanation

end tactic.rewrite_search
