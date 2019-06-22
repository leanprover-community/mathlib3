import lib.list
import .types

-- Required for us to emit more compact `conv` invocations
import tactic.converter.interactive

open interactive interactive.types expr tactic

variables {α β γ δ : Type}

namespace tactic.rewrite_search

private meta def hand : sided_pair string := ⟨"lhs", "rhs"⟩

meta def nth_rule (rs : list (expr × bool)) (i : ℕ) : expr × bool := (rs.nth i).iget

meta def pp_rule (r : expr × bool) : tactic string :=
  do pp ← pp r.1, return $ (if r.2 then "←" else "") ++ (to_string pp)

meta def how.to_rewrite (rs : list (expr × bool)) : how → option (expr × bool)
| (how.rewrite index _ _) := nth_rule rs index
| _ := none

meta def explain_using_location (rs : list (expr × bool)) (s : side) : how → tactic (option string)
| (how.rewrite index location _) := do
  rule ← pp_rule $ nth_rule rs index,
  return $ some ("nth_rewrite_" ++ hand.get s ++ " " ++ to_string location ++ " " ++ rule)
| _ := return none

meta def using_location.explain_rewrites (rs : list (expr × bool)) (s : side) (steps : list how) : tactic string := do
  rules ← steps.mmap $ λ h : how, option.to_list <$> explain_using_location rs s h,
  return $ string.intercalate ",\n" rules.join

namespace using_conv

inductive app_addr
| node (children : sided_pair (option app_addr)) : app_addr
| rw : list ℕ → app_addr

open app_addr

meta def app_addr.to_string : app_addr → string
| (node c) := "(node " ++ ((c.to_list.filter_map id).map app_addr.to_string).to_string ++ ")"
| (rw rws) := "(rw " ++ rws.to_string ++ ")"

inductive splice_result
-- There was more of the addr to be added left, but we hit a rw
| obstructed
-- The added addr was already fully contained, and did not terminate at an existing rw
| contained
-- The added addr terminated at an existing rw or we could create a new one for it
| new (addr : app_addr)

open splice_result

def splice_result.pack (s : side) : splice_result → sided_pair (option app_addr) → splice_result
| (new addr) c := new $ app_addr.node $ c.set s (some addr)
| sr _ := sr

-- TODO? prove well founded
private meta def splice_in_aux (new_rws : list ℕ) : option app_addr → list side → splice_result
| (some $ node _) [] := contained
| (some $ node c) (s :: rest) := (splice_in_aux (c.get s) rest).pack s c
| (some $ rw _) (_ :: _) := obstructed
| (some $ rw rws) [] := new $ rw (rws ++ new_rws)
| none [] := new $ rw new_rws
| none l := splice_in_aux (some $ node ⟨none, none⟩) l

private meta def to_congr_form : list side → tactic (list side)
| [] := return []
| (side.L :: (side.R :: rest)) := do
  r ← to_congr_form rest,
  return (side.L :: r)
| (side.R :: rest) := do
  r ← to_congr_form rest,
  return (side.R :: r)
| [side.L] := fail "app list ends in side.L!"
| (side.L :: (side.L :: _)) := fail "app list has repeated side.L!"

meta def splice_in (a : option app_addr) (rws : list ℕ) (s : list side) : tactic splice_result :=
  splice_in_aux rws a <$> to_congr_form s

meta def build_rw_tactic (rs : list (expr × bool)) (hs : list ℕ) : tactic string := do
  rws ← (hs.map $ nth_rule rs).mmap pp_rule,
  return $ "erw [" ++ (string.intercalate ", " rws) ++ "]"

meta def explain_tree_aux (rs : list (expr × bool)) : app_addr → tactic (option (list string))
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

-- TODO break the tree into pieces when the gaps are too big
meta def explain_tree (rs : list (expr × bool)) (tree : app_addr) : tactic (list string) :=
  list.join <$> option.to_list <$> explain_tree_aux rs tree

meta def compile_rewrites_aux (rs : list (expr × bool)) (s : side) : option app_addr → list how → tactic (list string)
| none [] := return []
| (some tree) [] := do
  tacs ← explain_tree rs tree,
  return $ if tacs.length = 0 then []
  else ["conv_" ++ hand.get s ++ " { " ++ string.intercalate ", " tacs ++ " }"]
| tree (h :: rest) := do
-- TODO handle other how.* values here, e.g. how.simp
-- At the moment we just silently drop these.
  (new_tree, rest_if_fail) ← match h with
  | how.rewrite index loc (some addr) := do
    new_tree ← splice_in tree [index] addr,
    return (some new_tree, list.cons h rest)
  | _ := do
    return (none, rest)
  end,

  match new_tree with
  | some (new new_tree) := compile_rewrites_aux new_tree rest
  | _ := do
    line ← compile_rewrites_aux tree [],
    lines ← compile_rewrites_aux none rest_if_fail,
    return $ line ++ lines
  end

meta def compile_rewrites (rs : list (expr × bool)) (s : side) : list how → tactic (list string) :=
  compile_rewrites_aux rs s none

meta def explain_rewrites (rs : list (expr × bool)) (s : side) (hows : list how) : tactic string :=
  string.intercalate ",\n" <$> compile_rewrites rs s hows

end using_conv

meta def explain_rewrites_concisely (steps : list (expr × bool)) (needs_refl : bool) : tactic string := do
  rules ← string.intercalate ", " <$> steps.mmap pp_rule,
  return $ "erw [" ++ rules ++ "]" ++ (if needs_refl then ", refl" else "")

-- fails if we can't just use rewrite
-- otherwise, returns 'tt' if we need a `refl` at the end
meta def check_if_simple_rewrite_succeeds (rewrites : list (expr × bool)) (goal : expr) : tactic bool :=
lock_tactic_state $ do
  m ← mk_meta_var goal,
  set_goals [m],
  rewrites.mmap' $ λ q, rewrite_target q.1 {symm := q.2, md := semireducible},
  (reflexivity reducible >> return ff) <|> (reflexivity >> return tt)

meta def proof_unit.rewrites (u : proof_unit) (rs : list (expr × bool)) : list (expr × bool) :=
  u.steps.filter_map $ how.to_rewrite rs

-- TODO rewrite this to use conv!
meta def proof_unit.explain (u : proof_unit) (rs : list (expr × bool)) (explain_using_conv : bool) : tactic string := do
  -- TODO We could try to merge adjacent proof units or something more complicated.

  -- FIXME using explain_rewrites_concisely:
  -- Currently we only try to explain away the whole proof, falling back on
  -- failure. Moreover, "single proof unit" is unfortunately broken, because
  -- `erw` inspects the goal when it performs its actions. As an example of a
  -- failing case, observe (or check) that given an axiom `foo` saying [1] = [2]`
  -- then `check_if_simple_rewrite_succeeds` will approve using `erw [foo]` to
  -- discharge the goal `[[1], [1]] = [[1], [2]]`, even though once part of the
  -- explaination of a bigger proof with multiple units `erw` will turn
  -- `[[1], [1]]` into `[[2], [2]]`, not what we want.

  -- One possible solution is to prepend `transitivity xxx` in front of such
  -- left-proof_units (currently we only do this for right-proof_units), but
  -- this seems to tend to be more clumsy that a one-line `congr` which would
  -- normally replace it.

  -- This is a bit of a shame, though, since it works quite well in many siutations.
  -- Perhaps we should run though given this optimisation, try to see if the
  -- resulting whole proof works, emit if it succeeds and if it fails go-again
  -- without the optimisations? This actually wouldn't be too hard to implement.

  -- (do
  --   goal ← infer_type u.proof,
  --   let rewrites := u.rewrites cfg,
  --   needs_refl ← check_if_simple_rewrite_succeeds rewrites goal,
  --   explain_rewrites_concisely rewrites needs_refl
  -- ) <|>

  if explain_using_conv then
    using_conv.explain_rewrites rs u.side u.steps
  else
    using_location.explain_rewrites rs u.side u.steps

meta def explain_proof_full (rs : list (expr × bool)) (explain_using_conv : bool) : list proof_unit → tactic string
| [] := return ""
| (u :: rest) := do
  -- This is an optimisation: don't use transitivity for the last unit, since
  -- it neccesarily must be redundant.
  head ← if rest.length = 0 ∨ u.side = side.L then pure [] else (do
    n ← infer_type u.proof >>= rw_equation.rhs >>= pp,
    pure $ ["transitivity " ++ to_string n]
  ),

  unit_expl ← u.explain rs explain_using_conv,
  rest_expl ← explain_proof_full rest,
  let expls := (head ++ [unit_expl, rest_expl]).filter $ λ t, ¬(t.length = 0),
  return $ string.intercalate ",\n" expls

meta def explain_proof_concisely (rs : list (expr × bool)) (proof : expr) (l : list proof_unit) : tactic string := do
  let rws : list (expr × bool) := list.join $ l.map (λ u, do
    (r, s) ← u.rewrites rs,
    return (r, if u.side = side.L then s else ¬s)
  ),
  goal ← infer_type proof,
  needs_refl ← check_if_simple_rewrite_succeeds rws goal,
  explain_rewrites_concisely rws needs_refl

meta def explain_search_result (cfg : core_cfg) (rs : list (expr × bool)) (proof : expr) (units : list proof_unit) : tactic string := do
  if cfg.trace then do
    pp ← pp proof,
    trace format!"rewrite_search found proof:\n{pp}"
  else skip,

  explanation ← explain_proof_concisely rs proof units <|> explain_proof_full rs cfg.explain_using_conv units,
  if cfg.explain then trace $ "/- `rewrite_search` says -/\n" ++ explanation
  else skip,
  return explanation

end tactic.rewrite_search
