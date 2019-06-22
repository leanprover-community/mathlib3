import lib.tactic

import .bundle

namespace tactic.rewrite_search.discovery

open tactic

private meta def suggest_fail {α : Type} : format → tactic α := atrr_fail "suggest"

-- Reads the name of a list/single annotated with `[suggest]`.
meta def read_suggestion (n : name) : tactic (list name) := do
  n ← mk_const n,
      (do l ← eval_expr (list name) n, return l) -- Is the suggestion a list?
  <|> (do s ← eval_expr name n, return [s])      -- Is the suggestion a singleton?
  <|> fail "[suggest] error: only `name`s, or `list name`s, can be tagged with `suggest`. These names should all refer to `bundle`s."

-- Reads a list of bundle names and converts them into the actual
-- identifiers of the bundles (which unfortunately are also just names).
-- I fail if I can't find a bundle, since `get_bundle` does too.
meta def lookup_suggestion (l : list name) : tactic (list name) :=
  l.mmap (λ n, do b ← get_bundle n, return b.name)

-- Reads the name of a list/single annotated with `[suggest]` and
-- returns the list of identifiers for the bundles which were
-- referred to.
meta def resolve_suggestion (n : name) : tactic (list name) :=
  read_suggestion n >>= lookup_suggestion

meta def fill_suggest_data (attr : user_attribute unit (list name)) (n : name) (l : list name) : tactic unit :=
  match l with
  | [] := do
    ls ← resolve_suggestion n,
    if ls.length = 0 then skip -- prevent infinite recursion
    else attr.set n ls tt
  | _ := skip
  end

@[user_attribute]
meta def suggest_attr : user_attribute unit (list name) := {
  name := `suggest,
  descr := "suggests the name of a bundle, or a list of names of bundles, to the `rewrite_search`er",
  parser := return [],
  after_set := some (λ n _ _,
    suggest_attr.get_param n >>= fill_suggest_data suggest_attr n
  ),
  before_unset := some (λ _ _, skip)
}

meta def get_suggested_bundle_idents : tactic (list name) := do
  ls ← attribute.get_instances `suggest,
  ls ← ls.mmap suggest_attr.get_param,
  return ls.join.erase_dup

@[suggest]
meta def default_suggestions : list name := default_bundles

end tactic.rewrite_search.discovery
