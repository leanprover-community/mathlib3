import lib.interactive

import .screening

namespace tactic.rewrite_search.discovery

open tactic
open lean.parser interactive interactive.types

meta def atrr_fail {α : Type} (attr : string) (reason : format) : tactic α :=
  fail $ "[" ++ attr ++ "] error: " ++ to_string reason
private meta def bundle_fail {α : Type} : format → tactic α := atrr_fail "bundle"
private meta def search_fail {α : Type} : format → tactic α := atrr_fail "search"

meta def pick_bundle_name : tactic unit := do
  d ← decl_name,
  n ← match d with
  | name.anonymous := fail "cannot create a bundle with name [anonymous]"
  | name.mk_string s _  := pure $ name.mk_string  s name.anonymous
  | name.mk_numeral n _ := pure $ name.mk_numeral n name.anonymous
  end,
  exact `(n)

-- Heuristic preferences can go in here
@[derive decidable_eq]
meta structure bundle :=
(name : name . pick_bundle_name)

@[derive decidable_eq]
meta structure bundle_ref :=
(name : name)
(bundle : bundle)

meta def cast_to_bundle (n : name) : tactic bundle :=
  type_cast bundle n <|> fail "only definitions of type bundle may be tagged @[bundle]"

meta def lookup_bundle (n : name) : tactic bundle_ref := do
  b ← cast_to_bundle n,
  return ⟨n, b⟩

meta def get_bundle_names : tactic (list name) := attribute.get_instances `bundle

meta def get_bundles : tactic (list bundle_ref) := do
  ns ← attribute.get_instances `bundle,
  ns.mmap lookup_bundle

meta def try_find_bundle_by_name_such_that (p : name → Prop) [decidable_pred p] (n : name) : list name → tactic (option (bundle_ref))
| [] := return none
| (bn :: rest) := do
  if p bn then do
    b ← cast_to_bundle bn,
    -- FIXME the following resolution probably isn't neccessary, attribute.get_instances probably always returns fully-qualified names...
    full_bn ← resolve_constant bn,
    if b.name = n then return $ some ⟨full_bn, b⟩
    else try_find_bundle_by_name_such_that rest
-- How could this double-else be eliminated, withough unneccessarily doing lookups and calling `cast_to_bundle`?
  else try_find_bundle_by_name_such_that rest

meta def try_find_bundle_by_name : name → list name → tactic (option (bundle_ref)) :=
  try_find_bundle_by_name_such_that $ λ _, tt

meta def find_bundle_by_name (n : name) (l : list name) : tactic bundle_ref := do
  ret ← try_find_bundle_by_name n l,
  match ret with
  | none := search_fail format!"there is no bundle named \"{n}\"!"
  | some b := return b
  end

meta def try_find_bundle_duplicate (original : name) : name → list name → tactic (option (bundle_ref)) :=
  try_find_bundle_by_name_such_that $ λ n, ¬(n = original)

meta def check_bundle (n : name) (b : bundle) : tactic unit := do
  bs ← get_bundle_names,
  ret ← try_find_bundle_duplicate n b.name bs,
  match ret with
  | some ⟨bn, b⟩ := bundle_fail format!"there is already a bundle \"{bn}\" named \"{b.name}\"!"
  | none := skip
  end

@[user_attribute]
meta def bundle_attr : user_attribute unit (list name) := {
  name := `bundle,
  descr := "register a definition of type `bundle` for use in the [search ...] attribute",
  parser := return [],
  after_set := some (λ n _ perm, do
    if ¬perm then
      bundle_fail "currently bundles cannot be declared locally"
    else do
      b ← cast_to_bundle n,
      check_bundle n b
  )
}

meta def bundle_ref.get_members (r : bundle_ref) : tactic (list name) := bundle_attr.get_param r.name
meta def bundle_ref.set_members (r : bundle_ref) (l : list name) : tactic unit := bundle_attr.set r.name l tt

meta def collect_bundle_members (l : list bundle_ref) : tactic (list name) := do
  l ← l.erase_dup.mmap bundle_ref.get_members,
  return l.join.erase_dup

meta def try_get_bundle (n : name) : tactic (option (bundle_ref)) := do
  get_bundle_names >>= try_find_bundle_by_name n

meta def get_bundle (n : name) : tactic bundle_ref := do
  get_bundle_names >>= find_bundle_by_name n

meta def get_bundle_members (n : name) : tactic (list name) := do
  b ← get_bundle n, b.get_members

meta def default_bundles : list name := [`default]

meta def for_each_annotated_bundle (attr : user_attribute unit (list name)) (n : name) (f : bundle_ref → tactic unit) : tactic unit := do
  targets ← attr.get_param n,
  let targets := if targets.empty then default_bundles else targets,
  bs ← get_bundle_names,
  targets ← targets.mmap $ λ t, (find_bundle_by_name t bs),
  -- We do this after to make sure we don't fail half-way-through
  targets.mmap' f

@[user_attribute]
meta def search_attr : user_attribute unit (list name) := {
  name := `search,
  descr := "declare that this definition belongs to some list of bundles",
  parser := opt_single_or_list ident,
  after_set := some (λ n _ perm, do
    mk_const n >>= assert_acceptable_lemma,
    for_each_annotated_bundle search_attr n $ λ t, do
      mems ← t.get_members,
      if n ∈ mems then skip
      else t.set_members (n :: mems)
  ),
  before_unset := some (λ n _, do
    for_each_annotated_bundle search_attr n $ λ t, do
      mems ← t.get_members,
      t.set_members $ mems.erase n
  )
}

-- This must be delcared in this file since the name "`default" is used above.
@[bundle] meta def default : bundle := {}

end tactic.rewrite_search.discovery
