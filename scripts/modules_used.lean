import all
import system.io
import tactic.algebra

/-!
# Find all imported modules which are used by the declarations in the target module.

```
lean --run scripts/modules_used.lean data.nat.order.basic
```

returns

```
order.synonym
order.rel_classes
order.monotone.basic
order.lattice
order.heyting.basic
order.bounded_order
order.boolean_algebra
order.basic
logic.nontrivial
logic.nonempty
logic.is_empty
logic.function.basic
logic.equiv.defs
logic.basic
data.subtype
data.set.basic
data.nat.order.basic
data.nat.cast.defs
data.nat.basic
algebra.ring.defs
algebra.order.zero_le_one
algebra.order.sub.defs
algebra.order.sub.canonical
algebra.order.ring.lemmas
algebra.order.ring.defs
algebra.order.ring.canonical
algebra.order.monoid.lemmas
algebra.order.monoid.defs
algebra.order.monoid.canonical.defs
algebra.order.monoid.cancel.defs
algebra.group_with_zero.defs
algebra.group.defs
algebra.group.basic
algebra.covariant_and_contravariant
```

This is useful for finding imports which might be removable.
-/

open tactic declaration environment io io.fs

meta def tactic.get_decls_used (env : environment) : name → name_set → tactic name_set
| n ns := if ns.contains n then pure ns else (do
  d ← env.get n,
  -- Add `n` to the accumulated name set.
  let ns := ns.insert n,
  -- Run `get_decls_used` on any ancestors of `n` (if `n` is a structure)
  ancestors ← get_ancestors n,
  ns ← ancestors.mfoldl (λ ns n, tactic.get_decls_used n ns) ns,
  -- Now traverse the body of the declaration, processing any constants.
  let process (v : expr) : tactic (name_set) :=
    v.fold (pure ns) $ λ e _ r, r >>= λ ns,
      if e.is_constant then tactic.get_decls_used e.const_name ns else pure ns,
  match d with
  | (declaration.defn _ _ _ v _ _) := process v
  | (declaration.thm _ _ _ v)      := process v.get
  | _ := pure ns
  end) <|> (do
  trace format!"Error while processing: {n}",
  pure ns)

meta def tactic.get_modules_used_by_theorems_in (tgt : string) : tactic (list string) :=
do env ← tactic.get_env,
  ns ← env.fold (pure mk_name_set) (λ d r,
    if env.decl_olean d.to_name = some tgt then
      r >>= tactic.get_decls_used env d.to_name
    else r),
  let mods := ns.fold native.mk_rb_set (λ n mods,
    match env.decl_olean n with
    | some mod := mods.insert mod
    | none := mods
    end),
  pure mods.to_list.reverse

meta def main : io unit := do
  [arg] ← io.cmdline_args,
  tgt' ← io.run_tactic ((lean.parser.ident).run_with_input arg),
  let tgt := module_info.resolve_module_name tgt',
  let home_len := tgt.length - (tgt'.length + 5),
  let project := ((tgt.to_list.take home_len)).as_string,
  run_tactic $ do
    files ← tactic.get_modules_used_by_theorems_in tgt,
    -- Only return files in the same project.
    let files := (files.filter_map (λ s, s.get_rest project)),
    -- Convert paths to imports, e.g. `data/nat/order/basic.lean` -> `data.nat.order.basic`.
    -- ... the string library is not exactly featureful.
    let files := files.map (λ s, ((s.to_list.reverse.drop 5).reverse.as_string.split_on '/').foldl
      (λ n s, name.mk_string s n) name.anonymous),
    files.mmap' trace
