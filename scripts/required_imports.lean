import all
import system.io

meta def decls_used_in : declaration → name_set → name_set
| d ns :=
  let process (v : expr) : name_set :=
    v.fold ns $ λ e _ ns, if e.is_constant then ns.insert e.const_name else ns in
  match d with
  | (declaration.defn _ _ _ v _ _) := process v
  | (declaration.thm _ _ _ v)      := process v.get
  | _ := ns
  end

meta def main : io unit := do
  env ← io.run_tactic tactic.get_env,
  let map := env.fold (native.rb_map.mk string name_set) (λ d map,
    match env.decl_olean d.to_name with
    | some tgt := map.insert tgt (decls_used_in d ((map.find tgt).get_or_else mk_name_set))
    | none := map
    end),
  map.mfold () $ λ mod ns _, do
    io.print_ln sformat!"module: {mod}",
    let mods := ns.fold (native.mk_rb_set) (λ n mods, match env.decl_olean n with
    | some tgt := mods.insert tgt
    | none := mods
    end),
    mods.mfold () $ λ mod _, do
      io.print_ln sformat!"needs: {mod}"
