import .core
import .module

open tactic

variables {α β γ δ : Type}

namespace tactic.rewrite_search

-- TODO If try_search fails due to a failure to init any of the tracer, metric,
-- or strategy we try again using the "fallback" default versions of all three
-- of these. Instead we could be more thoughtful, and try again only replacing
-- the failing one of these with its respective fallback module version.

meta def rewrite_search_pair (cfg : config α β γ δ) (prog : discovery.progress) (rs : list (expr × bool)) (eqn : sided_pair expr) : tactic string := do
  result ← try_search cfg prog rs eqn,
  match result with
  | some str := return str
  | none := do
    trace "\nError initialising rewrite_search instance, falling back to emergency config!",
    result ← try_search (mk_fallback_config cfg) prog rs eqn,
    match result with
    | some str := return str
    | none := fail "Could not initialise emergency rewrite_search instance!"
    end
end

-- TODO: @Keeley: instead of something like
--     `exprs ← close_under_apps exprs`
-- the ideal thing would be to look for lemmas that have a metavariable
-- for their LHS, and try substituting in hypotheses to these.

meta def collect_rw_lemmas (cfg : collect_cfg) (use_suggest_annotations : bool) (per : discovery.persistence) (extra_names : list name) (extra_rws : list (expr × bool)) : tactic (discovery.progress × list (expr × bool)) := do
  let per := if cfg.help_me then discovery.persistence.try_everything else per,
  (prog, rws) ← discovery.collect use_suggest_annotations per cfg.suggest extra_names,
  hyp_rws ← discovery.rewrite_list_from_hyps,
  let rws := rws ++ extra_rws ++ hyp_rws,

  locs ← local_context,
  rws ← if cfg.inflate_rws then list.join <$> (rws.mmap $ discovery.inflate_rw locs)
        else pure rws,
  return (prog, rws)

meta def rewrite_search_target (cfg : config α β γ δ) (try_harder : bool) (use_suggest_annotations : bool) (per : discovery.persistence) (extra_names : list name) (extra_rws : list (expr × bool)) : tactic string := do
  let cfg := if ¬try_harder then cfg
             else { cfg with try_simp := tt, max_discovers := max 3 cfg.max_discovers },
  t ← target,
  if t.has_meta_var then
    fail "rewrite_search is not suitable for goals containing metavariables"
  else skip,

  (prog, rws) ← collect_rw_lemmas cfg.to_collect_cfg use_suggest_annotations per extra_names extra_rws,

  (lhs, rhs) ← rw_equation.split t,
  rewrite_search_pair cfg prog rws ⟨lhs, rhs⟩

private meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

private meta def add_expr (s : simp_lemmas) (u : list name) (e : expr) : tactic (simp_lemmas × list name) :=
do
  let e := e.erase_annotations,
  match e with
  | expr.const n _ :=
    do { b ← is_valid_simp_lemma_cnst n,
         guard b,
         s ← s.add_simp n,
         return (s, u)
    } <|> do {
      eqns ← get_eqn_lemmas_for tt n,
      guard (eqns.length > 0),
      s ← add_simps s eqns,
      return (s, u)
    } <|> do {
      env ← get_env,
      guard (env.is_projection n).is_some,
      return (s, n::u)
    } <|> fail n
  | _ :=
    (do b ← is_valid_simp_lemma e, guard b, s ← s.add e, return (s, u))
    <|>
    fail e
  end

meta def simp_search_target (cfg : collect_cfg) (use_suggest_annotations : bool)
  (per : discovery.persistence) (extra_names : list name) (extra_rws : list (expr × bool))
  : tactic unit :=
do t ← target,
   (prog, rws) ← collect_rw_lemmas cfg use_suggest_annotations per extra_names extra_rws,

  --  if cfg.ibool `trace_rules ff then do
  --    rs_strings ← rws.mmap pp_rule,
  --    trace ("simp_search using:\n---\n" ++ (string.intercalate "\n" rs_strings) ++ "\n---")
  --  else skip,

   (s, to_unfold) ← mk_simp_set ff [] []
     >>= λ sset, rws.mfoldl (λ c e, add_expr c.1 c.2 e.1 <|> return c) sset,
   (n, pf) ← simplify s to_unfold t {contextual := tt} `eq failed,
   replace_target n pf >> try tactic.triv >> try (tactic.reflexivity reducible)

end tactic.rewrite_search

namespace tactic

open tactic.rewrite_search
open tactic.rewrite_search.discovery.persistence

meta def rewrite_search (cfg : config α β γ δ)
  (try_harder : bool := ff) : tactic string :=
rewrite_search_target cfg try_harder tt try_everything [] []

meta def rewrite_search_with (rs : list interactive.rw_rule) (cfg : config α β γ δ)
  (try_harder : bool := ff) : tactic string :=
do extra_rws ← discovery.rewrite_list_from_rw_rules rs,
   rewrite_search_target cfg try_harder tt speedy [] extra_rws

meta def rewrite_search_using (as : list name) (cfg : config α β γ δ)
  (try_harder : bool := ff) : tactic string :=
do extra_names ← discovery.load_attr_list as,
   rewrite_search_target cfg try_harder ff try_bundles extra_names []

meta def simp_search (cfg : collect_cfg) : tactic unit :=
simp_search_target cfg tt try_everything [] []

meta def simp_search_with (rs : list interactive.rw_rule) (cfg : collect_cfg) : tactic unit :=
do extra_rws ← discovery.rewrite_list_from_rw_rules rs,
   simp_search_target cfg tt try_everything [] extra_rws

end tactic
