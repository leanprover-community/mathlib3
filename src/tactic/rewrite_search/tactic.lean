/-
Copyright (c) 2020 Kevin Lacker, Keeley Hoek, Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Keeley Hoek, Scott Morrison
-/
import tactic.rewrite_search.module
import tactic.rewrite_search.discovery

/-!
# The noninteractive rewrite search tactic.
-/

open tactic

namespace tactic.rewrite_search

meta def rewrite_search_pair (cfg : config) (rs : list (expr × bool))
(eqn : sided_pair expr) : tactic string :=
do result ← try_search cfg rs eqn,
match result with
  | some str := return str
  | none := fail "Could not initialize rewrite_search instance."
end

meta def collect_rw_lemmas (cfg : config) (extra_names : list name)
(extra_rws : list (expr × bool)) : tactic (list (expr × bool)) :=
do rws ← discovery.collect extra_names,
   hyp_rws ← discovery.rewrite_list_from_hyps,
   let rws := rws ++ extra_rws ++ hyp_rws,

   locs ← local_context,
   if cfg.inflate_rws then list.join <$> (rws.mmap $ discovery.inflate_rw locs)
   else pure rws

meta def rewrite_search_target (cfg : config) (try_harder : bool)
  (extra_names : list name) (extra_rws : list (expr × bool)) : tactic string :=
do let cfg := if ¬try_harder then cfg
              else { cfg with try_simp := tt },
   t ← target,
   if t.has_meta_var then
     fail "rewrite_search is not suitable for goals containing metavariables"
   else skip,

   rws ← collect_rw_lemmas cfg extra_names extra_rws,

   (lhs, rhs) ← rw_equation.split t,
   rewrite_search_pair cfg rws ⟨lhs, rhs⟩

end tactic.rewrite_search

namespace tactic

open tactic.rewrite_search

meta def rewrite_search (cfg : config) (try_harder : bool := ff) : tactic string :=
rewrite_search_target cfg try_harder [] []

meta def rewrite_search_with (rs : list interactive.rw_rule) (cfg : config)
  (try_harder : bool := ff) : tactic string :=
do extra_rws ← discovery.rewrite_list_from_rw_rules rs,
   rewrite_search_target cfg try_harder [] extra_rws

meta def rewrite_search_using (as : list name) (cfg : config) (try_harder : bool := ff) :
tactic string :=
do extra_names ← discovery.load_attr_list as,
   rewrite_search_target cfg try_harder extra_names []

end tactic
