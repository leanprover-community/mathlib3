import tactic.basic

namespace tactic
namespace local_cache

section internal

variables {α : Type} [reflected α] [has_reflect α]

meta def mk_full_namespace (ns : name) : name := `local_cache ++ ns

meta def get_data_name (ns : name) : tactic name :=
do o ← tactic.get_options,
   let opt := mk_full_namespace ns,
   match o.get_string opt "" with
   | "" := do n ← mk_user_fresh_name,
              tactic.set_options $ o.set_string opt n.to_string,
              return n
   | s := return $ name.from_components $ s.split (λ c, c = '.')
   end

meta def save_data (dn : name) (a : α) [reflected a] : tactic unit :=
tactic.add_decl $ mk_definition dn [] (reflect α) (reflect a)

meta def load_data (dn : name) : tactic α :=
do e ← tactic.get_env,
   d ← e.get dn,
   tactic.eval_expr α d.value

end internal

-- Asks whether the namespace `ns` currently has a value-in-cache
meta def present (ns : name) : tactic bool :=
do o ← tactic.get_options,
   match o.get_string (mk_full_namespace ns) "" with
   | "" := return ff
   | s  := return tt
   end

-- Clear cache associated to namespace `ns`
meta def clear (ns : name) : tactic unit :=
do o ← tactic.get_options,
   set_options $ o.set_string (mk_full_namespace ns) ""

end local_cache

open local_cache

-- Using the namespace `ns` as its key, when called for the first
-- time `calculate_once ns t` runs `t`, saves and returns the result.
-- Upon subsequent invocations in the same `environment` (usually
-- just in the same tactic block) return the cached result.
--
-- If `α` is just `unit`, this means we just run `t` once each tactic
-- block.
meta def run_once {α : Type} [reflected α] [has_reflect α] (ns : name) (t : tactic α) : tactic α :=
do dn ← get_data_name ns,
   load_data dn <|>
   do {
     a ← t,
     save_data dn a,
     return a
   }

end tactic
