import tactic.basic

namespace tactic
namespace local_cache

section internal

variables {α : Type} [reflected α] [has_reflect α]

meta def mk_full_namespace (ns : name) : name := `local_cache ++ ns

-- `mk_new` gives a way to generate a new name if no current one
-- exists.
meta def get_data_name_aux (ns : name) (mk_new : options → name → tactic name) : tactic name :=
do o ← tactic.get_options,
   let opt := mk_full_namespace ns,
   match o.get_string opt "" with
   | "" := mk_new o opt
   | s := return $ name.from_components $ s.split (λ c, c = '.')
   end

meta def get_data_name (ns : name) : tactic name :=
get_data_name_aux ns $ λ o opt,
do n ← mk_user_fresh_name,
   tactic.set_options $ o.set_string opt n.to_string,
   return n

-- Like `get_data_name`, but fail if `ns` does not have a cached
-- decl name (we create a new one above).
meta def try_get_data_name (ns : name) : tactic name :=
get_data_name_aux ns $ λ o opt, fail format!"no cache for \"{ns}\""

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

-- Gets the (optionally present) value-in-cache for `ns`
meta def get (ns : name) (α : Type) [reflected α] [has_reflect α] : tactic (option α) :=
do dn ← some <$> try_get_data_name ns <|> return none,
   match dn with
   | none := return none
   | some dn := some <$> load_data dn
   end
-- Note: we can't just use `<|>` on `load_data` since it will fail
-- when a cached value is not present *as well as* when the type of
-- `α` is just wrong.

end local_cache

open local_cache

-- Using the namespace `ns` as its key, when called for the first
-- time `run_once ns t` runs `t`, then saves and returns the result.
-- Upon subsequent invocations with the same `tactic.get_options` state
-- (usually just in the same tactic block, with the scope of the caching
-- being inherited by child tactic blocks) we return the cached result
-- directly.
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
