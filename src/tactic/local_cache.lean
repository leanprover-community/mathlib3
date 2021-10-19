/-
Copyright (c) 2019 Keeley Hoek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keeley Hoek
-/
import tactic.norm_num

namespace tactic
namespace local_cache

namespace internal

variables {α : Type} [reflected α] [has_reflect α]

meta def mk_full_namespace (ns : name) : name := `local_cache ++ ns

meta def save_data (dn : name) (a : α) [reflected a] : tactic unit :=
tactic.add_decl $ mk_definition dn [] (reflect α) (reflect a)

meta def load_data (dn : name) : tactic α :=
do e ← tactic.get_env,
   d ← e.get dn,
   tactic.eval_expr α d.value

meta def poke_data (dn : name) : tactic bool :=
do e ← tactic.get_env,
   return (e.get dn).to_bool

meta def run_once_under_name {α : Type} [reflected α] [has_reflect α] (t : tactic α)
  (cache_name : name) : tactic α :=
do load_data cache_name <|>
   do {
     a ← t,
     save_data cache_name a,
     return a }

-- We maintain two separate caches with different scopes:
-- one local to `begin ... end` or `by` blocks, and another
-- for entire `def`/`lemma`s.
meta structure cache_scope :=
-- Returns the name of the def used to store the contents of is cache,
-- making a new one and recording this in private state if neccesary.
(get_name : name → tactic name)
-- Same as above but fails instead of making a new name, and never
-- mutates state.
(try_get_name : name → tactic name)
-- Asks whether the namespace `ns` currently has a value-in-cache
(present : name → tactic bool)
-- Clear cache associated to namespace `ns`
(clear : name → tactic unit)

namespace block_local

-- `mk_new` gives a way to generate a new name if no current one
-- exists.
private meta def get_name_aux (ns : name) (mk_new : options → name → tactic name) : tactic name :=
do o ← tactic.get_options,
   let opt := mk_full_namespace ns,
   match o.get_string opt "" with
   | "" := mk_new o opt
   | s := return $ name.from_components $ s.split (= '.')
   end

meta def get_name (ns : name) : tactic name :=
get_name_aux ns $ λ o opt,
do n ← mk_user_fresh_name,
   tactic.set_options $ o.set_string opt n.to_string,
   return n

-- Like `get_name`, but fail if `ns` does not have a cached
-- decl name (we create a new one above).
meta def try_get_name (ns : name) : tactic name :=
get_name_aux ns $ λ o opt, fail format!"no cache for \"{ns}\""

meta def present (ns : name) : tactic bool :=
do o ← tactic.get_options,
   match o.get_string (mk_full_namespace ns) "" with
   | "" := return ff
   | s  := return tt
   end

meta def clear (ns : name) : tactic unit :=
do o ← tactic.get_options,
   set_options $ o.set_string (mk_full_namespace ns) ""

end block_local

namespace def_local

-- Fowler-Noll-Vo hash function (FNV-1a)
section fnv_a1

def FNV_OFFSET_BASIS := 0xcbf29ce484222325
def FNV_PRIME := 0x100000001b3
def RADIX := by apply_normed 2^64

def hash_byte (seed : ℕ) (c : char) : ℕ :=
let n : ℕ := c.to_nat in ((seed.lxor n) * FNV_PRIME) % RADIX

def hash_string (s : string) : ℕ :=
s.to_list.foldl hash_byte FNV_OFFSET_BASIS

end fnv_a1

meta def hash_context : tactic string :=
do ns ← open_namespaces,
   dn ← decl_name,
   let flat := ((list.cons dn ns).map to_string).foldl string.append "",
   return $ (to_string dn) ++ (to_string (hash_string flat))

meta def get_root_name (ns : name) : tactic name :=
do hc ← hash_context,
   return $ mk_full_namespace $ hc ++ ns

meta def apply_tag (n : name) (tag : ℕ) : name := n ++ to_string format!"t{tag}"

meta def mk_dead_name (n : name) : name := n ++ `dead

meta def kill_name (n : name) : tactic unit :=
save_data (mk_dead_name n) ()

meta def is_name_dead (n : name) : tactic bool :=
do { witness : unit ← load_data $ mk_dead_name n, return true }
<|> return false

-- `get_with_status_tag_aux rn n` fails exactly when `rn ++ to_string n` does
-- not exist.
private meta def get_with_status_tag_aux (rn : name) : ℕ → tactic (ℕ × bool)
| tag := do let n := apply_tag rn tag,
            present ← poke_data n,
            if ¬present then fail format!"{rn} never seen in cache!"
            else do is_dead ← is_name_dead n,
                    if is_dead then get_with_status_tag_aux (tag + 1)
                                    <|> return (tag, false)
                    else return (tag, true)

-- Find the latest tag for the name `rn` and report whether it is alive.
meta def get_tag_with_status (rn : name) : tactic (ℕ × bool) :=
get_with_status_tag_aux rn 0

meta def get_name (ns : name) : tactic name :=
do rn ← get_root_name ns,
   (tag, alive) ← get_tag_with_status rn <|> return (0, true),
   return $ apply_tag rn $ if alive then tag
                           else tag + 1

meta def try_get_name (ns : name) : tactic name :=
do rn ← get_root_name ns,
   (tag, alive) ← get_tag_with_status rn,
   if alive then return $ apply_tag rn tag
   else fail format!"no cache for \"{ns}\""

meta def present (ns : name) : tactic bool :=
do rn ← get_root_name ns,
   (prod.snd <$> get_tag_with_status rn) <|> return false

meta def clear (ns : name) : tactic unit :=
do { n ← try_get_name ns, kill_name n }
<|> skip

end def_local

end internal

open internal

/-- This scope propogates the cache within a `begin ... end` or `by` block
    and its decendants. -/
meta def cache_scope.block_local : cache_scope :=
⟨ block_local.get_name,
  block_local.try_get_name,
  block_local.present,
  block_local.clear ⟩

/-- This scope propogates the cache within an entire `def`/`lemma`. -/
meta def cache_scope.def_local : cache_scope :=
⟨ def_local.get_name,
  def_local.try_get_name,
  def_local.present,
  def_local.clear ⟩

open cache_scope

/-- Asks whether the namespace `ns` currently has a value-in-cache. -/
meta def present (ns : name) (s : cache_scope := block_local) : tactic bool :=
s.present ns

/-- Clear cache associated to namespace `ns`. -/
meta def clear (ns : name) (s : cache_scope := block_local) : tactic unit :=
s.clear ns

/-- Gets the (optionally present) value-in-cache for `ns`. -/
meta def get (ns : name) (α : Type) [reflected α] [has_reflect α] (s : cache_scope := block_local) :
  tactic (option α) :=
do dn ← some <$> s.try_get_name ns <|> return none,
   match dn with
   | none := return none
   | some dn := some <$> load_data dn
   end
-- Note: we can't just use `<|>` on `load_data` since it will fail
-- when a cached value is not present *as well as* when the type of
-- `α` is just wrong.

end local_cache

open local_cache local_cache.internal

/-- Using the namespace `ns` as its key, when called for the first
    time `run_once ns t` runs `t`, then saves and returns the result.
    Upon subsequent invocations in the same tactic block, with the scope
    of the caching being inherited by child tactic blocks) we return the
    cached result directly.

    You can configure the cached scope to be entire `def`/`lemma`s changing
    the optional cache_scope argument to `cache_scope.def_local`.
    Note: the caches backing each scope are different.

    If `α` is just `unit`, this means we just run `t` once each tactic
    block. -/
meta def run_once {α : Type} [reflected α] [has_reflect α] (ns : name) (t : tactic α)
  (s : cache_scope := cache_scope.block_local) : tactic α :=
s.get_name ns >>= run_once_under_name t

end tactic
