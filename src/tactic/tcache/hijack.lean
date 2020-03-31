import .tactic

namespace tcache

open tactic

section locking

@[inline] def LOCKED_FLAG : name := `tcache.locked

@[inline] meta def is_locked : tactic bool :=
do o ← get_options,
   return $ o.get_bool LOCKED_FLAG ff

@[inline] meta def set_locked (b : bool) : tactic unit :=
do o ← get_options,
   set_options $ o.set_bool LOCKED_FLAG b

@[inline] meta def lock : tactic unit := set_locked tt

@[inline] meta def unlock : tactic unit := set_locked ff

@[inline] meta def try_under_lock {α : Type} (alt : tactic α) (t : tactic α) : tactic α := do
  b ← is_locked,
  if b then alt
  else do
    lock,
    r ← t,
    unlock,
    return r

@[inline] meta def try_apply_under_lock {α : Type} (h : tactic α → tactic α) (t : tactic α) : tactic α :=
try_under_lock t (h t)

@[inline] meta def ensure_no_caching {α : Type} (t : tactic α) : tactic α := do
  b ← is_locked,
  lock,
  r ← t,
  set_locked b,
  return r

end locking

section hook

@[inline] meta def bind {α β : Type} (t₁ : tactic α) (t₂ : α → tactic β) : tactic β :=
try_apply_under_lock tcache_force $ interaction_monad_bind t₁ t₂

@[priority 2000, inline] meta instance has_bind : has_bind tactic := ⟨@bind⟩

end hook

end tcache
