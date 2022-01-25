import meta.expr

open tactic

run_cmd do
  l ← mk_local' `l binder_info.default `(ℕ),
  m ← mk_local' `m binder_info.default `(ℕ),
  guard $ `(%%l + %%l = 3).has_local_constant l,
  guard $ bnot $ `(%%l + %%l = 3).has_local_constant m,
  guard $ `(%%l + %%m = 3).has_local_constant l,
  guard $ `(%%l + %%m = 3).has_local_constant m
