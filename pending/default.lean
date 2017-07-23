/- Temporary space for definitions pending merges to the lean repository -/

open tactic

-- PR #1761
meta def transport_multiplicative_to_additive' (ls : list (name × name)) : command :=
let dict := rb_map.of_list ls in
ls.foldl (λ t ⟨src, tgt⟩, do
  env ← get_env,
  if (env.get tgt).to_bool = ff
  then t >> transport_with_dict dict src tgt
  else t)
skip

namespace nat
  @[simp] theorem shiftl_zero (m) : shiftl m 0 = m := rfl
  @[simp] theorem shiftl_succ (m n) : shiftl m (n + 1) = bit0 (shiftl m n) := rfl
end nat