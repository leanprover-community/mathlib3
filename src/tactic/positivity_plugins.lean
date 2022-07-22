import tactic.positivity
import data.real.sqrt
import analysis.normed.group.basic


lemma lemma9 {x : ℝ} (hx : 0 < x) : 0 < real.sqrt x := real.sqrt_pos.mpr hx

@[positivity]
meta def positivity_sqrt : expr → tactic (bool × expr)
| `(real.sqrt %%a) := do
  (do -- if can prove `0 < a`, report positivity
    (strict_a, pa) ← positivity_core a,
    prod.mk tt <$> mk_app ``lemma9 [pa]) <|>
  prod.mk ff <$> mk_app ``real.sqrt_nonneg [a] -- else report nonnegativity
| _ := failed

@[positivity]
meta def positivity_norm : expr → tactic (bool × expr)
| `(∥%%a∥) := do prod.mk ff <$> mk_app ``norm_nonneg [a]
| _ := failed

@[positivity]
meta def positivity_dist : expr → tactic (bool × expr)
| `(dist %%a %%b) := do prod.mk ff <$> mk_app ``dist_nonneg [a, b]
| _ := failed
