import tactic.norm_num

namespace tactic

meta def get_pos_goal : tactic (expr × bool) := -- bool is "strict"
do t ← target,
match t with
| `(0 ≤ %%e₂) := pure (e₂, ff)
| `(%%e₂ ≥ 0) := pure (e₂, ff)
| `(0 < %%e₂) := pure (e₂, tt)
| `(%%e₂ > 0) := pure (e₂, tt)
| _ := failed
end

theorem lemma1 {α} [preorder α] {a b b' c : α} : b = b' → a ≤ b' → b < c → a < c :=
λ h1 h2 h3, lt_of_le_of_lt (by rw h1; exact h2) h3

theorem lemma2 {α} [preorder α] {a b b' c : α} : b = b' → a < b' → b ≤ c → a < c :=
λ h1 h2 h3, lt_of_lt_of_le (by rw h1; exact h2) h3

theorem lemma3 {α} [preorder α] {a a' b : α} : a = a' → a ≤ b → a' ≤ b :=
λ h1 h3, by rwa ← h1

theorem lemma4 {α} [preorder α] {b b' a : α} : b = b' → a < b' → a < b :=
λ h1 h3, by rwa h1

#check instance_cache.get _ `has_zero.zero

meta def orelse' (tac1 tac2 : tactic (bool × expr)) : tactic (bool × expr) := do
  res ← try_core tac1,
  match res with
  | none := tac2
  | some res@(ff, _) := tac2 <|> pure res
  | some res@(tt, _) := pure res
  end

meta def positivity_base (e : expr) : tactic (bool × expr) :=
orelse' (do -- try `norm_num` to prove the goal positive directly
  (e', p) ← norm_num.derive e <|> refl_conv e,
  e'' ← e'.to_rat,
  typ ← infer_type e',
  ic ← mk_instance_cache typ,
  if e'' > 0 then do
    (ic, p₁) ← norm_num.prove_pos ic e',
    p ← mk_app ``lemma4 [p, p₁],
    pure (tt, p)
  else if e'' = 0 then do
    p' ← mk_app ``ge_of_eq [p], -- check this lemma is the right one!
    pure (ff, p')
  else failed) $ -- loop over hypotheses
  local_context >>= list.foldl (λ tac p₃,
    orelse' tac $ do -- if RHS of the hypothesis is the object whose positivity is sought, try
    -- `norm_num` to prove positivity of the LHS and then apply transitivity
      p_typ ← infer_type p₃,
      (lo, hi, strict) ← match p_typ with
      | `(%%lo ≤ %%hi) := pure (lo, hi, ff)
      | `(%%hi ≥ %%lo) := pure (lo, hi, ff)
      | `(%%lo < %%hi) := pure (lo, hi, tt)
      | `(%%hi > %%lo) := pure (lo, hi, tt)
      | _ := failed
      end,
      is_def_eq e hi,
      (lo', p₂) ← norm_num.derive lo <|> refl_conv lo,
      typ ← infer_type lo',
      ic ← mk_instance_cache typ,
      if strict then do
        (ic, p₁) ← norm_num.prove_nonneg ic lo',
        p ← mk_app ``lemma1 [p₂, p₁, p₃],
        pure (tt, p)
      else do
        z ← mk_mapp ``has_zero.zero [some typ, none], -- there was a way to get from instance cache?
        if lo' = z then do
          p ← mk_app ``lemma3 [p₂, p₃],
          pure (ff, p)
        else do
          (ic, p₁) ← norm_num.prove_pos ic lo',
          p ← mk_app ``lemma2 [p₂, p₁, p₃],
          pure (tt, p)) failed

@[user_attribute]
meta def positivity_attr : user_attribute (expr → tactic (bool × expr)) unit :=
{ name      := `positivity,
  descr     := "Add positivity derivers",
  cache_cfg :=
  { mk_cache := λ ns, do
    { t ← ns.mfoldl
        (λ (t : expr → tactic (bool × expr)) n, do
          t' ← eval_expr (expr → tactic (bool × expr)) (expr.const n []),
          pure (λ e, orelse' (t' e) (t e)))
        (λ _, failed),
      pure (λ e, orelse' (positivity_base e) (t e)) },
    dependencies := [] } }

/-- Look for a proof of positivity/nonnegativity of an expression `e`; if found, return the proof
together with a boolean stating whether the proof found was for strict positivity (`tt`) or only
for nonnegativity (`ff`). -/
meta def positivity_core (e : expr) : tactic (bool × expr) := do
  f ← positivity_attr.get_cache,
  f e <|> fail "failed to prove positivity/nonnegativity"

@[positivity]
meta def positivity_add : expr → tactic (bool × expr)
| `(%%a + %%b) := do
  (strict_a, pa) ← positivity_core a,
  (strict_b, pb) ← positivity_core b,
  match strict_a, strict_b with
  | tt, tt := prod.mk tt <$> mk_app ``add_pos [pa, pb]
  | tt, ff := prod.mk tt <$> mk_app ``lt_add_of_pos_of_le [pa, pb]
  | ff, tt := prod.mk tt <$> mk_app ``lt_add_of_le_of_pos [pa, pb]
  | ff, ff := prod.mk ff <$> mk_app ``add_nonneg [pa, pb]
  end
| _ := failed

lemma lemma5 {R : Type*} [linear_ordered_semiring R] (a b : R) (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a * b :=
mul_nonneg ha.le hb

lemma lemma6 {R : Type*} [linear_ordered_semiring R] (a b : R) (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a * b :=
mul_nonneg ha hb.le

@[positivity]
meta def positivity_mul : expr → tactic (bool × expr)
| `(%%a * %%b) := do
  (strict_a, pa) ← positivity_core a,
  (strict_b, pb) ← positivity_core b,
  match strict_a, strict_b with
  | tt, tt := prod.mk tt <$> mk_app ``mul_pos [pa, pb]
  | tt, ff := prod.mk ff <$> mk_app ``lemma5 [pa, pb]
  | ff, tt := prod.mk ff <$> mk_app ``lemma6 [pa, pb]
  | ff, ff := prod.mk ff <$> mk_app ``mul_nonneg [pa, pb]
  end
| _ := failed

lemma lemma7 {R : Type*} [linear_ordered_field R] (a b : R) (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a / b :=
div_nonneg ha.le hb

lemma lemma8 {R : Type*} [linear_ordered_field R] (a b : R) (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a / b :=
div_nonneg ha hb.le

@[positivity]
meta def positivity_div : expr → tactic (bool × expr)
| `(%%a / %%b) := do
  (strict_a, pa) ← positivity_core a,
  (strict_b, pb) ← positivity_core b,
  match strict_a, strict_b with
  | tt, tt := prod.mk tt <$> mk_app ``div_pos [pa, pb]
  | tt, ff := prod.mk ff <$> mk_app ``lemma7 [pa, pb]
  | ff, tt := prod.mk ff <$> mk_app ``lemma8 [pa, pb]
  | ff, ff := prod.mk ff <$> mk_app ``div_nonneg [pa, pb] -- TODO handle eg `int.div_nonneg`
  end
| _ := failed

@[positivity]
meta def positivity_pow : expr → tactic (bool × expr)
| `(%%a ^ %%n) := do
  n_typ ← infer_type n,
  match n_typ with
  | `(ℕ) := do
    if n = `(0) then do
      -- if we're considering `a ^ 0` then it's strictly positive
      p₂ ← mk_app ``pow_zero [a],
      a_typ ← infer_type a,
      p₁ ← mk_mapp ``zero_lt_one [some a_typ, none, none], -- better way here?
      prod.mk tt <$> mk_app ``lemma4 [p₂, p₁]
    else do
      -- else, `a ^ n` is positive if `a` is and nonnegative if `a` is
      (strict_a, pa) ← positivity_core a,
      match strict_a with
      | tt := prod.mk tt <$> mk_app ``pow_pos [pa, n]
      | ff := prod.mk ff <$> mk_app ``pow_nonneg [pa, n]
      end
  | _ := failed -- TODO handle integer powers, maybe even real powers
  end
| _ := failed

@[positivity]
meta def positivity_abs : expr → tactic (bool × expr)
| `(|%%a|) := do
  (do -- if can prove `0 < a`, report positivity
    (strict_a, pa) ← positivity_core a,
    prod.mk tt <$> mk_app ``abs_pos_of_pos [pa]) <|>
  prod.mk ff <$> mk_app ``abs_nonneg [a] -- else report nonnegativity
| _ := failed

/- TODO: implement further plugins (raising to non-numeral powers, exp, log, norm) -/

meta def positivity : tactic unit := focus1 $ do
  (a, strict_desired) ← get_pos_goal,
  (strict_proved, p) ← positivity_core a,
  match strict_desired, strict_proved with
  | tt, ff := fail "failed to prove strict positivity, but it would be possible to prove nonnegativity if desired"
  | ff, tt := mk_app ``le_of_lt [p]
  | _, _ := pure p
  end >>= exact

namespace interactive

setup_tactic_parser

meta def positivity : tactic unit := tactic.positivity

end interactive

end tactic
