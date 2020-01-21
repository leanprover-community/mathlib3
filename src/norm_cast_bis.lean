import tactic.norm_cast

namespace norm_cast_bis
open tactic expr norm_cast

/--
This is an auxiliary function that proves e = new_e using only squash lemmas.
-/
meta def aux_squash (e new_e : expr) : tactic expr :=
do
  cache ← norm_cast_attr.get_cache,
  let s := cache.squash,
  (e', pr) ← s.rewrite new_e,
  is_def_eq e e',
  mk_eq_symm pr

/--
This is an auxiliary function that proves e = new_e squash and push lemmas.
-/
meta def aux_down (e new_e : expr) : tactic expr :=
do
  cache ← norm_cast_attr.get_cache,
  let s := cache.down,
  (e', pr) ← s.rewrite new_e,
  is_def_eq e e',
  mk_eq_symm pr

-- the unit argument is required for the `simplify` api.
/--
This is the main heuristic used alongside the elim_cast and move_cast lemmas.
The goal is to help casts move past operators by adding intermediate casts.
An expression of the shape: op (↑(x : α) : γ) (↑(y : β) : γ)
is rewritten to:            op (↑(↑(x : α) : β) : γ) (↑(y : β) : γ)
when (↑(↑(x : α) : β) : γ) = (↑(x : α) : γ) can be proven with a squash_cast lemma
-/
@[nolint] meta def heur (_ : unit) : expr → tactic (unit × expr × expr)
| (app (app op x) y) :=
( do
  `(@coe %%α %%δ %%coe1 %%xx) ← return x,
  `(@coe %%β %%γ %%coe2 %%yy) ← return y,
  success_if_fail $ is_def_eq α β,
  is_def_eq δ γ,

  (do
    coe3 ← mk_app `has_lift_t [α, β] >>= mk_instance',
    new_x ← to_expr ``(@coe %%β %%δ %%coe2 (@coe %%α %%β %%coe3 %%xx)),
    let new_e := app (app op new_x) y,
    eq_x ← aux_down x new_x,
    pr ← mk_congr_arg op eq_x,
    pr ← mk_congr_fun pr y,
    return ((), new_e, pr)
  ) <|> (do
    coe3 ← mk_app `has_lift_t [β, α] >>= mk_instance',
    new_y ← to_expr ``(@coe %%α %%δ %%coe1 (@coe %%β %%α %%coe3 %%yy)),
    let new_e := app (app op x) new_y,
    eq_y ← aux_down y new_y,
    pr ← mk_congr_arg (app op x) eq_y,
    return ((), new_e, pr)
  )
) <|> ( do
  `(@coe %%α %%β %%coe1 %%xx) ← return x,
  `(@has_one.one %%β %%h1) ← return y,
  h2 ← to_expr ``(has_one %%α) >>= mk_instance',
  new_y ← to_expr ``( @coe %%α %%β %%coe1 (@has_one.one %%α %%h2) ),
  eq_y ← aux_down y new_y,
  let new_e := app (app op x) new_y,
  pr ← mk_congr_arg (app op x) eq_y,
  return ((), new_e, pr)
) <|> ( do
  `(@coe %%α %%β %%coe1 %%xx) ← return x,
  `(@has_zero.zero %%β %%h1) ← return y,
  h2 ← to_expr ``(has_zero %%α) >>= mk_instance',
  new_y ← to_expr ``( @coe %%α %%β %%coe1 (@has_zero.zero %%α %%h2) ),
  eq_y ← aux_down y new_y,
  let new_e := app (app op x) new_y,
  pr ← mk_congr_arg (app op x) eq_y,
  return ((), new_e, pr)
) <|> ( do
  `(@has_one.one %%β %%h1) ← return x,
  `(@coe %%α %%β %%coe1 %%xx) ← return y,
  h1 ← to_expr ``(has_one %%α) >>= mk_instance',
  new_x ← to_expr ``( @coe %%α %%β %%coe1 (@has_one.one %%α %%h1) ),
  eq_x ← aux_down x new_x,
  let new_e := app (app op new_x) y,
  pr ← mk_congr_arg (lam `x binder_info.default β (app (app op (var 0)) y)) eq_x,
  return ((), new_e, pr)
) <|> ( do
  `(@has_zero.zero %%β %%h1) ← return x,
  `(@coe %%α %%β %%coe1 %%xx) ← return y,
  h1 ← to_expr ``(has_zero %%α) >>= mk_instance',
  new_x ← to_expr ``( @coe %%α %%β %%coe1 (@has_zero.zero %%α %%h1) ),
  eq_x ← aux_down x new_x,
  let new_e := app (app op new_x) y,
  pr ← mk_congr_arg (lam `x binder_info.default β (app (app op (var 0)) y)) eq_x,
  return ((), new_e, pr)
)
| _ := failed

/--
assumption is used to discharge proofs in step 2
TODO: norm_cast takes a list of expressions to use as lemmas for the discharger
TODO: a tactic to print the results the discharger fails to proove
-/
private meta def prove : tactic unit := assumption

-- the `unit` argument is required by the `simplify` api.
/--
This is an auxiliary function used in step 2.
It tries to rewrite an expression using the elim_cast and move_cast lemmas.
On failure, it calls the heuristic.
-/
@[nolint]
meta def post (s : simp_lemmas) (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
( do
  r ← mcond (is_prop e) (return `iff) (return `eq),
  (new_e, pr) ← s.rewrite e prove r,
  pr ← match r with
  | `iff := mk_app `propext [pr]
  | _    := return pr
  end,
  return ((), new_e, pr)
) <|> heur () e

/-!
The following auxiliary functions are used to handle numerals.
-/

/-- prove ↑n = n where n is a numeral -/
meta def aux_num_prove_eq (a b : expr) : tactic expr :=
do
  h ← to_expr ``(%%a = %%b),
  s1 ← simp_lemmas.mk_default,
  cache ← norm_cast_attr.get_cache,
  let s := simp_lemmas.join s1 cache.down,
  (_, pr) ← simplify s [] h,
  some (_, tmp) ← expr.is_eq <$> infer_type pr,
  is_def_eq tmp `(true) reducible,
  to_expr ``(eq.mpr %%pr trivial)

-- the `unit` argument is required by the `simplify` api.
/-- if possible, rewrite (n : α) to ((n : ℕ) : α) where n is a numeral and α ≠ ℕ -/
@[nolint] meta def aux_num_1 (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
do
  α ← infer_type e,
  success_if_fail $ is_def_eq α `(ℕ),
  n ← e.to_num,
  h1 ← mk_app `has_lift_t [`(ℕ), α] >>= mk_instance',
  new_e ← expr.of_num `(ℕ) n,
  new_e ← to_expr ``(@coe ℕ %%α %%h1 %%new_e),
  pr ← aux_num_prove_eq e new_e,
  return ((), new_e, pr)

-- the `unit` argument is required by the `simplify` api.
/-- if possible, rewrite (↑n : α) to (n : α) where n is a numeral -/
@[nolint] meta def aux_num_2 (_ : unit) (e : expr) : tactic (unit × expr × expr) :=
do
do
  `(@coe ℕ %%α %%h1 %%e') ← return e,
  n ← e'.to_num,
  new_e ← expr.of_num α n,
  h ← to_expr ``(%%e = %%new_e),
  pr ← aux_num_prove_eq e new_e,
  return ((), new_e, pr)

/-- A local variant on `simplify_top_down`. -/
private meta def simplify_top_down' {α} (a : α) (pre : α → expr → tactic (α × expr × expr)) (e : expr) (cfg : simp_config := {}) : tactic (α × expr × expr) :=
ext_simplify_core a cfg simp_lemmas.mk (λ _, failed)
  (λ a _ _ _ e, do (new_a, new_e, pr) ← pre a e, guard (¬ new_e =ₐ e), return (new_a, new_e, some pr, ff))
  (λ _ _ _ _ _, failed)
  `eq e

/--
The core simplification routine of `norm_cast`.
-/
meta def derive (e : expr) : tactic (expr × expr) :=
do
  cache ← norm_cast_attr.get_cache,
  e ← instantiate_mvars e,
  let cfg : simp_config := {
    zeta := ff,
    beta := ff,
    eta  := ff,
    proj := ff,
    iota := ff,
    iota_eqn := ff,
    fail_if_unchanged := ff },
  let e0 := e,

  -- step 1: pre-processing of numerals
  ((), e1, pr1) ← simplify_top_down' () aux_num_1 e0 cfg,

  -- step 2: casts are moved upwards and eliminated
  let s2 := cache.up,
  ((), e2, pr2) ← simplify_bottom_up () (post s2) e1 cfg,

  -- step 3: casts are squashed
  let s3 := cache.squash,
  (e3, pr3) ← simplify s3 [] e2 cfg,

  --step 4: post-processing of numerals
  ((), e4, pr4) ← simplify_top_down' () aux_num_2 e3 cfg,

  let new_e := e4,
  guard (¬ new_e =ₐ e),
  pr ← mk_eq_trans pr1 pr2,
  pr ← mk_eq_trans pr pr3,
  pr ← mk_eq_trans pr pr4,
  return (new_e, pr)

end norm_cast_bis

namespace tactic.interactive
open tactic interactive tactic.interactive interactive.types expr lean.parser
open norm_cast_bis

local postfix `?`:9001 := optional

/--
Normalize casts at the given locations by moving them "upwards".
As opposed to simp, norm_cast can be used without necessarily closing the goal.
-/
meta def norm_cast_bis (loc : parse location) : tactic unit :=
do
  ns ← loc.get_locals,
  tt ← replace_at derive ns loc.include_goal | fail "norm_cast failed to simplify",
  when loc.include_goal $ try tactic.reflexivity,
  when loc.include_goal $ try tactic.triv,
  when (¬ ns.empty) $ try tactic.contradiction

end tactic.interactive
