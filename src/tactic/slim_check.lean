/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Simon Hudon
-/
import testing.slim_check.testable

/-!
# `slim_check` tactics

Automation to check testable propositions

## Main definition
  * `slim_check` - tactic to find a counter example to the current goal

## Tags

random testing

## References

  * https://hackage.haskell.org/package/QuickCheck

-/

namespace tactic
open slim_check

private meta def applye (e : pexpr) : tactic unit := do
() <$ (to_expr e >>= tactic.apply)

/-- build an instance of testable for the given proposition
  -/
meta def is_testable : tactic unit := do
(do
tactic.target >>= instantiate_mvars >>= tactic.change,
`(testable %%e) ← target,
match e with
 | (expr.pi n bi d t) :=
   if bi = binder_info.inst_implicit then do
      h ← tactic.assert `h d,
      solve1 apply_instance,
      applye ``(@slim_check.test_one _ _ %%h _),
      is_testable
   else do
    p ← is_prop d,
    let var := reflect $ to_string n,
    let mk_testable_inst := (do
          h ← to_expr ``(testable %%t) >>= λ e, tactic.assert `h (expr.pi n bi d e),
          solve1 (tactic.intro1 >> is_testable)),
    if p then do
       mk_testable_inst,
       tactic.applyc `slim_check.imp_dec_testable
    else if d = `(Type) then do
      let t' := expr.instantiate_local n `(ℤ) t,
      h ← to_expr ``(testable %%t') >>= tactic.assert `h,
      solve1 is_testable,
      applye ``(slim_check.test_one _ _ ℤ (some (%%var,"ℤ"))) ; apply_instance
    else do
       mk_testable_inst,
       (  (applye ``(slim_check.test_forall_in_list _ _ %%var)  ; apply_instance)
         <|>
          (applye ``(slim_check.subtype_var_testable _ _ (some %%var)) ; apply_instance)
         <|>
          (applye ``(slim_check.unused_var_testable) ; apply_instance)
         <|>
          (applye ``(slim_check.var_testable _ _ (some %%var)) ; apply_instance))
 | _ := trace_error "is_testable" $ tactic.applyc ``slim_check.de_testable
end)
<|> trace_error "is_testable" (tactic.applyc ``slim_check.de_testable)

open slim_check.test_result nat

namespace interactive

def io.slim_check (t : Prop) [testable t] (cfg : slim_check_cfg := {}) : io (option $ bool × string) :=
do -- unfreeze_local_instances,
   -- n ← revert_all,
   -- t ← target,
   -- p ← is_prop t,
   -- when (¬ p) (fail "expecting a proposition"),
   -- cl ←  to_expr ``(testable %%t),
   -- hinst ← prod.snd <$> tactic.solve_aux cl is_testable,
   -- e ← to_expr ``(psigma.mk %%t %%hinst : Σ' t', testable t'),
   -- ⟨t',hinst⟩ ← eval_expr (psigma testable) e,
   r ← testable.check t cfg,
   match r with
    -- | (success (psum.inl ())) := admit
    | (success _) := pure none
    | (failure _ xs) := do
      -- intron n,
      let err := string.intercalate "\n" $
        [ "\n==================="
        , "Found problems!"
        , "" ] ++
        xs ++
        [ "-------------------" ],
      pure $ some (tt,err)
    | (gave_up n) :=
      let err := "Gave up " ++ repr n ++ " time(s)" in
      if n ≥ cfg.num_inst
      then pure $ some (tt,err)
      else pure $ some (ff,err)
   end

meta def mk_named_binder (s : string) (e : expr) : expr :=
@expr.const tt ``named_binder []
      ((`(@some string) : expr) (reflect s)) e

meta def add_existential_name : expr → expr
  | (expr.app (expr.app (@expr.const tt `Exists ls) α) (expr.lam n' bi' d' b')) :=
    mk_named_binder (to_string n') $
      (expr.app (expr.app (@expr.const tt `Exists ls) α)
        (expr.lam n' bi' d' b'))
  | e := e

meta def annotate_binders : expr → expr
| e :=
expr.replace e $ λ e i,
  match e with
  | expr.pi n bi d b :=
    mk_named_binder (to_string n)
      (expr.pi n bi (add_existential_name d) (annotate_binders b))
  | _ := none
  end

meta def slim_check_prop (t : expr) (cfg : slim_check_cfg := {}) : tactic unit :=
do p ← is_prop t,
   when (¬ p) (fail "expecting a proposition"),
   t ← instantiate_mvars t,
   let t' := annotate_binders t,
   cl ←  to_expr ``(testable %%t'),
   hinst ← mk_instance cl,
   e ← mk_mapp ``io.slim_check [t,hinst,some (reflect cfg)],
   run_slim_check ← eval_expr (io (option (bool × string))) e,
   r ← unsafe_run_io $ run_slim_check,
   match r with
    | none := admit
    | some (b,err) :=
      if b then fail err
           else trace err >> admit
   end


/-- in a goal of the shape `⊢ p` where `p` is testable, try to find
counter-examples to falsify `p`. If one is found, an assignment to the
local variables is printed and the tactic fails. Otherwise, the goal
is `admit`-ed.

```lean
example (i j) : i < j → i < 10 := by slim_check
  -- ./src/tactic/slim_check.lean:172:37: error:
  -- ===================
  -- Found problems!

  -- i := 15
  -- j := 23
  -- -------------------
  -- state:
  -- i j : ℕ
  -- ⊢ i < j → i < 10

example (i j) : i < j → i < 10 ∧ ∀ j, j < i := by slim_check
  -- ./src/tactic/slim_check.lean:176:42: error:
  -- ===================
  -- Found problems!

  -- i := 17
  -- j := 21
  -- -------------------
  -- state:
  -- i : ℕ
  -- ⊢ (∃ (j : ℕ), i < j) → i < 10

example (i) : (∃ j, i < j) → i < 10 := by slim_check
  -- ./src/tactic/slim_check.lean:174:50: error:
  -- ===================
  -- Found problems!

  -- i := 0
  -- j := 1
  -- j := 1
  -- -------------------
  -- state:
  -- i j : ℕ
  -- ⊢ i < j → (i < 10 ∧ ∀ (j : ℕ), j < i)

example (i) : (∃ j, i < j) → ∀ k, k > i → i < 10 := by slim_check
  -- ./src/tactic/slim_check.lean:177:55: error:
  -- ===================
  -- Found problems!

  -- i := 292
  -- j := 1338
  -- k := 1431
  -- -------------------
  -- state:
  -- i : ℕ
  -- ⊢ (∃ (j : ℕ), i < j) → ∀ (k : ℕ), k > i → i < 10
```
  -/
meta def slim_check (cfg : slim_check_cfg := {}) : tactic unit :=
do n ← revert_all,
   t ← target,
   intron n,
   slim_check_prop t cfg

setup_tactic_parser

-- #exit
/--
This command use randomized examples to test a proposition and report
any counterexample

```lean
conjecture : ∀ i, i < 10
-- ./src/tactic/slim_check.lean:168:0: error:
-- ===================
-- Found problems!
--
-- i := 16
-- -------------------

conjecture : ∀ i j, i < j → i < 10
-- ./src/tactic/slim_check.lean:170:0: error:
-- ===================
-- Found problems!

-- i := 13
-- j := 20
-- -------------------
```
-/
@[user_command]
meta def conjecture_cmd (_ : parse $ tk "conjecture") : lean.parser unit :=
do tk ":",
   p ← texpr,
   of_tactic $ do
     p ← i_to_expr p,
     slim_check_prop p

end interactive
end tactic
