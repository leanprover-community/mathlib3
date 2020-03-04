
import testing.slim_check.testable

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
      -- let specialize := (λ (sp : expr) (nm : string), do
      --     let t' := expr.instantiate_local n sp t,
      --     h ← to_expr ``(testable %%t') >>= tactic.assert `h,
      --     solve1 is_testable,
      --     let type := reflect nm,
      --     applye ``(slim_check.test_one _ _ %%sp (some (%%var,%%type)))
      --       ; apply_instance),
      -- apply ``(slim_check.combine_testable _ [_,_] _),
      -- specialize `(ℤ) "ℤ",
      -- specialize `(list ℤ) "list ℤ",
      -- apply ``(nat.zero_lt_succ)
    else do
       mk_testable_inst,
       (  (applye ``(slim_check.test_forall_in_list _ _ %%var)  ; apply_instance)
         <|>
          (applye ``(slim_check.var_testable _ _ (some %%var)) ; apply_instance))
 | _ := trace_error "is_testable" $ tactic.applyc ``slim_check.de_testable
end)
<|> trace_error "is_testable" (tactic.applyc ``slim_check.de_testable)

open slim_check.test_result nat

namespace interactive

/-- in a goal of the shape `⊢ p` where `p` is testable, try to find
counter-examples to falsify `p`. If one is found, an assignment to the
local variables is printed. Otherwise, the goal is `admit`-ed.  -/
meta def slim_check (bound : ℕ := 100) : tactic unit :=
do unfreeze_local_instances,
   n ← revert_all,
   t ← target,
   p ← is_prop t,
   when (¬ p) (fail "expecting a proposition"),
   cl ←  to_expr ``(testable %%t),
   hinst ← prod.snd <$> tactic.solve_aux cl is_testable,
   e ← to_expr ``(psigma.mk %%t %%hinst : Σ' t', testable t'),
   ⟨t',hinst⟩ ← eval_expr (psigma testable) e,
   r ← unsafe_run_io (@testable.check t' hinst bound),
   match r with
    | (success (psum.inl ())) := admit
    | (success (psum.inr p)) := do `[apply @of_as_true %%t, exact trivial]
                                -- if some testable instances are not based on decidable
                                -- the above might fail. The best would be to run
                                -- the gen
    | (failure _ xs) := do
      intron n,
      fail $ string.intercalate "\n" $
        [ "\n==================="
        , "Found problems!"
        , "" ] ++
        xs ++
        [ "-------------------" ]
    | (gave_up n) :=
      if n ≥ bound
      then fail ("Gave up " ++ repr n ++ " time(s)")
      else trace ("Gave up " ++ repr n ++ " time(s)") >> admit
   end

end interactive
end tactic
