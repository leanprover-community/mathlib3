/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

These tactics do straightforward things: they call the simplifier, split conjunctive assumptions,
eliminate existential quantifiers on the left, and look for contradictions. They rely on ematching
and congruence closure to try to finish off a goal at the end.

The procedures *do* split on disjunctions and recreate the smt state for each terminal call, so
they are only meant to be used on small, straightforward problems.

We provide the following tactics:

  finish  -- solves the goal or fails
  clarify -- makes as much progress as possible while not leaving more than one goal
  safe    -- splits freely, finishes off whatever subgoals it can, and leaves the rest

All accept an optional list of simplifier rules, typically definitions that should be expanded.
(The equations and identities should not refer to the local context.)

The variants ifinish, iclarify, and isafe restrict to intuitionistic logic. They do not work
well with the current heuristic instantiation method used by ematch, so they should be revisited
when the API changes.
-/
import logic.basic

declare_trace auto.done
declare_trace auto.finish

-- TODO(Jeremy): move these


namespace tactic

/- call (assert n t) with a fresh name n. -/
meta def assert_fresh (t : expr) : tactic expr :=
do n ← get_unused_name `h none,
   assert n t

/- call (assertv n t v) with a fresh name n. -/
meta def assertv_fresh (t : expr) (v : expr) : tactic expr :=
do h ← get_unused_name `h none,
   assertv h t v

namespace interactive

meta def revert_all := tactic.revert_all

end interactive

end tactic

open tactic expr

namespace auto

/- Utilities -/

meta def whnf_reducible (e : expr) : tactic expr := whnf e reducible

-- stolen from interactive.lean
meta def add_simps : simp_lemmas → list name → tactic simp_lemmas
| s []      := return s
| s (n::ns) := do s' ← s.add_simp n, add_simps s' ns

/-
  Configuration information for the auto tactics.
-/

structure auto_config : Type :=
(use_simp := tt)           -- call the simplifier
(classical := tt)          -- use classical logic
(max_ematch_rounds := 20)  -- for the "done" tactic

/-
  Preprocess goal.

  We want to move everything to the left of the sequent arrow. For intuitionistic logic,
  we replace the goal p with ∀ f, (p → f) → f and introduce.
-/

theorem by_contradiction_trick (p : Prop) (h : ∀ f : Prop, (p → f) → f) : p :=
h p id

meta def preprocess_goal (cfg : auto_config) : tactic unit :=
do repeat (intro1 >> skip),
   tgt ← target >>= whnf_reducible,
   if (¬ (is_false tgt)) then
     if cfg.classical then
       (mk_mapp ``classical.by_contradiction [some tgt]) >>= apply >> intro1 >> skip
     else
       (mk_mapp ``decidable.by_contradiction [some tgt, none] >>= apply >> intro1 >> skip) <|>
       applyc ``by_contradiction_trick >> intro1 >> intro1 >> skip
   else
     skip

/-
  Normalize hypotheses. Bring conjunctions to the outside (for splitting),
  bring universal quantifiers to the outside (for ematching). The classical normalizer
  eliminates a → b in favor of ¬ a ∨ b.

  For efficiency, we push negations inwards from the top down. (For example, consider
  simplifying ¬ ¬ (p ∨ q).)
-/

section

universe u
variable  {α : Type u}
variables (p q : Prop)
variable  (s : α → Prop)

local attribute [instance] classical.prop_decidable
theorem not_not_eq : (¬ ¬ p) = p := propext not_not
theorem not_and_eq : (¬ (p ∧ q)) = (¬ p ∨ ¬ q) := propext not_and_distrib
theorem not_or_eq : (¬ (p ∨ q)) = (¬ p ∧ ¬ q) := propext not_or_distrib
theorem not_forall_eq : (¬ ∀ x, s x) = (∃ x, ¬ s x) := propext not_forall
theorem not_exists_eq : (¬ ∃ x, s x) = (∀ x, ¬ s x) := propext not_exists
theorem not_implies_eq : (¬ (p → q)) = (p ∧ ¬ q) := propext not_imp

theorem classical.implies_iff_not_or : (p → q) ↔ (¬ p ∨ q) := imp_iff_not_or

end

def common_normalize_lemma_names : list name :=
[``bex_def, ``forall_and_distrib, ``exists_imp_distrib, ``or.assoc, ``or.comm, ``or.left_comm,
  ``and.assoc, ``and.comm, ``and.left_comm]

def classical_normalize_lemma_names : list name :=
common_normalize_lemma_names ++ [``classical.implies_iff_not_or]

-- optionally returns an equivalent expression and proof of equivalence
private meta def transform_negation_step (cfg : auto_config) (e : expr) :
  tactic (option (expr × expr)) :=
do e ← whnf_reducible e,
   match e with
   | `(¬ %%ne) :=
      (do ne ← whnf_reducible ne,
      match ne with
      | `(¬ %%a)      := do pr ← mk_app ``not_not_eq [a],
                            return (some (a, pr))
      | `(%%a ∧ %%b)  := do pr ← mk_app ``not_and_eq [a, b],
                            return (some (`(¬ %%a ∨ ¬ %%b), pr))
      | `(%%a ∨ %%b)  := do pr ← mk_app ``not_or_eq [a, b],
                            return (some (`(¬ %%a ∧ ¬ %%b), pr))
      | `(Exists %%p) := do pr ← mk_app ``not_exists_eq [p],
                            `(%%_ = %%e') ← infer_type pr,
                            return (some (e', pr))
      | (pi n bi d p) := if ¬ cfg.classical then return none
                         else if p.has_var then do
                            pr ← mk_app ``not_forall_eq [lam n bi d (expr.abstract_local p n)],
                            `(%%_ = %%e') ← infer_type pr,
                            return (some (e', pr))
                         else do
                            pr ← mk_app ``not_implies_eq [d, p],
                            `(%%_ = %%e') ← infer_type pr,
                            return (some (e', pr))
      | _             := return none
      end)
    | _        := return none
  end

-- given an expr 'e', returns a new expression and a proof of equality
private meta def transform_negation (cfg : auto_config) : expr → tactic (option (expr × expr)) :=
λ e, do
  opr ← transform_negation_step cfg e,
  match opr with
  | (some (e', pr)) := do
    opr' ← transform_negation e',
    match opr' with
    | none              := return (some (e', pr))
    | (some (e'', pr')) := do pr'' ← mk_eq_trans pr pr',
                              return (some (e'', pr''))
    end
  | none            := return none
  end

meta def normalize_negations (cfg : auto_config) (h : expr) : tactic unit :=
do t ← infer_type h,
   (_, e, pr) ← simplify_top_down ()
                   (λ _, λ e, do
                       oepr ← transform_negation cfg e,
                       match oepr with
                       | (some (e', pr)) := return ((), e', pr)
                       | none            := do pr ← mk_eq_refl e, return ((), e, pr)
                       end)
                   t,
   replace_hyp h e pr,
   skip

meta def normalize_hyp (cfg : auto_config) (simps : simp_lemmas) (h : expr) : tactic unit :=
(do h ← simp_hyp simps [] h, try (normalize_negations cfg h)) <|>
try (normalize_negations cfg h)

meta def normalize_hyps (cfg : auto_config) : tactic unit :=
do simps ← if cfg.classical then
             add_simps simp_lemmas.mk classical_normalize_lemma_names
           else
             add_simps simp_lemmas.mk common_normalize_lemma_names,
   local_context >>= monad.mapm' (normalize_hyp cfg simps)

/-
  Eliminate existential quantifiers.
-/

-- eliminate an existential quantifier if there is one
meta def eelim : tactic unit :=
do ctx ← local_context,
   first $ ctx.map $ λ h,
     do t ← infer_type h >>= whnf_reducible,
        guard (is_app_of t ``Exists),
        tgt ← target,
        to_expr ``(@exists.elim _ _ %%tgt %%h) >>= apply,
        intros,
        clear h

-- eliminate all existential quantifiers, fails if there aren't any
meta def eelims : tactic unit := eelim >> repeat eelim

/-
  Substitute if there is a hypothesis x = t or t = x.
-/

-- carries out a subst if there is one, fails otherwise
meta def do_subst : tactic unit :=
do ctx ← local_context,
   first $ ctx.map $ λ h,
     do t ← infer_type h >>= whnf_reducible,
        match t with
        | `(%%a = %%b) := subst h
        | _            := failed
        end

meta def do_substs : tactic unit := do_subst >> repeat do_subst

/-
  Split all conjunctions.
-/

-- Assumes pr is a proof of t. Adds the consequences of t to the context
-- and returns tt if anything nontrivial has been added.
meta def add_conjuncts : expr → expr → tactic bool :=
λ pr t,
let assert_consequences := λ e t, mcond (add_conjuncts e t) skip (assertv_fresh t e >> skip) in
do t' ← whnf_reducible t,
   match t' with
   | `(%%a ∧ %%b) :=
     do e₁ ← mk_app ``and.left [pr],
        assert_consequences e₁ a,
        e₂ ← mk_app ``and.right [pr],
        assert_consequences e₂ b,
        return tt
  | `(true) :=
     do return tt
  | _ := return ff
end

-- return tt if any progress is made
meta def split_hyp (h : expr) : tactic bool :=
do t ← infer_type h,
   mcond (add_conjuncts h t) (clear h >> return tt) (return ff)

-- return tt if any progress is made
meta def split_hyps_aux : list expr → tactic bool
| []        := return ff
| (h :: hs) := do b₁ ← split_hyp h,
                  b₂ ← split_hyps_aux hs,
                  return (b₁ || b₂)

-- fail if no progress is made
meta def split_hyps : tactic unit := local_context >>= split_hyps_aux >>= guardb

/-
  Eagerly apply all the preprocessing rules.
-/

meta def preprocess_hyps (cfg : auto_config) : tactic unit :=
do repeat (intro1 >> skip),
   preprocess_goal cfg,
   normalize_hyps cfg,
   repeat (do_substs <|> split_hyps <|> eelim /-<|> self_simplify_hyps-/)

/-
  The terminal tactic, used to try to finish off goals:
  - Call the contradiction tactic.
  - Open an SMT state, and use ematching and congruence closure, with all the universal
    statements in the context.

  TODO(Jeremy): allow users to specify attribute for ematching lemmas?
-/

meta def mk_hinst_lemmas : list expr → smt_tactic hinst_lemmas
| []        := -- return hinst_lemmas.mk
               do get_hinst_lemmas_for_attr `ematch
| (h :: hs) := do his ← mk_hinst_lemmas hs,
                  t ← infer_type h,
                  match t with
                  | (pi _ _ _ _) :=
                    do t' ← infer_type t,
                       if t' = `(Prop) then
                          (do new_lemma ← hinst_lemma.mk h,
                             return (hinst_lemmas.add his new_lemma)) <|> return his
                       else return his
                  | _ := return his
                  end

meta def done (cfg : auto_config := {}) : tactic unit :=
do when_tracing `auto.done (trace "entering done" >> trace_state),
   contradiction <|>
   (solve1 $
     (do revert_all,
         using_smt
         (do smt_tactic.intros,
             ctx ← local_context,
             hs ← mk_hinst_lemmas ctx,
             smt_tactic.iterate_at_most cfg.max_ematch_rounds
               (smt_tactic.ematch_using hs >> smt_tactic.try smt_tactic.close))))

/-
  Tactics that perform case splits.
-/

inductive case_option
| force        -- fail unless all goals are solved
| at_most_one  -- leave at most one goal
| accept       -- leave as many goals as necessary

private meta def case_cont (s : case_option) (cont : case_option → tactic unit) : tactic unit :=
do match s with
   | case_option.force := cont case_option.force >> cont case_option.force
   | case_option.at_most_one :=
       -- if the first one succeeds, commit to it, and try the second
       (mcond (cont case_option.force >> return tt) (cont case_option.at_most_one) skip) <|>
       -- otherwise, try the second
       (swap >> cont case_option.force >> cont case_option.at_most_one)
   | case_option.accept := focus [cont case_option.accept, cont case_option.accept]
   end

-- three possible outcomes:
--   finds something to case, the continuations succeed ==> returns tt
--   finds something to case, the continutations fail ==> fails
--   doesn't find anything to case ==> returns ff
meta def case_hyp (h : expr) (s : case_option) (cont : case_option → tactic unit) : tactic bool :=
do t ← infer_type h,
   match t with
   | `(%%a ∨ %%b) := cases h >> case_cont s cont >> return tt
   | _            := return ff
   end

meta def case_some_hyp_aux (s : case_option) (cont : case_option → tactic unit) :
  list expr → tactic bool
| []      := return ff
| (h::hs) := mcond (case_hyp h s cont) (return tt) (case_some_hyp_aux hs)

meta def case_some_hyp (s : case_option) (cont : case_option → tactic unit) : tactic bool :=
local_context >>= case_some_hyp_aux s cont

/-
  The main tactics.
-/

meta def safe_core (s : simp_lemmas × list name) (cfg : auto_config) : case_option → tactic unit :=
λ co, focus1 $
do when_tracing `auto.finish (trace "entering safe_core" >> trace_state),
   if cfg.use_simp then do
     when_tracing `auto.finish (trace "simplifying hypotheses"),
     simp_all s.1 s.2 { fail_if_unchanged := ff },
     when_tracing `auto.finish (trace "result:" >> trace_state)
   else skip,
   tactic.done <|>
   do when_tracing `auto.finish (trace "preprocessing hypotheses"),
      preprocess_hyps cfg,
      when_tracing `auto.finish (trace "result:" >> trace_state),
      done cfg <|>
        (mcond (case_some_hyp co safe_core)
          skip
          (match co with
            | case_option.force       := done cfg
            | case_option.at_most_one := try (done cfg)
            | case_option.accept      := try (done cfg)
            end))

meta def clarify (s : simp_lemmas × list name) (cfg : auto_config := {}) : tactic unit :=
  safe_core s cfg case_option.at_most_one
meta def safe (s : simp_lemmas × list name) (cfg : auto_config := {}) : tactic unit :=
  safe_core s cfg case_option.accept
meta def finish (s : simp_lemmas × list name) (cfg : auto_config := {}) : tactic unit :=
  safe_core s cfg case_option.force

meta def iclarify (s : simp_lemmas × list name) (cfg : auto_config := {}) : tactic unit :=
  clarify s {classical := ff, ..cfg}
meta def isafe (s : simp_lemmas × list name) (cfg : auto_config := {}) : tactic unit :=
  safe s {classical := ff, ..cfg}
meta def ifinish (s : simp_lemmas × list name) (cfg : auto_config := {}) : tactic unit :=
  finish s {classical := ff, ..cfg}

end auto

/- interactive versions -/

open auto

namespace tactic
namespace interactive

open lean lean.parser interactive interactive.types

local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def clarify (hs : parse simp_arg_list) (cfg : auto_config := {}) : tactic unit :=
do s ← mk_simp_set ff [] hs,
   auto.clarify s cfg

meta def safe (hs : parse simp_arg_list) (cfg : auto_config := {}) : tactic unit :=
do s ← mk_simp_set ff [] hs,
   auto.safe s cfg

meta def finish (hs : parse simp_arg_list) (cfg : auto_config := {}) : tactic unit :=
do s ← mk_simp_set ff [] hs,
   auto.finish s cfg

meta def iclarify (hs : parse simp_arg_list) (cfg : auto_config := {}) : tactic unit :=
do s ← mk_simp_set ff [] hs,
   auto.iclarify s cfg

meta def isafe (hs : parse simp_arg_list) (cfg : auto_config := {}) : tactic unit :=
do s ← mk_simp_set ff [] hs,
   auto.isafe s cfg

meta def ifinish (hs : parse simp_arg_list) (cfg : auto_config := {}) : tactic unit :=
do s ← mk_simp_set ff [] hs,
   auto.ifinish s cfg

end interactive
end tactic
