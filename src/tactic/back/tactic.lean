import .ideas .brains
import tactic.basic

variables {γ : Type}

namespace back

open tactic

meta def find_any_solved_node : list (node γ) → option (node γ)
| [] := none
| (n :: rest) := if n.goals.length = 0 then some n else find_any_solved_node rest

meta inductive explore_result (γ : Type)
| nodes (nodes : list (node γ)) : explore_result
| no_goals (ts : tactic_state) : explore_result

meta def explore_node (i : inst) (n : node i.b.γ) : tactic (explore_result i.b.γ) :=
do let (g, gs) := n.most_promising,
   match g with
   | none := tactic.fail "node has no goals"
   | some g :=
     do when_btrace $ do {
          ppg ← g.to_format n.ts,
          ppgs ← gs.mmap $ λ g, g.to_format n.ts,
          tactic.trace format!"explore_node {ppg}:\n  others={ppgs}"
        },

        ulift.up (ls, lg) ← uraise $ g.step n.ts,
        ls ← match ls with
                  | [] := option.to_list <$> option.map (n.with_goals gs) <$> i.rethink g
                  | ls := return $ ls.map $ n.with_idea_state gs g
                  end,
        lg ← lg.mmap $ n.with_tactic_state i gs,

        when_btrace $ do {
          ppls ← string.intercalate "\n      " <$> (ls.mmap $ λ s, to_string <$> tactic.pp s),
          pplg ← string.intercalate "\n      " <$> (lg.mmap $ λ s, to_string <$> tactic.pp s),
          tactic.trace format!"end explore:\n  ls={ppls},\n  lg={pplg}\n"
        },

        return $ match find_any_solved_node lg with
                 | some n := explore_result.no_goals _ n.ts
                 | none   := explore_result.nodes (lg ++ ls)
                 end
   end

meta def loop (i : inst) : list (node i.b.γ) → tactic tactic_state
| [] := tactic.fail "nodes exhausted"
| (n :: rest) := udescend $
  do ns ← explore_node i n,
     uraise $ match ns with
       | explore_result.nodes ns := loop (rest ++ ns)
       | explore_result.no_goals _ ts := return ts
     end

meta def initial_node (i : inst) : tactic (node i.b.γ) :=
do ulift.up gs ← uraise tactic.get_goals,
   gs ← list.mmap i.init gs,
   ulift.up state ← uraise interaction_monad.get_state,
   return ⟨gs, state, 0⟩

meta def idea_list : list idea := [
   ideas.local_hypotheses,
   ideas.helper_tactics,
   ideas.passed_lemmas,
   ideas.tagged_lemmas
]

meta def search (cfg : config) : tactic unit :=
udescend.{2} $
do ulift.up gs ← uraise get_goals,

   ulift.up i ← uraise.{1} $ inst.of_brain (brains.queue idea_list) cfg,
   ulift.up n ← uraise.{2} $ initial_node i,
   uraise $ loop i [n] >>= interaction_monad.set_state,

   uraise $ gs.mmap' $ λ e, instantiate_mvars e >>= pp >>= λ fmt, trace format!"exact {fmt}\n"

end back
