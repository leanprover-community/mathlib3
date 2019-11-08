import .ideas .brains
import tactic.basic

variables {γ : Type}

namespace back

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
          ppg ← tactic.pp g,
          ppgs ← tactic.pp gs,
          tactic.trace format!"explore_node {ppg}:\n  others={ppgs}"
        },

        ulift.up (ls, lg) ← uraise $ g.step n.ts,
        ls ← match ls with
                  | [] := option.to_list <$> option.map (n.with_goals gs) <$> i.rethink g
                  | ls := return $ ls.map $ n.with_idea_state gs g
                  end,
        lg ← lg.mmap $ n.with_tactic_state i gs,

        when_btrace $ do {
          ppls ← tactic.pp ls,
          pplg ← tactic.pp lg,
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
   ulift.up state ← uraise tactic.get_state,
   return ⟨gs, state, 0⟩

meta def idea_list : list idea := [
   ideas.local_hypotheses,
   ideas.helper_tactics,
   ideas.passed_lemmas,
   ideas.tagged_lemmas
]

meta def search (cfg : config) : tactic unit :=
udescend.{2} $
do ulift.up i ← uraise.{1} $ inst.of_brain (brains.queue idea_list) cfg,
   ulift.up n ← uraise.{2} $ initial_node i,
   uraise $ loop i [n] >>= tactic.set_state

end back
