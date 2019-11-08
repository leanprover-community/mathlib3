import .lib

universes u v

namespace back

open tactic

declare_trace back

meta def btrace (fmt : format) : tactic (ulift unit) :=
uraise $ tactic.when_tracing `back (tactic.trace fmt)

meta def when_btrace (t : tactic unit) : tactic (ulift.{u} unit) :=
if tactic.is_trace_enabled_for `back then uraise t >> uskip
else uskip

meta def debug_msg := option (unit → tactic format)

meta def maybe_debug (t : tactic format) : debug_msg :=
if tactic.is_trace_enabled_for `back then some $ λ _, t
else none

meta structure config :=
(passed_lemmas : list expr)

meta inductive idea
| mk
  {α : Type}
  {ρ : Type}
  (name : string)
  (startup : config → tactic ρ)
  (init : ρ → expr → α × ℕ × debug_msg)
  (step : ρ → tactic_state → expr → α → tactic (list (α × ℕ × debug_msg) × list tactic_state))

namespace idea

meta def α : idea → Type
| (@idea.mk vα _ _ _ _ _) := vα

meta def ρ : idea → Type
| (@idea.mk _ vρ _ _ _ _) := vρ

meta def startup : Π (t : idea), config → tactic t.ρ
| (@idea.mk _ _ _ vstartup _ _) := vstartup

end idea

meta structure thought :=
(id : idea)
(data : id.ρ)

meta structure goal (γ : Type) :=
(mvar : expr)
(penalty : ℕ)
(t : thought)
(state : t.id.α)
(mem : γ)
(debug : debug_msg)

variables {γ : Type}

namespace thought

meta def init : Π (t : thought), γ → expr → goal γ
| t@⟨(@idea.mk _ _ _ _ vinit _), data⟩ mem :=
λ e, let (state, penalty, debug) := vinit data e in ⟨e, penalty, t, state, mem, debug⟩

meta def step : Π (t : thought),
  tactic_state → expr → t.id.α → tactic (list (t.id.α × ℕ × debug_msg) × list tactic_state)
| ⟨@idea.mk _ _ _ _ _ vstep, data⟩ := vstep data

meta def of_idea (cfg : config) (i : idea) : tactic thought :=
do ulift.up data ← uraise $ i.startup cfg,
   return ⟨i, data⟩

end thought

namespace goal

meta instance : has_lt (goal γ) := ⟨λ g₁ g₂, g₁.penalty < g₂.penalty⟩

end goal

meta structure node (γ : Type) :=
(goals : list (goal γ))
(ts : tactic_state)
(penalty : ℕ)

namespace node

meta def prune_solved (n : node γ) : tactic (node γ) :=
do gs ← n.goals.mfilter' $
     λ g, interaction_monad.under_state n.ts (bnot <$> tactic.is_assigned g.mvar),
   return {n with goals := gs}

meta def most_promising (n : node γ) : (option (goal γ)) × list (goal γ) := n.goals.extract_least

end node

meta structure brain :=
{γ : Type}
{ρ : Type u}
(startup : config → tactic ρ)
(init : ρ → expr → tactic (thought × γ))
(rethink : ρ → goal γ → tactic (option (goal γ)))

meta structure inst :=
(b : brain)
(data : b.ρ)

namespace inst

meta def of_brain (b : brain.{u}) (cfg : config) : tactic inst.{u} :=
udescend.{u} $
do ulift.up data ← uraise.{u+1} $ b.startup cfg,
   uraise $ return ⟨b, data⟩

meta def init : Π (i : inst), expr → tactic (goal i.b.γ)
| ⟨b, data⟩ e := do (t, r) ← b.init data e,
                    return $ t.init r e

meta def rethink : Π (i : inst), goal i.b.γ → tactic (option (goal i.b.γ))
| ⟨b, data⟩ e := b.rethink data e

end inst

namespace goal

meta def from_tactic_state (i : inst) (ts : tactic_state) : tactic (list (goal i.b.γ)) :=
do ulift.up gs ← uraise $ interaction_monad.under_state ts tactic.get_goals,
   gs.mmap i.init

meta def with_idea_state (g : goal γ) (d : g.t.id.α × ℕ × debug_msg) : goal γ :=
let (state, penalty, debug) := d in
{g with state := state, penalty := penalty, debug := debug}

meta def step (g : goal γ) (ts : tactic_state)
  : tactic (list (g.t.id.α × ℕ × debug_msg) × list tactic_state) :=
g.t.step ts g.mvar g.state

end goal

namespace node

meta def with_goals (n : node γ) (gs : list (goal γ)) (g : goal γ) : node γ :=
{n with goals := g :: gs}

meta def with_idea_state (n : node γ) (gs : list (goal γ)) (g : goal γ)
  (state : g.t.id.α × ℕ × debug_msg) : node γ :=
n.with_goals gs (g.with_idea_state state)

meta def with_tactic_state (i : inst) (n : node i.b.γ) (gs : list (goal i.b.γ)) (ts : tactic_state)
  : tactic (node i.b.γ) :=
do ngs ← goal.from_tactic_state i ts,
   {n with ts := ts, goals := gs ++ ngs}.prune_solved

end node

section debug

meta instance goal.has_to_tactic_format : has_to_tactic_format (goal γ) := ⟨λ g,
  do mvar ← tactic.infer_type g.mvar >>= tactic.pp,
     match g.debug with
     | none := return format!"{{`{mvar}`@({g.penalty})}"
     | some t := do msg ← t (), return format!"{{`{mvar}`@({g.penalty})#{msg}}"
     end
⟩

meta instance node.has_to_tactic_format : has_to_tactic_format (node γ) := ⟨λ n,
  do gs ← tactic.pp n.goals,
     return format!"{gs}@({n.penalty})"
⟩

end debug

end back
