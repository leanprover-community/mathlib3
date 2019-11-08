import tactic.core

universes u v

meta def list.extract_least {α : Type v} [has_lt α] [decidable_rel ((<) : α → α → Prop)]
  : list α → (option α × list α)
| [] := (none, [])
| (a₁ :: t₁) := match t₁.extract_least with
              | (none, _) := (a₁, [])
              | (some a₂, t₂) :=
                let (b, o) := if a₁ < a₂ then (a₁, a₂)else (a₂, a₁) in
                (some b, o :: t₂)
              end

namespace tactic

meta def try_tactic_in_context (t : tactic unit) (ts : tactic_state) (g : expr)
  : tactic (option tactic_state) :=
under_state ts $ try_core $
do set_goals [g],
   t,
   get_state

meta def try_apply_in_context (e : expr) : tactic_state → expr → tactic (option tactic_state) :=
try_tactic_in_context (apply e >> skip)

end tactic
