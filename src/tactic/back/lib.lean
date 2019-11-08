import tactic.core

universes u v

meta def uraise {α : Type v} (t : tactic α) : tactic (ulift.{u} α) := λ s₁,
match t s₁ with
| interaction_monad.result.exception fn pos ts := interaction_monad.result.exception fn pos ts
| interaction_monad.result.success val s₂ := interaction_monad.result.success (ulift.up val) s₂
end

meta def udescend {α : Type v} (t : tactic (ulift.{u} α)) : tactic α :=
λ ts, match t ts with
| interaction_monad.result.success val state := interaction_monad.result.success val.down state
| interaction_monad.result.exception fn pos state := interaction_monad.result.exception fn pos state
end

meta def uskip : tactic (ulift.{u} unit) := return $ ulift.up ()

namespace list

meta def extract_least {α : Type v} [has_lt α] [decidable_rel ((<) : α → α → Prop)]
  : list α → (option α × list α)
| [] := (none, [])
| (a₁ :: t₁) := match t₁.extract_least with
              | (none, _) := (a₁, [])
              | (some a₂, t₂) :=
                let (b, o) := if a₁ < a₂ then (a₁, a₂)else (a₂, a₁) in
                (some b, o :: t₂)
              end

meta def mfilter' {α : Type v} (f : α → tactic bool) : list α → tactic (list α)
| []       := return []
| (h :: t) := do ulift.up v ← uraise $ f h,
                 rest ← mfilter' t,
                 return $ if v then h :: rest else rest

end list

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
