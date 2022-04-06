import algebra.group.defs
import data.subtype
import tactic.congr

section congr
open tactic.interactive

example (c : Prop → Prop → Prop → Prop) (x x' y z z' : Prop)
  (h₀ : x ↔ x')
  (h₁ : z ↔ z') :
  c x y z ↔ c x' y z' :=
begin
  congr',
  { guard_target x = x', ext, assumption },
  { guard_target z = z', ext, assumption },
end

example {α β γ δ} {F : ∀{α β}, (α → β) → γ → δ} {f g : α → β} {s : γ} (h : ∀ (x : α), f x = g x) :
  F f s = F g s :=
by { congr' with x, apply_assumption }

example {α β} {f : _ → β} {x y : {x : {x : α // x = x} // x = x} } (h : x.1 = y.1) :
  f x = f y :=
by { congr' with x : 1, exact h }

example {α β} {F : _ → β} {f g : {f : α → β // f = f} }
  (h : ∀ x : α, (f : α → β) x = (g : α → β) x) :
  F f = F g :=
begin
  rcongr x,
  revert x,
  do { t ← tactic.target, s ← tactic.get_local_type `h, guard (t =ₐ s) },
  exact h
end

example {ls : list ℕ} :
  ls.map (λ x, (ls.map (λ y, 1 + y)).sum + 1) = ls.map (λ x, (ls.map (λ y, nat.succ y)).sum + 1) :=
begin
  rcongr x y, guard_target (1 + y = y.succ), rw [nat.add_comm],
end

example {ls : list ℕ} {f g : ℕ → ℕ} {h : ∀ x, f x = g x} :
  ls.map (λ x, f x + 3) = ls.map (λ x, g x + 3)  :=
begin
  rcongr x, exact h x
end

-- succeed when either `ext` or `congr` can close the goal
example : () = () := by rcongr
example : 0 = 0 := by rcongr

example {α} (a : α) : a = a := by congr'

example {α} (a b : α) (h : false) : a = b :=
by { fail_if_success {congr'}, cases h }

end congr

section convert_to
example {α} [add_comm_monoid α] {a b c d : α} (H : a = c) (H' : b = d) : a + b = d + c :=
by {convert_to c + d = _ using 2, rw[add_comm]}

example {α} [add_comm_monoid α] {a b c d : α} (H : a = c) (H' : b = d) : a + b = d + c :=
by {convert_to c + d = _ using 0, congr' 2, rw[add_comm]}

example {α} [add_comm_monoid α] [partial_order α] {a b c d e f g : α} :
  (a + b) + (c + d) + (e + f) + g ≤ a + d + e + f + c + g + b :=
by {ac_change a + d + e + f + c + g + b ≤ _, refl}

end convert_to
