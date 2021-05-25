import tactic.lift
import data.set.basic

instance can_lift_subtype (R : Type*) (P : R → Prop) : can_lift R {x // P x} :=
{ coe := coe,
  cond := λ x, P x,
  prf := λ x hx, ⟨⟨x, hx⟩, rfl⟩ }

instance can_lift_set (R : Type*) (s : set R) : can_lift R s :=
{ coe := coe,
  cond := λ x, x ∈ s,
  prf := λ x hx, ⟨⟨x, hx⟩, rfl⟩ }

example {R : Type*} {P : R → Prop} (x : R) (hx : P x) : true :=
by { lift x to {x // P x} using hx with y, trivial }

/-! Test that `lift` elaborates `s` as a type, not as a set. -/
example {R : Type*} {s : set R} (x : R) (hx : x ∈ s) : true :=
by { lift x to s using hx with y, trivial }
