import algebra.group.defs

def bar (a b : nat) : nat := a * b

@[simp]
lemma foo (a b : nat) : bar a b = a * b := rfl

instance : add_semigroup nat :=
{ add := bar,
  add_assoc := λ f g h,
  begin
    simp, -- `+` has changed to `*`
    sorry
  end }
