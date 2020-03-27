import tactic.transport

def add_monoid.map {α β : Type} (e : α ≃ β) (S : add_monoid α) : add_monoid β :=
by transport
.

inductive mynat : Type
| zero : mynat
| succ : mynat → mynat

def mynat_equiv : ℕ ≃ mynat :=
{ to_fun := λ n, nat.rec_on n mynat.zero (λ n, mynat.succ),
  inv_fun := λ n, mynat.rec_on n nat.zero (λ n, nat.succ),
  left_inv := λ n, begin induction n, refl, exact congr_arg nat.succ n_ih, end,
  right_inv := λ n, begin induction n, refl, exact congr_arg mynat.succ n_ih, end }

@[simp] lemma mynat_equiv_apply_zero : mynat_equiv 0 = mynat.zero := rfl
@[simp] lemma mynat_equiv_apply_succ (n : ℕ) :
  mynat_equiv (n + 1) = mynat.succ (mynat_equiv n) := rfl
@[simp] lemma mynat_equiv_symm_apply_zero : mynat_equiv.symm mynat.zero = 0:= rfl
@[simp] lemma mynat_equiv_symm_apply_succ (n : mynat) :
  mynat_equiv.symm (mynat.succ n) = (mynat_equiv.symm n) + 1 := rfl

instance add_monoid_mynat : add_monoid mynat := add_monoid.map mynat_equiv (by apply_instance)

-- TODO this lemma should be automatically synthesised!
lemma mynat_add_def (a b : mynat) : a + b = mynat_equiv (mynat_equiv.symm a + mynat_equiv.symm b) :=
begin
  dsimp [add_monoid_mynat, add_monoid.map],
  unfold_projs,
  simp,
end

-- Verify that we can do computations with the transported structure.
example :
  (mynat.succ (mynat.succ mynat.zero)) + (mynat.succ mynat.zero) =
    (mynat.succ (mynat.succ (mynat.succ mynat.zero))) :=
by simp [mynat_add_def]

example {α : Type} [ring α] {β : Type} (e : α ≃ β) : ring β :=
by transport
.
