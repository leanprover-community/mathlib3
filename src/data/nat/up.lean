
import data.nat.basic

namespace nat

def up (p : ℕ → Prop) : Type := { i : ℕ // (∀ j < i, ¬ p j) }

namespace up

variable {p : ℕ → Prop}

protected def lt (p) : up p → up p → Prop := λ x y, x.1 > y.1

instance : has_lt (up p) :=
{ lt := λ x y, x.1 > y.1 }

protected def wf : Exists p → well_founded (up.lt p)
| ⟨x,h⟩ :=
have h : (<) = measure (λ y : nat.up p, x - y.val),
  by { ext, dsimp [measure,inv_image],
       rw nat.sub_lt_sub_left_iff, refl,
       by_contradiction h', revert h,
       apply x_1.property _ (lt_of_not_ge h'), },
cast (congr_arg _ h.symm) (measure_wf _)

def zero : nat.up p := ⟨ 0, λ j h, false.elim (nat.not_lt_zero _ h) ⟩

def succ (x : nat.up p) (h : ¬ p x.val) : nat.up p :=
⟨x.val.succ, by { intros j h', rw nat.lt_succ_iff_lt_or_eq at h',
                  cases h', apply x.property _ h', subst j, apply h } ⟩

section find

variables [decidable_pred p] (h : Exists p)

def find_aux : nat.up p → nat.up p :=
well_founded.fix (up.wf h) $ λ x f,
if h : p x.val then x
  else f (x.succ h) $ nat.lt_succ_self _

def find : ℕ := (find_aux h up.zero).val

lemma p_find : p (find h) :=
let P := (λ x : nat.up p, p (find_aux h x).val) in
suffices ∀ x, P x, from this _,
assume x,
well_founded.induction (nat.up.wf h) _ $ λ y ih,
by { dsimp [P], rw [find_aux,well_founded.fix_eq],
     by_cases h' : (p (y.val)); simp *,
     apply ih, apply nat.lt_succ_self, }

lemma find_least_solution (i : ℕ) (h' : i < find h) : ¬ p i :=
subtype.property (find_aux h nat.up.zero) _ h'

end find

end up
end nat
