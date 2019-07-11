import tactic.vampire.form2

universe u

variables {α : Type u}

namespace vampire

@[reducible] def lit : Type := bool × term₂

@[reducible] def cla : Type := list lit

@[reducible] def mat : Type := list cla

@[reducible] def maps : Type := list sub₂

namespace lit

def rsubst (n : nat) (μ : sub₂) : lit → lit
| (b, t) := (b, t.rsubst n μ)

def holds (M : model α) : lit → Prop
| (tt, t)  :=    (t.val M []).snd
| (ff, t)  :=  ¬ (t.val M []).snd

end lit

namespace cla

def tautology : cla := [(ff, term₂.var 0), (tt, term₂.var 0)]

def rsubst (n : nat) (μ : sub₂) : cla → cla :=
list.map (lit.rsubst n μ)

def holds (M : model α) (c : cla) : Prop :=
∃ l ∈ c, lit.holds M l

def fav (k : nat) (M : model α) (c : cla) : Prop :=
∀ v : vas α, holds (fmodel k M v) c

end cla

namespace mat

def nth (m : mat) (k : nat) : cla :=
option.get_or_else (list.nth m k) cla.tautology

def holds (M : model α) (m : mat) : Prop :=
∀ c ∈ m, cla.holds M c

def fav (k : nat) (M : model α) (m : mat) : Prop :=
∀ c ∈ m, cla.fav k M c

end mat

end vampire
