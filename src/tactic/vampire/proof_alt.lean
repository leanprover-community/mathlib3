import tactic.vampire.cnf_alt
import tactic.vampire.sub2
import tactic.vampire.list

universe u

variables {α : Type u}

namespace vampire

local notation `#` := term₂.var
local notation a `&` b := term₂.app a b

inductive proof (k : nat) (m : mat) : cla → Type
| hyp (n : nat) (μ : sub₂) : proof ((m.nth n).rsubst k μ)
| res (t : term₂) (c d : cla) :
  proof ((ff, t) :: c) →
  proof ((tt, t) :: d) →
  proof (c ++ d)
| rot (n : nat) (c : cla) :
  proof c → proof (list.rot n c)
| con (l : lit) (c : cla) :
  proof (l :: l :: c) → proof (l :: c)

def term₂.folt_on (χ : nat) : bool → term₂ → Prop
| ff (# k)   := k < χ
| tt (# _)   := true
| _  (a & b) := term₂.folt_on ff a ∧ term₂.folt_on tt b

instance folt_on.decidable {k : nat} :
  ∀ {b : bool} {t : term₂}, decidable (t.folt_on k b)
| ff (# m)   := by {unfold term₂.folt_on, apply_instance}
| tt (# m)   := decidable.true
| tt (a & b) := @and.decidable _ _ folt_on.decidable folt_on.decidable
| ff (a & b) := @and.decidable _ _ folt_on.decidable folt_on.decidable

def term₂.folt (χ : nat) : term₂ → Prop := term₂.folt_on χ ff

instance folt.decidable {k : nat} {t : term₂} : decidable (t.folt k) :=
by {unfold term₂.folt, apply_instance}

#exit
def lit.folt (χ : nat) : bool → term₂ → Prop

#exit
lemma fav_of_proof
  (χ : nat) (M : model α) (m : mat) (h0 : m.fav χ M) :
  ∀ c : cla, proof χ m c → c.fav χ M :=
begin
  intros c π, induction π with
    k μ,

end

end vampire
