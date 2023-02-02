import data.finset.basic
import data.nat.prime
import data.zmod.basic

def distinct_residue_classes (p : ℕ) (d : finset ℕ) : ℕ :=
  finset.card (d.image (λ n : ℕ, (n : zmod p)))

notation `ν ` := distinct_residue_classes

def admissible (tup: finset ℕ) : Prop := ∀ (p : ℕ) (hp : p.prime), ν p tup ≠ p - 1

lemma admissible_iff {tup : finset ℕ} :
  admissible tup ↔ ∀ (p : ℕ) (hp : p.prime), ν p tup ≠ p - 1 := iff.rfl

def prime_producing (tup: finset ℕ) : Prop :=
  set.infinite {n : ℕ | ∀ x ∈ tup, (n + x).prime}

lemma prime_producing_iff {tup : finset ℕ} :
  prime_producing tup ↔ set.infinite {n : ℕ | ∀ x ∈ tup, (n + x).prime} := iff.rfl

/-- Dickson–Hardy–Littlewood conjecture -/
def prime_producing_of_admissible (tup : finset ℕ) : Prop :=
  admissible tup → prime_producing tup
