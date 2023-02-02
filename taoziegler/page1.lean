import data.finset.basic
import data.nat.prime
import data.zmod.basic


def admissible (tup: multiset ℕ) : Prop := ∀ (p : ℕ) (hp : p.prime) [hf : fintype (zmod p)],
  tup.map (λ n : ℕ, (n : zmod p)) ≠ (@finset.univ (zmod p) hf).val

lemma admissible_iff {tup : multiset ℕ} :
  admissible tup ↔ ∀ (p : ℕ) (hp : p.prime) [hf : fintype (zmod p)],
  tup.map (λ n : ℕ, (n : zmod p)) ≠ (@finset.univ (zmod p) hf).val := iff.rfl

def prime_producing (tup: multiset ℕ) : Prop :=
  set.infinite {n : ℕ | ∀ x ∈ tup, (n + x).prime}

lemma prime_producing_iff {tup : multiset ℕ} :
  prime_producing tup ↔ set.infinite {n : ℕ | ∀ x ∈ tup, (n + x).prime} := iff.rfl

/-- Dickson–Hardy–Littlewood conjecture -/
def prime_producing_of_admissible (tup : multiset ℕ) : Prop :=
  admissible tup → prime_producing tup
