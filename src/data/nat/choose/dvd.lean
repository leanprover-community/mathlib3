import data.nat.choose.basic
import data.nat.prime
open nat

lemma nat.prime.dvd_choose_add {p a b : ℕ} (hap : a < p) (hbp : b < p) (h : p ≤ a + b)
  (hp : prime p) : p ∣ choose (a + b) a :=
have h₁ : p ∣ fact (a + b), from hp.dvd_fact.2 h,
have h₂ : ¬p ∣ fact a, from mt hp.dvd_fact.1 (not_le_of_gt hap),
have h₃ : ¬p ∣ fact b, from mt hp.dvd_fact.1 (not_le_of_gt hbp),
by
  rw [← choose_mul_fact_mul_fact (le.intro rfl), mul_assoc, hp.dvd_mul, hp.dvd_mul,
    nat.add_sub_cancel_left a b] at h₁;
  exact h₁.resolve_right (not_or_distrib.2 ⟨h₂, h₃⟩)

lemma nat.prime.dvd_choose_self {p k : ℕ} (hk : 0 < k) (hkp : k < p) (hp : prime p) :
  p ∣ choose p k :=
begin
  have r : k + (p - k) = p,
    by rw [← nat.add_sub_assoc (nat.le_of_lt hkp) k, nat.add_sub_cancel_left],
  have e : p ∣ choose (k + (p - k)) k,
    by exact nat.prime.dvd_choose_add hkp (sub_lt (lt.trans hk hkp) hk) (by rw r) hp,
  rwa r at e,
end
