import prerequisites

open_locale nat

theorem euclid (n : ℕ) : ∃ p > n, p.prime :=
begin
  let N := n! + 1,
  let p := nat.min_fac N,
  use p,
  have hp : p.prime,
  { refine nat.min_fac_prime _,
    have : n! > 0 := nat.factorial_pos n,
    linarith, },
  have hpn : p > n,
  { by_contra' hpn : p ≤ n,
    have aux1 : p ∣ n! := (nat.prime.dvd_factorial hp).mpr hpn,
    have aux2 : p ∣ N := nat.min_fac_dvd N,
    have aux3 : p ∣ 1 := (nat.dvd_add_right aux1).mp aux2,
    have : ¬p ∣ 1 := nat.prime.not_dvd_one hp,
    contradiction, },
  exact ⟨hpn, hp⟩,
end

#print axioms euclid

#print quot.sound

#print classical.axiom_of_choice
