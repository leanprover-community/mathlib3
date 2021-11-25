import prerequisites

open_locale nat

theorem euclid (n : ℕ) : ∃ p > n, p.prime :=
begin
  let N := n! + 1,
  let p := N.min_fac,
  use p,
  have hp : p.prime,
  { refine nat.min_fac_prime _,
    have : n! > 0 := nat.factorial_pos n,
    linarith, },
  have hpn : p > n,
  { by_contra' hpn : p ≤ n,
    have h1 : ¬p ∣ 1 := nat.prime.not_dvd_one hp,
    have h2 : p ∣ n! := (nat.prime.dvd_factorial hp).mpr hpn,
    have h3 : p ∣ N := nat.min_fac_dvd N,
    have : p ∣ 1 := (nat.dvd_add_right h2).mp h3,
    contradiction },
  finish,
end
