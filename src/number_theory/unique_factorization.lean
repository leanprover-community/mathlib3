import data.nat.prime
import ring_theory.unique_factorization_domain

theorem nat.prime_iff {p : ℕ} : p.prime ↔ prime p :=
begin
  split; intro h,
  { refine ⟨h.ne_zero, ⟨_,λ a b, _⟩⟩,
    { rw nat.is_unit_iff, apply h.ne_one },
    { apply h.dvd_mul.1 } },
  { refine ⟨_, λ m hm, _⟩,
    { cases p, { exfalso, apply h.ne_zero rfl },
      cases p, { exfalso, apply h.ne_one rfl },
      omega, },
    { cases hm with n hn,
      cases h.2.2 m n (hn ▸ dvd_refl _) with hpm hpn,
      { right, apply nat.dvd_antisymm (dvd.intro _ hn.symm) hpm },
      { left,
        cases n, { exfalso, rw [hn, mul_zero] at h, apply h.ne_zero rfl },
        apply nat.eq_of_mul_eq_mul_right (nat.succ_pos _),
        rw [← hn, one_mul],
        apply nat.dvd_antisymm hpn (dvd.intro m _),
        rw [mul_comm, hn], }, } }
end

theorem nat.irreducible_iff_prime {p : ℕ} : irreducible p ↔ prime p :=
begin
  refine ⟨λ h, _, irreducible_of_prime⟩,
  rw ← nat.prime_iff,
  refine ⟨_, λ m hm, _⟩,
  { cases p, { exfalso, apply h.ne_zero rfl },
    cases p, { exfalso, apply h.1 is_unit_one, },
    omega },
  { cases hm with n hn,
    cases h.2 m n hn with um un,
    { left, rw nat.is_unit_iff.1 um, },
    { right, rw [hn, nat.is_unit_iff.1 un, mul_one], } }
end

namespace nat

instance : wf_dvd_monoid ℕ :=
⟨begin
  apply rel_hom.well_founded _ (with_top.well_founded_lt nat.lt_wf),
  refine ⟨λ x, if x = 0 then ⊤ else x, _⟩,
  intros a b h,
  cases a,
  { exfalso, revert h, simp [dvd_not_unit] },
  cases b,
  {simp [succ_ne_zero, with_top.coe_lt_top]},
  cases dvd_and_not_dvd_iff.2 h with h1 h2,
  simp only [succ_ne_zero, with_top.coe_lt_coe, if_false],
  apply lt_of_le_of_ne (nat.le_of_dvd (nat.succ_pos _) h1) (λ con, h2 _),
  rw con,
end⟩

instance : unique_factorization_monoid ℕ :=
⟨λ _, nat.irreducible_iff_prime⟩

end nat

open unique_factorization_monoid

theorem nat.factors_eq {n : ℕ} : factors n = n.factors :=
begin
  cases n, {refl},
  rw [← multiset.rel_eq, ← associated_eq_eq],
  apply factors_unique (irreducible_of_factor) _,
  { rw [multiset.coe_prod, nat.prod_factors (nat.succ_pos _)],
    apply factors_prod (nat.succ_ne_zero _) },
  {apply_instance},
  { intros x hx,
    rw [nat.irreducible_iff_prime, ← nat.prime_iff],
    apply nat.mem_factors hx, }
end
