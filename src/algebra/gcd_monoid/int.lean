import algebra.gcd_monoid.finset
import ring_theory.int.basic

namespace finset

theorem gcd_is_unit_of_div_gcd {β : Type*} {f : β → ℤ} (s : finset β) {x : β} (hx : x ∈ s)
  (hfz : f x ≠ 0) :
  is_unit (s.gcd (λ b, f b / (s.gcd f))) :=
begin
  have : s.gcd (λ b, f b / (s.gcd f)) ≠ 0 := λ h, hfz (int.eq_zero_of_div_eq_zero (gcd_dvd hx)
    (by convert gcd_eq_zero_iff.1 h x hx)),
  have H0 : s.gcd f ≠ 0 := (not_iff_not.mpr gcd_eq_zero_iff).mpr (λ h, hfz $ h x hx),
  by_contra' hu,
  obtain ⟨p, hpirr, hp⟩ := wf_dvd_monoid.exists_irreducible_factor hu this,
  rw [dvd_gcd_iff] at hp,
  replace hp : ∀ b ∈ s, s.gcd f * p ∣ f b,
  { intros b hb,
    specialize hp b hb,
    obtain ⟨a, ha⟩ := hp,
    refine ⟨a, _⟩,
    rw [mul_assoc, ← ha, ← int.mul_div_assoc (s.gcd f), int.mul_div_cancel_left _ H0],
    exact gcd_dvd hb },
  obtain ⟨a, ha⟩ := dvd_gcd hp,
  refine hpirr.not_unit (is_unit_of_mul_eq_one _ a _),
  simp only at ha,
  rw [mul_assoc] at ha,
  nth_rewrite 0 [← mul_one (s.gcd f)] at ha,
  exact (int.eq_of_mul_eq_mul_left H0 ha).symm
end

theorem gcd_is_unit_of_div_gcd_id (s : finset ℤ) {x : ℤ} (hx : x ∈ s) (hnz : x ≠ 0) :
  is_unit (s.gcd (λ b, b / (s.gcd id))) :=
gcd_is_unit_of_div_gcd s hx hnz

end finset
