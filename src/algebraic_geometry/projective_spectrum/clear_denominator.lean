import ring_theory.localization

open_locale classical big_operators

section clear_denominator

variables (R : Type*) [comm_ring R] (f : R)

def clear_denominator (s : finset (localization.away f)) :
  ∃ (n : ℕ), ∀ (x : localization.away f), x ∈ s →
    x * (localization.mk (f^n) 1 : localization.away f) ∈
    (λ y : R, (localization.mk y 1 : localization.away f)) '' set.univ :=
begin
  induction s using finset.induction_on with a s a_nin_s ih,
  { refine ⟨0, λ x rid, _⟩, exfalso, erw set.mem_empty_eq x at rid, exact rid, },
  { obtain ⟨n, hn⟩ := ih,
    have : ∃ (m : ℕ) (x : R), a = localization.mk x ⟨f^m, ⟨m, rfl⟩⟩,
    { induction a using localization.induction_on with data,
      obtain ⟨a, ⟨b, ⟨m, rfl⟩⟩⟩ := data,
      refine ⟨m, a, _⟩, refl, },
    obtain ⟨m, x, rfl⟩ := this,
    refine ⟨n + m, λ y hy, _⟩,
    rw finset.mem_insert at hy,
    rcases hy,
    { erw [hy, localization.mk_mul],
      have : (localization.mk (x * f ^ (n + m)) (⟨f ^ m, _⟩ * 1) : localization.away f) =
        localization.mk (x * f ^ n) 1,
      { rw [localization.mk_eq_mk', is_localization.eq], use 1,
        erw [mul_one, mul_one, mul_one, mul_one, pow_add, mul_assoc],
        refl },
      erw [this, set.mem_image],
      refine ⟨_, set.mem_univ _, rfl⟩, },
    { specialize hn y hy,
      erw set.mem_image at hn,
      obtain ⟨y', _, eq1⟩ := hn,
      have : (localization.mk (f ^ (n + m)) 1 : localization.away f) =
        localization.mk (f ^ n) 1 * localization.mk (f^m) 1,
      { rw [localization.mk_mul], congr, rw pow_add, rw mul_one, },
      erw [this, ←mul_assoc, ←eq1, localization.mk_mul, mul_one],
      refine ⟨_, set.mem_univ _, rfl⟩, } }
end

end clear_denominator
