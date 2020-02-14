import ring_theory.algebra_operations
import ring_theory.localization

open localization

set_option class.instance_max_depth 100

universes u v w
namespace ring
variables (R : Type u) [integral_domain R]

/-- The fractional ideals of a ring `R` are submodules that are ideals of `R` when multiplied by `a ∈ R`. -/
structure fractional_ideal (S : set R) [is_submonoid S] :=
(submod : submodule R (localization R S))
(denominator : R)
(coefficient : denominator ≠ 0)
(fractional : ∀ b ∈ submod, is_integer R S (denominator • b))

variables {S : set R} [is_submonoid S]

instance : has_coe (ideal R) (fractional_ideal R S) :=
⟨ λ I, ⟨ ⟨ I.carrier.image coe,
    ⟨0, ideal.zero_mem _, rfl⟩,
    λ x' y' ⟨x, x_mem, hx⟩ ⟨y, y_mem, hy⟩, ⟨x + y, ideal.add_mem _ x_mem y_mem, by simp [hx, hy]⟩,
    λ c x' ⟨x, x_mem, hx⟩, ⟨c • x, submodule.smul_mem _ _ x_mem, by rw [coe_smul, hx]⟩⟩,
  1,
  one_ne_zero,
  λ b' ⟨b, b_mem, hb⟩, by { convert is_integer_coe R b, rw [one_smul, hb] }⟩⟩

instance fractional_ideal_has_zero : has_zero (fractional_ideal R S) :=
⟨(0 : ideal R)⟩

instance fractional_ideal_has_add : has_add (fractional_ideal R S) :=
⟨ λ ⟨I, aI, haI, hI⟩ ⟨J, aJ, haJ, hJ⟩, ⟨
  I + J,
  aI * aJ,
  mul_ne_zero haI haJ,
  λ b hb, begin
    obtain ⟨bI, hbI, bJ, hbJ, hbIJ⟩ := submodule.mem_sup.mp hb,
    rw [←hbIJ, smul_add],
    apply is_integer_add,
    { rw [mul_smul],
      apply hI,
      apply submodule.smul_mem,
      assumption },
    { rw [mul_comm, mul_smul],
      apply hJ,
      apply submodule.smul_mem,
      assumption },
  end ⟩ ⟩

instance fractional_ideal_has_mul : has_mul (fractional_ideal R S) :=
⟨ λ ⟨I, aI, haI, hI⟩ ⟨J, aJ, haJ, hJ⟩, ⟨
  I * J,
  aI * aJ,
  mul_ne_zero haI haJ,
  λ b hb, begin
    apply submodule.mul_induction_on hb,
    { intros m hm n hn,
      obtain ⟨n', hn', n'_eq⟩ := hJ n hn,
      rw [mul_smul, ←algebra.mul_smul_comm, ←n'_eq, mul_comm],
      apply hI,
      exact submodule.smul_mem _ _ hm },
    { rw [smul_zero],
      apply is_integer_coe },
    { intros x y hx hy,
      rw [smul_add],
      apply is_integer_add _ hx hy },
    { intros r x hx,
      rw [←mul_smul, mul_comm, mul_smul],
      apply is_integer_smul _ hx },
  end ⟩ ⟩

/-- The elements of `I / J` are the `x` such that `x J ⊆ I`.

  This is the general form of the ideal quotient, traditionally written $I : J$.
-/
instance {M : Type v} [ring M] [algebra R M] : has_div (submodule R M) :=
⟨ λ I J, {
  carrier := { x | ∀ y ∈ J, x * y ∈ I },
  zero := λ y hy, by { rw zero_mul, apply submodule.zero },
  add := λ a b ha hb y hy, by { rw add_mul, exact submodule.add _ (ha _ hy) (hb _ hy) },
  smul := λ r x hx y hy, by { rw algebra.smul_mul_assoc, exact submodule.smul _ _ (hx _ hy) } } ⟩

lemma exists_nonzero_of_ne_bot {M : Type v} [add_comm_group M] [module R M] {I : submodule R M} (h : I ≠ 0) :
  ∃ (x : M), x ∈ I ∧ x ≠ 0 :=
begin
  obtain ⟨x, mem_I, not_bot⟩ := submodule.exists_of_lt (lattice.bot_lt_iff_ne_bot.mpr h),
  use x,
  use mem_I,
  intro h,
  apply not_bot,
  exact (submodule.mem_bot R).mpr h
end

section
open_locale classical -- for deciding J = 0

noncomputable instance fractional_ideal_has_div : has_div (fractional_ideal R S) :=
⟨ λ ⟨I, aI, haI, hI⟩ ⟨J, aJ, haJ, hJ⟩, if h : J = 0 then 0 else begin
    obtain ⟨y, mem_J, nonzero⟩ := classical.indefinite_description _ (exists_nonzero_of_ne_bot _ h),
    obtain ⟨y', _, hy'⟩ := classical.indefinite_description _ (hJ y mem_J),
    apply fractional_ideal.mk (I / J) (aI * y'),
    { apply mul_ne_zero haI,
      intro y'_eq_zero,
      have : ↑aJ * y = 0 := by rw [coe_mul_eq_smul, ←hy', y'_eq_zero, coe_zero],
      sorry },
    intros b hb,
    rw [mul_smul],
    convert hI _ (hb _ (submodule.smul_mem _ aJ mem_J)),
    rw [←hy', mul_coe_eq_smul]
  end ⟩
end

end ring
