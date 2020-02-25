import ring_theory.algebra_operations
import ring_theory.localization

open localization

set_option class.instance_max_depth 100

universes u v w
namespace ring

/-- The fractional ideals of a ring `R` are submodules that are ideals of `R` when multiplied by `a ∈ R`. -/
structure fractional_ideal (R : Type u) [integral_domain R] (S : set R) [is_submonoid S] :=
(submod : submodule R (localization R S))
(fractional : ∃ a ≠ (0 : R), ∀ b ∈ submod, is_integer R S (a • b))

namespace fractional_ideal

variables {R : Type u} [integral_domain R] {S : set R} [is_submonoid S]

@[ext]
lemma ext {I J : fractional_ideal R S} (h : I.submod = J.submod) : I = J :=
by { cases I, cases J, congr, assumption }

instance : has_mem (localization R S) (fractional_ideal R S) :=
⟨ λ x I, x ∈ I.submod ⟩

instance : has_coe (ideal R) (fractional_ideal R S) :=
⟨ λ I, ⟨ ⟨ I.carrier.image coe,
    ⟨0, ideal.zero_mem _, rfl⟩,
    λ x' y' ⟨x, x_mem, hx⟩ ⟨y, y_mem, hy⟩, ⟨x + y, ideal.add_mem _ x_mem y_mem, by simp [hx, hy]⟩,
    λ c x' ⟨x, x_mem, hx⟩, ⟨c • x, submodule.smul_mem _ _ x_mem, by rw [coe_smul, hx]⟩⟩,
  1,
  one_ne_zero,
  λ b' ⟨b, b_mem, hb⟩, by { convert is_integer_coe R b, rw [one_smul, hb] }⟩⟩

instance : has_zero (fractional_ideal R S) :=
⟨(0 : ideal R)⟩

lemma mem_zero_iff {x : localization R S} : x ∈ (0 : fractional_ideal R S) ↔ x = 0 :=
⟨ (λ ⟨x', x'_mem_zero, x'_eq_x⟩,
    have x'_eq_zero : x' = 0 := (or_false _).mp x'_mem_zero,
    by simp [x'_eq_x.symm, x'_eq_zero]),
  (λ hx, ⟨0, or.inl rfl, by simp [hx]⟩) ⟩

instance : has_one (fractional_ideal R S) :=
⟨(1 : ideal R)⟩

lemma mem_one_iff {x : localization R S} : x ∈ (1 : fractional_ideal R S) ↔ ∃ x' : R, ↑x' = x :=
iff.intro (λ ⟨x', _, h⟩, ⟨x', h⟩) (λ ⟨x', h⟩, ⟨x', ⟨x', set.mem_univ _, rfl⟩, h⟩)

lemma coe_mem_one {x : R} : (x : localization R S) ∈ (1 : fractional_ideal R S) :=
mem_one_iff.mpr ⟨x, rfl⟩

instance : has_add (fractional_ideal R S) :=
⟨ λ I J, ⟨
  I.submod + J.submod,
  begin
    rcases I with ⟨I, aI, haI, hI⟩,
    rcases J with ⟨J, aJ, haJ, hJ⟩,
    use aI * aJ,
    use mul_ne_zero haI haJ,
    intros b hb,
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
      assumption }
  end ⟩ ⟩

@[simp]
lemma submod_add_submod (I J : fractional_ideal R S) : (I + J).submod = I.submod + J.submod := rfl

instance : has_mul (fractional_ideal R S) :=
⟨ λ I J, ⟨
  I.submod * J.submod,
  begin
    rcases I with ⟨I, aI, haI, hI⟩,
    rcases J with ⟨I, aJ, haJ, hJ⟩,
    use aI * aJ,
    use mul_ne_zero haI haJ,
    intros b hb,
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

@[simp]
lemma submod_mul_submod (I J : fractional_ideal R S) : (I * J).submod = I.submod * J.submod := rfl

section lattice

open lattice

instance : partial_order (fractional_ideal R S) :=
{ le := λ I J, I.submod ≤ J.submod,
  le_refl := λ I, le_refl I.submod,
  le_antisymm := λ ⟨I, hI⟩ ⟨J, hJ⟩ hIJ hJI, by { congr, exact le_antisymm hIJ hJI },
  le_trans := λ _ _ _ hIJ hJK, le_trans hIJ hJK }

@[simp]
lemma le_iff {I J : fractional_ideal R S} : I ≤ J ↔ (∀ x ∈ I, x ∈ J) := iff.refl _

lemma fractional_bot :
  ∃ a ≠ (0 : R), ∀ b ∈ (⊥ : submodule R (localization R S)), is_integer R S (a • b) :=
begin
  use 1,
  use one_ne_zero,
  intros b hb,
  cases (or_false _).mp hb,
  apply is_integer_smul,
  use 0,
  split,
  { apply set.mem_univ },
  { refl }
end

instance order_bot : order_bot (fractional_ideal R S) :=
{ bot := ⟨⊥, fractional_bot⟩,
  bot_le := λ I, show ⊥ ≤ I.1, from lattice.bot_le,
  ..fractional_ideal.partial_order }

@[simp] lemma bot_eq_zero : (⊥ : fractional_ideal R S) = 0 :=
have mem_if_mem : ∀ x ∈ (0 : fractional_ideal R S), x ∈ (⊥ : fractional_ideal R S) :=
  λ x h, or.inl (mem_zero_iff.mp h),
(lattice.le_bot_iff.mp (le_iff.mpr mem_if_mem)).symm

lemma zero_le (I : fractional_ideal R S) : 0 ≤ I := by { convert bot_le, simp }

lemma eq_zero_iff {I : fractional_ideal R S} : I = 0 ↔ (∀ x ∈ I, x = (0 : localization R S)) :=
⟨ (λ h x hx, by simpa [h, mem_zero_iff] using hx),
  (λ h, le_antisymm (le_iff.mpr (λ x hx, mem_zero_iff.mpr (h x hx))) (zero_le _)) ⟩

lemma fractional_sup (I J : fractional_ideal R S) :
  ∃ a ≠ (0 : R), ∀ b ∈ I.submod ⊔ J.submod, is_integer R S (a • b) :=
begin
  rcases I.fractional with ⟨aI, haI, hI⟩,
  rcases J.fractional with ⟨aJ, haJ, hJ⟩,
  use aI * aJ,
  use mul_ne_zero haI haJ,
  intros b hb,
  rcases submodule.mem_sup.mp hb with ⟨bI, hbI, bJ, hbJ, hbIJ⟩,
  -- TODO: this seems analogous to has_add?
  rw [←hbIJ, smul_add],
  apply is_integer_add,
  { rw [mul_comm, mul_smul],
    apply is_integer_smul _ (hI bI hbI) },
  { rw [mul_smul],
    apply is_integer_smul _ (hJ bJ hbJ) }
end

lemma fractional_inf (I J : fractional_ideal R S) :
  ∃ a ≠ (0 : R), ∀ b ∈ I.submod ⊓ J.submod, is_integer R S (a • b) :=
begin
  rcases I.fractional with ⟨aI, haI, hI⟩,
  use aI,
  use haI,
  intros b hb,
  rcases submodule.mem_inf.mp hb with ⟨hbI, hbJ⟩,
  exact (hI b hbI)
end

instance lattice : lattice (fractional_ideal R S) :=
{ inf := λ I J, ⟨I.1 ⊓ J.1, fractional_inf I J⟩,
  sup := λ I J, ⟨I.1 ⊔ J.1, fractional_sup I J⟩,
  inf_le_left := λ I J, show I.1 ⊓ J.1 ≤ I.1, from inf_le_left,
  inf_le_right := λ I J, show I.1 ⊓ J.1 ≤ J.1, from inf_le_right,
  le_inf := λ I J K hIJ hIK, show I.1 ≤ (J.1 ⊓ K.1), from le_inf hIJ hIK,
  le_sup_left := λ I J, show I.1 ≤ I.1 ⊔ J.1, from le_sup_left,
  le_sup_right := λ I J, show J.1 ≤ I.1 ⊔ J.1, from le_sup_right,
  sup_le := λ I J K hIK hJK, show (I.1 ⊔ J.1) ≤ K.1, from sup_le hIK hJK,
  ..fractional_ideal.partial_order }

instance : semilattice_sup_bot (fractional_ideal R S) :=
{ ..fractional_ideal.order_bot, ..fractional_ideal.lattice }

end lattice

instance : add_comm_monoid (fractional_ideal R S) :=
{ add_assoc := λ I J K, lattice.sup_assoc,
  add_comm := λ I J, lattice.sup_comm,
  add_zero := λ I, by { convert lattice.sup_bot_eq, simp },
  zero_add := λ I, by { convert lattice.bot_sup_eq, simp },
  ..fractional_ideal.has_zero,
  ..fractional_ideal.has_add }

instance : comm_monoid (fractional_ideal R S) :=
{ mul_assoc := λ I J K, ext (submodule.mul_assoc _ _ _),
  mul_comm := λ I J, ext (mul_comm _ _),
  mul_one := λ I, begin
    ext,
    split; intro h,
    { apply submodule.mul_le.mpr _ h,
      rintros x hx y ⟨y', y'_mem_R, y'_eq_y⟩,
      rw [←y'_eq_y, mul_comm, coe_mul_eq_smul],
      apply submodule.smul,
      exact hx },
    { have : x * 1 ∈ (I * 1) := submodule.mul_mem_mul h coe_mem_one,
      simpa }
  end,
  one_mul := λ I, begin
    ext,
    split; intro h,
    { apply submodule.mul_le.mpr _ h,
      rintros x ⟨x', x'_mem_R, x'_eq_x⟩ y hy,
      rw [←x'_eq_x, coe_mul_eq_smul],
      apply submodule.smul,
      exact hy },
    { have : 1 * x ∈ (1 * I) := submodule.mul_mem_mul coe_mem_one h,
      simpa }
  end,
  ..fractional_ideal.has_mul,
  ..fractional_ideal.has_one }

instance : comm_semiring (fractional_ideal R S) :=
{ mul_zero := λ I, eq_zero_iff.mpr (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, by simp [mem_zero_iff.mp hy])
    rfl
    (λ x y hx hy, by simp [hx, hy])
    (λ r x hx, by simp [hx])),
  zero_mul := λ I, eq_zero_iff.mpr (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, by simp [mem_zero_iff.mp hx])
    rfl
    (λ x y hx hy, by simp [hx, hy])
    (λ r x hx, by simp [hx])),
  left_distrib := λ I J K, ext (mul_add _ _ _),
  right_distrib := λ I J K, ext (add_mul _ _ _),
  ..fractional_ideal.add_comm_monoid,
  ..fractional_ideal.comm_monoid }

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

section quotient
open_locale classical

noncomputable instance fractional_ideal_has_div :
  has_div (fractional_ideal R (non_zero_divisors R)) :=
⟨ λ I J, if h : J.submod = 0 then 0 else ⟨
  I.submod / J.submod,
  begin
    rcases I with ⟨I, aI, haI, hI⟩,
    rcases J with ⟨J, aJ, haJ, hJ⟩,
    obtain ⟨y, mem_J, nonzero⟩ := classical.indefinite_description _ (exists_nonzero_of_ne_bot h),
    obtain ⟨y', _, hy'⟩ := classical.indefinite_description _ (hJ y mem_J),
    use (aI * y'),
    split,
    { apply mul_ne_zero haI,
      intro y'_eq_zero,
      have : ↑aJ * y = 0 := by rw [coe_mul_eq_smul, ←hy', y'_eq_zero, coe_zero],
      obtain aJ_zero | y_zero := mul_eq_zero.mp this,
      { have : aJ = 0 := fraction_ring.of.injective (trans aJ_zero (of_zero _ _).symm),
        contradiction },
      { contradiction } },
    intros b hb,
    rw [mul_smul],
    convert hI _ (hb _ (submodule.smul_mem _ aJ mem_J)),
    rw [←hy', mul_coe_eq_smul]
  end ⟩
end quotient

end ring
