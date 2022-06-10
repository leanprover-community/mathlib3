/-
Copyright (c) 2022 Jon Eugster.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import algebra.char_p.algebra
import ring_theory.ideal.quotient

/-!
# Equal and mixed characteristics

A commutative ring of characteristic zero can either be of 'equal characteristic zero'
or of 'mixed characteristic'. 'Equal characteristic zero' means that the quotient
ring `R⧸I` has characteristic zero for all proper ideals `I ⊆ R`.
Equivalently, `R` has equal characteristics zero if there is an injective
ring homomorphism `ℚ → R`, i.e. `R` contains a copy of `ℚ`.

Mixed characteristics `(0,p)` means `R` has characteristics `0` but there
exists an ideal such that `R⧸I` has characteristics `p`. Note that a ring
can be of different mixed characteristics simultaneously, e.g. `ℤ` has mixed
characteristics `(0,p)` for any `p ≠ 0`.

In this document we define equal characteristics zero and provide a theorem to split
into cases by characteristics.

## Main definitions

- `equal_char_zero` : class for a ring to be of 'equal characteristic zero'.
- `mixed_char_zero` : class for a ring to be of 'mixed characteristic zero'.

- `equal_char_zero.rat_cast` : The injective homomorphism `ℚ →+* R`.

## Main results

- `equal_char_zero.iff_rat_cast_inj`: A ring has equal characteristic zero iff there is an
                                      injective homomorphism `ℚ →+* R`.

## Implementation notes

## References

-/

/-!
### Equal characteristics zero
-/

/-- A ring has equal characteristic zero if `char(R⧸I) = 0` for all proper ideals `I ⊂ R`. -/
class equal_char_zero (R : Type*) [comm_ring R] : Prop :=
  (residue_char_zero : ∀(I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I))

/-- This definition is trivial if `R` is a field. -/
lemma field.equal_char_zero (K : Type*) [field K] [h_char : char_zero K] :
  equal_char_zero K :=
⟨begin
  intros I hI',
  have hI := or_iff_not_imp_right.1 (ideal.eq_bot_or_top I) hI',
  exact ⟨begin
    intros x y h,
    apply h_char.cast_injective,
    calc ↑x = I.quot_equiv_of_eq_bot hI (submodule.quotient.mk x) : rfl
        ... = I.quot_equiv_of_eq_bot hI (submodule.quotient.mk y) : by {simp only [
                                                                    ideal.quotient.mk_eq_mk,
                                                                    map_nat_cast], rw h}
        ... = ↑y                                                  : rfl,
  end⟩
end⟩

namespace equal_char_zero

/-- Equal characteristics zero implies `char(R) = 0`. -/
@[priority 100] instance char_zero (R : Type*) [comm_ring R] [nontrivial R] [equal_char_zero R] :
  char_zero R :=
⟨begin
  intros x y h,
  apply (equal_char_zero.residue_char_zero (⊥:ideal R) bot_ne_top).cast_injective,
  replace h := congr_arg (ideal.quotient.mk ⊥) h,
  simp at h,
  exact h,
end⟩

/-!
# Alternative definition
A ring has equal characteristics zero iff there exists an injective
homomorphism `ℚ →+* R`.
-/

section rat_cast

/-- Equal characteristics zero implies `char(R) = 0`. -/
-- This is very similar to `algebra.char_p.algebra.char_zero_of_injective_algebra_map`.
example {R : Type*} [semiring R]
  {i: ℚ →+* R} (h_inj: function.injective i): char_zero R :=
char_zero_of_injective_algebra_map h_inj

lemma of_rat_cast_inj (R : Type*) [comm_ring R] [char_zero R] {i : ℚ →+* R} (h_inj: function.injective i) :
  equal_char_zero R :=
⟨begin
  intros I hI,
  exact { cast_injective :=
    begin
      -- Let `a,b ∈ img(ℕ) ⊆ R` with `[a]=[b]∈ R ⧸ I`.
      intros a b h_ab,

      -- This means `a-b ∈ I ⊆ R`.
      let c := (a : R) - ↑b,
      have h_c : c ∈  I := begin
        apply iff.elim_left ideal.quotient.eq,
        simp only [map_nat_cast],
        exact h_ab,
      end,

      -- But also `a-b ∈ img(ℚ) ⊆ R` (i.e. there is a `t:ℚ` such that `i(t) = a-b`).
      have h_inj_t : ∃(d : ℚ), (i d) = c := begin
        -- We simply do the subtraction `a-b` in `ℚ` instead of `ℕ`.
        use (a : ℚ) - (b : ℚ),
        simp only [map_nat_cast, map_sub],
      end,
      cases h_inj_t with t ht,

      -- Either `c := a-b` is zero or a unit in `R`.
      have h_c' : c = 0 ∨ is_unit c := begin
        -- To show this let's assume `c ≠ 0`. We need to show that `c` is a unit.
        rw or_iff_not_imp_left,
        intro h1,
        -- We use that `c = i(t)` and show that `t` is a unit in `ℚ`.
        rw ←ht,
        have h2 : ¬t = 0 :=
        begin  -- TODO: I'm sure this can be done simpler...
          by_contradiction h',
          apply h1,
          rw ←ht,
          apply (map_eq_zero_iff i h_inj).elim_right,
          exact h',
        end,
        have h3 : is_unit t := is_unit.mk0 t h2,
        -- Therefore `i(t)` is a unit, too.
        refine ring_hom.is_unit_map i h3,
      end,

      -- If `a-b` is a unit then `I=R`. Contradiction!
      have h_c_not_unit: ¬(is_unit c) := begin
        by_contradiction h_unit,
        have h_is_top := I.eq_top_of_is_unit_mem h_c h_unit,
        contradiction,
      end,

      -- Therefore `a-b = 0`, i.e. `a=b ∈ R`.
      have h_a_eq_b : (a:R)=↑b := begin
        refine sub_eq_zero.mp (or.resolve_right h_c' h_c_not_unit),
      end,

      -- Using injectivity we conclude `a=b ∈ ℕ`. (This uses the instance `char_zero R`)
      apply @nat.cast_injective R,
      exact h_a_eq_b,
    end}
end⟩

/-- Any element in `ℕ ⊂ R` has an inverse in `R`. -/
lemma nat_inv_exists_of_pos (R : Type*) [comm_ring R] [equal_char_zero R] {n : ℕ} (hn : 0 < n) :
  ∃(x : R), x * n = 1 :=
begin
  -- Assume `n` is not invertible.
  by_contradiction h1,
  rw not_exists at h1,
  -- Then `(n)` is a proper ideal.
  let I := ideal.span ({n} : set R),
  have hI : (1 : R) ∉ I := begin
    by_contradiction,
    -- `1 ∈ I` means `∃x:x*n = 1`.
    have h2 : ∃(x : R), x * n = 1 :=
    begin
      apply ideal.mem_span_singleton'.1,
      exact h,
    end,
    cases h2 with x hx,
    have hx' := h1 x,
    contradiction,
  end,
  -- so  `char R⧸(n) = 0`
  have h_charzero := equal_char_zero.residue_char_zero I ((ideal.ne_top_iff_one I).2 hI),
  -- but also `char R⧸(n)` is not zero, because `n*1 = 0`.
  have h2 : (ideal.quotient.mk I n) = 0 :=
  begin
    rw ideal.quotient.eq_zero_iff_mem,
    rw ideal.mem_span_singleton',
    use 1,
    rw one_mul,
  end,
  simp only [map_nat_cast] at h2, -- workouround because I formulated h2 ugly.
  have h3: n=0 := begin
    apply h_charzero.cast_injective,
    exact h2,
  end,
  rw h3 at hn,
  have not_hn := lt_irrefl 0,
  contradiction,
end

lemma nat_is_unit_of_pos (R : Type*) [comm_ring R] [equal_char_zero R] {n:ℕ} (hn: 0 < n) :
  is_unit (n:R) :=
begin
  rw is_unit_iff_exists_inv',
  exact nat_inv_exists_of_pos R hn,
end

noncomputable def nat_inv (R : Type*) [comm_ring R] [equal_char_zero R] {n:ℕ} (hn: 0 < n): R :=
  ↑((nat_is_unit_of_pos R hn).unit)⁻¹

@[simp] lemma nat_inv_mul (R : Type*) [comm_ring R] [equal_char_zero R] {n:ℕ} (hn: 0 < n) :
(nat_inv R hn) * n = 1 := (nat_is_unit_of_pos R hn).coe_inv_mul

@[simp] lemma mul_nat_inv (R : Type*) [comm_ring R] [equal_char_zero R] {n:ℕ} (hn: 0 < n) :
↑n * (nat_inv R hn) = 1 :=
begin
  rw mul_comm,
  exact nat_inv_mul R hn,
end

theorem to_rat_cast_inj (R : Type*) [comm_ring R] [nontrivial R] [equal_char_zero R] :
  ∃ (i : ℚ →+* R), function.injective i :=
begin
  let cast : ℚ →+* R := {
    -- invert the denominator in R.
    to_fun := λx, x.num * (nat_inv R x.pos),
    map_zero' := by simp only [rat.num_zero, int.cast_zero, zero_mul],
    map_one' := by apply mul_nat_inv,
    map_mul' := begin
      -- This is just a boring calculation using commutativity & associativity
      intros a b,
      apply (is_unit.mul_left_inj (nat_is_unit_of_pos R (a*b).pos)).mp,
      conv_lhs {rw [mul_assoc, nat_inv_mul, mul_one]},
      apply (is_unit.mul_right_inj (nat_is_unit_of_pos R a.pos)).mp,
      repeat {rw ←mul_assoc},
      conv in (_ * _ * nat_inv R a.pos) {rw [mul_comm, ←mul_assoc, nat_inv_mul, one_mul]},
      apply (is_unit.mul_left_inj (nat_is_unit_of_pos R b.pos)).mp,
      repeat {rw mul_assoc},
      conv in (nat_inv R _ * _) {rw [mul_comm, mul_assoc, mul_nat_inv, mul_one]},
      simp_rw [←int.cast_coe_nat, ←int.cast_mul, ←mul_assoc, ←rat.mul_num_denom'],
      ring_nf,
    end,
    map_add' := begin
      -- This is just a boring calculation using commutativity, associativity & distributivity
      intros a b,
      apply (is_unit.mul_left_inj (nat_is_unit_of_pos R ((a+b).pos))).mp,
      conv_lhs {rw [mul_assoc, nat_inv_mul, mul_one]},
      apply (is_unit.mul_right_inj (nat_is_unit_of_pos R (a.pos))).mp,
      rw [add_mul, mul_add, ←mul_assoc],
      conv in (_ * (_ * nat_inv R a.pos)) {rw [mul_comm, mul_assoc, nat_inv_mul, mul_one]},
      apply (is_unit.mul_left_inj (nat_is_unit_of_pos R (b.pos))).mp,
      simp_rw [add_mul, mul_assoc],
      conv in (nat_inv R _ * _) {rw [mul_comm, mul_assoc, mul_nat_inv, mul_one]},
      rw ←mul_assoc,
      nth_rewrite 1 mul_comm,
      simp_rw [←int.cast_coe_nat, ←int.cast_mul, rat.add_eq_def],
      rw [add_mul, int.cast_add],
      ring_nf,
    end
  },
  use cast,
  {
    intros x y hxy,
    rw ←ring_hom.to_fun_eq_coe at hxy,
    simp at hxy,
    replace hxy := congr_arg (has_mul.mul (x.denom:R)) hxy,
    replace hxy := congr_arg (has_mul.mul (y.denom:R)) hxy,
    have hxy' : (y.denom:R) * (↑(x.denom) * (↑(x.num) * nat_inv R x.pos)) = (x.num * y.denom:ℤ) * (nat_inv R x.pos * x.denom)
    := by {simp only [int.cast_mul, int.cast_coe_nat], ring},
    have hxy'' : (y.denom:R) * (↑(x.denom) * (↑(y.num) * nat_inv R y.pos)) = (y.num *x.denom:ℤ) * (nat_inv R y.pos * y.denom) :=
    by {simp only [int.cast_mul, int.cast_coe_nat], ring},
    rw [hxy', hxy''] at hxy,
    clear hxy' hxy'',

    rw nat_inv_mul R x.pos at hxy,
    rw nat_inv_mul R y.pos at hxy,
    repeat {rw mul_one at hxy},
    --simp only [int.cast_mul, int.cast_coe_nat],

    rw ←@rat.num_denom x,
    rw ←@rat.num_denom y,
    rw rat.mk_eq (int.coe_nat_ne_zero_iff_pos.mpr x.pos) (int.coe_nat_ne_zero_iff_pos.mpr y.pos),

    exact int.cast_injective hxy,
  },
end


/-- Alternative definition of equal characteristic zero, in terms injective `ℚ →+* R`. -/
theorem iff_rat_cast_inj (R : Type*) [comm_ring R] [nontrivial R]:
  equal_char_zero R ↔ ∃ (i : ℚ →+* R), function.injective i :=
begin
  split,
  {
    introI,
    exact to_rat_cast_inj R,
  }, {
    intro h,
    cases h with i hi,
    haveI h_char := char_zero_of_injective_algebra_map hi,
    exact of_rat_cast_inj R hi,
  }
end

/-- The injective homomorphism `ℚ →+* R`. -/
noncomputable def rat_cast (R: Type*) [comm_ring R] [nontrivial R] [equal_char_zero R] :=
classical.some (to_rat_cast_inj R)

lemma rat_cast_inj (R : Type*) [comm_ring R] [nontrivial R] [equal_char_zero R] :
  function.injective (rat_cast R) :=
classical.some_spec (to_rat_cast_inj R)

-- see Note [coercion into rings]
@[priority 900] noncomputable instance cast_coe {R : Type*} [comm_ring R] [nontrivial R]
  [equal_char_zero R] : has_coe_t ℚ R := ⟨rat_cast R⟩

@[simp, norm_cast] theorem cast_zero {R : Type*} [comm_ring R] [nontrivial R] [equal_char_zero R]:
  ((0 : ℚ) : R) = 0 := ring_hom.map_zero (rat_cast R)

end rat_cast


end equal_char_zero

/-!
### Mixed characteristics
-/

/--
A ring `R` of `char_zero` is of mixed characteristics if it is not of `equal_char_zero`.
i.e. if there exists an ideal `I` such that `R/I` has positive characteristic.
-/
class mixed_char_zero (R : Type*) [comm_ring R] (p : ℕ) : Prop :=
  (char_zero : char_zero R)
  (p_pos : p ≠ 0)
  (residue_char_p : ∃(I : ideal R), (I ≠ ⊤) ∧ char_p (R⧸I) p)
