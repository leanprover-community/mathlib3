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

- `is_domain.split_by_characteristic`: Split a statement over a domain `R` into the three
                                        different cases by characteristic.
- `local_ring.split_by_characteristic`: Split a statement over a local ring `R` into the three
                                        different cases by characteristic.

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
instance char_zero (R : Type*) [comm_ring R] [nontrivial R] [equal_char_zero R] : char_zero R :=
⟨begin
  intros x y h,
  apply (equal_char_zero.residue_char_zero (⊥:ideal R) bot_ne_top).cast_injective,
  replace h := congr_arg (ideal.quotient.mk ⊥) h,
  simp at h,
  exact h,
end⟩

/-!
# Alternative definition
A ring has equal characteristic zero iff there exists an injective homomorphism `ℚ →+* R`.
-/

section rat_cast

theorem of_rat_cast_inj (R : Type*) [comm_ring R] [char_zero R] {i : ℚ →+* R}
  (h_inj : function.injective i) : equal_char_zero R :=
⟨begin
  intros I hI,
  exact { cast_injective :=
    begin
      intros a b h_ab,                     -- Let `a, b ∈ img(ℕ) ⊆ R` with `a ≡ b ∈ R ⧸ I`.
      let c := (a:R) - ↑b,
      have h_c : c ∈ I:=                   -- This means `a - b ∈ I ⊆ R`.
      begin
        apply iff.elim_left ideal.quotient.eq,
        simp only [map_nat_cast],
        exact h_ab,
      end,
      have h_inj_t : ∃d:ℚ, (i d) = c :=    -- But also `a - b ∈ img(ℚ) ⊆ R`
      begin                                -- (i.e. there is a `d:ℚ` such that `i(d) = a - b`).
        use (a:ℚ) - (b:ℚ),                 -- Do the subtraction `a - b` in `ℚ` instead of `ℕ`.
        simp only [map_nat_cast, map_sub],
      end,
      cases h_inj_t with t ht,
      have h_c' : c = 0 ∨ is_unit c :=     -- Either `c := a - b` is zero or a unit in `R`.
      begin                                -- To show this let's assume `c ≠ 0`. We need to show
        rw or_iff_not_imp_left,            -- that `c` is a unit.
        intro h1,                          -- We use that `c = i(t)` and show that `t` is
        rw ←ht,                            -- a unit in `ℚ`.
        have h2 : ¬t = 0 :=
        begin
          by_contradiction h',
          apply h1,
          rw ←ht,
          apply (map_eq_zero_iff i h_inj).elim_right,
          exact h',
        end,
        have h3 : is_unit t := is_unit.mk0 t h2, -- Therefore `i(t)` is a unit, too.
        refine ring_hom.is_unit_map i h3,
      end,
      have h_c_not_unit: ¬(is_unit c) :=  -- If `a-b` is a unit then `I=R`. Contradiction!
      begin
        by_contradiction h_unit,
        have h_is_top := I.eq_top_of_is_unit_mem h_c h_unit,
        contradiction,
      end,
      have h_a_eq_b : (a:R)=↑b :=                -- Therefore `a-b = 0`, i.e. `a=b ∈ R`.
      begin
        refine sub_eq_zero.mp (or.resolve_right h_c' h_c_not_unit),
      end,
      apply @nat.cast_injective R,               -- Using injectivity we conclude `a=b ∈ ℕ`.
      exact h_a_eq_b,                            -- (This uses the instance `char_zero R`)
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
  let I := ideal.span ({n}: set R),
  have hI : (1 : R) ∉ I :=
  begin
    by_contradiction,
    -- `1 ∈ I` means `∃x:x*n = 1`.
    have h2 : ∃(x : R), x * n = 1 :=
    begin
      apply ideal.mem_span_singleton'.1,
      exact h,
    end,
    cases h2 with x hx,
    have hx':= h1 x,
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
  simp only [map_nat_cast] at h2,
  have h3 : n = 0 :=
  begin
    apply h_charzero.cast_injective,
    exact h2,
  end,
  rw h3 at hn,
  have not_hn := lt_irrefl 0,
  contradiction,
end

lemma nat_is_unit_of_pos (R : Type*) [comm_ring R] [equal_char_zero R] {n : ℕ} (hn : 0 < n) :
  is_unit (n:R) :=
begin
  rw is_unit_iff_exists_inv',
  exact nat_inv_exists_of_pos R hn,
end

noncomputable def nat_inv (R : Type*) [comm_ring R] [equal_char_zero R] {n : ℕ} (hn : 0 < n) : R :=
  ↑((nat_is_unit_of_pos R hn).unit)⁻¹

@[simp] lemma nat_inv_mul (R : Type*) [comm_ring R] [equal_char_zero R] {n : ℕ} (hn : 0 < n) :
(nat_inv R hn) * n = 1 := (nat_is_unit_of_pos R hn).coe_inv_mul

@[simp] lemma mul_nat_inv (R : Type*) [comm_ring R] [equal_char_zero R] {n : ℕ} (hn : 0 < n) :
↑n * (nat_inv R hn) = 1 :=
begin
  rw mul_comm,
  exact nat_inv_mul R hn,
end

theorem to_rat_cast_inj (R : Type*) [comm_ring R] [nontrivial R] [equal_char_zero R] :
  ∃ (i : ℚ →+* R), function.injective i :=
begin
  let cast : ℚ →+* R :=
  { to_fun := λx, x.num * (nat_inv R x.pos),
    map_zero' := by simp only [rat.num_zero, int.cast_zero, zero_mul],
    map_one' := by apply mul_nat_inv,
    map_mul' :=
    begin
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
      simp_rw [←int.cast_coe_nat, ←int.cast_mul, ←mul_assoc, ←rat.mul_num_denom_def],
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
    end},
  use cast,
  { intros x y hxy,
    rw ←ring_hom.to_fun_eq_coe at hxy,
    simp at hxy,
    replace hxy := congr_arg (has_mul.mul (x.denom:R)) hxy,
    replace hxy := congr_arg (has_mul.mul (y.denom:R)) hxy,
    have hxy' : (y.denom:R) * (↑(x.denom) * (↑(x.num) * nat_inv R x.pos)) =
      (x.num * y.denom:ℤ) * (nat_inv R x.pos * x.denom) :=
    by {simp only [int.cast_mul, int.cast_coe_nat], ring},
    have hxy'' : (y.denom:R) * (↑(x.denom) * (↑(y.num) * nat_inv R y.pos)) =
      (y.num *x.denom:ℤ) * (nat_inv R y.pos * y.denom) :=
    by {simp only [int.cast_mul, int.cast_coe_nat], ring},
    rw [hxy', hxy''] at hxy,
    clear hxy' hxy'',

    rw nat_inv_mul R x.pos at hxy,
    rw nat_inv_mul R y.pos at hxy,
    repeat {rw mul_one at hxy},

    rw ←@rat.num_denom x,
    rw ←@rat.num_denom y,
    rw rat.mk_eq (int.coe_nat_ne_zero_iff_pos.mpr x.pos) (int.coe_nat_ne_zero_iff_pos.mpr y.pos),

    exact int.cast_injective hxy},
end


/-- Alternative definition of equal characteristic zero, in terms injective `ℚ →+* R`. -/
theorem iff_rat_cast_inj (R : Type*) [comm_ring R] [nontrivial R] :
  equal_char_zero R ↔ ∃ (i : ℚ →+* R), function.injective i :=
begin
  split,
  { introI,
    exact to_rat_cast_inj R},
  { intro h,
    cases h with i hi,
    sorry,
    -- haveI h_char := char_zero_of_injective_algebra_map hi,
    -- exact of_rat_cast_inj R hi}
end

/-- The injective homomorphism `ℚ →+* R`. -/
noncomputable def rat_cast (R: Type*) [comm_ring R] [nontrivial R] [equal_char_zero R] :=
classical.some (to_rat_cast_inj R)

def rat_cast_inj (R: Type*) [comm_ring R] [nontrivial R] [equal_char_zero R] :=
classical.some_spec (to_rat_cast_inj R)

-- see Note [coercion into rings]
@[priority 900] noncomputable instance cast_coe {R : Type*} [comm_ring R] [nontrivial R]
  [equal_char_zero R] : has_coe_t ℚ R := ⟨rat_cast R⟩

@[simp, norm_cast] theorem cast_zero {R : Type*} [comm_ring R] [nontrivial R] [equal_char_zero R] :
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

namespace mixed_char_zero

/--
Reduction to `p` prime: When proving any statement `P` about mixed characteristic rings we
can always assume that `p` is prime.
-/
lemma reduce_to_p_prime (R : Type*) [comm_ring R] (P : Prop):
  (∀(p : ℕ), (mixed_char_zero R p → P)) ↔ (∀(p : ℕ), (nat.prime p → mixed_char_zero R p → P)) :=
begin
  split,
  { intros h q q_prime q_mixed_char,
    exact h q q_mixed_char},
  { intros h q q_mixed_char,
    rcases q_mixed_char.residue_char_p with ⟨I, ⟨hI_ne_top, hI_char⟩⟩,

    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases ideal.exists_le_maximal I hI_ne_top with ⟨M, ⟨hM_max, h_IM⟩⟩,

    let r := ring_char (R ⧸ M),
    resetI,

    have r_pos : r ≠ 0 := begin
      let f_IM := ideal.quotient.factor I M h_IM,
      have q_zero := congr_arg f_IM (char_p.cast_eq_zero (R ⧸ I) q),
      simp only [map_nat_cast, map_zero] at q_zero,
      exact char_p.ne_zero_of_coe_zero (R⧸M) r q_mixed_char.hp q_zero,
    end,
    have r_prime : nat.prime r :=
    or_iff_not_imp_right.1 (char_p.char_is_prime_or_zero (R ⧸ M) r) r_pos,

    apply h r r_prime,
    exact {
      char_zero := q_mixed_char.char_zero,
      hp := nat.prime.ne_zero r_prime,
      residue_char_p := begin
        use M,
        split,
        exact hM_max.ne_top,
        refine ring_char.of_eq rfl,
      end}},

end

/-- Reduction to `I` prime ideal: When proving statements about mixed characteristic rings,
after we reduced to `p` prime, we can assume that the ideal `I` in the definition is prime.-/
lemma reduce_to_prime_ideal (R : Type*) [comm_ring R] {p : ℕ} (hp : nat.prime p):
(∃(I : ideal R), (I ≠ ⊤) ∧ char_p (R ⧸ I) p) ↔ (∃(I : ideal R), (I.is_prime) ∧ char_p (R ⧸ I) p) :=
begin
  split,
  { intro g,
    rcases g with ⟨I, ⟨hI_not_top, hI⟩⟩,
    resetI,

    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases ideal.exists_le_maximal I hI_not_top with ⟨P, ⟨hP_max, hP⟩⟩,

    use P,
    split,
    exact hP_max.is_prime,
    cases char_p.exists (R⧸P) with r hr,
    convert hr,
    resetI,

    have r_dvd_p : r ∣ p := begin
      rw ←char_p.cast_eq_zero_iff (R⧸P) r p,
      let fIm := ideal.quotient.factor I P hP,
      convert congr_arg fIm (char_p.cast_eq_zero (R ⧸ I) p),
      simp,
    end,
    have one_or_p := nat.prime.eq_one_or_self_of_dvd hp r r_dvd_p,  -- here we use that p is prime
    have q := char_p.char_ne_one (R ⧸ P) r,
    rw or_iff_not_imp_left at one_or_p,
    exact (one_or_p q).symm},
  {
    intro g,
    rcases g with ⟨I, ⟨hI_prime, hI⟩⟩,
    use I,
    exact ⟨ideal.is_prime.ne_top hI_prime, hI⟩}
end

end mixed_char_zero


/-!
# Splitting statements into different characteristics
-/

lemma equal_or_mixed_char (R : Type*) [comm_ring R] [g : char_zero R] :
  equal_char_zero R ↔ ¬(∃p, mixed_char_zero R p) :=
begin
  apply iff.intro,
  {
    introI h,
    by_contradiction hp,
    cases hp with p hp,
    rcases hp.residue_char_p with ⟨I, ⟨hI_ne_top, hI_p⟩⟩,
    have hI_zero := @char_p.of_char_zero _ _ _ (equal_char_zero.residue_char_zero I hI_ne_top),
    exact absurd (char_p.eq (R⧸I) hI_p hI_zero) hp.hp},
  { intro h,
    exact ⟨
    begin
      intros I hI_ne_top,
      apply char_p.char_p_to_char_zero _,
      by_cases hr : ring_char (R⧸I) = 0,
      exact ring_char.of_eq hr,
      { by_contradiction h_unused,
        apply h,
        use (ring_char (R ⧸ I)),
        exact {
          char_zero := g,
          hp := hr,
          residue_char_p := ⟨I, ⟨hI_ne_top, ring_char.char_p _⟩⟩}},
    end⟩
  },
end

/--
  Split a `Prop` in characteristic zero into equal and mixed characteristics.
-/
theorem split_equal_mixed_char (R : Type) [comm_ring R] [char_zero R] {P : Prop}
  (h_equal : equal_char_zero R → P)
  (h_mixed : ∀(p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  cases or_iff_not_imp_right.2 (equal_or_mixed_char R).2,
  { -- The case `char(R) = (0,0)`.
    exact h_equal h},
  { -- The case `char(R) = (0,q)`.
    cases h with p h_char,
    rw ←mixed_char_zero.reduce_to_p_prime R P at h_mixed,
    exact h_mixed p h_char}
end

/-- This is the less useful version of the theorem:
Without `is_domain R` or `local_ring R` we have to
consider non-prime characteristics, too.
-/
theorem split_by_characteristic' (R : Type) [comm_ring R] {P : Prop}
  (h1 : ∀(p : ℕ), (p ≠ 0 → char_p R p → P))
  (h2 : equal_char_zero R → P)
  (h3 : ∀(p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  -- There exists a `p:ℕ` such that `char(R) = p`.
  casesI char_p.exists R with p hp,
  by_cases p=0,
  { haveI h0' : char_p R 0 :=
    begin
      rw ←h,
      exact hp,
    end,
    haveI h0 := char_p.char_p_to_char_zero R,
    clear hp h1 h p h0',
    apply split_equal_mixed_char R,
    exact h2,
    exact h3},
  { -- The case `char(R) = p > 0`.
    clear h2 h3,
    apply (h1 p),
    exact h,
    exact hp},
end

theorem is_domain.split_by_characteristic (R : Type) [comm_ring R] [is_domain R] {P : Prop}
  (h1 : ∀(p : ℕ), (nat.prime p → char_p R p → P))
  (h2 : equal_char_zero R → P)
  (h3 : ∀(p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  -- There exists a `p:ℕ` such that `char(R) = p`.
  casesI char_p.exists R with p hp,
  -- The characteristics `p` is either prime or zero.
  cases char_p.char_is_prime_or_zero R p with g g,  -- This uses `is_domain R`.
  { -- The case `char(R) = p > 0`.
    clear h2 h3,
    apply (h1 p),
    exact g,
    exact hp},
  haveI h0' : char_p R 0 :=
  begin
    rw ←g,
    exact hp,
  end,
  haveI h0 := char_p.char_p_to_char_zero R,
  clear hp h1 g p h0',
  apply split_equal_mixed_char R,
  exact h2,
  exact h3,
end

theorem local_ring.split_by_characteristic (R : Type) [comm_ring R] [local_ring R] {P : Prop}
  (h1 : ∀(p : ℕ), (is_prime_pow p → char_p R p → P))
  (h2 : equal_char_zero R → P)
  (h3 : ∀(p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  -- There exists a `p:ℕ` such that `char(R) = p`.
  casesI char_p.exists R with p hp,
  -- The characteristics `p` is either prime or zero.
  cases char_p_zero_or_prime_power R p with g g,  -- This uses `local_ring R`.
  { haveI h0' : char_p R 0 :=
    begin
      rw ←g,
      exact hp,
    end,
    haveI h0 := char_p.char_p_to_char_zero R,
    clear hp h1 g p h0',
    apply split_equal_mixed_char R,
    exact h2,
    exact h3},
  { -- The case `char(R) = p > 0`.
    clear h2 h3,
    apply (h1 p),
    exact g,
    exact hp},
end
