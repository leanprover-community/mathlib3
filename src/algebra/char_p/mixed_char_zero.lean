/-
Copyright (c) 2022 Jon Eugster.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import algebra.char_p.algebra
import algebra.char_p.local_ring
import ring_theory.ideal.quotient
import tactic.field_simp
import data.pnat.basic

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

Note that the injectivity is automatically given as `ℚ` is a field and
accessed by `(rat_cast R).injective`.

## Main results

- `equal_char_zero.of_rat_cast`: A ring has equal characteristic zero iff there is an
  injective homomorphism `ℚ →+* R`. This theorem is the backwards direction.
- `split_by_characteristic`: Split a statement over a domain `R` into the three
   different cases by characteristic.
-/

/-!
### Equal characteristics zero
-/

variables (R : Type*) [comm_ring R]

/-- A ring has equal characteristic zero if `char(R⧸I) = 0` for all proper ideals `I ⊂ R`. -/
class equal_char_zero : Prop :=
  (residue_char_zero : ∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I))

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
@[priority 100] instance char_zero [nontrivial R] [equal_char_zero R] :
  char_zero R :=
⟨begin
  intros x y h,
  apply (equal_char_zero.residue_char_zero (⊥:ideal R) bot_ne_top).cast_injective,
  simp_rw [←map_nat_cast (ideal.quotient.mk (⊥ : ideal R)), h],
end⟩

/-!
#### Embedded copy of ℚ
A (nontrivial) ring has equal characteristic zero iff there
exists an injective homomorphism `ℚ →+* R`.

Note: Injectivity is automatically given by `(rat_cast R).injective` as `ℚ` is a field.
-/

section rat_cast

theorem of_rat_cast [char_zero R] (i : ℚ →+* R) : equal_char_zero R :=
⟨λI hI,
  ⟨begin
    intros a b h_ab,
    apply @nat.cast_injective R,
    rw ←sub_eq_zero,

    set c := (a : R) - ↑b with ←c_def,
    rw c_def,
    let d := (a : ℚ) - ↑b,

    have c_eq_cast_d : c = (i d) := by simp,
    rw [c_eq_cast_d, ←map_zero i],
    apply congr_arg i,
    apply not_not.mp (mt (is_unit.mk0 d) _),
    apply mt (ring_hom.is_unit_map i),
    by_contradiction c_unit,
    apply hI,
    apply I.eq_top_of_is_unit_mem _ c_unit,
    rw [←c_eq_cast_d, ←ideal.quotient.eq, map_nat_cast, map_nat_cast, h_ab],
  end⟩⟩

variable [equal_char_zero R]

/-- Equal characteristic zero means every `(n : ℕ+)` is invertible in `R`. -/
lemma pnat_coe_is_unit (n : ℕ+) : is_unit (n : R) :=
begin
  rw is_unit_iff_exists_inv',

  -- Assume `n` is not invertible.
  by_contradiction h,
  rw not_exists at h,

  -- Then `(n)` is a proper ideal in `R`.
  let I := ideal.span ({n} : set R),
  have hI : (1 : R) ∉ I :=
  begin
    by_contradiction one_mem_I,
    cases ideal.mem_span_singleton'.mp one_mem_I with x hx,
    exact absurd hx (h x),
  end,

  -- by assumption `char_zero R⧸(n)` so `n = 0`.
  have h_char_zero : char_zero (R ⧸ I) :=
  equal_char_zero.residue_char_zero I ((ideal.ne_top_iff_one I).mpr hI),
  have n_zero : (n : ℕ) = 0 :=
  begin
    apply h_char_zero.cast_injective,
    rw ←map_nat_cast (ideal.quotient.mk I),
    rw [nat.cast_zero, ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton'],
    use 1,
    simp,
  end,
  exact absurd n_zero (ne_of_gt n.property),
end

-- see Note [coercion into rings]
@[priority 900] noncomputable instance pnat_has_coe : has_coe_t ℕ+ Rˣ :=
⟨λn, (pnat_coe_is_unit R n).unit⟩

/-- `(1 : ℕ+)` lifts to `(1 : Rˣ)`. -/
@[simp, norm_cast] lemma pnat_coe_eq_one : ((1 : ℕ+) : Rˣ) = 1 :=
begin
  change (pnat_coe_is_unit R 1).unit = 1,
  convert is_unit_one_def,
  rw [coe_coe, pnat.one_coe, nat.cast_one],
end

/-- Lifting `(n : ℕ+)` trough `ℕ+ → Rˣ → R` and `ℕ+ → ℕ → R` are the same thing. -/
@[simp, norm_cast] lemma coe_coe_eq_coe_coe (n : ℕ+) : ((n : Rˣ) : R) = ↑n :=
begin
  change ((pnat_coe_is_unit R n).unit : R) = ↑n,
  simp only [is_unit.unit_spec],
end

variable [nontrivial R]

/-- The injective homomorphism `ℚ →+* R`. -/
noncomputable def rat_cast : ℚ →+* R :=
{ to_fun := λx, x.num /ₚ ↑(x.pnat_denom),
  map_zero' := by simp [divp],
  map_one' := by simp [divp],
  map_mul' :=
  begin
    intros a b,
    field_simp,
    simp_rw [←int.cast_coe_nat, ←int.cast_mul],
    rw mul_comm ↑(b.denom),
    assoc_rw rat.mul_num_denom' a b,
  end,
  map_add' :=
  begin
    intros a b,
    field_simp,
    simp_rw [←int.cast_coe_nat, ←int.cast_mul, ←int.cast_add, ←int.cast_mul],
    rw mul_comm ↑(b.denom),
    assoc_rw rat.add_num_denom',
  end }

-- see Note [coercion into rings]
@[priority 900] noncomputable instance cast_coe : has_coe_t ℚ R := ⟨rat_cast R⟩

@[simp, norm_cast] lemma cast_nat (n : ℕ) : ((n : ℚ) : R) = ↑n := map_nat_cast (rat_cast R) n

@[simp, norm_cast] lemma cast_zero : ((0 : ℚ) : R) = 0 := ring_hom.map_zero (rat_cast R)

@[simp, norm_cast] lemma cast_one : ((1 : ℚ) : R) = 1 := ring_hom.map_one (rat_cast R)

end rat_cast

end equal_char_zero

/-!
### Mixed characteristics
-/

/--
A ring `R` of `char_zero` is of mixed characteristics if it does not have equal characteristic,
i.e. if there exists an ideal `I` such that `R/I` has positive characteristic.
-/
class mixed_char_zero (p : ℕ) : Prop :=
  (char_zero : char_zero R)
  (p_pos : p ≠ 0)
  (residue_char_p : ∃ (I : ideal R), (I ≠ ⊤) ∧ char_p (R ⧸ I) p)

namespace mixed_char_zero

/--
Reduction to `p` prime: When proving any statement `P` about mixed characteristic rings we
can always assume that `p` is prime.
-/
lemma reduce_to_p_prime (P : Prop):
  (∀ (p : ℕ), (mixed_char_zero R p → P)) ↔ (∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) :=
begin
  split,
  { intros h q q_prime q_mixed_char,
    exact h q q_mixed_char },
  { intros h q q_mixed_char,
    rcases q_mixed_char.residue_char_p with ⟨I, ⟨hI_ne_top, hI_char⟩⟩,

    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases ideal.exists_le_maximal I hI_ne_top with ⟨M, ⟨hM_max, h_IM⟩⟩,

    let r := ring_char (R ⧸ M),
    resetI,

    have r_pos : r ≠ 0 :=
    begin
      let f_IM := ideal.quotient.factor I M h_IM,
      have q_zero := congr_arg f_IM (char_p.cast_eq_zero (R ⧸ I) q),
      simp only [map_nat_cast, map_zero] at q_zero,
      apply ne_zero_of_dvd_ne_zero q_mixed_char.p_pos,
      exact (char_p.cast_eq_zero_iff (R⧸M) r q).mp q_zero,
    end,
    have r_prime : nat.prime r :=
    or_iff_not_imp_right.1 (char_p.char_is_prime_or_zero (R ⧸ M) r) r_pos,

    apply h r r_prime,
    exact
    { char_zero := q_mixed_char.char_zero,
      p_pos := nat.prime.ne_zero r_prime,
      residue_char_p :=
      begin
        use M,
        split,
        exact hM_max.ne_top,
        refine ring_char.of_eq rfl,
      end }}
end

/-- Reduction to `I` prime ideal: When proving statements about mixed characteristic rings,
after we reduced to `p` prime, we can assume that the ideal `I` in the definition is prime.-/
lemma reduce_to_maximal_ideal {p : ℕ} (hp : nat.prime p) :
  (∃ (I : ideal R), (I ≠ ⊤) ∧ char_p (R ⧸ I) p) ↔
  (∃ (I : ideal R), (I.is_maximal) ∧ char_p (R ⧸ I) p) :=
begin
  split,
  { intro g,
    rcases g with ⟨I, ⟨hI_not_top, hI⟩⟩,
    resetI,

    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases ideal.exists_le_maximal I hI_not_top with ⟨P, ⟨hP_max, hP⟩⟩,

    use P,
    split,
    exact hP_max,
    cases char_p.exists (R ⧸ P) with r hr,
    convert hr,
    resetI,

    have r_dvd_p : r ∣ p := begin
      rw ←char_p.cast_eq_zero_iff (R ⧸ P) r p,
      let fIm := ideal.quotient.factor I P hP,
      convert congr_arg fIm (char_p.cast_eq_zero (R ⧸ I) p),
      simp,
    end,
    have one_or_p := nat.prime.eq_one_or_self_of_dvd hp r r_dvd_p,
    have q := char_p.char_ne_one (R ⧸ P) r,
    rw or_iff_not_imp_left at one_or_p,
    exact (one_or_p q).symm},
  { intro g,
    rcases g with ⟨I, ⟨hI_max, hI⟩⟩,
    use I,
    exact ⟨ideal.is_maximal.ne_top hI_max, hI⟩ }
end

end mixed_char_zero

/-!
# Splitting statements into different characteristics
-/

lemma equal_iff_not_mixed_char [g : char_zero R] :
  equal_char_zero R ↔ ¬(∃ p, mixed_char_zero R p) :=
begin
  apply iff.intro,
  { introI h,
    by_contradiction hp,
    cases hp with p hp,
    rcases hp.residue_char_p with ⟨I, ⟨hI_ne_top, hI_p⟩⟩,
    have hI_zero := @char_p.of_char_zero _ _ _ (equal_char_zero.residue_char_zero I hI_ne_top),
    exact absurd (char_p.eq (R⧸I) hI_p hI_zero) hp.p_pos },
  { intro h,
    exact
    ⟨begin
      intros I hI_ne_top,
      apply char_p.char_p_to_char_zero _,
      by_cases hr : ring_char (R⧸I) = 0,
      exact ring_char.of_eq hr,
      { by_contradiction h_unused,
        apply h,
        use (ring_char (R ⧸ I)),
        exact
        { char_zero := g,
          p_pos := hr,
          residue_char_p := ⟨I, ⟨hI_ne_top, ring_char.char_p _⟩⟩ }},
    end⟩ }
end

lemma equal_or_mixed_char [char_zero R] :
  equal_char_zero R ∨ ∃ p, mixed_char_zero R p :=
or_iff_not_imp_right.mpr (equal_iff_not_mixed_char R).mpr

variable {P : Prop}

/--
  Split a `Prop` in characteristic zero into equal and mixed characteristics.
-/
theorem split_equal_mixed_char [char_zero R]
  (h_equal : equal_char_zero R → P)
  (h_mixed : ∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  cases equal_or_mixed_char R with h h,
  exact h_equal h,
  { cases h with p h_char,
    rw ←mixed_char_zero.reduce_to_p_prime R P at h_mixed,
    exact h_mixed p h_char }
end

/--
  Split a statement by characteristics:

  - Positive characteristic
  - Equal char. zero
  - Mixed char. `(0,p)` with `p` prime
-/
theorem split_by_characteristic
  (h1 : ∀ (p : ℕ), (p ≠ 0 → char_p R p → P))
  (h2 : equal_char_zero R → P)
  (h3 : ∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  casesI char_p.exists R with p hp,
  by_cases p = 0,
  { haveI h0' : char_p R 0 :=
    begin
      rw ←h,
      exact hp,
    end,
    haveI h0 := char_p.char_p_to_char_zero R,
    clear hp h1 h p h0',
    exact split_equal_mixed_char R h2 h3 },
  exact (h1 p) h hp,
end

/-- In a `is_domain R` one can reduce the positive characteristic case to prime `p`.-/
lemma local_ring_split_by_characteristic [is_domain R]
  (h1 : ∀ (p : ℕ), (nat.prime p → char_p R p → P))
  (h2 : equal_char_zero R → P)
  (h3 : ∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  apply split_by_characteristic R _ h2 h3,
  intros p p_pos,
  introI p_char,
  have p_prime := or_iff_not_imp_right.mp (char_p.char_is_prime_or_zero R p) p_pos,
  exact h1 p p_prime p_char,
end

/-- In a `local_ring R` one can reduce the positive characteristic case to prime powers `p`. -/
lemma is_domain_split_by_characteristic [local_ring R]
  (h1 : ∀ (p : ℕ), (is_prime_pow p → char_p R p → P))
  (h2 : equal_char_zero R → P)
  (h3 : ∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  apply split_by_characteristic R _ h2 h3,
  intros p p_pos,
  introI p_char,
  have p_prime := or_iff_not_imp_left.mp (char_p_zero_or_prime_power R p) p_pos,
  exact h1 p p_prime p_char,
end
