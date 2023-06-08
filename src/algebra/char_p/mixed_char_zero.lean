/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import algebra.char_p.algebra
import algebra.char_p.local_ring
import ring_theory.ideal.quotient
import tactic.field_simp

/-!
# Equal and mixed characteristic

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In commutative algebra, some statments are simpler when working over a `ℚ`-algebra `R`, in which
case one also says that the ring has "equal characteristic zero". A ring that is not a
`ℚ`-algebra has either positive characteristic or there exists a prime ideal `I ⊂ R` such that
the quotient `R ⧸ I` has positive characteristic `p > 0`. In this case one speaks of
"mixed characteristic `(0, p)`", where `p` is only unique if `R` is local.

Examples of mixed characteristic rings are `ℤ` or the `p`-adic integers/numbers.

This file provides the main theorem `split_by_characteristic` that splits any proposition `P` into
the following three cases:

1) Positive characteristic: `char_p R p` (where `p ≠ 0`)
2) Equal characteristic zero: `algebra ℚ R`
3) Mixed characteristic: `mixed_char_zero R p` (where `p` is prime)

## Main definitions

- `mixed_char_zero` : A ring has mixed characteristic `(0, p)` if it has characteristic zero
  and there exists an ideal such that the quotient `R ⧸ I` has characteristic `p`.

## Main results

- `split_equal_mixed_char` : Split a statement into equal/mixed characteristic zero.

This main theorem has the following three corollaries which include the positive
characteristic case for convenience:

- `split_by_characteristic` : Generally consider positive char `p ≠ 0`.
- `split_by_characteristic_domain` : In a domain we can assume that `p` is prime.
- `split_by_characteristic_local_ring` : In a local ring we can assume that `p` is a prime power.

## TODO

- Relate mixed characteristic in a local ring to p-adic numbers [number_theory.padics].

-/

variables (R : Type*) [comm_ring R]

/-!
### Mixed characteristic
-/

/--
A ring of characteristic zero is of "mixed characteristic `(0, p)`" if there exists an ideal
such that the quotient `R ⧸ I` has caracteristic `p`.

**Remark:** For `p = 0`, `mixed_char R 0` is a meaningless definition as `R ⧸ ⊥ ≅ R` has by
definition always characteristic zero.
One could require `(I ≠ ⊥)` in the definition, but then `mixed_char R 0` would mean something
like `ℤ`-algebra of extension degree `≥ 1` and would be completely independent from
whether something is a `ℚ`-algebra or not (e.g. `ℚ[X]` would satisfy it but `ℚ` wouldn't).
-/
class mixed_char_zero (p : ℕ) : Prop :=
[to_char_zero : char_zero R]
(char_p_quotient : ∃ (I : ideal R), (I ≠ ⊤) ∧ char_p (R ⧸ I) p)

namespace mixed_char_zero

/--
Reduction to `p` prime: When proving any statement `P` about mixed characteristic rings we
can always assume that `p` is prime.
-/
lemma reduce_to_p_prime {P : Prop} :
  (∀ p > 0, mixed_char_zero R p → P) ↔
  (∀ (p : ℕ), p.prime → mixed_char_zero R p → P) :=
begin
  split,
  { intros h q q_prime q_mixed_char,
    exact h q (nat.prime.pos q_prime) q_mixed_char },
  { intros h q q_pos q_mixed_char,
    rcases q_mixed_char.char_p_quotient with ⟨I, hI_ne_top, hI_char⟩,

    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases ideal.exists_le_maximal I hI_ne_top with ⟨M, hM_max, h_IM⟩,
    resetI, -- make `hI_char : char_p (R ⧸ I) q` an instance.

    let r := ring_char (R ⧸ M),
    have r_pos : r ≠ 0,
    { have q_zero := congr_arg (ideal.quotient.factor I M h_IM) (char_p.cast_eq_zero (R ⧸ I) q),
      simp only [map_nat_cast, map_zero] at q_zero,
      apply ne_zero_of_dvd_ne_zero (ne_of_gt q_pos),
      exact (char_p.cast_eq_zero_iff (R ⧸ M) r q).mp q_zero },
    have r_prime : nat.prime r :=
      or_iff_not_imp_right.1 (char_p.char_is_prime_or_zero (R ⧸ M) r) r_pos,
    apply h r r_prime,
    haveI : char_zero R := q_mixed_char.to_char_zero,
    exact ⟨⟨M, hM_max.ne_top, ring_char.of_eq rfl⟩⟩ }
end

/--
Reduction to `I` prime ideal: When proving statements about mixed characteristic rings,
after we reduced to `p` prime, we can assume that the ideal `I` in the definition is maximal.
-/
lemma reduce_to_maximal_ideal {p : ℕ} (hp : nat.prime p) :
  (∃ (I : ideal R), (I ≠ ⊤) ∧ char_p (R ⧸ I) p) ↔
  (∃ (I : ideal R), (I.is_maximal) ∧ char_p (R ⧸ I) p) :=
begin
  split,
  { intro g,
    rcases g with ⟨I, ⟨hI_not_top, hI⟩⟩,

    -- Krull's Thm: There exists a prime ideal `M` such that `I ≤ M`.
    rcases ideal.exists_le_maximal I hI_not_top with ⟨M, ⟨hM_max, hM⟩⟩,

    use M,
    split,
    exact hM_max,
    { cases char_p.exists (R ⧸ M) with r hr,
      convert hr,
      resetI, -- make `hr : char_p (R ⧸ M) r` an instance.

      have r_dvd_p : r ∣ p,
      { rw ←char_p.cast_eq_zero_iff (R ⧸ M) r p,
        convert congr_arg (ideal.quotient.factor I M hM) (char_p.cast_eq_zero (R ⧸ I) p) },
      symmetry,
      apply (nat.prime.eq_one_or_self_of_dvd hp r r_dvd_p).resolve_left,
      exact char_p.char_ne_one (R ⧸ M) r }},
  { rintro ⟨I, hI_max, hI⟩,
    use I,
    exact ⟨ideal.is_maximal.ne_top hI_max, hI⟩ }
end

end mixed_char_zero

/-!
### Equal characteristic zero

A commutative ring `R` has "equal characteristic zero" if it satisfies one of the following
equivalent properties:

1) `R` is a `ℚ`-algebra.
2) The quotient `R ⧸ I` has characteristic zero for any proper ideal `I ⊂ R`.
3) `R` has characteristic zero and does not have mixed characteristic for any prime `p`.

We show `(1) ↔ (2) ↔ (3)`, and most of the following is concerned with constructing
an explicit algebra map `ℚ →+* R` (given by `x ↦ (x.num : R) /ₚ ↑x.pnat_denom`)
for the direction `(1) ← (2)`.

Note: Property `(2)` is denoted as `equal_char_zero` in the statement names below.
-/
section equal_char_zero

/--
`ℚ`-algebra implies equal characteristic.
-/
@[nolint unused_arguments] -- argument `[nontrivial R]` is used in the first line of the proof.
lemma Q_algebra_to_equal_char_zero [nontrivial R] [algebra ℚ R] :
  ∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I) :=
begin
  haveI : char_zero R := algebra_rat.char_zero R,
  intros I hI,
  constructor,
  intros a b h_ab,
  contrapose! hI,
  -- `↑a - ↑b` is a unit contained in `I`, which contradicts `I ≠ ⊤`.
  refine I.eq_top_of_is_unit_mem _ (is_unit.map (algebra_map ℚ R) (is_unit.mk0 (a - b : ℚ) _)),
  { simpa only [← ideal.quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_nat_cast] },
  simpa only [ne.def, sub_eq_zero] using (@nat.cast_injective ℚ _ _).ne hI
end

section construction_of_Q_algebra

/-- Internal: Not intended to be used outside this local construction. -/
lemma equal_char_zero.pnat_coe_is_unit [h : fact (∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I))]
  (n : ℕ+) : is_unit (n : R) :=
begin
  -- `n : R` is a unit iff `(n)` is not a proper ideal in `R`.
  rw ← ideal.span_singleton_eq_top,
  -- So by contrapositive, we should show the quotient does not have characteristic zero.
  apply not_imp_comm.mp (h.elim (ideal.span {n})),
  unfreezingI { intro h_char_zero },
  -- In particular, the image of `n` in the quotient should be nonzero.
  apply (h_char_zero.cast_injective).ne n.ne_zero,
  -- But `n` generates the ideal, so its image is clearly zero.
  rw [←map_nat_cast (ideal.quotient.mk _), nat.cast_zero, ideal.quotient.eq_zero_iff_mem],
  exact ideal.subset_span (set.mem_singleton _)
end

/-- Internal: Not intended to be used outside this local construction. -/
noncomputable instance equal_char_zero.pnat_has_coe_units
  [fact (∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I))] : has_coe_t ℕ+ Rˣ :=
⟨λn, (equal_char_zero.pnat_coe_is_unit R n).unit⟩

/-- Internal: Not intended to be used outside this local construction. -/
lemma equal_char_zero.pnat_coe_units_eq_one [fact (∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I))] :
  ((1 : ℕ+) : Rˣ) = 1 :=
begin
  apply units.ext,
  rw units.coe_one,
  change ((equal_char_zero.pnat_coe_is_unit R 1).unit : R) = 1,
  rw is_unit.unit_spec (equal_char_zero.pnat_coe_is_unit R 1),
  rw [coe_coe, pnat.one_coe, nat.cast_one],
end

/-- Internal: Not intended to be used outside this local construction. -/
lemma equal_char_zero.pnat_coe_units_coe_eq_coe
  [fact (∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I))] (n : ℕ+) :
  ((n : Rˣ) : R) = ↑n :=
begin
  change ((equal_char_zero.pnat_coe_is_unit R n).unit : R) = ↑n,
  simp only [is_unit.unit_spec],
end

/--
Equal characteristic implies `ℚ`-algebra.
-/
noncomputable def equal_char_zero_to_Q_algebra (h : ∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I)) :
  algebra ℚ R :=
by haveI : fact (∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I)) := ⟨h⟩; exact
ring_hom.to_algebra
  { to_fun := λ x, x.num /ₚ ↑(x.pnat_denom),
    map_zero' := by simp [divp],
    map_one' := by simp [equal_char_zero.pnat_coe_units_eq_one],
    map_mul' :=
    begin
      intros a b,
      field_simp,
      repeat { rw equal_char_zero.pnat_coe_units_coe_eq_coe R },
      transitivity (↑((a * b).num * (a.denom) * (b.denom)) : R),
      { simp_rw [int.cast_mul, int.cast_coe_nat, coe_coe, rat.coe_pnat_denom],
        ring },
      rw rat.mul_num_denom' a b,
      simp
    end,
    map_add' :=
    begin
      intros a b,
      field_simp,
      repeat { rw equal_char_zero.pnat_coe_units_coe_eq_coe R },
      transitivity (↑((a + b).num * a.denom * b.denom) : R),
      { simp_rw [int.cast_mul, int.cast_coe_nat, coe_coe, rat.coe_pnat_denom],
        ring },
      rw rat.add_num_denom' a b,
      simp
    end }

end construction_of_Q_algebra

end equal_char_zero

/--
Not mixed characteristic implies equal characteristic.
-/
lemma not_mixed_char_to_equal_char_zero [char_zero R] (h : ∀ p > 0, ¬mixed_char_zero R p) :
  ∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I) :=
begin
  intros I hI_ne_top,
  apply char_p.char_p_to_char_zero _,
  cases char_p.exists (R ⧸ I) with p hp,
  cases p,
  { exact hp },
  { have h_mixed : mixed_char_zero R p.succ := ⟨⟨I, ⟨hI_ne_top, hp⟩⟩⟩,
    exact absurd h_mixed (h p.succ p.succ_pos) }
end

/--
Equal characteristic implies not mixed characteristic.
-/
lemma equal_char_zero_to_not_mixed_char (h : ∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I)) :
  ∀ p > 0, ¬mixed_char_zero R p :=
begin
  intros p p_pos,
  by_contradiction hp_mixed_char,
  rcases hp_mixed_char.char_p_quotient with ⟨I, hI_ne_top, hI_p⟩,
  replace hI_zero : char_p (R ⧸ I) 0 := @char_p.of_char_zero _ _ (h I hI_ne_top),
  exact absurd (char_p.eq (R ⧸ I) hI_p hI_zero) (ne_of_gt p_pos),
end

/--
A ring of characteristic zero has equal characteristic iff it does not
have mixed characteristic for any `p`.
-/
lemma equal_char_zero_iff_not_mixed_char [char_zero R] :
  (∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I)) ↔ (∀ p > 0, ¬mixed_char_zero R p) :=
⟨equal_char_zero_to_not_mixed_char R, not_mixed_char_to_equal_char_zero R⟩

/--
A ring is a `ℚ`-algebra iff it has equal characteristic zero.
-/
theorem Q_algebra_iff_equal_char_zero [nontrivial R] :
  nonempty (algebra ℚ R) ↔ ∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I) :=
begin
  split,
  { intro h_alg,
    haveI h_alg' : algebra ℚ R := h_alg.some,
    apply Q_algebra_to_equal_char_zero },
  { intro h,
    apply nonempty.intro,
    exact equal_char_zero_to_Q_algebra R h }
end

/--
A ring of characteristic zero is not a `ℚ`-algebra iff it has mixed characteristic for some `p`.
-/
theorem not_Q_algebra_iff_not_equal_char_zero [char_zero R] :
  is_empty (algebra ℚ R) ↔ (∃ p > 0, mixed_char_zero R p) :=
begin
  rw ←not_iff_not,
  push_neg,
  rw [not_is_empty_iff, ←equal_char_zero_iff_not_mixed_char],
  apply Q_algebra_iff_equal_char_zero,
end

/-!
# Splitting statements into different characteristic

Statements to split a proof by characteristic. There are 3 theorems here that are very
similar. They only differ in the assumptions we can make on the positive characteristic
case:
Generally we need to consider all `p ≠ 0`, but if `R` is a local ring, we can assume
that `p` is a prime power. And if `R` is a domain, we can even assume that `p` is prime.
-/
section main_statements

variable {P : Prop}

/--
Split a `Prop` in characteristic zero into equal and mixed characteristic.
-/
theorem split_equal_mixed_char [char_zero R]
  (h_equal : algebra ℚ R → P)
  (h_mixed : ∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  by_cases h : ∃ p > 0, mixed_char_zero R p,
  { rcases h with ⟨p, ⟨H, hp⟩⟩,
    rw ←mixed_char_zero.reduce_to_p_prime at h_mixed,
    exact h_mixed p H hp },
  { apply h_equal,
    rw [←not_Q_algebra_iff_not_equal_char_zero, not_is_empty_iff] at h,
    exact h.some },
end

example (n : ℕ) (h : n ≠ 0) :0 < n := zero_lt_iff.mpr h


/-- Split any `Prop` over `R` into the three cases:
- positive characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
theorem split_by_characteristic
  (h_pos : ∀ (p : ℕ), (p ≠ 0 → char_p R p → P))
  (h_equal : algebra ℚ R → P)
  (h_mixed : ∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  cases char_p.exists R with p p_char,
  by_cases p = 0,
  { rw h at p_char,
    resetI, -- make `p_char : char_p R 0` an instance.
    haveI h0 : char_zero R := char_p.char_p_to_char_zero R,
    exact split_equal_mixed_char R h_equal h_mixed },
  exact h_pos p h p_char,
end

/-- In a `is_domain R`, split any `Prop` over `R` into the three cases:
- *prime* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
theorem split_by_characteristic_domain [is_domain R]
  (h_pos : ∀ (p : ℕ), (nat.prime p → char_p R p → P))
  (h_equal : algebra ℚ R → P)
  (h_mixed : ∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  refine split_by_characteristic R _ h_equal h_mixed,
  introsI p p_pos p_char,
  have p_prime : nat.prime p :=
    or_iff_not_imp_right.mp (char_p.char_is_prime_or_zero R p) p_pos,
  exact h_pos p p_prime p_char,
end

/-- In a `local_ring R`, split any `Prop` over `R` into the three cases:
- *prime power* characteristic.
- equal characteristic zero.
- mixed characteristic `(0, p)`.
-/
theorem split_by_characteristic_local_ring [local_ring R]
  (h_pos : ∀ (p : ℕ), (is_prime_pow p → char_p R p → P))
  (h_equal : algebra ℚ R → P)
  (h_mixed : ∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  refine split_by_characteristic R _ h_equal h_mixed,
  introsI p p_pos p_char,
  have p_ppow : is_prime_pow (p : ℕ) :=
    or_iff_not_imp_left.mp (char_p_zero_or_prime_power R p) p_pos,
  exact h_pos p p_ppow p_char,
end

end main_statements
