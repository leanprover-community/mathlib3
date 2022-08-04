/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster
-/
import algebra.char_p.algebra
import algebra.char_p.local_ring
import ring_theory.ideal.quotient
import tactic.field_simp
import data.pnat.basic

/-!
# Equal and mixed characteristic

A commutative ring of characteristic zero can either be of 'equal characteristic zero'
or of 'mixed characteristic'. 'Equal characteristic zero' means that the quotient
ring `R ⧸ I` has characteristic zero for all proper ideals `I ⊆ R`.
Equivalently, `R` has equal characteristic zero if there is a
ring homomorphism `ℚ →+* R`. If `R` is nontrivial, then this homomorphism is injective,
so `R` contains a copy of `ℚ`.

Mixed characteristic `(0, p)` means `R` has characteristic `0` but there
exists an ideal such that `R ⧸ I` has characteristic `p`. Note that a ring
can be of different mixed characteristic simultaneously, e.g. `ℤ` has mixed
characteristic `(0, p)` for any `p ≠ 0`.

In this document we define equal characteristic zero and provide a theorem to split
into cases by characteristic.

## Main definitions

- `equal_char_zero` : class for a ring to be of 'equal characteristic zero'.
- `mixed_char_zero` : class for a ring to be of 'mixed characteristic zero'.

- `equal_char_zero.rat_cast` : The homomorphism `ℚ →+* R`.

## Main results

- `equal_char_zero.of_rat_cast`: A ring has equal characteristic zero iff there is an
  injective homomorphism `ℚ →+* R`. This theorem is the backwards direction.
- `split_by_characteristic`: Split a statement over a domain `R` into the three
   different cases by characteristic.

## TODO

- Relate mixed characteristic in a local ring to p-adic numbers [number_theory.padics].

-/

/-!
### Equal characteristic zero
-/

variables (R : Type*) [comm_ring R]

/-- A ring has equal characteristic zero if `char(R⧸I) = 0` for all proper ideals `I ⊂ R`. -/
class equal_char_zero : Prop :=
  (residue_char_zero : ∀ (I : ideal R), I ≠ ⊤ → char_zero (R ⧸ I))

/-- This definition is trivial if `R` is a field. -/
lemma field.equal_char_zero (K : Type*) [field K] [h_char : char_zero K] :
  equal_char_zero K :=
⟨begin
  intros I hI,
  replace hI := or_iff_not_imp_right.1 (ideal.eq_bot_or_top I) hI,
  exact
  ⟨begin
    intros x y h,
    apply h_char.cast_injective,
    rw [←I.quot_equiv_of_eq_bot_apply_mk hI ↑x, ←I.quot_equiv_of_eq_bot_apply_mk hI ↑y],
    simp_rw [ideal.quotient.mk_eq_mk, map_nat_cast (ideal.quotient.mk I), h],
  end⟩
end⟩

namespace equal_char_zero

/-- Equal characteristic zero implies `char(R) = 0`. -/
@[priority 100] instance char_zero [nontrivial R] [equal_char_zero R] :
  char_zero R :=
⟨begin
  intros x y h,
  apply (equal_char_zero.residue_char_zero (⊥:ideal R) bot_ne_top).cast_injective,
  simp_rw [←map_nat_cast (ideal.quotient.mk (⊥ : ideal R)), h],
end⟩

/-!
### Embedded copy of ℚ

A ring has equal characteristic zero iff there
exists an injective homomorphism `ℚ →+* R`.

Note: If `R` is nontrivial, then injectivity is automatically given by
`(rat_cast R).injective` as `ℚ` is a field.
-/

section rat_cast

/--  -/
theorem of_rat_cast [char_zero R] (i : ℚ →+* R) : equal_char_zero R :=
⟨λI hI,
  ⟨begin
    intros a b h,
    apply @nat.cast_injective R,
    simp_rw ←map_nat_cast (ideal.quotient.mk I) at h,
    simp_rw ←map_nat_cast i at ⊢ h,
    apply congr_arg,
    rw ←sub_eq_zero at ⊢ h,
    simp_rw ←map_sub at ⊢ h,
    rw ideal.quotient.eq_zero_iff_mem at h,

    -- `i(↑a - ↑b)` is a unit contained in `I`, which contradicts `I ≠ ⊤`.
    by_contradiction h_ne_zero,
    exact absurd (I.eq_top_of_is_unit_mem h (is_unit.map i (is_unit.mk0 _ h_ne_zero))) hI,
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

lemma is_unit_one_def {M : Type*} [monoid M] : (@is_unit_one M _).unit = 1 :=
begin
  have h : is_unit ((1 : Mˣ) : M) := by simp only [units.coe_one, is_unit_one],
  exact h.unit_of_coe_units,
end

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

/-- The injective homomorphism `ℚ →+* R`. -/
noncomputable def rat_cast : ℚ →+* R :=
{ to_fun := λ x, x.num /ₚ ↑(x.pnat_denom),
  map_zero' := by simp [divp],
  map_one' := by simp,
  map_mul' :=
  begin
    intros a b,
    field_simp,
    convert_to (↑((a * b).num * (a.denom) * (b.denom)) : R) = _,
    { simp_rw [int.cast_mul, int.cast_coe_nat],
      ring },
    rw rat.mul_num_denom' a b,
    simp only [int.cast_mul, int.cast_coe_nat],
  end,
  map_add' :=
  begin
    intros a b,
    field_simp,
    convert_to (↑((a + b).num * a.denom * b.denom) : R)  = _,
    { simp_rw [int.cast_mul, int.cast_coe_nat],
      ring },
    rw rat.add_num_denom' a b,
    simp only [int.cast_mul, int.cast_add, int.cast_coe_nat],
  end }

lemma rat_cast_def (x : ℚ) : rat_cast R x = x.num /ₚ ↑(x.pnat_denom) := rfl

-- see Note [coercion into rings]
/--
This instance has priority `< 900` to prioritise `rat.cast_coe` in the case
when `R` is a field of characteristic zero, as this also defines a cast `ℚ → R`.
-/
@[priority 850] noncomputable instance rat_coe : has_coe_t ℚ R := ⟨rat_cast R⟩

@[simp, norm_cast] lemma cast_nat (n : ℕ) : ((n : ℚ) : R) = ↑n := map_nat_cast (rat_cast R) n

@[simp, norm_cast] lemma cast_zero : ((0 : ℚ) : R) = 0 := ring_hom.map_zero (rat_cast R)

@[simp, norm_cast] lemma cast_one : ((1 : ℚ) : R) = 1 := ring_hom.map_one (rat_cast R)

section field

variables (K : Type*) [field K] [char_zero K] [algebra R K]

/--
In the case of a field of characteristic zero we have two coersions `ℚ → K`,
namely `equal_char_zero.rat_cast : ℚ →+* K` and `rat.cast_coe : ℚ → K` (defined
in [data.rat.cast]). This lemma shows that they are the same.
-/
lemma rat_cast_eq_cast_coe (x : ℚ) :
  (@rat_cast _ _ (field.equal_char_zero K)) x =
  @coe _ K (@coe_to_lift _ _ rat.cast_coe) x :=
begin
  rw [rat.cast_def, rat_cast_def],
  rw divp_eq_div,
  simp,
end

lemma field.algebra_map_eq_cast_coe (x : ℚ) :
  (algebra_map R K) ↑x = ↑x :=
begin
  haveI := field.equal_char_zero K,
  rw ←rat_cast_eq_cast_coe K,
  change (algebra_map R K) (x.num /ₚ ↑(x.pnat_denom)) = (x.num /ₚ ↑(x.pnat_denom)),
  simp_rw [divp],
  simp only [map_mul, ring_hom.map_int_cast, ring_hom.map_units_inv,
    coe_coe_eq_coe_coe, coe_coe, map_nat_cast, units.coe_inv],
end

end field

end rat_cast

end equal_char_zero

/-!
### Mixed characteristic
-/

/--
A ring `R` of `char_zero` is of mixed characteristic if it does not have equal characteristic,
i.e. if there exists an ideal `I` such that `R ⧸ I` has positive characteristic.
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
lemma reduce_to_p_prime {P : Prop} :
  (∀ (p : ℕ), (mixed_char_zero R p → P)) ↔ (∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) :=
begin
  split,
  { intros h q q_prime q_mixed_char,
    exact h q q_mixed_char },
  { intros h q q_mixed_char,
    rcases q_mixed_char.residue_char_p with ⟨I, ⟨hI_ne_top, hI_char⟩⟩,

    -- Krull's Thm: There exists a prime ideal `P` such that `I ≤ P`
    rcases ideal.exists_le_maximal I hI_ne_top with ⟨M, ⟨hM_max, h_IM⟩⟩,
    resetI,

    let r := ring_char (R ⧸ M),
    have r_pos : r ≠ 0 :=
    begin
      have q_zero := congr_arg (ideal.quotient.factor I M h_IM) (char_p.cast_eq_zero (R ⧸ I) q),
      simp only [map_nat_cast, map_zero] at q_zero,
      apply ne_zero_of_dvd_ne_zero q_mixed_char.p_pos,
      exact (char_p.cast_eq_zero_iff (R ⧸ M) r q).mp q_zero,
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

/--
Reduction to `I` prime ideal: When proving statements about mixed characteristic rings,
after we reduced to `p` prime, we can assume that the ideal `I` in the definition is prime.
-/
lemma reduce_to_maximal_ideal {p : ℕ} (hp : nat.prime p) :
  (∃ (I : ideal R), (I ≠ ⊤) ∧ char_p (R ⧸ I) p) ↔
  (∃ (I : ideal R), (I.is_maximal) ∧ char_p (R ⧸ I) p) :=
begin
  split,
  { intro g,
    rcases g with ⟨I, ⟨hI_not_top, hI⟩⟩,
    resetI,

    -- Krull's Thm: There exists a prime ideal `M` such that `I ≤ M`.
    rcases ideal.exists_le_maximal I hI_not_top with ⟨M, ⟨hM_max, hM⟩⟩,

    use M,
    split,
    exact hM_max,
    { cases char_p.exists (R ⧸ M) with r hr,
      convert hr,
      resetI,

      have r_dvd_p : r ∣ p :=
      begin
        rw ←char_p.cast_eq_zero_iff (R ⧸ M) r p,
        convert congr_arg (ideal.quotient.factor I M hM) (char_p.cast_eq_zero (R ⧸ I) p),
      end,
      rw eq_comm,
      apply or_iff_not_imp_left.mp (nat.prime.eq_one_or_self_of_dvd hp r r_dvd_p),
      exact char_p.char_ne_one (R ⧸ M) r }},
  { intro g,
    rcases g with ⟨I, ⟨hI_max, hI⟩⟩,
    use I,
    exact ⟨ideal.is_maximal.ne_top hI_max, hI⟩ }
end

end mixed_char_zero

/-!
# Splitting statements into different characteristic
-/

section char_zero

variable [char_zero R]

lemma equal_iff_not_mixed_char :
  equal_char_zero R ↔ ¬(∃ p, mixed_char_zero R p) :=
begin
  split,
  { introI h,
    push_neg,
    intro p,
    by_contradiction hp,
    rcases hp.residue_char_p with ⟨I, ⟨hI_ne_top, hI_p⟩⟩,
    haveI hI_zero := (equal_char_zero.residue_char_zero I hI_ne_top),
    replace hI_zero : char_p (R ⧸ I) 0 := char_p.of_char_zero _,
    exact absurd (char_p.eq (R ⧸ I) hI_p hI_zero) hp.p_pos },
  { intro h,
    push_neg at h,
    exact
    ⟨begin
      intros I hI_ne_top,
      apply char_p.char_p_to_char_zero _,
      cases char_p.exists (R ⧸ I) with p hp,
      cases p,
      exact hp,
      { have h_mixed : mixed_char_zero R p.succ :=
          ⟨infer_instance, p.succ_ne_zero , ⟨I, ⟨hI_ne_top, hp⟩⟩⟩,
        exact absurd h_mixed (h p.succ) },
    end⟩ }
end

lemma equal_or_mixed_char : equal_char_zero R ∨ ∃ p, mixed_char_zero R p :=
or_iff_not_imp_right.mpr (equal_iff_not_mixed_char R).mpr

variable {P : Prop}

/--
  Split a `Prop` in characteristic zero into equal and mixed characteristic.
-/
theorem split_equal_mixed_char
  (h_equal : equal_char_zero R → P)
  (h_mixed : ∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  cases equal_or_mixed_char R with h h,
  exact h_equal h,
  { cases h with p h_char,
    rw ←mixed_char_zero.reduce_to_p_prime R at h_mixed,
    exact h_mixed p h_char }
end

end char_zero

variable {P : Prop}

/--
Split a statement by characteristic:

- Positive characteristic
- Equal char. zero
- Mixed char. `(0, p)` with `p` prime
-/
theorem split_by_characteristic
  (h1 : ∀ (p : ℕ), (p ≠ 0 → char_p R p → P))
  (h2 : equal_char_zero R → P)
  (h3 : ∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  casesI char_p.exists R with p p_char,
  by_cases p = 0,
  { rw h at p_char,
    resetI,
    haveI h0 := char_p.char_p_to_char_zero R,
    exact split_equal_mixed_char R h2 h3 },
  exact h1 p h p_char,
end

/-- In a `is_domain R` one can reduce the positive characteristic case to prime `p`.-/
lemma local_ring_split_by_characteristic [is_domain R]
  (h1 : ∀ (p : ℕ), (nat.prime p → char_p R p → P))
  (h2 : equal_char_zero R → P)
  (h3 : ∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  refine split_by_characteristic R _ h2 h3,
  introsI p p_pos p_char,
  have p_prime := or_iff_not_imp_right.mp (char_p.char_is_prime_or_zero R p) p_pos,
  exact h1 p p_prime p_char,
end

/-- In a `local_ring R` one can reduce the positive characteristic case to prime powers `p`. -/
lemma is_domain_split_by_characteristic [local_ring R]
  (h1 : ∀ (p : ℕ), (is_prime_pow p → char_p R p → P))
  (h2 : equal_char_zero R → P)
  (h3 : ∀ (p : ℕ), (nat.prime p → mixed_char_zero R p → P)) : P :=
begin
  refine split_by_characteristic R _ h2 h3,
  introsI p p_pos p_char,
  have p_prime_pow := or_iff_not_imp_left.mp (char_p_zero_or_prime_power R p) p_pos,
  exact h1 p p_prime_pow p_char,
end
