/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/

import data.zmod.quotient
import ring_theory.roots_of_unity

/-!
# Dirichlet characters

This file defines Dirichlet characters over (ℤ/nℤ)* and then relates them
to multiplicative homomorphisms over ℤ/nℤ for any n divisible by the conductor.

## Main definitions
 * `dirichlet_character`

## Implementation notes
TODO (optional)

## References
Introduction to Cyclotomic Fields, Washington (Chapter 12, Section 2)

## Tags
p-adic, L-function, Bernoulli measure, Dirichlet character
-/

lemma is_unit.unit_mul {α : Type*} [monoid α] {x y : α} (hx : is_unit x) (hy : is_unit y) :
  hx.unit * hy.unit = (hx.mul hy).unit :=
  by { rw ←units.eq_iff, simp [is_unit.unit_spec] }

/-- A Dirichlet character is defined as a multiplicative homomorphism which is periodic. -/
abbreviation dirichlet_character (R : Type*) [monoid R] (n : ℕ) := units (zmod n) →* units R

open_locale classical

lemma extend_eq_char {R : Type*} [monoid_with_zero R] {n : ℕ}
  (χ : dirichlet_character R n) {x : zmod n} (hx : is_unit x) :
  function.extend (units.coe_hom (zmod n)) ((units.coe_hom R) ∘ χ) 0 x = χ hx.unit :=
begin
  conv_lhs { congr, skip, skip, skip, rw ←is_unit.unit_spec hx, },
  rw ←units.coe_hom_apply, rw function.extend_apply _,
  { simp only [units.coe_hom_apply, function.comp_app], },
  { exact units.ext, },
end

lemma extend_eq_zero {R : Type*} [monoid_with_zero R] {n : ℕ}
  (χ : dirichlet_character R n) {x : zmod n} (hx : ¬ is_unit x) :
  function.extend (units.coe_hom (zmod n)) ((units.coe_hom R) ∘ χ) 0 x = 0 :=
begin
  rw [function.extend_def, dif_neg],
  { simp only [pi.zero_apply], },
  { contrapose hx, rw not_not at *, cases hx with a ha, rw ←ha, apply units.is_unit, },
end

/-- The Dirichlet character on ℤ/nℤ →* R determined by χ, 0 on non-units. -/
noncomputable abbreviation asso_dirichlet_character {R : Type*} [monoid_with_zero R] {n : ℕ}
  (χ : dirichlet_character R n) : zmod n →* R :=
{ to_fun := function.extend (units.coe_hom (zmod n)) ((units.coe_hom R) ∘ χ) 0,
  map_one' := begin
    rw [extend_eq_char _ is_unit_one, units.coe_eq_one],
    convert χ.map_one',
    rw [←units.eq_iff, is_unit.unit_spec, units.coe_one],
  end,
  map_mul' := λ x y, begin
    by_cases is_unit x ∧ is_unit y,
    { rw [extend_eq_char _ (is_unit.mul h.1 h.2), extend_eq_char _ h.1, extend_eq_char _ h.2],
      change (units.coe_hom R) (χ _) = (units.coe_hom R) (χ _) * (units.coe_hom R) (χ _),
      repeat { rw ←monoid_hom.comp_apply _ χ, },
      convert ←monoid_hom.map_mul' (monoid_hom.comp (units.coe_hom R) χ) _ _,
      rw is_unit.unit_mul, },
    { have : ¬ (is_unit (x * y)),
      { contrapose h, rw not_not at *, rw ←is_unit.mul_iff, assumption, },
      rw extend_eq_zero _ this,
      push_neg at h,
      by_cases h' : is_unit x,
      { rw [extend_eq_zero _ (h h'), mul_zero], },
      { rw [extend_eq_zero _ h', zero_mul], }, },
  end, }
-- is it possible to construct monoid_hom.extend?

lemma asso_dirichlet_character_eq_char {R : Type*} [monoid_with_zero R] {n : ℕ}
  (χ : dirichlet_character R n) (a : units (zmod n)) : asso_dirichlet_character χ a = χ a :=
by { convert extend_eq_char χ a.is_unit, rw [←units.eq_iff, (a.is_unit).unit_spec], }

lemma asso_dirichlet_character_eq_char' {R : Type*} [monoid_with_zero R] {n : ℕ}
  (χ : dirichlet_character R n) {a : zmod n} (ha : is_unit a) :
  asso_dirichlet_character χ a = χ ha.unit :=
by { convert extend_eq_char χ ha, }

lemma asso_dirichlet_character_eq_zero {R : Type*} [monoid_with_zero R] {n : ℕ}
  (χ : dirichlet_character R n) {a : zmod n} (ha : ¬ is_unit a) :
  asso_dirichlet_character χ a = 0 :=
by { convert extend_eq_zero χ ha, }

lemma asso_dirichlet_character_eq_iff {R : Type*} [monoid_with_zero R] {n : ℕ}
  (χ : dirichlet_character R n) (ψ : dirichlet_character R n) :
  χ = ψ ↔ asso_dirichlet_character χ = asso_dirichlet_character ψ :=
⟨λ h, begin
  ext, by_cases is_unit x,
  { repeat { convert asso_dirichlet_character_eq_char _ h.unit, }, },
  { repeat { rw asso_dirichlet_character_eq_zero _ h, }, },
  end,
λ h, begin
  ext,
  repeat { rw ←asso_dirichlet_character_eq_char _ x, }, rw h,
  end⟩

namespace dirichlet_character

variables {R : Type*} [comm_monoid_with_zero R] {n : ℕ} (χ : dirichlet_character R n)
--commutativity is needed to define mul, not before that

lemma asso_dirichlet_character_eval_sub (x : zmod n) :
  asso_dirichlet_character χ (n - x) = asso_dirichlet_character χ (-x) :=
by { congr, simp, }

lemma is_periodic (m : ℕ) (hm : n ∣ m) (a : ℤ) :
  asso_dirichlet_character χ (a + m) = asso_dirichlet_character χ a :=
begin
  rw ← zmod.nat_coe_zmod_eq_zero_iff_dvd at hm,
  simp only [hm, add_zero],
end

/-- Extends the Dirichlet character χ of level n to level m, where n ∣ m. -/
def change_level {m : ℕ} (hm : n ∣ m) : dirichlet_character R m :=
χ.comp (units.map (zmod.cast_hom hm (zmod n)))
--χ.comp (zmod.cast_hom hm (zmod n))

lemma change_level_self : χ.change_level (dvd_refl n) = χ :=
by { convert monoid_hom.comp_id _, apply congr_arg2 _ rfl, ext, simp, }

lemma change_level_dvd {m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
  χ.change_level (dvd_trans hm hd) = (χ.change_level hm).change_level hd :=
begin
  repeat { rw change_level, },
  rw monoid_hom.comp_assoc,
  congr,
  rw ←units.map_comp,
  congr,
  change _ = ↑((zmod.cast_hom hm (zmod n)).comp (zmod.cast_hom hd (zmod m))),
  congr,
end

lemma change_level_asso_dirichlet_character_eq {m : ℕ} (hm : n ∣ m) (a : units (zmod m)) :
  asso_dirichlet_character (χ.change_level hm) a = asso_dirichlet_character χ a :=
begin
  rw asso_dirichlet_character_eq_char' _,
  swap, { apply (units.is_unit a), },
  { rw asso_dirichlet_character_eq_char' _,
    swap, { change is_unit ((a : zmod m) : zmod n),
      rw ←zmod.cast_hom_apply (a : zmod m),
      swap 3, { apply zmod.char_p _, },
      swap, { assumption, },
      rw [←ring_hom.coe_monoid_hom, ←units.coe_map _ _],
      apply units.is_unit, },
    { rw [units.eq_iff, change_level],
      simp only [function.comp_app, monoid_hom.coe_comp, coe_coe], congr,
      rw [←units.eq_iff, units.coe_map, is_unit.unit_spec _, is_unit.unit_spec _], refl, }, },
end

lemma change_level_asso_dirichlet_character_eq' {m : ℕ} (hm : n ∣ m) {a : zmod m}
  (ha : is_unit a) : asso_dirichlet_character (χ.change_level hm) a =
  asso_dirichlet_character χ a :=
begin
  rw [←is_unit.unit_spec ha, change_level_asso_dirichlet_character_eq], congr,
end

/-- χ₀ of level d factors through χ of level n if d ∣ n and χ₀ = χ ∘ (zmod n → zmod d). -/
structure factors_through (d : ℕ) : Prop :=
(dvd : d ∣ n)
(ind_char : ∃ χ₀ : dirichlet_character R d, χ = χ₀.change_level dvd)

/-lemma factors_through_dvd (hd : factors_through χ hd) :
  d ∣ n := -/

lemma factors_through_spec {d : ℕ} (h : factors_through χ d) :
  χ = (classical.some (h.ind_char)).change_level h.1 := classical.some_spec (h.ind_char)

/-- The set of natural numbers for which a Dirichlet character is periodic. -/
def conductor_set : set ℕ :=
  {x : ℕ | χ.factors_through x}

lemma mem_conductor_set_iff {x : ℕ} : x ∈ χ.conductor_set ↔ χ.factors_through x := iff.refl _

lemma level_mem_conductor_set : n ∈ conductor_set χ :=
(mem_conductor_set_iff _).2
  { dvd := dvd_rfl,
    ind_char := ⟨χ, (χ.change_level_self).symm⟩, }
--⟨dvd_rfl, λ _, ⟨χ, (χ.change_level_self).symm⟩⟩

lemma mem_conductor_set_dvd {x : ℕ} (hx : x ∈ χ.conductor_set) : x ∣ n := hx.1

lemma mem_conductor_set_factors_through {x : ℕ} (hx : x ∈ χ.conductor_set) :
  χ.factors_through x := hx

/-lemma mem_dvd {d m : ℕ} (h₁ : d ∣ m) (h₂ : m ∣ n)
  (mem : d ∈ conductor_set χ) : m ∈ conductor_set χ :=
begin
  have mem' := mem,
  change factors_through χ d at mem',
  change factors_through χ m,
  have := factors_through_spec d χ mem',
  rcases mem with ⟨h₃, χ₁, h⟩,
  refine ⟨h₂, change_level χ₁ h₁, λ a, _⟩,
  --have h1 : m ∈ χ₁.conductor_set, sorry,
  --convert change_level_asso_dirichlet_character_eq χ₁ h₁ _,
  have u1 : is_unit (a : zmod m), sorry,
  have u2 : is_unit (a : zmod d), sorry,
  convert h a,
  convert asso_dirichlet_character_eq_char _ u1.unit,
  convert asso_dirichlet_character_eq_char _ u2.unit,
  rw change_level, simp,
  congr,
  sorry,
/-  change asso_dirichlet_character χ₁ ((a : zmod m) : zmod d) = _,
  apply congr_arg,
  rw zmod.cast_int_cast h₁, apply_instance,-/
end-/

/-- The minimum natural number n for which a Dirichlet character is periodic.
  The Dirichlet character χ can then alternatively be reformulated on ℤ/nℤ. -/
noncomputable def conductor : ℕ := Inf (conductor_set χ)

lemma mem_conductor : conductor χ ∈ conductor_set χ :=
Inf_mem (set.nonempty_of_mem χ.level_mem_conductor_set)

lemma conductor_dvd : χ.conductor ∣ n := χ.mem_conductor.1

lemma factors_through_conductor : χ.factors_through χ.conductor := χ.mem_conductor

lemma conductor_eq_one (hχ : χ.conductor = 1) : χ = 1 :=
begin
  obtain ⟨h', χ₀, h⟩ := factors_through_conductor χ,
  rw h, ext, rw units.eq_iff, rw change_level,
  simp only [function.comp_app, monoid_hom.one_apply, monoid_hom.coe_comp],
  convert χ₀.map_one',
  apply subsingleton.elim _ _,
  rw hχ,
  refine fintype.card_le_one_iff_subsingleton.mp _,
  rw [zmod.card_units_eq_totient _, nat.totient_one],
end

lemma nat.le_one {n : ℕ} (h : n ≤ 1) : n = 0 ∨ n = 1 :=
by { cases n, { left, refl, },
  { right, rw nat.succ_le_succ_iff at h, rw nat.le_zero_iff at h, rw h, }, }

lemma conductor_one (hn : 0 < n) : (1 : dirichlet_character R n).conductor = 1 :=
begin
  suffices : (1 : dirichlet_character R n).conductor ≤ 1,
  { cases nat.le_one this,
    { rw h, exfalso,
      have := factors_through.dvd (1 : dirichlet_character R n).factors_through_conductor,
      rw h at this, rw zero_dvd_iff at this, rw this at hn, apply lt_irrefl _ hn, },
    { exact h, }, },
  { apply nat.Inf_le,
    refine ⟨one_dvd _, 1, _⟩,
    ext, rw units.eq_iff, rw change_level, simp only [monoid_hom.one_comp], },
end

lemma conductor_eq_one_iff (hn : 0 < n) : χ = 1 ↔ χ.conductor = 1 :=
⟨λ h, by { rw h, rw conductor_one hn, }, λ h, by {rw χ.conductor_eq_one h,}⟩

/-lemma asso_dirichlet_character_eval_add_conductor (m k : ℕ) :
  asso_dirichlet_character χ (m + k * χ.conductor : zmod n) = asso_dirichlet_character χ m :=
begin
  by_cases is_unit (m : zmod n),
  { rw asso_dirichlet_character_eq_char' χ h, },
end -/

/-- A character is primitive if its level is equal to its conductor. -/
def is_primitive : Prop := χ.conductor = n

lemma is_primitive_def : χ.is_primitive ↔ χ.conductor = n := ⟨λ h, h, λ h, h⟩

lemma one_is_primitive : is_primitive (1 : dirichlet_character R 1) :=
nat.dvd_one.1 (conductor_dvd _)

lemma conductor_one_dvd_nat (n : ℕ) : conductor (1 : dirichlet_character R 1) ∣ n :=
by { rw (is_primitive_def _).1 one_is_primitive, apply one_dvd _, }

lemma conductor_zero_eq : (1 : dirichlet_character R 0).is_primitive :=
begin
  rw [is_primitive_def, conductor, nat.Inf_eq_zero],
  left, rw conductor_set,
  simp only [set.mem_set_of_eq], fconstructor,
  simp only [true_and, zmod.cast_id', id.def, monoid_hom.coe_mk, dvd_zero, coe_coe],
  refine ⟨1, rfl⟩,
end

/-- If m = n are positive natural numbers, then zmod m ≃ zmod n. -/
def zmod.mul_equiv {a b : ℕ} (h : a = b) : zmod a ≃* zmod b :=
begin
  rw h,
/-  by_cases h' : b = 0,
  { rw h' at h, rw h, rw h', }, rw h,
  { haveI : fact (0 < b), { apply fact_iff.2 (nat.pos_of_ne_zero h'), },
    haveI : char_p (zmod b) a, { rw h, exact zmod.char_p b, },
    convert (zmod.ring_equiv (zmod b) (by { convert h.symm, rw zmod.card, })).to_mul_equiv, }, -/
end

/-- If m = n are positive natural numbers, then their Dirichlet character spaces are the same. -/
def equiv {a b : ℕ} (h : a = b) :
  dirichlet_character R a ≃* dirichlet_character R b := by { rw h, }
--mul_equiv.monoid_hom_congr (units.map_equiv (zmod.mul_equiv h)) (mul_equiv.refl _)

lemma conductor_eq_zero_iff_level_eq_zero : χ.conductor = 0 ↔ n = 0 :=
⟨λ h, by {rw ←zero_dvd_iff, convert χ.conductor_dvd, rw h, },
  λ h, by {rw [conductor, nat.Inf_eq_zero], left, refine ⟨zero_dvd_iff.2 h,
  begin refine ⟨χ.change_level _, _⟩,
    { rw h, },
    { rw ←change_level_dvd _ _ _,
      rw change_level_self _, }, end⟩, }⟩

lemma zmod_one_mul_hom_subsingleton {R : Type*} [monoid R] {ψ : dirichlet_character R 1} : ψ = 1 :=
begin
  rw monoid_hom.ext_iff, intro x,
  have : x = 1, { rw ←units.eq_iff, exact subsingleton.elim ↑x ↑1, },
  simp only [this, monoid_hom.map_one],
end

/-lemma conductor_eq_one [nontrivial (zmod n)] (hχ : χ.conductor = 1) : (0 : R) = 1 :=
begin
  have mem := χ.factors_through_conductor,
  rw hχ at mem,
  rcases mem with ⟨h1, h'⟩,
  obtain ⟨ψ, h2⟩ := h' h1,
  rw asso_dirichlet_character_eq_iff at h2, rw monoid_hom.ext_iff at h2,
  specialize h2 0,
--  rw eq_comm at h2,
  rw asso_dirichlet_character_eq_zero _ _ at h2,
  { rw h2,
    have unit_zero : is_unit (0 : zmod 1),
    { simp only [fin.zero_eq_one_iff, is_unit_zero_iff], },
    have asso_eq_one : asso_dirichlet_character ψ 0 = 1,
    { convert asso_dirichlet_character_eq_char' ψ (by { convert unit_zero, }),
      have : ψ = 1 := zmod_one_mul_hom_subsingleton,
      rw this,
      simp only [units.coe_one, monoid_hom.one_apply], },
    have : (0 : zmod 1) = ((0 : zmod n) : zmod 1),
    { simp only [eq_iff_true_of_subsingleton], },
    rw this at asso_eq_one,
    rw asso_eq_one at h2, exact h2, },
  { exact not_is_unit_zero, },
end-/

/-lemma conductor_eq [nontrivial R] : (1 : dirichlet_character R n).is_primitive :=
begin
  rw is_primitive_def,
  induction n with d hd,
  { refine conductor_zero_eq, },
  rw eq_iff_le_not_lt,
  refine ⟨nat.le_of_dvd (nat.succ_pos _) (conductor_dvd _), λ h, _⟩,
  have f1 : asso_dirichlet_character (1 : dirichlet_character R d.succ)
    (1 : dirichlet_character R d.succ).conductor = 0,
  { apply asso_dirichlet_character_eq_zero,
    intro h1,
    have h2 : (1 : dirichlet_character R d.succ).conductor.coprime d.succ,
    convert ((zmod.units_equiv_coprime).to_fun h1.unit).prop,
    { sorry, },
--    convert (1 : dirichlet_character R d.succ).conductor.coprime d.scc at h2,
    have h3 := nat.coprime.eq_one_of_dvd h2 (1 : dirichlet_character R d.succ).conductor_dvd,
    sorry, },
  have f2 : asso_dirichlet_character (1 : dirichlet_character R n)
    (1 : dirichlet_character R n).conductor = 1,
  { sorry, },
  rw f1 at f2,
  apply zero_ne_one f2,
end-/

/-- The primitive character associated to a Dirichlet character. -/
noncomputable def asso_primitive_character : dirichlet_character R χ.conductor :=
  classical.some (χ.factors_through_conductor).ind_char

/-lemma change_level_conductor_eq_conductor {m : ℕ} (hm :n ∣ m) :
  (χ.change_level hm).conductor = χ.conductor :=
begin
  suffices : (χ.change_level hm).conductor_set = χ.conductor_set,
  { rw conductor, rw this, refl, },
  ext,
  refine ⟨λ h, _, λ h, ⟨dvd_trans h.1 hm, (h.2).some, λ a, _⟩⟩,
  sorry,
  { by_cases is_unit a,
    { sorry, },
    { rw asso_dirichlet_character_eq_zero _ h,
      rw asso_dirichlet_character_eq_zero _ _,
      contrapose h, rw not_not at *,
      rw zmod.uni }, },
end -/

lemma mem_conductor_set_eq_conductor {d : ℕ} (hd : d ∈ χ.conductor_set) :
  χ.conductor ≤ (classical.some hd.2).conductor :=
begin
  apply nat.Inf_le,
  rw conductor_set, simp only [set.mem_set_of_eq, monoid_hom.coe_mk],
  refine ⟨dvd_trans (conductor_dvd _) hd.1,
    (classical.some hd.2).factors_through_conductor.2.some, _⟩,
  convert factors_through_spec χ hd using 1,
  have : (zmod.cast_hom (dvd_trans (conductor_dvd hd.2.some) hd.1)
    (zmod (classical.some hd.2).conductor) : monoid_hom (zmod n)
    (zmod (classical.some hd.2).conductor)) = ((zmod.cast_hom (conductor_dvd hd.2.some)
    (zmod (classical.some hd.2).conductor)) : monoid_hom (zmod d)
    (zmod (classical.some hd.2).conductor)).comp (zmod.cast_hom hd.1
    (zmod d) : monoid_hom (zmod n) (zmod d)),
  { suffices : (zmod.cast_hom (dvd_trans (conductor_dvd hd.2.some) hd.1)
    (zmod (classical.some hd.2).conductor)) = ((zmod.cast_hom (conductor_dvd hd.2.some)
    (zmod (classical.some hd.2).conductor))).comp (zmod.cast_hom hd.1
    (zmod d)),
    { rw this, refl, },
    { convert ring_hom.ext_zmod _ _, }, },
  rw [change_level, this, units.map_comp, ←monoid_hom.comp_assoc],
  congr,
  change change_level _ _ = _,
  convert (factors_through_spec _ _).symm,
end

lemma asso_primitive_character_is_primitive :
  (χ.asso_primitive_character).is_primitive :=
begin
  by_cases χ.conductor = 0,
  { rw is_primitive_def, conv_rhs { rw h, },
    rw conductor_eq_zero_iff_level_eq_zero, rw h, },
  refine le_antisymm (nat.le_of_dvd (nat.pos_of_ne_zero h) (conductor_dvd _))
  (mem_conductor_set_eq_conductor _ (mem_conductor _)),
end

lemma asso_primitive_character_one (hn : 0 < n) :
  (1 : dirichlet_character R n).asso_primitive_character = 1 :=
begin
  rw conductor_eq_one_iff _ _,
  { convert (1 : dirichlet_character R n).asso_primitive_character_is_primitive,
    rw conductor_one hn, },
  { rw conductor_one hn, apply nat.one_pos, },
end

/-def primitive_dirichlet_character_n (S : Type*) [comm_monoid_with_zero S] (m : ℕ) :
set (dirichlet_character S m) := { χ : dirichlet_character S m | χ.is_primitive}-/

--def primitive_dirichlet_character := ⋃ n : ℕ, (primitive_dirichlet_character_n R n)
--def primitive_dirichlet_character : set.range (λ n : ℕ, primitive_dirichlet_character_n R n)

lemma asso_dirichlet_character_mul (ψ : dirichlet_character R n) :
  asso_dirichlet_character (χ * ψ) = (asso_dirichlet_character χ) * (asso_dirichlet_character ψ) :=
begin
  ext,
  simp only [monoid_hom.mul_apply],
  by_cases is_unit x,
  { repeat { rw asso_dirichlet_character_eq_char' _ h, },
    simp only [monoid_hom.mul_apply, units.coe_mul], },
  { repeat { rw asso_dirichlet_character_eq_zero _ h, }, rw zero_mul, },
end

/-/-- Multiplication of primitive Dirichlet characters χ₁ of level m and χ₂ of level n is the
  primitive character associated to χ₁ * χ₂ of level lcm n m. -/
noncomputable def mul {m : ℕ} {χ₁ : dirichlet_character R n} (h1 : is_primitive χ₁)
  {χ₂ : dirichlet_character R m} (h2 : is_primitive χ₂) :=
asso_primitive_character (change_level χ₁ (dvd_lcm_left n m) * change_level χ₂ (dvd_lcm_right n m))
--can we define this for characters which are not primitive? -/

/-- Similar to multiplication of Dirichlet characters, without needing the characters to be
  primitive. -/
noncomputable def mul {m : ℕ} (χ₁ : dirichlet_character R n) (χ₂ : dirichlet_character R m) :=
asso_primitive_character (change_level χ₁ (dvd_lcm_left n m) * change_level χ₂ (dvd_lcm_right n m))

lemma is_primitive_mul {m : ℕ} (ψ : dirichlet_character R m) : (mul χ ψ).is_primitive :=
asso_primitive_character_is_primitive _

/-- Composition of a Dirichlet character with a multiplicative homomorphism of units. -/
abbreviation comp {S : Type*} [comm_monoid_with_zero S] (f : units R →* units S) :
  dirichlet_character S n := f.comp χ

/-lemma asso_primitive_dir_char_mul (hχ : χ.is_primitive) (a : zmod n) :
  asso_dirichlet_character (mul hχ hχ) a =
  asso_dirichlet_character (χ.asso_primitive_character * χ.asso_primitive_character) a :=
begin

end-/

/-inductive pow {m : ℕ} (hm : 0 < m) (hχ : χ.is_primitive) : ℕ → _
| zero
--| one := χ
| succ := -/

/-lemma is_primitive_pow (hχ : χ.is_primitive) {m : ℕ} (hm : 0 < m) : (χ^m).is_primitive :=
begin
  induction m with d hd,
  { exfalso, simp only [not_lt_zero'] at hm, exact hm, },
  { by_cases d = 0,
    { simp only [hχ, h, pow_one], },
    { rw pow_succ, apply is_primitive_mul, }, },
  sorry,
end-/

/-/-- Reformulating a Dirichlet character modulo an element of the `conductor_set`. -/
abbreviation dirichlet_character_to_zmod {m : ℕ} (mem : m ∈ conductor_set χ) : mul_hom (zmod m) R :=
{ to_fun := λ x, χ.to_monoid_hom (x : ℤ),
  map_mul' := map_mul' χ, }-/

/-/-- Using a multiplicative homomorphism ℤ/mℤ to construct a Dirichlet character having modulus m. -/
abbreviation zmod_to_dirichlet_character {m : ℕ} (χ : mul_hom (zmod m) R) : dirichlet_character R :=
{ to_monoid_hom := mul_hom.comp χ (int.cast_ring_hom (zmod m)).to_monoid_hom,
  periodic := ⟨m, λ a, by simp only [int.coe_cast_ring_hom, int.cast_coe_nat,
    monoid_hom.coe_eq_to_mul_hom, add_zero, int.cast_add, ring_hom.coe_monoid_hom,
    ring_hom.to_monoid_hom_eq_coe, function.comp_app, zmod.nat_cast_self,
    monoid_hom.to_mul_hom_coe, mul_hom.coe_comp]⟩, }-/

/-lemma mem_zmod_to_dirichlet_character {m : ℕ} (χ : mul_hom (zmod m) R) :
  m ∈ conductor_set (zmod_to_dirichlet_character χ) := sorry-/

/-noncomputable instance {R : Type*} [comm_semigroup R] : has_mul (dirichlet_character R) :=
⟨λ f g, begin
    apply zmod_to_dirichlet_character _,
    { exact lcm (conductor f) (conductor g), },
    have : (lcm (conductor f) (conductor g)) ∈ conductor_set g,
    { convert mem_lcm g (conductor f) using 1, rw lcm_comm, },
    refine ⟨λ x, dirichlet_character_to_zmod f (mem_lcm f (conductor g)) x *
      dirichlet_character_to_zmod g this x,
      λ x y, by {rw [mul_hom.map_mul, mul_hom.map_mul, mul_mul_mul_comm]}⟩,
  end,⟩
--should I find an equiv similar to zmod.lift?-/

--open_locale big_operators
/-lemma sum_dirichlet_character {n : ℕ} {S : Type*} [comm_semiring S] --[has_mul S]
  (ψ : dirichlet_character S n) :
  ∑ i in finset.range (conductor ψ).succ, asso_dirichlet_character ψ i = 0 := sorry -/

variables {S : Type*} [comm_ring S] {m : ℕ} (ψ : dirichlet_character S m)

def is_odd : Prop := ψ (-1) = -1

def is_even : Prop := ψ (-1) = 1

lemma is_odd_or_is_even [no_zero_divisors S] : ψ.is_odd ∨ ψ.is_even :=
begin
  suffices : (ψ (-1))^2 = 1,
  { rw ←units.eq_iff at this,
    conv_rhs at this { rw ←one_pow 2 },
    rw ←sub_eq_zero at this,
    simp only [units.coe_one, units.coe_pow] at this,
    rw [sq_sub_sq, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg] at this,
    cases this,
    { left, rw [is_odd, ←units.eq_iff], simp only [this, units.coe_neg_one], },
    { right, rw [is_even, ←units.eq_iff], simp only [this, units.coe_one], }, },
  { rw [←monoid_hom.map_pow, ←monoid_hom.map_one ψ],
    congr, rw units.ext_iff,
    simp only [units.coe_one, units.coe_neg_one, nat.neg_one_sq, units.coe_pow], },
end
-- can conditions on S be relaxed? comm needed for sq_sub_sq, and no_divisors needed for mul_eq_zero

lemma asso_odd_dirichlet_character_eval_neg_one (hψ : ψ.is_odd) :
  asso_dirichlet_character ψ (-1) = -1 :=
begin
  rw is_odd at hψ,
  convert asso_dirichlet_character_eq_char _ (-1),
  rw hψ, simp,
end

lemma asso_even_dirichlet_character_eval_neg_one (hψ : ψ.is_even) :
  asso_dirichlet_character ψ (-1) = 1 :=
begin
  rw is_even at hψ,
  convert asso_dirichlet_character_eq_char _ (-1),
  rw hψ, simp,
end

lemma asso_odd_dirichlet_character_eval_sub (x : zmod m) (hψ : ψ.is_odd) :
  asso_dirichlet_character ψ (m - x) = -(asso_dirichlet_character ψ x) :=
begin
  rw [asso_dirichlet_character_eval_sub, ←neg_one_mul, monoid_hom.map_mul,
    asso_odd_dirichlet_character_eval_neg_one _ hψ],
  simp,
end

lemma asso_even_dirichlet_character_eval_sub (x : zmod m) (hψ : ψ.is_even) :
  asso_dirichlet_character ψ (m - x) = asso_dirichlet_character ψ x :=
begin
  rw [asso_dirichlet_character_eval_sub, ←neg_one_mul, monoid_hom.map_mul,
    asso_even_dirichlet_character_eval_neg_one _ hψ],
  simp,
end

end dirichlet_character
