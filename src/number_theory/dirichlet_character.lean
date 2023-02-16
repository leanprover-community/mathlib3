/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import data.zmod.quotient
import ring_theory.roots_of_unity
/-!
## Dirichlet characters
This file defines Dirichlet characters over (ℤ/nℤ)* and then relates them
to multiplicative homomorphisms over ℤ/nℤ for any n divisible by the conductor.

## Main definitions
 * `dirichlet_character`
 * `asso_dirichlet_character`
 * `change_level`
 * `conductor`

## Tags
Dirichlet character
-/

lemma is_unit.unit_mul {α : Type*} [monoid α] {x y : α} (hx : is_unit x) (hy : is_unit y) :
  hx.unit * hy.unit = (hx.mul hy).unit :=
  by { rw ←units.eq_iff, simp [is_unit.unit_spec] }

/-- A Dirichlet character is defined as a monoid homomorphism which is periodic. -/
abbreviation dirichlet_character (R : Type*) [monoid R] (n : ℕ) := units (zmod n) →* units R

open_locale classical

lemma extend_eq_char {R : Type*} [monoid_with_zero R] {n : ℕ}
  (χ : dirichlet_character R n) {x : zmod n} (hx : is_unit x) :
  function.extend (units.coe_hom (zmod n)) ((units.coe_hom R) ∘ χ) 0 x = χ hx.unit :=
begin
  conv_lhs { congr, skip, skip, skip, rw ←is_unit.unit_spec hx, },
  rw ←units.coe_hom_apply, rw function.factors_through.extend_apply _,
  { simp only [units.coe_hom_apply, function.comp_app], },
  { apply function.injective.factors_through,
    exact units.ext, },
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
  ext, by_cases hx : is_unit x,
  { simp_rw asso_dirichlet_character_eq_char' _ hx, rw h, },
  { rw asso_dirichlet_character_eq_zero _ hx, rw asso_dirichlet_character_eq_zero _ hx, },
  end,
λ h, begin
  ext,
  repeat { rw ←asso_dirichlet_character_eq_char _ x, }, rw h,
  end⟩

namespace zmod
@[simp]
lemma cast_hom_self {n : ℕ} : zmod.cast_hom dvd_rfl (zmod n) = ring_hom.id (zmod n) := by simp
end zmod

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
def change_level {m : ℕ} (hm : n ∣ m) : dirichlet_character R n →* dirichlet_character R m :=
{ to_fun := λ ψ, ψ.comp (units.map (zmod.cast_hom hm (zmod n))),
  map_one' := by simp,
  map_mul' := λ ψ₁ ψ₂, monoid_hom.mul_comp _ _ _, }

lemma change_level_def {m : ℕ} (hm : n ∣ m) :
  change_level hm χ = χ.comp (units.map (zmod.cast_hom hm (zmod n))) := rfl

namespace change_level
lemma self : change_level (dvd_refl n) χ = χ := by { rw change_level_def, simp, }

lemma dvd {m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
  change_level (dvd_trans hm hd) χ = change_level hd (change_level hm χ) :=
begin
  repeat { rw change_level_def, },
  rw [monoid_hom.comp_assoc, ←units.map_comp],
  change _ = χ.comp (units.map ↑((zmod.cast_hom hm (zmod n)).comp (zmod.cast_hom hd (zmod m)))),
  congr,
end

lemma asso_dirichlet_character_eq {m : ℕ} (hm : n ∣ m) (a : units (zmod m)) :
  asso_dirichlet_character (change_level hm χ) a = asso_dirichlet_character χ a :=
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
    { rw [units.eq_iff, change_level_def],
      simp only [function.comp_app, monoid_hom.coe_comp, coe_coe], congr,
      rw [←units.eq_iff, units.coe_map, is_unit.unit_spec _, is_unit.unit_spec _], refl, }, },
end

lemma asso_dirichlet_character_eq' {m : ℕ} (hm : n ∣ m) {a : zmod m}
  (ha : is_unit a) : asso_dirichlet_character (change_level hm χ) a =
  asso_dirichlet_character χ a :=
begin
  rw [←is_unit.unit_spec ha, asso_dirichlet_character_eq], congr,
end
end change_level

/-- χ₀ of level d factors through χ of level n if d ∣ n and χ₀ = χ ∘ (zmod n → zmod d). -/
structure factors_through (d : ℕ) : Prop :=
(dvd : d ∣ n)
(ind_char : ∃ χ₀ : dirichlet_character R d, χ = change_level dvd χ₀)

namespace factors_through
lemma spec {d : ℕ} (h : factors_through χ d) :
  χ = change_level h.1 (classical.some (h.ind_char)) := classical.some_spec (h.ind_char)
end factors_through

/-- The set of natural numbers for which a Dirichlet character is periodic. -/
def conductor_set : set ℕ := {x : ℕ | χ.factors_through x}

lemma mem_conductor_set_iff {x : ℕ} : x ∈ χ.conductor_set ↔ χ.factors_through x := iff.refl _

lemma level_mem_conductor_set : n ∈ conductor_set χ := (mem_conductor_set_iff _).2
{ dvd := dvd_rfl,
  ind_char := ⟨χ, (change_level.self χ).symm⟩, }

lemma mem_conductor_set_dvd {x : ℕ} (hx : x ∈ χ.conductor_set) : x ∣ n := hx.1

lemma mem_conductor_set_factors_through {x : ℕ} (hx : x ∈ χ.conductor_set) :
  χ.factors_through x := hx

/-- The minimum natural number n for which a Dirichlet character is periodic.
  The Dirichlet character χ can then alternatively be reformulated on ℤ/nℤ. -/
noncomputable def conductor : ℕ := Inf (conductor_set χ)

lemma nat.le_one {n : ℕ} (h : n ≤ 1) : n = 0 ∨ n = 1 :=
by { cases n, { left, refl, },
  { right, rw nat.succ_le_succ_iff at h, rw le_zero_iff at h, rw h, }, }

namespace conductor
lemma mem_conductor_set : conductor χ ∈ conductor_set χ :=
Inf_mem (set.nonempty_of_mem χ.level_mem_conductor_set)

lemma dvd_lev : χ.conductor ∣ n := (mem_conductor_set χ).1

lemma factors_through : χ.factors_through χ.conductor := mem_conductor_set χ

lemma eq_one (hχ : χ.conductor = 1) : χ = 1 :=
begin
  obtain ⟨h', χ₀, h⟩ := factors_through χ,
  rw h, ext, rw units.eq_iff, rw change_level_def,
  simp only [function.comp_app, monoid_hom.one_apply, monoid_hom.coe_comp],
  convert χ₀.map_one',
  apply subsingleton.elim _ _,
  rw hχ,
  refine fintype.card_le_one_iff_subsingleton.mp _,
  rw [zmod.card_units_eq_totient _, nat.totient_one], exact ne_zero.one ℕ,
end

lemma one (hn : 0 < n) : (1 : dirichlet_character R n).conductor = 1 :=
begin
  suffices : (1 : dirichlet_character R n).conductor ≤ 1,
  { cases nat.le_one this,
    { rw h, exfalso,
      have := factors_through.dvd (factors_through (1 : dirichlet_character R n)),
      rw [h, zero_dvd_iff] at this,
      rw this at hn,
      apply lt_irrefl _ hn, },
    { exact h, }, },
  { refine nat.Inf_le ⟨one_dvd _, 1, _⟩,
    ext,
    rw [units.eq_iff, change_level_def],
    simp only [monoid_hom.one_comp], },
end

variable {χ}
lemma eq_one_iff (hn : 0 < n) : χ = 1 ↔ χ.conductor = 1 :=
⟨λ h, by { rw [h, one hn], }, λ h, by {rw eq_one χ h}⟩

lemma eq_zero_iff_level_eq_zero : χ.conductor = 0 ↔ n = 0 :=
⟨λ h, by {rw ←zero_dvd_iff, convert dvd_lev χ, rw h, },
  λ h, by {rw [conductor, nat.Inf_eq_zero], left, refine ⟨zero_dvd_iff.2 h,
  ⟨change_level (by {rw h}) χ, by { rw [←change_level.dvd _ _ _, change_level.self _], }⟩, ⟩, }⟩
end conductor

/-- A character is primitive if its level is equal to its conductor. -/
def is_primitive : Prop := χ.conductor = n

lemma is_primitive_def : χ.is_primitive ↔ χ.conductor = n := ⟨λ h, h, λ h, h⟩

namespace is_primitive
lemma one : is_primitive (1 : dirichlet_character R 1) := nat.dvd_one.1 (conductor.dvd_lev _)

lemma one_lev_zero : (1 : dirichlet_character R 0).is_primitive :=
begin
  rw [is_primitive_def, conductor, nat.Inf_eq_zero],
  left, rw conductor_set,
  simp only [set.mem_set_of_eq], fconstructor,
  simp only [true_and, zmod.cast_id', id.def, monoid_hom.coe_mk, dvd_zero, coe_coe],
  refine ⟨1, rfl⟩,
end
end is_primitive

lemma conductor_one_dvd (n : ℕ) : conductor (1 : dirichlet_character R 1) ∣ n :=
by { rw (is_primitive_def _).1 is_primitive.one, apply one_dvd _, }

/-- If m = n are positive natural numbers, then zmod m ≃ zmod n. -/
def zmod.mul_equiv {a b : ℕ} (h : a = b) : zmod a ≃* zmod b :=
by { rw h }

/-- If m = n are positive natural numbers, then their Dirichlet character spaces are the same. -/
def equiv {a b : ℕ} (h : a = b) :
  dirichlet_character R a ≃* dirichlet_character R b := by { rw h, }

/-- The primitive character associated to a Dirichlet character. -/
noncomputable def asso_primitive_character : dirichlet_character R χ.conductor :=
  classical.some (conductor.factors_through χ).ind_char

lemma mem_conductor_set_eq_conductor {d : ℕ} (hd : d ∈ χ.conductor_set) :
  χ.conductor ≤ (classical.some hd.2).conductor :=
begin
  apply nat.Inf_le,
  rw conductor_set, simp only [set.mem_set_of_eq, monoid_hom.coe_mk],
  refine ⟨dvd_trans (conductor.dvd_lev _) hd.1,
    (conductor.factors_through (classical.some hd.2)).2.some, _⟩,
  convert factors_through.spec χ hd using 1,
  have : (zmod.cast_hom (dvd_trans (conductor.dvd_lev hd.2.some) hd.1)
    (zmod (classical.some hd.2).conductor) : monoid_hom (zmod n)
    (zmod (classical.some hd.2).conductor)) = ((zmod.cast_hom (conductor.dvd_lev hd.2.some)
    (zmod (classical.some hd.2).conductor)) : monoid_hom (zmod d)
    (zmod (classical.some hd.2).conductor)).comp (zmod.cast_hom hd.1
    (zmod d) : monoid_hom (zmod n) (zmod d)),
  { suffices : (zmod.cast_hom (dvd_trans (conductor.dvd_lev hd.2.some) hd.1)
    (zmod (classical.some hd.2).conductor)) = ((zmod.cast_hom (conductor.dvd_lev hd.2.some)
    (zmod (classical.some hd.2).conductor))).comp (zmod.cast_hom hd.1
    (zmod d)),
    { rw this, refl, },
    { convert ring_hom.ext_zmod _ _, }, },
  rw [change_level_def, this, units.map_comp, ←monoid_hom.comp_assoc],
  congr,
  change change_level _ _ = _,
  convert (factors_through.spec _ _).symm,
end

lemma asso_primitive_character_is_primitive : (χ.asso_primitive_character).is_primitive :=
begin
  by_cases χ.conductor = 0,
  { rw is_primitive_def, conv_rhs { rw h, },
    rw conductor.eq_zero_iff_level_eq_zero, rw h, },
  refine le_antisymm (nat.le_of_dvd (nat.pos_of_ne_zero h) (conductor.dvd_lev _))
  (mem_conductor_set_eq_conductor _ (conductor.mem_conductor_set _)),
end

lemma asso_primitive_character_one (hn : 0 < n) :
  (1 : dirichlet_character R n).asso_primitive_character = 1 :=
begin
  rw conductor.eq_one_iff _,
  { convert (1 : dirichlet_character R n).asso_primitive_character_is_primitive,
    rw conductor.one hn, },
  { rw conductor.one hn, apply nat.one_pos, },
end

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

-- `mul_eq_asso_pri_char` changed to `asso_primitive_conductor_eq`
lemma asso_primitive_conductor_eq {n : ℕ} (χ : dirichlet_character R n) :
  χ.asso_primitive_character.conductor = χ.conductor :=
(is_primitive_def χ.asso_primitive_character).1 (asso_primitive_character_is_primitive χ)

/-- Similar to multiplication of Dirichlet characters, without needing the characters to be
  primitive. -/
noncomputable def mul {m : ℕ} (χ₁ : dirichlet_character R n) (χ₂ : dirichlet_character R m) :=
asso_primitive_character (change_level (dvd_lcm_left n m) χ₁ * change_level (dvd_lcm_right n m) χ₂)

lemma mul_def {n m : ℕ} {χ : dirichlet_character R n} {ψ : dirichlet_character R m} :
  χ.mul ψ = (change_level _ χ * change_level _ ψ).asso_primitive_character := rfl

namespace is_primitive
lemma mul {m : ℕ} (ψ : dirichlet_character R m) : (mul χ ψ).is_primitive :=
asso_primitive_character_is_primitive _
end is_primitive

variables {S : Type*} [comm_ring S] {m : ℕ} (ψ : dirichlet_character S m)

/-- A Dirichlet character is odd if its value at -1 is -1. -/
def is_odd : Prop := ψ (-1) = -1

/-- A Dirichlet character is even if its value at -1 is 1. -/
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
    simp only [units.coe_one, units.coe_neg_one, units.coe_pow], rw neg_one_sq, },
end

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
