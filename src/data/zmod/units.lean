/-
Copyright (c) 2023 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan
-/
import data.zmod.basic
import topology.algebra.constructions

/-!
# Properties of units of ℤ/nℤ

This file enlists some properties of units of `zmod n`. We then define a topological structure
(the discrete topology) on `zmod n` for all `n` and consequently on the units.
We also enlist several properties that are helpful with modular arithmetic.

## Main definitions and theorems
 * `zmod.topological_space`
 * `cast_hom_apply'` : a version of `cast_hom_apply` where `R` is explicit
 * `disc_top_units` : giving discrete topology to `units (zmod n)`

## Tags
zmod, units
-/

open zmod nat
namespace zmod
/-- Same as `zmod.cast_hom_apply` with some hypotheses being made explicit. -/
lemma cast_hom_apply' {n : ℕ} (R : Type*) [ring R] {m : ℕ} [char_p R m]
  (h : m ∣ n) (i : zmod n) : (cast_hom h R) i = ↑i := cast_hom_apply i

lemma coe_map_of_dvd {a b : ℕ} (h : a ∣ b) (x : units (zmod b)) :
  is_unit (x : zmod a) :=
begin
  change is_unit ((x : zmod b) : zmod a),
  rw [←zmod.cast_hom_apply' (zmod a) h (x : zmod b), ←ring_hom.coe_monoid_hom, ←units.coe_map],
  apply units.is_unit,
end

lemma is_unit_of_is_coprime_dvd {a b : ℕ} (h : a ∣ b) {x : ℕ} (hx : x.coprime b) :
  is_unit (x : zmod a) :=
begin
  convert_to is_unit ((zmod.unit_of_coprime _ hx : zmod b) : zmod a),
  { rw ←cast_nat_cast h x,
    { congr, },
    { refine zmod.char_p _, }, },
  { apply coe_map_of_dvd h _, },
end

lemma is_unit_mul {a b g : ℕ} (n : ℕ) (h1 : g.coprime a) (h2 : g.coprime b) :
  is_unit (g : zmod (a * b^n)) :=
is_unit_of_is_coprime_dvd dvd_rfl ((coprime.mul_right h1 (coprime.pow_right _ h2)))

lemma cast_inv {a m n : ℕ} (ha : a.coprime n) (h : m ∣ n) :
  (((a : zmod n)⁻¹ : zmod n) : zmod m) = ((a : zmod n) : zmod m)⁻¹ :=
begin
  change ((((zmod.unit_of_coprime a ha)⁻¹ : units (zmod n)) : zmod n) : zmod m) = _,
  have h1 : ∀ c : (zmod m)ˣ, (c : zmod m)⁻¹ = ((c⁻¹ : units (zmod m)) : zmod m),
  { intro c, simp only [inv_coe_unit], },
  rw [← zmod.cast_hom_apply' (zmod m) h _, ← ring_hom.coe_monoid_hom,
    ← units.coe_map_inv _ (zmod.unit_of_coprime a ha), ← h1],
  congr,
end

lemma coprime_of_is_unit {m a : ℕ} (ha : is_unit (a : zmod m)) : a.coprime m :=
begin
  have f := zmod.val_coe_unit_coprime (is_unit.unit ha),
  rw is_unit.unit_spec at f,
  obtain ⟨y, hy⟩ : m ∣ (a - (a : zmod m).val),
  { rw [← zmod.nat_coe_zmod_eq_zero_iff_dvd, nat.cast_sub (zmod.val_le_self _ _), sub_eq_zero],
    cases m,
    { simp only [int.coe_nat_inj'], refl, },
    { rw zmod.nat_cast_val, simp only [zmod.cast_nat_cast'], }, },
  rw nat.sub_eq_iff_eq_add (zmod.val_le_self _ _) at hy,
  rw [hy, add_comm, ← nat.is_coprime_iff_coprime],
  simp only [int.coe_nat_add, int.coe_nat_mul],
  rw [is_coprime.add_mul_left_left_iff, nat.is_coprime_iff_coprime],
  convert zmod.val_coe_unit_coprime (is_unit.unit ha),
end

instance units_fintype {n : ℕ} : fintype (zmod n)ˣ :=
begin
  by_cases n = 0,
  { rw h, refine units_int.fintype, },
  { haveI : ne_zero n := ⟨h⟩,
    apply units.fintype, },
end

lemma is_unit_of_is_unit_mul {m n : ℕ} (x : ℕ) (hx : is_unit (x : zmod (m * n))) :
  is_unit (x : zmod m) :=
begin
  rw is_unit_iff_dvd_one at *,
  cases hx with k hk,
  refine ⟨(k : zmod m), _⟩,
  rw [← zmod.cast_nat_cast (dvd_mul_right m n), ← zmod.cast_mul (dvd_mul_right m n),
   ← hk, zmod.cast_one (dvd_mul_right m n)],
  any_goals { refine zmod.char_p _, },
end

lemma is_unit_of_is_unit_mul' {m n : ℕ} (x : ℕ) (hx : is_unit (x : zmod (m * n))) :
  is_unit (x : zmod n) :=
begin
  rw mul_comm at hx,
  apply is_unit_of_is_unit_mul x hx,
end

open zmod
lemma is_unit_of_is_unit_mul_iff {m n : ℕ} (x : ℕ) : is_unit (x : zmod (m * n)) ↔
  is_unit (x : zmod m) ∧ is_unit (x : zmod n) :=
  ⟨λ h, ⟨is_unit_of_is_unit_mul x h, is_unit_of_is_unit_mul' x h⟩,
   λ ⟨h1, h2⟩, units.is_unit (zmod.unit_of_coprime x (nat.coprime.mul_right
      (coprime_of_is_unit h1) (coprime_of_is_unit h2))), ⟩

lemma not_is_unit_of_not_is_unit_mul {m n x : ℕ} (hx : ¬ is_unit (x : zmod (m * n))) :
  ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) :=
begin
  rw ← not_and_distrib,
  contrapose hx,
  rw not_not at *,
  rw is_unit_of_is_unit_mul_iff,
  refine ⟨hx.1, hx.2⟩,
end

lemma not_is_unit_of_not_is_unit_mul' {m n : ℕ} [ne_zero (m * n)] (x : zmod (m * n))
  (hx : ¬ is_unit x) : ¬ is_unit (x : zmod m) ∨ ¬ is_unit (x : zmod n) :=
begin
  rw [← zmod.cast_id _ x, ← zmod.nat_cast_val] at hx,
  rw [← zmod.nat_cast_val, ← zmod.nat_cast_val],
  apply not_is_unit_of_not_is_unit_mul hx,
end

lemma is_unit_val_of_unit {n k : ℕ} [ne_zero n] (hk : k ∣ n) (u : (zmod n)ˣ) :
  is_unit ((u : zmod n).val : zmod k) :=
by { apply zmod.is_unit_of_is_coprime_dvd hk (coprime_of_is_unit _),
  rw [zmod.nat_cast_val, zmod.cast_id], apply units.is_unit _, }

lemma unit_ne_zero {n : ℕ} [fact (1 < n)] (a : (zmod n)ˣ) : (a : zmod n).val ≠ 0 :=
begin
  intro h,
  rw zmod.val_eq_zero at h,
  have : is_unit (0 : zmod n),
  { rw ← h, simp, },
  rw is_unit_zero_iff at this,
  apply @zero_ne_one _ _ _ _,
  rw this,
  apply_instance,
end

lemma inv_is_unit_of_is_unit {n : ℕ} {u : zmod n} (h : is_unit u) : is_unit u⁻¹ :=
begin
  have h' := is_unit_iff_dvd_one.1 h,
  cases h' with k h',
  rw is_unit_iff_dvd_one,
  refine ⟨u, _⟩,
  rw zmod.inv_mul_of_unit u h,
end
end zmod

/-- Making `zmod` a discrete topological space. -/
def zmod.topological_space (d : ℕ) : topological_space (zmod d) := ⊥

local attribute [instance] zmod.topological_space
instance {n : ℕ} : discrete_topology (zmod n) := ⟨rfl⟩

namespace zmod
@[continuity]
lemma induced_top_cont_inv {n : ℕ} : @continuous _ _ (topological_space.induced
  (units.coe_hom (zmod n)) infer_instance) _ (units.inv : (zmod n)ˣ → zmod n) :=
units.induced_top_cont_inv

instance {k : ℕ} : discrete_topology (zmod k)ˣ := units.discrete_topology_of_discrete

instance discrete_prod_units {m n : ℕ} : discrete_topology (zmod m × zmod n)ˣ :=
units.discrete_prod_units
end zmod
