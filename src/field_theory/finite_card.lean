/-
Copyright (c) 2019 Casper Putz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joey van Langen, Casper Putz
-/

import data.zmod.basic
import linear_algebra.basis
import field_theory.finite
import algebra.geom_sum

universes u
variables (K : Type u) [field K] [fintype K]

namespace finite_field

theorem card (p : ℕ) [char_p K p] : ∃ (n : ℕ+), nat.prime p ∧ fintype.card K = p^(n : ℕ) :=
begin
  haveI hp : fact p.prime := char_p.char_is_prime K p,
  have V : vector_space (zmod p) K, from { .. (zmod.cast_hom p K).to_module },
  obtain ⟨n, h⟩ := @vector_space.card_fintype _ _ _ _ V _ _,
  rw zmod.card at h,
  refine ⟨⟨n, _⟩, hp, h⟩,
  apply or.resolve_left (nat.eq_zero_or_pos n),
  rintro rfl,
  rw nat.pow_zero at h,
  have : (0 : K) = 1, { apply fintype.card_le_one_iff.mp (le_of_eq h) },
  exact absurd this zero_ne_one,
end

theorem card' : ∃ (p : ℕ) (n : ℕ+), nat.prime p ∧ fintype.card K = p^(n : ℕ) :=
let ⟨p, hc⟩ := char_p.exists K in ⟨p, @finite_field.card K _ _ p hc⟩

end finite_field

section
variables {G : Type*} {R : Type*} [group G] [integral_domain R]

open_locale big_operators
open finset

def to_hom_units {G M : Type*} [group G] [monoid M] (f : G →* M) : G →* units M :=
{ to_fun := λ g,
    ⟨f g, f (g⁻¹),
      by rw [← monoid_hom.map_mul, mul_inv_self, monoid_hom.map_one],
      by rw [← monoid_hom.map_mul, inv_mul_self, monoid_hom.map_one]⟩,
  map_one' := units.ext (monoid_hom.map_one _),
  map_mul' := λ _ _, units.ext (monoid_hom.map_mul _ _ _) }

@[simp] lemma coe_to_hom_units {G M : Type*} [group G] [monoid M] (f : G →* M) (g : G):
  (to_hom_units f g : M) = f g := rfl

lemma subtype.property' {α : Type*} {p : α → Prop} (a : subtype p) : p a := a.2

def preimage_equiv {H : Type*} [group H] (f : G →* H) (x y : G) :
  f ⁻¹' {f x} ≃ f ⁻¹' {f y} :=
{ to_fun := λ a, ⟨a * x⁻¹ * y, by simp [show f a = f x, from a.2]⟩,
  inv_fun := λ a, ⟨a * y⁻¹ * x, by simp [show f a = f y, from a.2]⟩,
  left_inv := λ _, by simp,
  right_inv := λ _, by simp }

noncomputable def preimage_equiv_of_mem_range {H : Type*} [group H] (f : G →* H) {x y : H}
  (hx : x ∈ set.range f) (hy : y ∈ set.range f) : f ⁻¹' {x} ≃ f ⁻¹ {y} :=
begin
  cases classical.some_spec hx,
  cases classical.some_spec hy,
  exact preimage_equiv _ _ _
end

lemma sum_subtype {R M : Type*} [add_comm_monoid M]
  {p : R → Prop} {F : fintype (subtype p)} {s : finset R} (h : ∀ x, x ∈ s ↔ p x) {f : R → M} :
  ∑ a in s, f a = ∑ a : subtype p, f a :=
have (∈ s) = p, from set.ext h,
begin
  rw ← sum_attach,
  resetI,
  subst p,
  congr,
  simp [finset.ext]
end
#print sum_subtype

variables [fintype G] [decidable_eq G]
variable (G)
lemma is_cyclic.exists_monoid_generator [is_cyclic G] :
  ∃ x : G, ∀ y : G, y ∈ powers x := sorry

open_locale classical add_monoid

lemma sum_units_subgroup (f : G →* R) (hf : f ≠ 1) : ∑ g : G, f g = 0 :=
let ⟨x, hx⟩ := is_cyclic.exists_monoid_generator (set.range (to_hom_units f)) in
have hx1 : (x : R) - 1 ≠ 0, from sorry,
calc ∑ g : G, f g
    = ∑ g : G, to_hom_units f g : rfl
... = ∑ b : units R in univ.image (to_hom_units f),
      (univ.filter (λ a, to_hom_units f a = b)).card • b :
        sum_comp (coe : units R → R) (to_hom_units f)
... = ∑ b : units R in univ.image (to_hom_units f),
      fintype.card (to_hom_units f ⁻¹' {b}) • b :
  sum_congr rfl (λ b hb, congr_arg2 _ (fintype.card_of_finset' _ (by simp)).symm rfl)
... = ∑ b : units R in univ.image (to_hom_units f),
      fintype.card (to_hom_units f ⁻¹' {x}) • b :
  sum_congr rfl (λ b hb, congr_arg2 _
    (fintype.card_congr (preimage_equiv_of_mem_range _ (by finish) x.2)) rfl)
... = ∑ b : set.range (to_hom_units f),
      fintype.card (to_hom_units f ⁻¹' {x}) • ↑b : sum_subtype (by simp)
... = fintype.card (to_hom_units f ⁻¹' {x}) * ∑ b : set.range (to_hom_units f), (b : R) :
  by simp [mul_sum, add_monoid.smul_eq_mul]
... = (fintype.card (to_hom_units f ⁻¹' {x}) : R) * 0 : (congr_arg2 _ rfl $
  calc ∑ b : set.range (to_hom_units f), (b : R)
      = ∑ n in range (order_of x), x ^ n :
    eq.symm $ sum_bij (λ n _, x ^ n) (by simp) (by simp)
      (λ m n hm hn, pow_injective_of_lt_order_of _ (by simpa using hm) (by simpa using hn))
      (λ b hb, let ⟨n, hn⟩ := hx b in ⟨n % order_of x, mem_range.2 (nat.mod_lt _ (order_of_pos _)),
        by rw [← pow_eq_mod_order_of, hn]⟩)
  ... = 0 : begin
    rw [← domain.mul_right_inj hx1, ← geom_series, geom_sum_mul],
    norm_cast,
    rw [pow_eq_mod_order_of, sub_self, zero_mul]
   end)
... = 0 : mul_zero _

end
