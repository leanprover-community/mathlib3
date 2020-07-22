/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.group_action_hom
import field_theory.normal
import field_theory.subfield
import ring_theory.polynomial

/-!
# Fixed field under a group action.

This is the basis of the Fundamental Theorem of Galois Theory.
Given a (finite) group `G` that acts on a field `F`, we define `fixed G F`,
the subfield consisting of elements of `F` fixed by every element of `G`.

This subfield is then normal (proved in this file) and separable (TODO), and in addition
if `G` acts faithfully on `F` then `findim (fixed G F) F = fintype.card G` (TODO).

## Main Deifnitions

- `fixed G F`, the subfield consisting of elements of `F` fixed by every element of `G`, where
`G` is a group that acts on `F`.

-/

noncomputable theory
open_locale classical

universes u v w

variables (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] (g : G)

def fixed : set F :=
{ x | ∀ g : G, g • x = x }

def fixed_one : set F :=
{ x | g • x = x }

instance fixed_one.is_subfield : is_subfield (fixed_one G F g) :=
{ zero_mem := smul_zero g,
  add_mem := λ x y hx hy, (smul_add g x y).trans $ congr_arg2 _ hx hy,
  neg_mem := λ x hx, (smul_neg g x).trans $ congr_arg _ hx,
  one_mem := smul_one g,
  mul_mem := λ x y hx hy, (smul_mul' g x y).trans $ congr_arg2 _ hx hy,
  inv_mem := λ x hx, (smul_inv F g x).trans $ congr_arg _ hx }

theorem fixed_eq_Inter_fixed_one : fixed G F = ⋂ g : G, fixed_one G F g :=
set.ext $ λ x, ⟨λ hx, set.mem_Inter.2 $ λ g, hx g, λ hx g, by convert set.mem_Inter.1 hx g⟩

instance fixed.is_subfield : is_subfield (fixed G F) :=
by convert @is_subfield.Inter F _ G (fixed_one G F) _; rw fixed_eq_Inter_fixed_one

instance fixed.is_invariant_subring : is_invariant_subring G (fixed G F) :=
{ smul_mem := λ g x hx g', by rw [hx, hx] }

theorem fixed.smul (g : G) (x : fixed G F) : g • x = x :=
subtype.eq $ x.2 g

theorem fixed.smul_polynomial (g : G) (p : polynomial (fixed G F)) : g • p = p :=
polynomial.induction_on p
  (λ x, by rw [polynomial.smul_C, fixed.smul])
  (λ p q ihp ihq, by rw [smul_add, ihp, ihq])
  (λ n x ih, by rw [smul_mul', polynomial.smul_C, fixed.smul, smul_pow, polynomial.smul_X])

@[priority 1000000000]
instance fixed.algebra : algebra (fixed G F) F :=
algebra.of_subring _

theorem fixed.coe_algebra_map : (algebra_map (fixed G F) F) = is_subring.subtype (fixed G F) :=
rfl

variables [fintype G] (x : F)

def fixed.polynomial : polynomial (fixed G F) :=
(mul_semiring_action.minpoly G F x).to_subring _ $ λ c hc g,
let ⟨hc0, n, hn⟩ := finsupp.mem_frange.1 hc in
hn ▸ mul_semiring_action.minpoly.coeff G F x g n

theorem fixed.polynomial.monic : (fixed.polynomial G F x).monic :=
subtype.eq $ mul_semiring_action.minpoly.monic G F x

theorem fixed.polynomial.eval₂ : polynomial.eval₂ (is_subring.subtype $ fixed G F) x (fixed.polynomial G F x) = 0 :=
mul_semiring_action.minpoly.eval G F x

theorem fixed.is_integral : is_integral (fixed G F) x :=
⟨fixed.polynomial G F x, fixed.polynomial.monic G F x, fixed.polynomial.eval₂ G F x⟩

theorem fixed.polynomial.ne_one : fixed.polynomial G F x ≠ (1 : polynomial (fixed G F)) :=
λ H, have _ := fixed.polynomial.eval₂ G F x,
(one_ne_zero : (1 : F) ≠ 0) $ by rwa [H, polynomial.eval₂_one] at this

theorem fixed.of_eval₂ (f : polynomial (fixed G F))
  (hf : polynomial.eval₂ (is_subring.subtype $ fixed G F) x f = 0) :
  fixed.polynomial G F x ∣ f :=
begin
  rw [← polynomial.map_dvd_map' (is_subring.subtype $ fixed G F),
      fixed.polynomial, polynomial.map_to_subring, mul_semiring_action.minpoly],
  refine fintype.prod_dvd_of_coprime
    (polynomial.pairwise_coprime_X_sub $ mul_action.injective_of_quotient_stabilizer G x)
    (λ y, quotient_group.induction_on y $ λ g, _),
  rw [polynomial.dvd_iff_is_root, polynomial.is_root.def, mul_action.of_quotient_stabilizer_mk,
      polynomial.eval_smul', ← is_invariant_subring.coe_subtype' G (fixed G F),
      ← mul_semiring_action_hom.coe_polynomial, ← mul_semiring_action_hom.map_smul,
      fixed.smul_polynomial, mul_semiring_action_hom.coe_polynomial,
      is_invariant_subring.coe_subtype', polynomial.eval_map, hf, smul_zero]
end

/- Why is this so slow? -/
theorem fixed.polynomial.irreducible_aux (f g : polynomial (fixed G F))
  (hf : f.monic) (hg : g.monic) (hfg : f * g = fixed.polynomial G F x) :
  f = 1 ∨ g = 1 :=
begin
  have hf2 : f ∣ fixed.polynomial G F x,
  { rw ← hfg, exact dvd_mul_right _ _ },
  have hg2 : g ∣ fixed.polynomial G F x,
  { rw ← hfg, exact dvd_mul_left _ _ },
  have := fixed.polynomial.eval₂ G F x,
  rw [← hfg, polynomial.eval₂_mul, mul_eq_zero] at this,
  cases this,
  { right,
    have hf3 : f = fixed.polynomial G F x,
    { exact polynomial.eq_of_monic_of_associated hf (fixed.polynomial.monic G F x)
        (associated_of_dvd_dvd hf2 $ @fixed.of_eval₂ G _ F _ _ _  x f this) },
    rwa [← mul_one (fixed.polynomial G F x), hf3,
        mul_right_inj' (fixed.polynomial.monic G F x).ne_zero] at hfg },
  { left,
    have hg3 : g = fixed.polynomial G F x,
    { exact polynomial.eq_of_monic_of_associated hg (fixed.polynomial.monic G F x)
        (associated_of_dvd_dvd hg2 $ @fixed.of_eval₂ G _ F _ _ _  x g this) },
    rwa [← one_mul (fixed.polynomial G F x), hg3,
        mul_left_inj' (fixed.polynomial.monic G F x).ne_zero] at hfg }
end

theorem fixed.polynomial.irreducible : irreducible (fixed.polynomial G F x) :=
polynomial.irreducible_of_monic
  (fixed.polynomial.monic G F x)
  (fixed.polynomial.ne_one G F x)
  (fixed.polynomial.irreducible_aux G F x)

theorem fixed.polynomial.minimal_polynomial :
  fixed.polynomial G F x = minimal_polynomial (fixed.is_integral G F x) :=
minimal_polynomial.unique' _ (fixed.polynomial.irreducible G F x)
  (fixed.polynomial.eval₂ G F x) (fixed.polynomial.monic G F x)

instance fixed.normal : normal (fixed G F) F :=
λ x, ⟨fixed.is_integral G F x, (polynomial.splits_id_iff_splits _).1 $
by { rw [← fixed.polynomial.minimal_polynomial, fixed.polynomial, fixed.coe_algebra_map,
    polynomial.map_to_subring, mul_semiring_action.minpoly],
  exact polynomial.splits_prod _ (λ _ _, polynomial.splits_X_sub_C _) }⟩
