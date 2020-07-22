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
Given a (finite) group `G` that acts on a field `F`, we define `fixed_points G F`,
the subfield consisting of elements of `F` fixed_points by every element of `G`.

This subfield is then normal (proved in this file) and separable (TODO), and in addition
if `G` acts faithfully on `F` then `findim (fixed_points G F) F = fintype.card G` (TODO).

## Main Deifnitions

- `fixed_points G F`, the subfield consisting of elements of `F` fixed_points by every element of `G`, where
`G` is a group that acts on `F`.

-/

noncomputable theory
open_locale classical
open mul_action

universes u v w

variables (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] (g : G)

/-- The subfield fixed_points by one element of the group. -/
def fixed_by : set F :=
{ x | g • x = x }

instance fixed_by.is_subfield : is_subfield (fixed_by G F g) :=
{ zero_mem := smul_zero g,
  add_mem := λ x y hx hy, (smul_add g x y).trans $ congr_arg2 _ hx hy,
  neg_mem := λ x hx, (smul_neg g x).trans $ congr_arg _ hx,
  one_mem := smul_one g,
  mul_mem := λ x y hx hy, (smul_mul' g x y).trans $ congr_arg2 _ hx hy,
  inv_mem := λ x hx, (smul_inv F g x).trans $ congr_arg _ hx }

theorem fixed_eq_Inter_fixed_by : fixed_points G F = ⋂ g : G, fixed_by G F g :=
set.ext $ λ x, ⟨λ hx, set.mem_Inter.2 $ λ g, hx g, λ hx g, by convert set.mem_Inter.1 hx g; refl⟩

instance fixed_points.is_subfield : is_subfield (fixed_points G F) :=
by convert @is_subfield.Inter F _ G (fixed_by G F) _; rw fixed_eq_Inter_fixed_by

instance fixed_points.is_invariant_subring : is_invariant_subring G (fixed_points G F) :=
{ smul_mem := λ g x hx g', by rw [hx, hx] }

theorem fixed_points.smul (g : G) (x : fixed_points G F) : g • x = x :=
subtype.eq $ x.2 g

theorem fixed_points.smul_polynomial (g : G) (p : polynomial (fixed_points G F)) : g • p = p :=
polynomial.induction_on p
  (λ x, by rw [polynomial.smul_C, fixed_points.smul])
  (λ p q ihp ihq, by rw [smul_add, ihp, ihq])
  (λ n x ih, by rw [smul_mul', polynomial.smul_C, fixed_points.smul, smul_pow, polynomial.smul_X])

instance fixed_points.algebra : algebra (fixed_points G F) F :=
algebra.of_subring _

theorem fixed_points.coe_algebra_map :
  (algebra_map (fixed_points G F) F) = is_subring.subtype (fixed_points G F) :=
rfl

variables [fintype G] (x : F)

def fixed_points.polynomial : polynomial (fixed_points G F) :=
(mul_semiring_action.minpoly G F x).to_subring _ $ λ c hc g,
let ⟨hc0, n, hn⟩ := finsupp.mem_frange.1 hc in
hn ▸ mul_semiring_action.minpoly.coeff G F x g n

theorem fixed_points.polynomial.monic : (fixed_points.polynomial G F x).monic :=
subtype.eq $ mul_semiring_action.minpoly.monic G F x

theorem fixed_points.polynomial.eval₂ :
  polynomial.eval₂ (is_subring.subtype $ fixed_points G F) x (fixed_points.polynomial G F x) = 0 :=
mul_semiring_action.minpoly.eval G F x

theorem fixed_points.is_integral : is_integral (fixed_points G F) x :=
⟨fixed_points.polynomial G F x,
fixed_points.polynomial.monic G F x,
fixed_points.polynomial.eval₂ G F x⟩

theorem fixed_points.polynomial.ne_one :
  fixed_points.polynomial G F x ≠ (1 : polynomial (fixed_points G F)) :=
λ H, have _ := fixed_points.polynomial.eval₂ G F x,
(one_ne_zero : (1 : F) ≠ 0) $ by rwa [H, polynomial.eval₂_one] at this

theorem fixed_points.of_eval₂ (f : polynomial (fixed_points G F))
  (hf : polynomial.eval₂ (is_subring.subtype $ fixed_points G F) x f = 0) :
  fixed_points.polynomial G F x ∣ f :=
begin
  rw [← polynomial.map_dvd_map' (is_subring.subtype $ fixed_points G F),
      fixed_points.polynomial, polynomial.map_to_subring, mul_semiring_action.minpoly],
  refine fintype.prod_dvd_of_coprime
    (polynomial.pairwise_coprime_X_sub $ mul_action.injective_of_quotient_stabilizer G x)
    (λ y, quotient_group.induction_on y $ λ g, _),
  rw [polynomial.dvd_iff_is_root, polynomial.is_root.def, mul_action.of_quotient_stabilizer_mk,
      polynomial.eval_smul', ← is_invariant_subring.coe_subtype' G (fixed_points G F),
      ← mul_semiring_action_hom.coe_polynomial, ← mul_semiring_action_hom.map_smul,
      fixed_points.smul_polynomial, mul_semiring_action_hom.coe_polynomial,
      is_invariant_subring.coe_subtype', polynomial.eval_map, hf, smul_zero]
end

/- Why is this so slow? -/
theorem fixed_points.polynomial.irreducible_aux (f g : polynomial (fixed_points G F))
  (hf : f.monic) (hg : g.monic) (hfg : f * g = fixed_points.polynomial G F x) :
  f = 1 ∨ g = 1 :=
begin
  have hf2 : f ∣ fixed_points.polynomial G F x,
  { rw ← hfg, exact dvd_mul_right _ _ },
  have hg2 : g ∣ fixed_points.polynomial G F x,
  { rw ← hfg, exact dvd_mul_left _ _ },
  have := fixed_points.polynomial.eval₂ G F x,
  rw [← hfg, polynomial.eval₂_mul, mul_eq_zero] at this,
  cases this,
  { right,
    have hf3 : f = fixed_points.polynomial G F x,
    { exact polynomial.eq_of_monic_of_associated hf (fixed_points.polynomial.monic G F x)
        (associated_of_dvd_dvd hf2 $ @fixed_points.of_eval₂ G _ F _ _ _  x f this) },
    rwa [← mul_one (fixed_points.polynomial G F x), hf3,
        mul_right_inj' (fixed_points.polynomial.monic G F x).ne_zero] at hfg },
  { left,
    have hg3 : g = fixed_points.polynomial G F x,
    { exact polynomial.eq_of_monic_of_associated hg (fixed_points.polynomial.monic G F x)
        (associated_of_dvd_dvd hg2 $ @fixed_points.of_eval₂ G _ F _ _ _  x g this) },
    rwa [← one_mul (fixed_points.polynomial G F x), hg3,
        mul_left_inj' (fixed_points.polynomial.monic G F x).ne_zero] at hfg }
end

theorem fixed_points.polynomial.irreducible : irreducible (fixed_points.polynomial G F x) :=
polynomial.irreducible_of_monic
  (fixed_points.polynomial.monic G F x)
  (fixed_points.polynomial.ne_one G F x)
  (fixed_points.polynomial.irreducible_aux G F x)

theorem fixed_points.polynomial.minimal_polynomial :
  fixed_points.polynomial G F x = minimal_polynomial (fixed_points.is_integral G F x) :=
minimal_polynomial.unique' _ (fixed_points.polynomial.irreducible G F x)
  (fixed_points.polynomial.eval₂ G F x) (fixed_points.polynomial.monic G F x)

instance fixed_points.normal : normal (fixed_points G F) F :=
λ x, ⟨fixed_points.is_integral G F x, (polynomial.splits_id_iff_splits _).1 $
by { rw [← fixed_points.polynomial.minimal_polynomial, fixed_points.polynomial,
    fixed_points.coe_algebra_map, polynomial.map_to_subring, mul_semiring_action.minpoly],
  exact polynomial.splits_prod _ (λ _ _, polynomial.splits_X_sub_C _) }⟩
