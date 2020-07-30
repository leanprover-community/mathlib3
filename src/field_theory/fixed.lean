/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.group_action_hom
import field_theory.normal
import field_theory.separable
import field_theory.subfield
import ring_theory.polynomial

/-!
# Fixed field under a group action.

This is the basis of the Fundamental Theorem of Galois Theory.
Given a (finite) group `G` that acts on a field `F`, we define `fixed_points G F`,
the subfield consisting of elements of `F` fixed_points by every element of `G`.

This subfield is then normal and separable, and in addition (TODO) if `G` acts faithfully on `F`
then `findim (fixed_points G F) F = fintype.card G`.

## Main Definitions

- `fixed_points G F`, the subfield consisting of elements of `F` fixed_points by every element of `G`, where
`G` is a group that acts on `F`.

-/

noncomputable theory
open_locale classical
open mul_action

universes u v w

variables (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] (g : G)

instance fixed_by.is_subfield : is_subfield (fixed_by G F g) :=
{ zero_mem := smul_zero g,
  add_mem := λ x y hx hy, (smul_add g x y).trans $ congr_arg2 _ hx hy,
  neg_mem := λ x hx, (smul_neg g x).trans $ congr_arg _ hx,
  one_mem := smul_one g,
  mul_mem := λ x y hx hy, (smul_mul' g x y).trans $ congr_arg2 _ hx hy,
  inv_mem := λ x hx, (smul_inv F g x).trans $ congr_arg _ hx }

instance fixed_points.is_subfield : is_subfield (fixed_points G F) :=
by convert @is_subfield.Inter F _ G (fixed_by G F) _; rw fixed_eq_Inter_fixed_by

instance fixed_points.is_invariant_subring : is_invariant_subring G (fixed_points G F) :=
{ smul_mem := λ g x hx g', by rw [hx, hx] }

@[simp] theorem fixed_points.smul (g : G) (x : fixed_points G F) : g • x = x :=
subtype.eq $ x.2 g

-- Why is this so slow?
@[simp] theorem fixed_points.smul_polynomial (g : G) (p : polynomial (fixed_points G F)) : g • p = p :=
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

/-- `fixed_points.minpoly G F x` is the minimal polynomial of `(x : F)` over `fixed_points G F`. -/
def fixed_points.minpoly : polynomial (fixed_points G F) :=
(prod_X_sub_smul G F x).to_subring _ $ λ c hc g,
let ⟨hc0, n, hn⟩ := finsupp.mem_frange.1 hc in
hn ▸ prod_X_sub_smul.coeff G F x g n

theorem fixed_points.minpoly.monic : (fixed_points.minpoly G F x).monic :=
subtype.eq $ prod_X_sub_smul.monic G F x

theorem fixed_points.minpoly.eval₂ :
  polynomial.eval₂ (is_subring.subtype $ fixed_points G F) x (fixed_points.minpoly G F x) = 0 :=
begin
  rw [← prod_X_sub_smul.eval G F x, polynomial.eval₂_eq_eval_map],
  simp [fixed_points.minpoly],
end

theorem fixed_points.is_integral : is_integral (fixed_points G F) x :=
⟨fixed_points.minpoly G F x,
fixed_points.minpoly.monic G F x,
fixed_points.minpoly.eval₂ G F x⟩

theorem fixed_points.minpoly.ne_one :
  fixed_points.minpoly G F x ≠ (1 : polynomial (fixed_points G F)) :=
λ H, have _ := fixed_points.minpoly.eval₂ G F x,
(one_ne_zero : (1 : F) ≠ 0) $ by rwa [H, polynomial.eval₂_one] at this

theorem fixed_points.of_eval₂ (f : polynomial (fixed_points G F))
  (hf : polynomial.eval₂ (is_subring.subtype $ fixed_points G F) x f = 0) :
  fixed_points.minpoly G F x ∣ f :=
begin
  rw [← polynomial.map_dvd_map' (is_subring.subtype $ fixed_points G F),
      fixed_points.minpoly, polynomial.map_to_subring, prod_X_sub_smul],
  refine fintype.prod_dvd_of_coprime
    (polynomial.pairwise_coprime_X_sub $ mul_action.injective_of_quotient_stabilizer G x)
    (λ y, quotient_group.induction_on y $ λ g, _),
  rw [polynomial.dvd_iff_is_root, polynomial.is_root.def, mul_action.of_quotient_stabilizer_mk,
      polynomial.eval_smul', ← is_invariant_subring.coe_subtype_hom' G (fixed_points G F),
      ← mul_semiring_action_hom.coe_polynomial, ← mul_semiring_action_hom.map_smul,
      fixed_points.smul_polynomial, mul_semiring_action_hom.coe_polynomial,
      is_invariant_subring.coe_subtype_hom', polynomial.eval_map, hf, smul_zero]
end

/- Why is this so slow? -/
theorem fixed_points.minpoly.irreducible_aux (f g : polynomial (fixed_points G F))
  (hf : f.monic) (hg : g.monic) (hfg : f * g = fixed_points.minpoly G F x) :
  f = 1 ∨ g = 1 :=
begin
  have hf2 : f ∣ fixed_points.minpoly G F x,
  { rw ← hfg, exact dvd_mul_right _ _ },
  have hg2 : g ∣ fixed_points.minpoly G F x,
  { rw ← hfg, exact dvd_mul_left _ _ },
  have := fixed_points.minpoly.eval₂ G F x,
  rw [← hfg, polynomial.eval₂_mul, mul_eq_zero] at this,
  cases this,
  { right,
    have hf3 : f = fixed_points.minpoly G F x,
    { exact polynomial.eq_of_monic_of_associated hf (fixed_points.minpoly.monic G F x)
        (associated_of_dvd_dvd hf2 $ @fixed_points.of_eval₂ G _ F _ _ _  x f this) },
    rwa [← mul_one (fixed_points.minpoly G F x), hf3,
        mul_right_inj' (fixed_points.minpoly.monic G F x).ne_zero] at hfg },
  { left,
    have hg3 : g = fixed_points.minpoly G F x,
    { exact polynomial.eq_of_monic_of_associated hg (fixed_points.minpoly.monic G F x)
        (associated_of_dvd_dvd hg2 $ @fixed_points.of_eval₂ G _ F _ _ _  x g this) },
    rwa [← one_mul (fixed_points.minpoly G F x), hg3,
        mul_left_inj' (fixed_points.minpoly.monic G F x).ne_zero] at hfg }
end

theorem fixed_points.minpoly.irreducible : irreducible (fixed_points.minpoly G F x) :=
(polynomial.irreducible_of_monic
  (fixed_points.minpoly.monic G F x)
  (fixed_points.minpoly.ne_one G F x)).2
  (fixed_points.minpoly.irreducible_aux G F x)

theorem fixed_points.minpoly.minimal_polynomial :
  fixed_points.minpoly G F x = minimal_polynomial (fixed_points.is_integral G F x) :=
minimal_polynomial.unique' _ (fixed_points.minpoly.irreducible G F x)
  (fixed_points.minpoly.eval₂ G F x) (fixed_points.minpoly.monic G F x)

instance fixed_points.normal : normal (fixed_points G F) F :=
λ x, ⟨fixed_points.is_integral G F x, (polynomial.splits_id_iff_splits _).1 $
by { rw [← fixed_points.minpoly.minimal_polynomial, fixed_points.minpoly,
    fixed_points.coe_algebra_map, polynomial.map_to_subring, prod_X_sub_smul],
  exact polynomial.splits_prod _ (λ _ _, polynomial.splits_X_sub_C _) }⟩

instance fixed_points.separable : is_separable (fixed_points G F) F :=
λ x, ⟨fixed_points.is_integral G F x,
by { rw [← fixed_points.minpoly.minimal_polynomial,
        ← polynomial.separable_map (is_subring.subtype (fixed_points G F)),
        fixed_points.minpoly, polynomial.map_to_subring],
  exact polynomial.separable_prod_X_sub_C_iff.2 (injective_of_quotient_stabilizer G x) }⟩
