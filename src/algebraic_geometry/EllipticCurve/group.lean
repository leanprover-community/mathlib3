/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebra.direct_sum.basic
import data.zmod.quotient
import group_theory.torsion

/-!
# Group theory lemmas
-/

noncomputable theory
open_locale classical direct_sum

universe u

variables {G H : Type u}

notation n`⬝`G := (pow_monoid_hom n : G →* G).range

----------------------------------------------------------------------------------------------------
/-! ## Group theory -/

/-- `(G ∪ {0})ˣ ≃* G`. -/
def group.with_zero_units [group G] : (with_zero G)ˣ ≃* G :=
{ to_fun    := λ x, (with_zero.ne_zero_iff_exists.mp x.ne_zero).some,
  inv_fun   := λ x,
  ⟨_, _, mul_inv_cancel $ @with_zero.coe_ne_zero _ x, inv_mul_cancel $ @with_zero.coe_ne_zero _ x⟩,
  left_inv  := λ x,
  by simp only [(with_zero.ne_zero_iff_exists.mp x.ne_zero).some_spec, units.mk_coe],
  right_inv := λ x,
  by { rw [← with_zero.coe_inj,
           (with_zero.ne_zero_iff_exists.mp (_ : (with_zero G)ˣ).ne_zero).some_spec],
       refl },
  map_mul'  := λ x y,
  by { rw [← with_zero.coe_inj, with_zero.coe_mul,
           (with_zero.ne_zero_iff_exists.mp (x * y).ne_zero).some_spec,
           (with_zero.ne_zero_iff_exists.mp x.ne_zero).some_spec,
           (with_zero.ne_zero_iff_exists.mp y.ne_zero).some_spec],
       refl } }

variables [comm_group G] [comm_group H]

/-- The map of quotients by powers of an integer induced by a group homomorphism. -/
@[to_additive "The map of quotients by multiples of an integer induced by an additive group
homomorphism."]
def quotient_group.hom_quotient_zpow_of_hom (f : G →* H) (n : ℤ) :
  G ⧸ (zpow_group_hom n : G →* G).range →* H ⧸ (zpow_group_hom n : H →* H).range :=
quotient_group.lift _ ((quotient_group.mk' _).comp f) $
  λ g ⟨h, (hg : h ^ n = g)⟩, (quotient_group.eq_one_iff _).mpr ⟨_, by simpa only [← hg, map_zpow]⟩

@[to_additive]
lemma quotient_group.hom_quotient_zpow_of_hom_inverse (f : G →* H) (f' : H →* G)
  (hf : function.left_inverse f f') (n : ℤ) :
  (quotient_group.hom_quotient_zpow_of_hom f n).comp (quotient_group.hom_quotient_zpow_of_hom f' n)
    = monoid_hom.id _ :=
quotient_group.monoid_hom_ext _ $ monoid_hom.ext $ λ g, congr_arg coe $ hf g

/-- The equivalence of quotients by powers of an integer induced by a group isomorphism. -/
@[to_additive "The equivalence of quotients by multiples of an integer induced by an additive group
isomorphism."]
def quotient_group.equiv_quotient_zpow_of_equiv (e : G ≃* H) (n : ℤ) :
  G ⧸ (zpow_group_hom n : G →* G).range ≃* H ⧸ (zpow_group_hom n : H →* H).range :=
monoid_hom.to_mul_equiv _ _
  (quotient_group.hom_quotient_zpow_of_hom_inverse e.symm e e.left_inv n)
  (quotient_group.hom_quotient_zpow_of_hom_inverse e e.symm e.right_inv n)

variables [group.fg G]

/-- If `G` is finitely generated torsion abelian, then `G` is a direct sum of `ℤ/nℤ`. -/
theorem comm_group.torsion_decomposition (hG : monoid.is_torsion G) :
  ∃ (ι : Type u) [fintype ι] (p : ι → ℤ) (h : ∀ i : ι, p i ≠ 0),
  nonempty $ multiplicative (⨁ i : ι, ℤ ⧸ ℤ ∙ p i) ≃* G :=
sorry

/-- If `G` is finitely generated torsion abelian, then `G` is finite. -/
def comm_group.fintype_of_fg_torsion (hG : monoid.is_torsion G) : fintype G :=
let hG := (comm_group.torsion_decomposition hG).some_spec in
@fintype.of_equiv _ _
  (@fintype.of_equiv _ _
    (@pi.fintype _ _ _ hG.some $ λ n, @fintype.of_equiv _ _
      (@zmod.fintype _ ⟨int.nat_abs_pos_of_ne_zero $ hG.some_spec.some_spec.some n⟩)
      (int.quotient_span_equiv_zmod _).symm.to_equiv)
    (@dfinsupp.equiv_fun_on_fintype _ _ _ hG.some).symm)
  hG.some_spec.some_spec.some_spec.some.to_equiv

/-- If `G` is finitely generated, then `G/Gⁿ` is finite. -/
def quotient_group.fintype_of_fg (n : ℕ) [fact $ 0 < n] : fintype $ G ⧸ (n⬝G) :=
@comm_group.fintype_of_fg_torsion _ _ (quotient_group.fg $ n⬝G) $
  λ g, (is_of_fin_order_iff_pow_eq_one g).mpr ⟨n, _inst_4.elim,
  by { rw [← quotient_group.out_eq' g], exact (quotient_group.eq_one_iff _).mpr ⟨g.out', rfl⟩ }⟩
