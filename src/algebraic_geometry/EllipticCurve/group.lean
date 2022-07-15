/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebra.module.pid
import data.zmod.quotient

/-!
# Group theory lemmas
-/

noncomputable theory
open_locale classical direct_sum

universe u

variables {G H : Type u}

notation n`⬝`G := (pow_monoid_hom n : G →* G).range

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

/-- If `G` is a finitely generated torsion `ℤ`-module, then `G` is finite. -/
def module.fintype_of_fg_torsion [add_comm_group G] [module ℤ G] [module.finite ℤ G]
  (hit : module.is_torsion ℤ G) : fintype G :=
let hG := (module.equiv_direct_sum_of_is_torsion hit).some_spec in
@fintype.of_equiv _ _
  (@fintype.of_equiv _ _
    (@pi.fintype _ _ _ hG.some $ λ i,
      @fintype.of_equiv _ _
        (@zmod.fintype _
          ⟨int.nat_abs_pos_of_ne_zero $ pow_ne_zero (hG.some_spec.some_spec.some_spec.some i) $
            irreducible.ne_zero $ hG.some_spec.some_spec.some i⟩)
        (int.quotient_span_equiv_zmod _).symm.to_equiv)
    (@dfinsupp.equiv_fun_on_fintype _ _ _ hG.some).symm)
  hG.some_spec.some_spec.some_spec.some_spec.some.symm.to_equiv

variables [comm_group G] [hfg : group.fg G]

include hfg

/-- If `G` is a finitely generated torsion abelian group, then `G` is finite. -/
def comm_group.fintype_of_fg_torsion (hit : monoid.is_torsion G) : fintype G :=
@module.fintype_of_fg_torsion _ _ _
  (module.finite.iff_add_group_fg.mpr $ add_group.fg_iff_add_monoid.fg.mpr $
    monoid.fg_iff_add_fg.mp $ group.fg_iff_monoid.fg.mp hfg) $
  add_monoid.is_torsion_iff_is_torsion_int.mp hit

/-- If `G` is finitely generated, then `G/Gⁿ` is finite. -/
def quotient_group.fintype_of_fg (n : ℕ) [fact $ 0 < n] : fintype $ G ⧸ (n⬝G) :=
@comm_group.fintype_of_fg_torsion _ _ (quotient_group.fg $ n⬝G) $
  λ g, (is_of_fin_order_iff_pow_eq_one g).mpr ⟨n, _inst_2.elim,
  by { rw [← quotient_group.out_eq' g], exact (quotient_group.eq_one_iff _).mpr ⟨g.out', rfl⟩ }⟩
