/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import group_theory.quotient_group
import group_theory.finiteness

/-!
# Group theory lemmas
-/

noncomputable theory

universe u

variables {G H : Type u}

notation n`⬝`G := (zpow_group_hom n : G →* G).range

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

/-- If `ker(G →* H)` and `H` are finite, then `G` is finite. -/
@[to_additive "If `ker(G →+ H)` and `H` are finite, then `G` is finite."]
def group.fintype_of_ker_codom [group G] [group H] {f : G →* H} :
  fintype f.ker → fintype H → fintype G :=
λ hK hH, @fintype.of_equiv _ _
  (@prod.fintype _ _ (@fintype.of_injective _ _ hH _ $ quotient_group.ker_lift_injective f) hK)
  subgroup.group_equiv_quotient_times_subgroup.symm

variables [comm_group G] [comm_group H]

/-- If `G` is finitely generated, then `G/Gⁿ` is finite. -/
@[to_additive "If `G` is finitely generated, then `G/nG` is finite."]
def quotient_group.fintype_of_fg [group.fg G] (n : ℤ) : fintype $ G ⧸ (n⬝G) :=
begin
  sorry
end

/-- If `G ≃* H`, then `G/Gⁿ ≃* H/Hⁿ`. -/
@[to_additive "If `G ≃+ H`, then `G/nG ≃+ H/nH`."]
def quotient_group.quotient_equiv_of_equiv (e : G ≃* H) (n : ℤ) : G ⧸ (n⬝G) ≃* H ⧸ (n⬝H) :=
begin
  have ker_eq_range : (n⬝G) = ((quotient_group.mk' (n⬝H)).comp e.to_monoid_hom).ker :=
  begin
    ext g,
    change (∃ h : G, h ^ n = g) ↔ ↑(e.to_monoid_hom g) = _,
    rw [quotient_group.eq_one_iff],
    change _ ↔ ∃ h : H, h ^ n = e.to_monoid_hom g,
    exact ⟨λ hg, ⟨e.to_monoid_hom hg.some, by rw [← map_zpow, hg.some_spec]⟩,
           λ hg, ⟨e.symm.to_monoid_hom hg.some, by simpa only [← map_zpow, hg.some_spec]
                                                   using e.left_inv g⟩⟩
  end,
  rw [ker_eq_range],
  apply quotient_group.quotient_ker_equiv_of_surjective,
  intro g,
  existsi [e.inv_fun $ quot.out g],
  change ↑(e.to_fun $ e.inv_fun $ quot.out g) = g,
  rw [e.right_inv],
  exact quot.out_eq g
end

----------------------------------------------------------------------------------------------------
