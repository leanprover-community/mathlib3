/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Eric Rodriguez
-/
import group_theory.group_action.quotient
import algebra.big_operators.finprod
import data.finite.card
import algebra.group.conj_finite
/-!
# Class Formula

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open conj_act

open mul_action
open_locale big_operators
variables (G : Type*) [group G] {M : Type*} [monoid M]

lemma carrier_eq_orbit (g : G) : (conj_classes.mk g).carrier = orbit (conj_act G) g :=
begin
  ext h,
  rw [conj_classes.mem_carrier_iff_mk_eq, conj_classes.mk_eq_mk_iff_is_conj, mem_orbit_conj_act_iff]
end

lemma card_carrier (g : G) [fintype G] [fintype $ (conj_classes.mk g).carrier]
  [fintype $ stabilizer (conj_act G) g] : fintype.card (conj_classes.mk g).carrier =
    fintype.card (conj_act G) / fintype.card (stabilizer (conj_act G) g) :=
begin
  classical,
  rw [← card_orbit_mul_card_stabilizer_eq_card_group (conj_act G) g, nat.mul_div_cancel],
  simp_rw [carrier_eq_orbit],
  exact fintype.card_pos_iff.mpr infer_instance
end

lemma class_equation' [fintype (conj_classes G)] [∀ x : conj_classes G, fintype (x.carrier)]
  [fintype G] : ∑ x : conj_classes G, x.carrier.to_finset.card = fintype.card G :=
begin
  let e : quotient (orbit_rel (conj_act G) G) ≃ conj_classes G :=
  quotient.congr_right (λ g h, mem_orbit_conj_act_iff g h),
  letI : fintype (quotient (orbit_rel (conj_act G) G)) := by { classical, apply_instance },
  rw ← e.sum_comp,
  classical,
  rw card_eq_sum_card_group_div_card_stabilizer (conj_act G) G,
  refine finset.sum_congr rfl _,
  rintro ⟨g⟩ -,
  rw [← card_orbit_mul_card_stabilizer_eq_card_group (conj_act G) (quotient.out' (quot.mk _ g)),
    nat.mul_div_cancel, fintype.card_of_finset],
  swap, { rw fintype.card_pos_iff, apply_instance },
  intro h,
  simp only [mem_orbit_conj_act_iff, ←conj_classes.mk_eq_mk_iff_is_conj, set.mem_to_finset,
             conj_classes.mem_carrier_iff_mk_eq],
  refine eq_iff_eq_cancel_left.2 (conj_classes.mk_eq_mk_iff_is_conj.2 (_ : is_conj g _)),
  rw [← mem_orbit_conj_act_iff, ← orbit_rel_r_apply],
  apply quotient.exact',
  rw [quotient.out_eq'],
  refl
end

alias is_conj.is_conj.eq_of_mem_center_right ← is_conj.eq_of_mem_center_right
alias is_conj.is_conj.eq_of_mem_center_left ← is_conj.eq_of_mem_center_left

namespace conj_classes

def noncenter (G : Type*) [monoid G] : set (conj_classes G) :=
{x | ¬ x.carrier.subsingleton }


lemma mk_bij_on (G : Type*) [group G] :
  set.bij_on conj_classes.mk ↑(subgroup.center G) (noncenter G)ᶜ :=
begin
  refine ⟨_, _, _⟩,
  { intros g hg, dsimp [noncenter], rw not_not,
    intros x hx y hy,
    simp only [mem_carrier_iff_mk_eq, mk_eq_mk_iff_is_conj] at hx hy,
    rw [hx.eq_of_mem_center_right hg, hy.eq_of_mem_center_right hg], },
  { intros x hx y hy H, rw [mk_eq_mk_iff_is_conj] at H, exact H.eq_of_mem_center_left hx },
  { rintros ⟨g⟩ hg, refine ⟨g, _, rfl⟩,
    dsimp [noncenter] at hg, rw not_not at hg,
    intro h, rw ← mul_inv_eq_iff_eq_mul, refine hg _ mem_carrier_mk, rw mem_carrier_iff_mk_eq,
    apply mk_eq_mk_iff_is_conj.2, rw [is_conj_comm, is_conj_iff], exact ⟨h, rfl⟩, }
end

end conj_classes

open conj_classes

lemma class_equation [fintype G] :
  nat.card (subgroup.center G) + ∑ᶠ x ∈ noncenter G, nat.card (carrier x) = nat.card G :=
begin
  classical,
  rw [@nat.card_eq_fintype_card G, ← class_equation',
      ←finset.sum_sdiff (conj_classes.noncenter G).to_finset.subset_univ],
  simp only [nat.card_eq_fintype_card, set.to_finset_card],
  congr' 1, swap,
  { convert finsum_cond_eq_sum_of_cond_iff _ _,
    intros, simp only [set.mem_to_finset] },
  calc fintype.card (subgroup.center G)
      = fintype.card ((noncenter G)ᶜ : set _) : fintype.card_congr ((mk_bij_on G).equiv _)
  ... = finset.card (finset.univ \ (noncenter G).to_finset) : _
  ... = _ : _,
  { rw fintype.card_of_finset,
    congr' 1,
    ext x,
    simp only [set.mem_to_finset, finset.mem_sdiff, finset.mem_filter, set.mem_compl_iff] },
  rw [finset.card_eq_sum_ones],
  convert finset.sum_congr rfl _,
  rintro ⟨g⟩ hg,
  simp only [true_and, finset.mem_univ, set.mem_to_finset, finset.mem_sdiff,
             noncenter, not_not, set.mem_set_of_eq] at hg,
  rw [eq_comm, ←set.to_finset_card, finset.card_eq_one],
  exact ⟨g, finset.coe_injective $ by simpa using hg.eq_singleton_of_mem mem_carrier_mk⟩
end
