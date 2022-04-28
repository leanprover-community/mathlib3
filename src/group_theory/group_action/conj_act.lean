/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action.basic
import group_theory.subgroup.basic
import set_theory.cardinal.finite
import algebra.big_operators.finprod
import algebra.group_ring_action

/-!
# Conjugation action of a group on itself

This file defines the conjugation action of a group on itself. See also `mul_aut.conj` for
the definition of conjugation as a homomorphism into the automorphism group.

## Main definitions

A type alias `conj_act G` is introduced for a group `G`. The group `conj_act G` acts on `G`
by conjugation. The group `conj_act G` also acts on any normal subgroup of `G` by conjugation.

As a generalization, this also allows:
* `conj_act Mˣ` to act on `M`, when `M` is a `monoid`
* `conj_act G₀` to act on `G₀`, when `G₀` is a `group_with_zero`

## Implementation Notes

The scalar action in defined in this file can also be written using `mul_aut.conj g • h`. This
has the advantage of not using the type alias `conj_act`, but the downside of this approach
is that some theorems about the group actions will not apply when since this
`mul_aut.conj g • h` describes an action of `mul_aut G` on `G`, and not an action of `G`.

-/

open_locale big_operators

variables (M G G₀ R K : Type*)

/-- A type alias for a group `G`. `conj_act G` acts on `G` by conjugation -/
def conj_act : Type* := G

namespace conj_act
open mul_action subgroup

variables {M G G₀ R K}

instance : Π [group G], group (conj_act G) := id
instance : Π [div_inv_monoid G], div_inv_monoid (conj_act G) := id
instance : Π [group_with_zero G], group_with_zero (conj_act G) := id
instance : Π [fintype G], fintype (conj_act G) := id

@[simp] lemma card [fintype G] : fintype.card (conj_act G) = fintype.card G := rfl

section div_inv_monoid

variable [div_inv_monoid G]

instance : inhabited (conj_act G) := ⟨1⟩

/-- Reinterpret `g : conj_act G` as an element of `G`. -/
def of_conj_act : conj_act G ≃* G := ⟨id, id, λ _, rfl, λ _, rfl, λ _ _, rfl⟩

/-- Reinterpret `g : G` as an element of `conj_act G`. -/
def to_conj_act : G ≃* conj_act G := of_conj_act.symm

/-- A recursor for `conj_act`, for use as `induction x using conj_act.rec` when `x : conj_act G`. -/
protected def rec {C : conj_act G → Sort*} (h : Π g, C (to_conj_act g)) : Π g, C g := h

@[simp] lemma of_mul_symm_eq : (@of_conj_act G _).symm = to_conj_act := rfl
@[simp] lemma to_mul_symm_eq : (@to_conj_act G _).symm = of_conj_act := rfl
@[simp] lemma to_conj_act_of_conj_act (x : conj_act G) : to_conj_act (of_conj_act x) = x := rfl
@[simp] lemma of_conj_act_to_conj_act (x : G) : of_conj_act (to_conj_act x) = x := rfl
@[simp] lemma of_conj_act_one : of_conj_act (1 : conj_act G) = 1 := rfl
@[simp] lemma to_conj_act_one : to_conj_act (1 : G) = 1 := rfl
@[simp] lemma of_conj_act_inv (x : conj_act G) : of_conj_act (x⁻¹) = (of_conj_act x)⁻¹ := rfl
@[simp] lemma to_conj_act_inv (x : G) : to_conj_act (x⁻¹) = (to_conj_act x)⁻¹ := rfl
@[simp] lemma of_conj_act_mul (x y : conj_act G) :
  of_conj_act (x * y) = of_conj_act x * of_conj_act y := rfl
@[simp] lemma to_conj_act_mul (x y : G) : to_conj_act (x * y) =
  to_conj_act x * to_conj_act y := rfl

instance : has_scalar (conj_act G) G :=
{ smul := λ g h, of_conj_act g * h * (of_conj_act g)⁻¹ }

lemma smul_def (g : conj_act G) (h : G) : g • h = of_conj_act g * h * (of_conj_act g)⁻¹ := rfl

@[simp] lemma «forall» (p : conj_act G → Prop) :
  (∀ (x : conj_act G), p x) ↔ ∀ x : G, p (to_conj_act x) := iff.rfl

end div_inv_monoid

section units

section monoid
variables [monoid M]

instance has_units_scalar : has_scalar (conj_act Mˣ) M :=
{ smul := λ g h, of_conj_act g * h * ↑(of_conj_act g)⁻¹ }

lemma units_smul_def (g : conj_act Mˣ) (h : M) : g • h = of_conj_act g * h * ↑(of_conj_act g)⁻¹ :=
rfl

instance units_mul_distrib_mul_action : mul_distrib_mul_action (conj_act Mˣ) M :=
{ smul := (•),
  one_smul := by simp [units_smul_def],
  mul_smul := by simp [units_smul_def, mul_assoc, mul_inv_rev₀],
  smul_mul := by simp [units_smul_def, mul_assoc],
  smul_one := by simp [units_smul_def], }

end monoid

section semiring
variables [semiring R]

instance units_mul_semiring_action : mul_semiring_action (conj_act Rˣ) R :=
{ smul := (•),
  smul_zero := by simp [units_smul_def],
  smul_add := by simp [units_smul_def, mul_add, add_mul],
  ..conj_act.units_mul_distrib_mul_action}

end semiring

end units

section group_with_zero
variable [group_with_zero G₀]

@[simp] lemma of_conj_act_zero : of_conj_act (0 : conj_act G₀) = 0 := rfl
@[simp] lemma to_conj_act_zero : to_conj_act (0 : G₀) = 0 := rfl

instance mul_action₀ : mul_action (conj_act G₀) G₀ :=
{ smul := (•),
  one_smul := by simp [smul_def],
  mul_smul := by simp [smul_def, mul_assoc, mul_inv_rev₀] }

end group_with_zero

section division_ring
variables [division_ring K]

instance distrib_mul_action₀ : distrib_mul_action (conj_act K) K :=
{ smul := (•),
  smul_zero := by simp [smul_def],
  smul_add := by simp [smul_def, mul_add, add_mul],
  ..conj_act.mul_action₀ }

end division_ring

variables [group G]

instance : mul_distrib_mul_action (conj_act G) G :=
{ smul := (•),
  smul_mul := by simp [smul_def, mul_assoc],
  smul_one := by simp [smul_def],
  one_smul := by simp [smul_def],
  mul_smul := by simp [smul_def, mul_assoc] }

lemma smul_eq_mul_aut_conj (g : conj_act G) (h : G) : g • h = mul_aut.conj (of_conj_act g) h := rfl

/-- The set of fixed points of the conjugation action of `G` on itself is the center of `G`. -/
lemma fixed_points_eq_center : fixed_points (conj_act G) G = center G :=
begin
  ext x,
  simp [mem_center_iff, smul_def, mul_inv_eq_iff_eq_mul]
end

/-- As normal subgroups are closed under conjugation, they inherit the conjugation action
  of the underlying group. -/
instance subgroup.conj_action {H : subgroup G} [hH : H.normal] :
  has_scalar (conj_act G) H :=
⟨λ g h, ⟨g • h, hH.conj_mem h.1 h.2 (of_conj_act g)⟩⟩

lemma subgroup.coe_conj_smul {H : subgroup G} [hH : H.normal] (g : conj_act G) (h : H) :
  ↑(g • h) = g • (h : G) := rfl

instance subgroup.conj_mul_distrib_mul_action {H : subgroup G} [hH : H.normal] :
  mul_distrib_mul_action (conj_act G) H :=
(subtype.coe_injective).mul_distrib_mul_action H.subtype subgroup.coe_conj_smul

/-- Group conjugation on a normal subgroup. Analogous to `mul_aut.conj`. -/
def _root_.mul_aut.conj_normal {H : subgroup G} [hH : H.normal] : G →* mul_aut H :=
(mul_distrib_mul_action.to_mul_aut (conj_act G) H).comp to_conj_act.to_monoid_hom

@[simp] lemma _root_.mul_aut.conj_normal_apply {H : subgroup G} [H.normal] (g : G) (h : H) :
  ↑(mul_aut.conj_normal g h) = g * h * g⁻¹ := rfl

@[simp] lemma _root_.mul_aut.conj_normal_symm_apply {H : subgroup G} [H.normal] (g : G) (h : H) :
  ↑((mul_aut.conj_normal g).symm h) = g⁻¹ * h * g :=
by { change _ * (_)⁻¹⁻¹ = _, rw inv_inv, refl }

@[simp] lemma _root_.mul_aut.conj_normal_inv_apply {H : subgroup G} [H.normal] (g : G) (h : H) :
  ↑((mul_aut.conj_normal g)⁻¹ h) = g⁻¹ * h * g :=
mul_aut.conj_normal_symm_apply g h

lemma _root_.mul_aut.conj_normal_coe {H : subgroup G} [H.normal] {h : H} :
  mul_aut.conj_normal ↑h = mul_aut.conj h :=
mul_equiv.ext (λ x, rfl)

instance normal_of_characteristic_of_normal {H : subgroup G} [hH : H.normal]
  {K : subgroup H} [h : K.characteristic] : (K.map H.subtype).normal :=
⟨λ a ha b, by
{ obtain ⟨a, ha, rfl⟩ := ha,
  exact K.apply_coe_mem_map H.subtype
    ⟨_, ((set_like.ext_iff.mp (h.fixed (mul_aut.conj_normal b)) a).mpr ha)⟩ }⟩

end conj_act

section fintype

open mul_action

variables (G) [group G] {M} [monoid M]

-- move this
lemma is_conj.eq_of_mem_center_left {g h : M} (H : is_conj g h) (Hg : g ∈ set.center M) :
  g = h :=
by { rcases H with ⟨u, hu⟩, rwa [← u.mul_left_inj, ← Hg u], }

-- move this
lemma is_conj.eq_of_mem_center_right {g h : M} (H : is_conj g h) (Hh : h ∈ set.center M) :
  g = h :=
(H.symm.eq_of_mem_center_left Hh).symm

-- move this
lemma mem_orbit_conj_act_iff {G : Type*} [group G] (g h : G) :
  g ∈ orbit (conj_act G) h ↔ is_conj g h :=
by { rw [is_conj.comm, is_conj_iff, mem_orbit_iff], exact iff.rfl }

-- move this
lemma orbit_rel_r (X : Type*) [mul_action G X] :
  (orbit_rel G X).r = λ x y, x ∈ orbit G y := rfl

-- move this
lemma orbit_rel_r_apply {X : Type*} [mul_action G X] (x y : X) :
  @setoid.r _ (orbit_rel G X) x y ↔ x ∈ orbit G y := iff.rfl

section
open_locale classical

lemma carrier_eq_orbit (g : G) : (conj_classes.mk g).carrier = orbit (conj_act G) g :=
begin
  ext h,
  rw [conj_classes.mem_carrier_iff_mk_eq, conj_classes.mk_eq_mk_iff_is_conj, mem_orbit_conj_act_iff]
end


lemma card_carrier (g : G) [fintype G] [fintype ((conj_classes.mk g).carrier)] :
  fintype.card (conj_classes.mk g).carrier =
    fintype.card (conj_act G) / fintype.card (stabilizer (conj_act G) g) :=
begin
  rw [← card_orbit_mul_card_stabilizer_eq_card_group (conj_act G) g, nat.mul_div_cancel],
  simp_rw [carrier_eq_orbit],
  exact fintype.card_pos_iff.mpr infer_instance
end

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
    apply mk_eq_mk_iff_is_conj.2, rw [is_conj.comm, is_conj_iff], exact ⟨h, rfl⟩, }
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
    simp only [set.mem_to_finset, finset.mem_sdiff, finset.mem_filter, set.mem_compl_eq] },
  rw [finset.card_eq_sum_ones],
  convert finset.sum_congr rfl _,
  rintro ⟨g⟩ hg,
  simp only [true_and, finset.mem_univ, set.mem_to_finset, finset.mem_sdiff,
             noncenter, not_not, set.mem_set_of_eq] at hg,
  rw [eq_comm, ←set.to_finset_card, finset.card_eq_one],
  exact ⟨g, finset.coe_injective $ by simpa using hg.eq_singleton_of_mem mem_carrier_mk⟩
end

end fintype
