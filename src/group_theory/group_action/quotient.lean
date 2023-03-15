/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/
import algebra.hom.group_action
import data.fintype.big_operators
import dynamics.periodic_pts
import group_theory.group_action.conj_act
import group_theory.commutator
import group_theory.coset

/-!
# Properties of group actions involving quotient groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves properties of group actions which use the quotient group construction, notably
* the orbit-stabilizer theorem `card_orbit_mul_card_stabilizer_eq_card_group`
* the class formula `card_eq_sum_card_group_div_card_stabilizer'`
* Burnside's lemma `sum_card_fixed_by_eq_card_orbits_mul_card_group`
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open function
open_locale big_operators

namespace mul_action

variables [group α]

section quotient_action

open subgroup mul_opposite quotient_group

variables (β) [monoid β] [mul_action β α] (H : subgroup α)

/-- A typeclass for when a `mul_action β α` descends to the quotient `α ⧸ H`. -/
class quotient_action : Prop :=
(inv_mul_mem : ∀ (b : β) {a a' : α}, a⁻¹ * a' ∈ H → (b • a)⁻¹ * (b • a') ∈ H)

/-- A typeclass for when an `add_action β α` descends to the quotient `α ⧸ H`. -/
class _root_.add_action.quotient_action {α : Type*} (β : Type*) [add_group α] [add_monoid β]
  [add_action β α] (H : add_subgroup α) : Prop :=
(inv_mul_mem : ∀ (b : β) {a a' : α}, -a + a' ∈ H → -(b +ᵥ a) + (b +ᵥ a') ∈ H)

attribute [to_additive add_action.quotient_action] mul_action.quotient_action

@[to_additive] instance left_quotient_action : quotient_action α H :=
⟨λ _ _ _ _, by rwa [smul_eq_mul, smul_eq_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]⟩

@[to_additive] instance right_quotient_action : quotient_action H.normalizer.opposite H :=
⟨λ b c _ _, by rwa [smul_def, smul_def, smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, ←mul_assoc,
  mem_normalizer_iff'.mp b.prop, mul_assoc, mul_inv_cancel_left]⟩

@[to_additive] instance right_quotient_action' [hH : H.normal] : quotient_action αᵐᵒᵖ H :=
⟨λ _ _ _ _, by rwa [smul_eq_mul_unop, smul_eq_mul_unop, mul_inv_rev, mul_assoc, hH.mem_comm_iff,
  mul_assoc, mul_inv_cancel_right]⟩

@[to_additive] instance quotient [quotient_action β H] : mul_action β (α ⧸ H) :=
{ smul := λ b, quotient.map' ((•) b) (λ a a' h, left_rel_apply.mpr $
    quotient_action.inv_mul_mem b $ left_rel_apply.mp h),
  one_smul := λ q, quotient.induction_on' q (λ a, congr_arg quotient.mk' (one_smul β a)),
  mul_smul := λ b b' q, quotient.induction_on' q (λ a, congr_arg quotient.mk' (mul_smul b b' a)) }

variables {β}

@[simp, to_additive] lemma quotient.smul_mk [quotient_action β H] (b : β) (a : α) :
  (b • quotient_group.mk a : α ⧸ H) = quotient_group.mk (b • a) := rfl

@[simp, to_additive] lemma quotient.smul_coe [quotient_action β H] (b : β) (a : α) :
  (b • a : α ⧸ H) = ↑(b • a) := rfl

@[simp, to_additive] lemma quotient.mk_smul_out' [quotient_action β H] (b : β) (q : α ⧸ H) :
  quotient_group.mk (b • q.out') = b • q :=
by rw [←quotient.smul_mk, quotient_group.out_eq']

@[simp, to_additive] lemma quotient.coe_smul_out' [quotient_action β H] (b : β) (q : α ⧸ H) :
  ↑(b • q.out') = b • q :=
quotient.mk_smul_out' H b q

lemma _root_.quotient_group.out'_conj_pow_minimal_period_mem
  (a : α) (q : α ⧸ H) : q.out'⁻¹ * a ^ function.minimal_period ((•) a) q * q.out' ∈ H :=
by rw [mul_assoc, ←quotient_group.eq', quotient_group.out_eq', ←smul_eq_mul, quotient.mk_smul_out',
  eq_comm, pow_smul_eq_iff_minimal_period_dvd]

end quotient_action

open quotient_group

/-- The canonical map to the left cosets. -/
def _root_.mul_action_hom.to_quotient (H : subgroup α) : α →[α] α ⧸ H :=
⟨coe, quotient.smul_coe H⟩

@[simp] lemma _root_.mul_action_hom.to_quotient_apply (H : subgroup α) (g : α) :
  mul_action_hom.to_quotient H g = g := rfl

@[to_additive] instance mul_left_cosets_comp_subtype_val (H I : subgroup α) :
  mul_action I (α ⧸ H) :=
mul_action.comp_hom (α ⧸ H) (subgroup.subtype I)

variables (α) {β} [mul_action α β] (x : β)

/-- The canonical map from the quotient of the stabilizer to the set. -/
@[to_additive "The canonical map from the quotient of the stabilizer to the set. "]
def of_quotient_stabilizer (g : α ⧸ (mul_action.stabilizer α x)) : β :=
quotient.lift_on' g (•x) $ λ g1 g2 H,
calc  g1 • x
    = g1 • (g1⁻¹ * g2) • x : congr_arg _ ((left_rel_apply.mp H).symm)
... = g2 • x : by rw [smul_smul, mul_inv_cancel_left]

@[simp, to_additive] theorem of_quotient_stabilizer_mk (g : α) :
  of_quotient_stabilizer α x (quotient_group.mk g) = g • x :=
rfl

@[to_additive] theorem of_quotient_stabilizer_mem_orbit (g) :
  of_quotient_stabilizer α x g ∈ orbit α x :=
quotient.induction_on' g $ λ g, ⟨g, rfl⟩

@[to_additive] theorem of_quotient_stabilizer_smul (g : α)
  (g' : α ⧸ (mul_action.stabilizer α x)) :
  of_quotient_stabilizer α x (g • g') = g • of_quotient_stabilizer α x g' :=
quotient.induction_on' g' $ λ _, mul_smul _ _ _

@[to_additive] theorem injective_of_quotient_stabilizer :
  function.injective (of_quotient_stabilizer α x) :=
λ y₁ y₂, quotient.induction_on₂' y₁ y₂ $ λ g₁ g₂ (H : g₁ • x = g₂ • x), quotient.sound' $
by { rw [left_rel_apply], show (g₁⁻¹ * g₂) • x = x, rw [mul_smul, ← H, inv_smul_smul] }

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
noncomputable def orbit_equiv_quotient_stabilizer (b : β) :
  orbit α b ≃ α ⧸ (stabilizer α b) :=
equiv.symm $ equiv.of_bijective
  (λ g, ⟨of_quotient_stabilizer α b g, of_quotient_stabilizer_mem_orbit α b g⟩)
  ⟨λ x y hxy, injective_of_quotient_stabilizer α b (by convert congr_arg subtype.val hxy),
  λ ⟨b, ⟨g, hgb⟩⟩, ⟨g, subtype.eq hgb⟩⟩

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
noncomputable def orbit_prod_stabilizer_equiv_group (b : β) :
  orbit α b × stabilizer α b ≃ α :=
(equiv.prod_congr (orbit_equiv_quotient_stabilizer α _) (equiv.refl _)).trans
subgroup.group_equiv_quotient_times_subgroup.symm

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
lemma card_orbit_mul_card_stabilizer_eq_card_group (b : β) [fintype α] [fintype $ orbit α b]
  [fintype $ stabilizer α b] :
  fintype.card (orbit α b) * fintype.card (stabilizer α b) = fintype.card α :=
by rw [← fintype.card_prod, fintype.card_congr (orbit_prod_stabilizer_equiv_group α b)]

@[simp, to_additive] theorem orbit_equiv_quotient_stabilizer_symm_apply (b : β) (a : α) :
  ((orbit_equiv_quotient_stabilizer α b).symm a : β) = a • b :=
rfl

@[simp, to_additive] lemma stabilizer_quotient {G} [group G] (H : subgroup G) :
  mul_action.stabilizer G ((1 : G) : G ⧸ H) = H :=
by { ext, simp [quotient_group.eq] }

variable (β)

local notation `Ω` := (quotient $ orbit_rel α β)

/-- **Class formula** : given `G` a group acting on `X` and `φ` a function mapping each orbit of `X`
under this action (that is, each element of the quotient of `X` by the relation `orbit_rel G X`) to
an element in this orbit, this gives a (noncomputable) bijection between `X` and the disjoint union
of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want `φ` to be `quotient.out'`, so we
provide `mul_action.self_equiv_sigma_orbits_quotient_stabilizer` as a special case. -/
@[to_additive "**Class formula** : given `G` an additive group acting on `X` and `φ` a function
mapping each orbit of `X` under this action (that is, each element of the quotient of `X` by the
relation `orbit_rel G X`) to an element in this orbit, this gives a (noncomputable) bijection
between `X` and the disjoint union of `G/Stab(φ(ω))` over all orbits `ω`. In most cases you'll want
`φ` to be `quotient.out'`, so we provide `add_action.self_equiv_sigma_orbits_quotient_stabilizer`
as a special case. "]
noncomputable def self_equiv_sigma_orbits_quotient_stabilizer' {φ : Ω → β}
  (hφ : left_inverse quotient.mk' φ) : β ≃ Σ (ω : Ω), α ⧸ (stabilizer α (φ ω)) :=
calc  β
    ≃ Σ (ω : Ω), orbit_rel.quotient.orbit ω : self_equiv_sigma_orbits' α β
... ≃ Σ (ω : Ω), α ⧸ (stabilizer α (φ ω)) :
        equiv.sigma_congr_right (λ ω,
          (equiv.set.of_eq $ orbit_rel.quotient.orbit_eq_orbit_out _ hφ).trans $
            orbit_equiv_quotient_stabilizer α (φ ω))

/-- **Class formula** for a finite group acting on a finite type. See
`mul_action.card_eq_sum_card_group_div_card_stabilizer` for a specialized version using
`quotient.out'`. -/
@[to_additive "**Class formula** for a finite group acting on a finite type. See
`add_action.card_eq_sum_card_add_group_div_card_stabilizer` for a specialized version using
`quotient.out'`."]
lemma card_eq_sum_card_group_div_card_stabilizer' [fintype α] [fintype β] [fintype Ω]
  [Π (b : β), fintype $ stabilizer α b] {φ : Ω → β} (hφ : left_inverse quotient.mk' φ) :
  fintype.card β = ∑ (ω : Ω), fintype.card α / fintype.card (stabilizer α (φ ω)) :=
begin
  classical,
  have : ∀ ω : Ω, fintype.card α / fintype.card ↥(stabilizer α (φ ω)) =
    fintype.card (α ⧸ stabilizer α (φ ω)),
  { intro ω,
    rw [fintype.card_congr (@subgroup.group_equiv_quotient_times_subgroup α _ (stabilizer α $ φ ω)),
        fintype.card_prod, nat.mul_div_cancel],
    exact fintype.card_pos_iff.mpr (by apply_instance) },
  simp_rw [this, ← fintype.card_sigma, fintype.card_congr
            (self_equiv_sigma_orbits_quotient_stabilizer' α β hφ)],
end

/-- **Class formula**. This is a special case of
`mul_action.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = quotient.out'`. -/
@[to_additive "**Class formula**. This is a special case of
`add_action.self_equiv_sigma_orbits_quotient_stabilizer'` with `φ = quotient.out'`. "]
noncomputable def self_equiv_sigma_orbits_quotient_stabilizer :
  β ≃ Σ (ω : Ω), α ⧸ (stabilizer α ω.out') :=
self_equiv_sigma_orbits_quotient_stabilizer' α β quotient.out_eq'

/-- **Class formula** for a finite group acting on a finite type. -/
@[to_additive "**Class formula** for a finite group acting on a finite type."]
lemma card_eq_sum_card_group_div_card_stabilizer [fintype α] [fintype β] [fintype Ω]
  [Π (b : β), fintype $ stabilizer α b] :
  fintype.card β = ∑ (ω : Ω), fintype.card α / fintype.card (stabilizer α ω.out') :=
card_eq_sum_card_group_div_card_stabilizer' α β quotient.out_eq'

/-- **Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is a group acting on `X` and
`X/G`denotes the quotient of `X` by the relation `orbit_rel G X`. -/
@[to_additive "**Burnside's lemma** : a (noncomputable) bijection between the disjoint union of all
`{x ∈ X | g • x = x}` for `g ∈ G` and the product `G × X/G`, where `G` is an additive group acting
on `X` and `X/G`denotes the quotient of `X` by the relation `orbit_rel G X`. "]
noncomputable def sigma_fixed_by_equiv_orbits_prod_group :
  (Σ (a : α), (fixed_by α β a)) ≃ Ω × α :=
calc  (Σ (a : α), fixed_by α β a)
    ≃ {ab : α × β // ab.1 • ab.2 = ab.2} :
        (equiv.subtype_prod_equiv_sigma_subtype _).symm
... ≃ {ba : β × α // ba.2 • ba.1 = ba.1} :
        (equiv.prod_comm α β).subtype_equiv (λ ab, iff.rfl)
... ≃ Σ (b : β), stabilizer α b :
        equiv.subtype_prod_equiv_sigma_subtype (λ (b : β) a, a ∈ stabilizer α b)
... ≃ Σ (ωb : (Σ (ω : Ω), orbit α ω.out')), stabilizer α (ωb.2 : β) :
        (self_equiv_sigma_orbits α β).sigma_congr_left'
... ≃ Σ (ω : Ω), (Σ (b : orbit α ω.out'), stabilizer α (b : β)) :
        equiv.sigma_assoc (λ (ω : Ω) (b : orbit α ω.out'), stabilizer α (b : β))
... ≃ Σ (ω : Ω), (Σ (b : orbit α ω.out'), stabilizer α ω.out') :
        equiv.sigma_congr_right (λ ω, equiv.sigma_congr_right $
          λ ⟨b, hb⟩, (stabilizer_equiv_stabilizer_of_orbit_rel hb).to_equiv)
... ≃ Σ (ω : Ω), orbit α ω.out' × stabilizer α ω.out' :
        equiv.sigma_congr_right (λ ω, equiv.sigma_equiv_prod _ _)
... ≃ Σ (ω : Ω), α :
        equiv.sigma_congr_right (λ ω, orbit_prod_stabilizer_equiv_group α ω.out')
... ≃ Ω × α :
        equiv.sigma_equiv_prod Ω α

/-- **Burnside's lemma** : given a finite group `G` acting on a set `X`, the average number of
elements fixed by each `g ∈ G` is the number of orbits. -/
@[to_additive "**Burnside's lemma** : given a finite additive group `G` acting on a set `X`,
the average number of elements fixed by each `g ∈ G` is the number of orbits. "]
lemma sum_card_fixed_by_eq_card_orbits_mul_card_group [fintype α] [Π a, fintype $ fixed_by α β a]
  [fintype Ω] :
  ∑ (a : α), fintype.card (fixed_by α β a) = fintype.card Ω * fintype.card α :=
by rw [← fintype.card_prod, ← fintype.card_sigma,
        fintype.card_congr (sigma_fixed_by_equiv_orbits_prod_group α β)]

@[to_additive] instance is_pretransitive_quotient (G) [group G] (H : subgroup G) :
  is_pretransitive G (G ⧸ H) :=
{ exists_smul_eq := begin
    rintros ⟨x⟩ ⟨y⟩,
    refine ⟨y * x⁻¹, quotient_group.eq.mpr _⟩,
    simp only [smul_eq_mul, H.one_mem, mul_left_inv, inv_mul_cancel_right],
  end }

end mul_action

namespace subgroup

variables {G : Type*} [group G] (H : subgroup G)

lemma normal_core_eq_ker :
  H.normal_core = (mul_action.to_perm_hom G (G ⧸ H)).ker :=
begin
  refine le_antisymm (λ g hg, equiv.perm.ext (λ q, quotient_group.induction_on q
    (λ g', (mul_action.quotient.smul_mk H g g').trans (quotient_group.eq.mpr _))))
    (subgroup.normal_le_normal_core.mpr (λ g hg, _)),
  { rw [smul_eq_mul, mul_inv_rev, ←inv_inv g', inv_inv],
    exact H.normal_core.inv_mem hg g'⁻¹ },
  { rw [←H.inv_mem_iff, ←mul_one g⁻¹, ←quotient_group.eq, ←mul_one g],
    exact (mul_action.quotient.smul_mk H g 1).symm.trans (equiv.perm.ext_iff.mp hg (1 : G)) },
end

open quotient_group

/-- Cosets of the centralizer of an element embed into the set of commutators. -/
noncomputable def quotient_centralizer_embedding (g : G) :
  G ⧸ centralizer (zpowers (g : G)) ↪ commutator_set G :=
((mul_action.orbit_equiv_quotient_stabilizer (conj_act G) g).trans (quotient_equiv_of_eq
  (conj_act.stabilizer_eq_centralizer g))).symm.to_embedding.trans ⟨λ x, ⟨x * g⁻¹,
  let ⟨_, x, rfl⟩ := x in ⟨x, g, rfl⟩⟩, λ x y, subtype.ext ∘ mul_right_cancel ∘ subtype.ext_iff.mp⟩

lemma quotient_centralizer_embedding_apply (g : G) (x : G) :
  quotient_centralizer_embedding g x = ⟨⁅x, g⁆, x, g, rfl⟩ :=
rfl

/-- If `G` is generated by `S`, then the quotient by the center embeds into `S`-indexed sequences
of commutators. -/
noncomputable def quotient_center_embedding {S : set G} (hS : closure S = ⊤) :
  G ⧸ center G ↪ S → commutator_set G :=
(quotient_equiv_of_eq (center_eq_infi' S hS)).to_embedding.trans ((quotient_infi_embedding _).trans
  (function.embedding.Pi_congr_right (λ g, quotient_centralizer_embedding g)))

lemma quotient_center_embedding_apply {S : set G} (hS : closure S = ⊤) (g : G) (s : S) :
  quotient_center_embedding hS g s = ⟨⁅g, s⁆, g, s, rfl⟩ :=
rfl

end subgroup
