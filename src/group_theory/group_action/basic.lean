/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.group_action.defs
import group_theory.group_action.group
import group_theory.quotient_group
import data.setoid.basic
import data.fintype.card

/-!
# Basic properties of group actions
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open_locale big_operators
open function

namespace mul_action

variables (α) [monoid α] [mul_action α β]

/-- The orbit of an element under an action. -/
@[to_additive "The orbit of an element under an action."]
def orbit (b : β) := set.range (λ x : α, x • b)

variable {α}

@[to_additive] lemma mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ orbit α b₁ ↔ ∃ x : α, x • b₁ = b₂ :=
iff.rfl

@[simp, to_additive] lemma mem_orbit (b : β) (x : α) : x • b ∈ orbit α b :=
⟨x, rfl⟩

@[simp, to_additive] lemma mem_orbit_self (b : β) : b ∈ orbit α b :=
⟨1, by simp [mul_action.one_smul]⟩

variables (α) (β)

/-- The set of elements fixed under the whole action. -/
@[to_additive "The set of elements fixed under the whole action."]
def fixed_points : set β := {b : β | ∀ x : α, x • b = b}

/-- `fixed_by g` is the subfield of elements fixed by `g`. -/
@[to_additive "`fixed_by g` is the subfield of elements fixed by `g`."]
def fixed_by (g : α) : set β :=
{ x | g • x = x }

@[to_additive] theorem fixed_eq_Inter_fixed_by : fixed_points α β = ⋂ g : α, fixed_by α β g :=
set.ext $ λ x, ⟨λ hx, set.mem_Inter.2 $ λ g, hx g, λ hx g, by exact (set.mem_Inter.1 hx g : _)⟩

variables {α} (β)

@[simp, to_additive] lemma mem_fixed_points {b : β} :
  b ∈ fixed_points α β ↔ ∀ x : α, x • b = b := iff.rfl

@[simp, to_additive] lemma mem_fixed_by {g : α} {b : β} :
  b ∈ fixed_by α β g ↔ g • b = b := iff.rfl

@[to_additive] lemma mem_fixed_points' {b : β} : b ∈ fixed_points α β ↔
  (∀ b', b' ∈ orbit α b → b' = b) :=
⟨λ h b h₁, let ⟨x, hx⟩ := mem_orbit_iff.1 h₁ in hx ▸ h x,
λ h b, h _ (mem_orbit _ _)⟩

variables (α) {β}

/-- The stabilizer of a point `b` as a submonoid of `α`. -/
@[to_additive "The stabilizer of a point `b` as an additive submonoid of `α`."]
def stabilizer.submonoid (b : β) : submonoid α :=
{ carrier := { a | a • b = b },
  one_mem' := one_smul _ b,
  mul_mem' := λ a a' (ha : a • b = b) (hb : a' • b = b),
    show (a * a') • b = b, by rw [←smul_smul, hb, ha] }

@[simp, to_additive] lemma mem_stabilizer_submonoid_iff {b : β} {a : α} :
  a ∈ stabilizer.submonoid α b ↔ a • b = b := iff.rfl

variables (α β)
/-- `α` acts pretransitively on `β` if for any `x y` there is `g` such that `g • x = y`.
  A transitive action should furthermore have `β` nonempty. -/
class is_pretransitive : Prop :=
(exists_smul_eq : ∀ x y : β, ∃ g : α, g • x = y)

variables {β}

lemma exists_smul_eq [is_pretransitive α β] (x y : β) :
  ∃ m : α, m • x = y := is_pretransitive.exists_smul_eq x y

end mul_action

namespace add_action
variables (α β) [add_monoid α] [add_action α β]

/-- `α` acts pretransitively on `β` if for any `x y` there is `g` such that `g +ᵥ x = y`.
  A transitive action should furthermore have `β` nonempty. -/
class is_pretransitive : Prop :=
(exists_vadd_eq : ∀ x y : β, ∃ g : α, g +ᵥ x = y)

variables {β}

lemma exists_vadd_eq [is_pretransitive α β] (x y : β) :
  ∃ m : α, m +ᵥ x = y := is_pretransitive.exists_vadd_eq x y

end add_action

namespace mul_action
variable (α)
variables [group α] [mul_action α β]

/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup. -/
@[to_additive "The stabilizer of an element under an action, i.e. what sends the element to itself.
An additive subgroup."]
def stabilizer (b : β) : subgroup α :=
{ inv_mem' := λ a (ha : a • b = b), show a⁻¹ • b = b, by rw [inv_smul_eq_iff, ha]
  ..stabilizer.submonoid α b }

variables {α} {β}

@[simp, to_additive] lemma mem_stabilizer_iff {b : β} {a : α} :
  a ∈ stabilizer α b ↔ a • b = b := iff.rfl

@[to_additive] lemma orbit_eq_iff {a b : β} :
   orbit α a = orbit α b ↔ a ∈ orbit α b:=
⟨λ h, h ▸ mem_orbit_self _,
λ ⟨x, (hx : x • b = a)⟩, set.ext (λ c, ⟨λ ⟨y, (hy : y • a = c)⟩, ⟨y * x,
  show (y * x) • b = c, by rwa [mul_action.mul_smul, hx]⟩,
  λ ⟨y, (hy : y • b = c)⟩, ⟨y * x⁻¹,
    show (y * x⁻¹) • a = c, by
      conv {to_rhs, rw [← hy, ← mul_one y, ← inv_mul_self x, ← mul_assoc,
        mul_action.mul_smul, hx]}⟩⟩)⟩

@[to_additive] instance {b : β} : mul_action α (orbit α b) :=
{ smul := λ a b', ⟨a • b', orbit_eq_iff.mp (eq.trans (orbit_eq_iff.mpr (mem_orbit b' a))
    (orbit_eq_iff.mpr b'.2))⟩,
  one_smul := λ a, subtype.ext (one_smul α a),
  mul_smul := λ a a' b', subtype.ext (mul_smul a a' b') }

@[simp, to_additive] lemma orbit.coe_smul {b : β} {a : α} {b' : orbit α b} :
  ↑(a • b') = a • (b' : β) :=
rfl

@[to_additive] lemma mem_fixed_points_iff_card_orbit_eq_one {a : β}
  [fintype (orbit α a)] : a ∈ fixed_points α β ↔ fintype.card (orbit α a) = 1 :=
begin
  rw [fintype.card_eq_one_iff, mem_fixed_points],
  split,
  { exact λ h, ⟨⟨a, mem_orbit_self _⟩, λ ⟨b, ⟨x, hx⟩⟩, subtype.eq $ by simp [h x, hx.symm]⟩ },
  { assume h x,
    rcases h with ⟨⟨z, hz⟩, hz₁⟩,
    exact calc x • a = z : subtype.mk.inj (hz₁ ⟨x • a, mem_orbit _ _⟩)
      ... = a : (subtype.mk.inj (hz₁ ⟨a, mem_orbit_self _⟩)).symm }
end

variables (α) {β}

@[simp, to_additive] lemma mem_orbit_smul (g : α) (a : β) : a ∈ orbit α (g • a) :=
⟨g⁻¹, by simp⟩

@[simp, to_additive] lemma smul_mem_orbit_smul (g h : α) (a : β) : g • a ∈ orbit α (h • a) :=
⟨g * h⁻¹, by simp [mul_smul]⟩

variables (α) (β)
/-- The relation 'in the same orbit'. -/
@[to_additive "The relation 'in the same orbit'."]
def orbit_rel : setoid β :=
{ r := λ a b, a ∈ orbit α b,
  iseqv := ⟨mem_orbit_self, λ a b, by simp [orbit_eq_iff.symm, eq_comm],
    λ a b, by simp [orbit_eq_iff.symm, eq_comm] {contextual := tt}⟩ }

local notation `Ω` := (quotient $ orbit_rel α β)

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action.
This version works with any right inverse to `quotient.mk'` in order to stay computable. In most
cases you'll want to use `quotient.out'`, so we provide `mul_action.self_equiv_sigma_orbits` as
a special case. -/
@[to_additive "Decomposition of a type `X` as a disjoint union of its orbits under an additive group
action. This version works with any right inverse to `quotient.mk'` in order to stay computable.
In most cases you'll want to use `quotient.out'`, so we provide `add_action.self_equiv_sigma_orbits`
as a special case."]
def self_equiv_sigma_orbits' {φ : Ω → β} (hφ : right_inverse φ quotient.mk') :
  β ≃ Σ (ω : Ω), orbit α (φ ω) :=
calc  β
    ≃ Σ (ω : Ω), {b // quotient.mk' b = ω} : (equiv.sigma_preimage_equiv quotient.mk').symm
... ≃ Σ (ω : Ω), orbit α (φ ω) :
        equiv.sigma_congr_right (λ ω, equiv.subtype_equiv_right $
          λ x, by {rw [← hφ ω, quotient.eq', hφ ω], refl })

/-- Decomposition of a type `X` as a disjoint union of its orbits under a group action. -/
@[to_additive "Decomposition of a type `X` as a disjoint union of its orbits under an additive group
action."]
noncomputable def self_equiv_sigma_orbits : β ≃ Σ (ω : Ω), orbit α ω.out' :=
self_equiv_sigma_orbits' α β quotient.out_eq'

variables {α β}

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g • x` is `gSg⁻¹`. -/
lemma stabilizer_smul_eq_stabilizer_map_conj (g : α) (x : β) :
  (stabilizer α (g • x) = (stabilizer α x).map (mul_aut.conj g).to_monoid_hom) :=
begin
  ext h,
  rw [mem_stabilizer_iff, ← smul_left_cancel_iff g⁻¹, smul_smul, smul_smul, smul_smul, mul_left_inv,
      one_smul, ← mem_stabilizer_iff, subgroup.mem_map_equiv, mul_aut.conj_symm_apply]
end

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizer_equiv_stabilizer_of_orbit_rel {x y : β} (h : (orbit_rel α β).rel x y) :
  stabilizer α x ≃* stabilizer α y :=
let g : α := classical.some h in
have hg : g • y = x := classical.some_spec h,
have this : stabilizer α x = (stabilizer α y).map (mul_aut.conj g).to_monoid_hom,
  by rw [← hg, stabilizer_smul_eq_stabilizer_map_conj],
(mul_equiv.subgroup_congr this).trans ((mul_aut.conj g).subgroup_equiv_map $ stabilizer α y).symm

end mul_action

namespace add_action

variables [add_group α] [add_action α β]

/-- If the stabilizer of `x` is `S`, then the stabilizer of `g +ᵥ x` is `g + S + (-g)`. -/
lemma stabilizer_vadd_eq_stabilizer_map_conj (g : α) (x : β) :
  (stabilizer α (g +ᵥ x) = (stabilizer α x).map (add_aut.conj g).to_add_monoid_hom) :=
begin
  ext h,
  rw [mem_stabilizer_iff, ← vadd_left_cancel_iff (-g) , vadd_vadd, vadd_vadd, vadd_vadd,
      add_left_neg, zero_vadd, ← mem_stabilizer_iff, add_subgroup.mem_map_equiv,
      add_aut.conj_symm_apply]
end

/-- A bijection between the stabilizers of two elements in the same orbit. -/
noncomputable def stabilizer_equiv_stabilizer_of_orbit_rel {x y : β}
  (h : (orbit_rel α β).rel x y) :
  stabilizer α x ≃+ stabilizer α y :=
let g : α := classical.some h in
have hg : g +ᵥ y = x := classical.some_spec h,
have this : stabilizer α x = (stabilizer α y).map (add_aut.conj g).to_add_monoid_hom,
  by rw [← hg, stabilizer_vadd_eq_stabilizer_map_conj],
(add_equiv.add_subgroup_congr this).trans
  ((add_aut.conj g).add_subgroup_equiv_map $ stabilizer α y).symm

end add_action

namespace mul_action

variables [group α] [mul_action α β]

open quotient_group

/-- Action on left cosets. -/
@[to_additive "Action on left cosets."]
def mul_left_cosets (H : subgroup α)
  (x : α) (y : quotient H) : quotient H :=
quotient.lift_on' y (λ y, quotient_group.mk ((x : α) * y))
  (λ a b (hab : _ ∈ H), quotient_group.eq.2
    (by rwa [mul_inv_rev, ← mul_assoc, mul_assoc (a⁻¹), inv_mul_self, mul_one]))

@[to_additive] instance quotient (H : subgroup α) : mul_action α (quotient H) :=
{ smul := mul_left_cosets H,
  one_smul := λ a, quotient.induction_on' a (λ a, quotient_group.eq.2
    (by simp [subgroup.one_mem])),
  mul_smul := λ x y a, quotient.induction_on' a (λ a, quotient_group.eq.2
    (by simp [mul_inv_rev, subgroup.one_mem, mul_assoc])) }

@[simp, to_additive] lemma quotient.smul_mk (H : subgroup α) (a x : α) :
  (a • quotient_group.mk x : quotient_group.quotient H) = quotient_group.mk (a * x) := rfl

@[simp, to_additive] lemma quotient.smul_coe (H : subgroup α) (a x : α) :
  (a • x : quotient_group.quotient H) = ↑(a * x) := rfl

@[to_additive] instance mul_left_cosets_comp_subtype_val (H I : subgroup α) :
  mul_action I (quotient H) :=
mul_action.comp_hom (quotient H) (subgroup.subtype I)

variables (α) {β} (x : β)

/-- The canonical map from the quotient of the stabilizer to the set. -/
@[to_additive "The canonical map from the quotient of the stabilizer to the set. "]
def of_quotient_stabilizer (g : quotient (mul_action.stabilizer α x)) : β :=
quotient.lift_on' g (•x) $ λ g1 g2 H,
calc  g1 • x
    = g1 • (g1⁻¹ * g2) • x : congr_arg _ H.symm
... = g2 • x : by rw [smul_smul, mul_inv_cancel_left]

@[simp, to_additive] theorem of_quotient_stabilizer_mk (g : α) :
  of_quotient_stabilizer α x (quotient_group.mk g) = g • x :=
rfl

@[to_additive] theorem of_quotient_stabilizer_mem_orbit (g) :
  of_quotient_stabilizer α x g ∈ orbit α x :=
quotient.induction_on' g $ λ g, ⟨g, rfl⟩

@[to_additive] theorem of_quotient_stabilizer_smul (g : α)
  (g' : quotient (mul_action.stabilizer α x)) :
  of_quotient_stabilizer α x (g • g') = g • of_quotient_stabilizer α x g' :=
quotient.induction_on' g' $ λ _, mul_smul _ _ _

@[to_additive] theorem injective_of_quotient_stabilizer :
  function.injective (of_quotient_stabilizer α x) :=
λ y₁ y₂, quotient.induction_on₂' y₁ y₂ $ λ g₁ g₂ (H : g₁ • x = g₂ • x), quotient.sound' $
show (g₁⁻¹ * g₂) • x = x, by rw [mul_smul, ← H, inv_smul_smul]

/-- Orbit-stabilizer theorem. -/
@[to_additive "Orbit-stabilizer theorem."]
noncomputable def orbit_equiv_quotient_stabilizer (b : β) :
  orbit α b ≃ quotient (stabilizer α b) :=
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
  mul_action.stabilizer G ((1 : G) : quotient H) = H :=
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
  (hφ : left_inverse quotient.mk' φ) : β ≃ Σ (ω : Ω), quotient (stabilizer α (φ ω)) :=
calc  β
    ≃ Σ (ω : Ω), orbit α (φ ω) : self_equiv_sigma_orbits' α β hφ
... ≃ Σ (ω : Ω), quotient (stabilizer α (φ ω)) :
        equiv.sigma_congr_right (λ ω, orbit_equiv_quotient_stabilizer α (φ ω))

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
    fintype.card (quotient $ stabilizer α (φ ω)),
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
  β ≃ Σ (ω : Ω), quotient (stabilizer α ω.out') :=
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
  is_pretransitive G (quotient_group.quotient H) :=
{ exists_smul_eq := begin
    rintros ⟨x⟩ ⟨y⟩,
    refine ⟨y * x⁻¹, quotient_group.eq.mpr _⟩,
    simp only [H.one_mem, mul_left_inv, inv_mul_cancel_right],
  end }

end mul_action

section
variables [monoid α] [add_monoid β] [distrib_mul_action α β]

lemma list.smul_sum {r : α} {l : list β} :
  r • l.sum = (l.map ((•) r)).sum :=
(distrib_mul_action.to_add_monoid_hom β r).map_list_sum l

/-- `smul` by a `k : M` over a ring is injective, if `k` is not a zero divisor.
The general theory of such `k` is elaborated by `is_smul_regular`.
The typeclass that restricts all terms of `M` to have this property is `no_zero_smul_divisors`. -/
lemma smul_cancel_of_non_zero_divisor {M R : Type*} [monoid M] [ring R] [distrib_mul_action M R]
  (k : M) (h : ∀ (x : R), k • x = 0 → x = 0) {a b : R} (h' : k • a = k • b) :
  a = b :=
begin
  rw ←sub_eq_zero,
  refine h _ _,
  rw [smul_sub, h', sub_self]
end

end

section
variables [monoid α] [monoid β] [mul_distrib_mul_action α β]

@[simp] lemma smul_pow (x : α) (m : β) (n : ℕ) :
  x • m ^ n = (x • m) ^ n :=
begin
  induction n with n ih,
  { rw [pow_zero, pow_zero], exact smul_one x },
  { rw [pow_succ, pow_succ], exact (smul_mul' x m (m ^ n)).trans (congr_arg _ ih) }
end

lemma list.smul_prod {r : α} {l : list β} :
  r • l.prod = (l.map ((•) r)).prod :=
(mul_distrib_mul_action.to_monoid_hom β r).map_list_prod l

end

section
variables [monoid α] [add_comm_monoid β] [distrib_mul_action α β]

lemma multiset.smul_sum {r : α} {s : multiset β} :
  r • s.sum = (s.map ((•) r)).sum :=
(distrib_mul_action.to_add_monoid_hom β r).map_multiset_sum s

lemma finset.smul_sum {r : α} {f : γ → β} {s : finset γ} :
  r • ∑ x in s, f x = ∑ x in s, r • f x :=
(distrib_mul_action.to_add_monoid_hom β r).map_sum f s

end

section
variables [monoid α] [comm_monoid β] [mul_distrib_mul_action α β]

lemma multiset.smul_prod {r : α} {s : multiset β} :
  r • s.prod = (s.map ((•) r)).prod :=
(mul_distrib_mul_action.to_monoid_hom β r).map_multiset_prod s

lemma finset.smul_prod {r : α} {f : γ → β} {s : finset γ} :
  r • ∏ x in s, f x = ∏ x in s, r • f x :=
(mul_distrib_mul_action.to_monoid_hom β r).map_prod f s

end

namespace subgroup

variables {G : Type*} [group G] (H : subgroup G)

lemma normal_core_eq_ker :
  H.normal_core = (mul_action.to_perm_hom G (quotient_group.quotient H)).ker :=
begin
  refine le_antisymm (λ g hg, equiv.perm.ext (λ q, quotient_group.induction_on q
    (λ g', (mul_action.quotient.smul_mk H g g').trans (quotient_group.eq.mpr _))))
    (subgroup.normal_le_normal_core.mpr (λ g hg, _)),
  { rw [mul_inv_rev, ←inv_inv g', inv_inv],
    exact H.normal_core.inv_mem hg g'⁻¹ },
  { rw [←H.inv_mem_iff, ←mul_one g⁻¹, ←quotient_group.eq, ←mul_one g],
    exact (mul_action.quotient.smul_mk H g 1).symm.trans (equiv.perm.ext_iff.mp hg (1 : G)) },
end

noncomputable instance fintype_quotient_normal_core [fintype (quotient_group.quotient H)] :
  fintype (quotient_group.quotient H.normal_core) :=
begin
  rw H.normal_core_eq_ker,
  classical,
  exact fintype.of_equiv _ (quotient_group.quotient_ker_equiv_range _).symm.to_equiv,
end

end subgroup
