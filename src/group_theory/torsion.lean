/-
Copyright (c) 2022 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/

import group_theory.exponent
import group_theory.order_of_element
import group_theory.p_group
import group_theory.quotient_group
import group_theory.submonoid.operations

/-!
# Torsion groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines torsion groups, i.e. groups where all elements have finite order.

## Main definitions

* `monoid.is_torsion` a predicate asserting `G` is torsion, i.e. that all
  elements are of finite order.
* `comm_group.torsion G`, the torsion subgroup of an abelian group `G`
* `comm_monoid.torsion G`, the above stated for commutative monoids
* `monoid.is_torsion_free`, asserting no nontrivial elements have finite order in `G`
* `add_monoid.is_torsion` and `add_monoid.is_torsion_free` the additive versions of the above

## Implementation

All torsion monoids are really groups (which is proven here as `monoid.is_torsion.group`), but since
the definition can be stated on monoids it is implemented on `monoid` to match other declarations in
the group theory library.

## Tags

periodic group, aperiodic group, torsion subgroup, torsion abelian group

## Future work

* generalize to π-torsion(-free) groups for a set of primes π
* free, free solvable and free abelian groups are torsion free
* complete direct and free products of torsion free groups are torsion free
* groups which are residually finite p-groups with respect to 2 distinct primes are torsion free
-/

variables {G H : Type*}

namespace monoid

variables (G) [monoid G]

/-- A predicate on a monoid saying that all elements are of finite order. -/
@[to_additive "A predicate on an additive monoid saying that all elements are of finite order."]
def is_torsion := ∀ g : G, is_of_fin_order g

/-- A monoid is not a torsion monoid if it has an element of infinite order. -/
@[simp, to_additive
  "An additive monoid is not a torsion monoid if it has an element of infinite order."]
lemma not_is_torsion_iff : ¬ is_torsion G ↔ ∃ g : G, ¬is_of_fin_order g :=
by rw [is_torsion, not_forall]

end monoid

open monoid

/-- Torsion monoids are really groups. -/
@[to_additive "Torsion additive monoids are really additive groups"]
noncomputable def is_torsion.group [monoid G] (tG : is_torsion G) : group G :=
{ inv := λ g, g ^ (order_of g - 1),
  mul_left_inv := λ g,
  begin
    erw [←pow_succ', tsub_add_cancel_of_le, pow_order_of_eq_one],
    exact order_of_pos' (tG g)
  end,
  ..‹monoid G› }

section group

variables [group G] {N : subgroup G} [group H]

/-- Subgroups of torsion groups are torsion groups. -/
@[to_additive "Subgroups of additive torsion groups are additive torsion groups."]
lemma is_torsion.subgroup (tG : is_torsion G) (H : subgroup G) : is_torsion H :=
λ h, (is_of_fin_order_iff_coe H.to_submonoid h).mpr $ tG h

/-- The image of a surjective torsion group homomorphism is torsion. -/
@[to_additive add_is_torsion.of_surjective
  "The image of a surjective additive torsion group homomorphism is torsion."]
lemma is_torsion.of_surjective {f : G →* H} (hf : function.surjective f) (tG : is_torsion G) :
  is_torsion H :=
λ h, begin
  obtain ⟨g, hg⟩ := hf h,
  rw ←hg,
  exact f.is_of_fin_order (tG g),
end

/-- Torsion groups are closed under extensions. -/
@[to_additive add_is_torsion.extension_closed
  "Additive torsion groups are closed under extensions."]
lemma is_torsion.extension_closed
  {f : G →* H} (hN : N = f.ker) (tH : is_torsion H) (tN : is_torsion N) :
  is_torsion G :=
λ g, (is_of_fin_order_iff_pow_eq_one _).mpr $ begin
  obtain ⟨ngn, ngnpos, hngn⟩ := (is_of_fin_order_iff_pow_eq_one _).mp (tH $ f g),
  have hmem := f.mem_ker.mpr ((f.map_pow g ngn).trans hngn),
  lift g ^ ngn to N using hN.symm ▸ hmem with gn,
  obtain ⟨nn, nnpos, hnn⟩ := (is_of_fin_order_iff_pow_eq_one _).mp (tN gn),
  exact ⟨ngn * nn, mul_pos ngnpos nnpos, by rw [pow_mul, ←h, ←subgroup.coe_pow,
                                                hnn, subgroup.coe_one]⟩
end

/-- The image of a quotient is torsion iff the group is torsion. -/
@[to_additive add_is_torsion.quotient_iff
  "The image of a quotient is additively torsion iff the group is torsion."]
lemma is_torsion.quotient_iff
  {f : G →* H} (hf : function.surjective f) (hN : N = f.ker) (tN : is_torsion N) :
  is_torsion H ↔ is_torsion G :=
⟨λ tH, is_torsion.extension_closed hN tH tN, λ tG, is_torsion.of_surjective hf tG⟩

/-- If a group exponent exists, the group is torsion. -/
@[to_additive exponent_exists.is_add_torsion
  "If a group exponent exists, the group is additively torsion."]
lemma exponent_exists.is_torsion (h : exponent_exists G) : is_torsion G := λ g, begin
  obtain ⟨n, npos, hn⟩ := h,
  exact (is_of_fin_order_iff_pow_eq_one g).mpr ⟨n, npos, hn g⟩,
end

/-- The group exponent exists for any bounded torsion group. -/
@[to_additive is_add_torsion.exponent_exists
  "The group exponent exists for any bounded additive torsion group."]
lemma is_torsion.exponent_exists
  (tG : is_torsion G) (bounded : (set.range (λ g : G, order_of g)).finite) :
  exponent_exists G :=
exponent_exists_iff_ne_zero.mpr $
  (exponent_ne_zero_iff_range_order_of_finite (λ g, order_of_pos' (tG g))).mpr bounded

/-- Finite groups are torsion groups. -/
@[to_additive is_add_torsion_of_finite "Finite additive groups are additive torsion groups."]
lemma is_torsion_of_finite [finite G] : is_torsion G :=
exponent_exists.is_torsion $ exponent_exists_iff_ne_zero.mpr exponent_ne_zero_of_finite

end group

section module

-- A (semi/)ring of scalars and a commutative monoid of elements
variables (R M : Type*) [add_comm_monoid M]

namespace add_monoid

/-- A module whose scalars are additively torsion is additively torsion. -/
lemma is_torsion.module_of_torsion [semiring R] [module R M] (tR : is_torsion R) :
is_torsion M := λ f, (is_of_fin_add_order_iff_nsmul_eq_zero _).mpr $ begin
  obtain ⟨n, npos, hn⟩ := (is_of_fin_add_order_iff_nsmul_eq_zero _).mp (tR 1),
  exact ⟨n, npos, by simp only [nsmul_eq_smul_cast R _ f, ←nsmul_one, hn, zero_smul]⟩,
end

/-- A module with a finite ring of scalars is additively torsion. -/
lemma is_torsion.module_of_finite [ring R] [finite R] [module R M] : is_torsion M :=
(is_add_torsion_of_finite : is_torsion R).module_of_torsion _ _

end add_monoid

end module

section comm_monoid

variables (G) [comm_monoid G]

namespace comm_monoid

/--
The torsion submonoid of a commutative monoid.

(Note that by `monoid.is_torsion.group` torsion monoids are truthfully groups.)
-/
@[to_additive add_torsion "The torsion submonoid of an additive commutative monoid."]
def torsion : submonoid G :=
{ carrier := {x | is_of_fin_order x},
  one_mem' := is_of_fin_order_one,
  mul_mem' := λ _ _ hx hy, hx.mul hy }

variable {G}

/-- Torsion submonoids are torsion. -/
@[to_additive "Additive torsion submonoids are additively torsion."]
lemma torsion.is_torsion : is_torsion $ torsion G :=
λ ⟨_, n, npos, hn⟩,
  ⟨n, npos, subtype.ext $
    by rw [mul_left_iterate, _root_.mul_one, submonoid.coe_pow,
           subtype.coe_mk, submonoid.coe_one, (is_periodic_pt_mul_iff_pow_eq_one _).mp hn]⟩

variables (G) (p : ℕ) [hp : fact p.prime]
include hp

/-- The `p`-primary component is the submonoid of elements with order prime-power of `p`. -/
@[to_additive
  "The `p`-primary component is the submonoid of elements with additive order prime-power of `p`.",
  simps]
def primary_component : submonoid G :=
{ carrier := {g | ∃ n : ℕ, order_of g = p ^ n},
  one_mem' := ⟨0, by rw [pow_zero, order_of_one]⟩,
  mul_mem' := λ g₁ g₂ hg₁ hg₂, exists_order_of_eq_prime_pow_iff.mpr $ begin
    obtain ⟨m, hm⟩ := exists_order_of_eq_prime_pow_iff.mp hg₁,
    obtain ⟨n, hn⟩ := exists_order_of_eq_prime_pow_iff.mp hg₂,
    exact ⟨m + n, by rw [mul_pow, pow_add, pow_mul, hm, one_pow, monoid.one_mul,
                         mul_comm, pow_mul, hn, one_pow]⟩,
  end }

variables {G} {p}

/-- Elements of the `p`-primary component have order `p^n` for some `n`. -/
@[to_additive "Elements of the `p`-primary component have additive order `p^n` for some `n`"]
lemma primary_component.exists_order_of_eq_prime_pow (g : comm_monoid.primary_component G p) :
  ∃ n : ℕ, order_of g = p ^ n :=
by simpa [primary_component] using g.property

/-- The `p`- and `q`-primary components are disjoint for `p ≠ q`. -/
@[to_additive "The `p`- and `q`-primary components are disjoint for `p ≠ q`."]
lemma primary_component.disjoint {p' : ℕ} [hp' : fact p'.prime] (hne : p ≠ p') :
  disjoint (comm_monoid.primary_component G p) (comm_monoid.primary_component G p') :=
submonoid.disjoint_def.mpr $
begin
  rintro g ⟨(_|n), hn⟩ ⟨n', hn'⟩,
  { rwa [pow_zero, order_of_eq_one_iff] at hn },
  { exact absurd (eq_of_prime_pow_eq hp.out.prime hp'.out.prime n.succ_pos
      (hn.symm.trans hn')) hne }
end

end comm_monoid

open comm_monoid (torsion)

namespace monoid.is_torsion

variable {G}

/-- The torsion submonoid of a torsion monoid is `⊤`. -/
@[simp, to_additive "The additive torsion submonoid of an additive torsion monoid is `⊤`."]
lemma torsion_eq_top (tG : is_torsion G) : torsion G = ⊤ := by ext; tauto

/-- A torsion monoid is isomorphic to its torsion submonoid. -/
@[to_additive "An additive torsion monoid is isomorphic to its torsion submonoid."]
def torsion_mul_equiv (tG : is_torsion G) : torsion G ≃* G :=
(mul_equiv.submonoid_congr tG.torsion_eq_top).trans submonoid.top_equiv

@[to_additive] lemma torsion_mul_equiv_apply (tG : is_torsion G) (a : torsion G) :
  tG.torsion_mul_equiv a = mul_equiv.submonoid_congr tG.torsion_eq_top a := rfl

@[to_additive] lemma torsion_mul_equiv_symm_apply_coe (tG : is_torsion G) (a : G) :
  tG.torsion_mul_equiv.symm a = ⟨submonoid.top_equiv.symm a, tG _⟩ := rfl

end monoid.is_torsion

/-- Torsion submonoids of a torsion submonoid are isomorphic to the submonoid. -/
@[simp, to_additive add_comm_monoid.torsion.of_torsion
  "Additive torsion submonoids of an additive torsion submonoid are isomorphic to the submonoid."]
def torsion.of_torsion : (torsion (torsion G)) ≃* (torsion G) :=
monoid.is_torsion.torsion_mul_equiv comm_monoid.torsion.is_torsion

end comm_monoid

section comm_group

variables (G) [comm_group G]

namespace comm_group

/-- The torsion subgroup of an abelian group. -/
@[to_additive "The torsion subgroup of an additive abelian group."]
def torsion : subgroup G := { comm_monoid.torsion G with inv_mem' := λ x, is_of_fin_order.inv }

/-- The torsion submonoid of an abelian group equals the torsion subgroup as a submonoid. -/
@[to_additive add_torsion_eq_add_torsion_submonoid
  "The additive torsion submonoid of an abelian group equals the torsion subgroup as a submonoid."]
lemma torsion_eq_torsion_submonoid : comm_monoid.torsion G = (torsion G).to_submonoid := rfl

variables (p : ℕ) [hp : fact p.prime]
include hp

/-- The `p`-primary component is the subgroup of elements with order prime-power of `p`. -/
@[to_additive
  "The `p`-primary component is the subgroup of elements with additive order prime-power of `p`.",
  simps]
def primary_component : subgroup G :=
{ comm_monoid.primary_component G p with inv_mem' := λ g ⟨n, hn⟩, ⟨n, (order_of_inv g).trans hn⟩ }

variables {G} {p}

/-- The `p`-primary component is a `p` group. -/
lemma primary_component.is_p_group : is_p_group p $ primary_component G p :=
λ g, (propext exists_order_of_eq_prime_pow_iff.symm).mpr
  (comm_monoid.primary_component.exists_order_of_eq_prime_pow g)

end comm_group

end comm_group

namespace monoid

variables (G) [monoid G]

/-- A predicate on a monoid saying that only 1 is of finite order. -/
@[to_additive "A predicate on an additive monoid saying that only 0 is of finite order."]
def is_torsion_free := ∀ g : G, g ≠ 1 → ¬is_of_fin_order g

/-- A nontrivial monoid is not torsion-free if any nontrivial element has finite order. -/
@[simp, to_additive
  "An additive monoid is not torsion free if any nontrivial element has finite order."]
lemma not_is_torsion_free_iff : ¬ (is_torsion_free G) ↔ ∃ g : G, g ≠ 1 ∧ is_of_fin_order g :=
by simp_rw [is_torsion_free, ne.def, not_forall, not_not, exists_prop]

end monoid

section group

open monoid

variables [group G]

/-- A nontrivial torsion group is not torsion-free. -/
@[to_additive add_monoid.is_torsion.not_torsion_free
  "A nontrivial additive torsion group is not torsion-free."]
lemma is_torsion.not_torsion_free [hN : nontrivial G] : is_torsion G → ¬is_torsion_free G :=
λ tG, (not_is_torsion_free_iff _).mpr $ begin
  obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne (1 : G)).mp hN,
  exact ⟨x, hx, tG x⟩,
end

/-- A nontrivial torsion-free group is not torsion. -/
@[to_additive add_monoid.is_torsion_free.not_torsion
  "A nontrivial torsion-free additive group is not torsion."]
lemma is_torsion_free.not_torsion [hN : nontrivial G] : is_torsion_free G → ¬is_torsion G :=
λ tfG, (not_is_torsion_iff _).mpr $ begin
  obtain ⟨x, hx⟩ := (nontrivial_iff_exists_ne (1 : G)).mp hN,
  exact ⟨x, (tfG x) hx⟩,
end

/-- Subgroups of torsion-free groups are torsion-free. -/
@[to_additive "Subgroups of additive torsion-free groups are additively torsion-free."]
lemma is_torsion_free.subgroup (tG : is_torsion_free G) (H : subgroup G) : is_torsion_free H :=
λ h hne, (is_of_fin_order_iff_coe H.to_submonoid h).not.mpr $
  tG h $ by norm_cast; simp [hne, not_false_iff]

/-- Direct products of torsion free groups are torsion free. -/
@[to_additive add_monoid.is_torsion_free.prod
  "Direct products of additive torsion free groups are torsion free."]
lemma is_torsion_free.prod
  {η : Type*} {Gs : η → Type*} [∀ i, group (Gs i)] (tfGs : ∀ i, is_torsion_free (Gs i)) :
is_torsion_free $ Π i, Gs i :=
λ w hne h, hne $ funext $ λ i, not_not.mp $ mt (tfGs i (w i)) $ not_not.mpr $ h.apply i

end group

section comm_group

open monoid (is_torsion_free)
open comm_group (torsion)

variables (G) [comm_group G]

/-- Quotienting a group by its torsion subgroup yields a torsion free group. -/
@[to_additive add_is_torsion_free.quotient_torsion
  "Quotienting a group by its additive torsion subgroup yields an additive torsion free group."]
lemma is_torsion_free.quotient_torsion : is_torsion_free $ G ⧸ torsion G :=
λ g hne hfin, hne $ begin
  induction g using quotient_group.induction_on',
  obtain ⟨m, mpos, hm⟩ := (is_of_fin_order_iff_pow_eq_one _).mp hfin,
  obtain ⟨n, npos, hn⟩ :=
    (is_of_fin_order_iff_pow_eq_one _).mp ((quotient_group.eq_one_iff _).mp hm),
  exact (quotient_group.eq_one_iff g).mpr
    ((is_of_fin_order_iff_pow_eq_one _).mpr ⟨m * n, mul_pos mpos npos, (pow_mul g m n).symm ▸ hn⟩),
end

end comm_group
