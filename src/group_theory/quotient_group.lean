/-
Copyright (c) 2018 Kevin Buzzard and Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot.

This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
-/
import group_theory.coset

universes u v

namespace quotient_group

variables {G : Type u} [group G] (N : set G) [normal_subgroup N] {H : Type v} [group H]

instance : group (quotient N) :=
{ one := (1 : G),
  mul := λ a b, quotient.lift_on₂' a b
    (λ a b, ((a * b : G) : quotient N))
  (λ a₁ a₂ b₁ b₂ hab₁ hab₂,
      quot.sound
    ((is_subgroup.mul_mem_cancel_left N (is_subgroup.inv_mem hab₂)).1
        (by rw [mul_inv_rev, mul_inv_rev, ← mul_assoc (a₂⁻¹ * a₁⁻¹),
          mul_assoc _ b₂, ← mul_assoc b₂, mul_inv_self, one_mul, mul_assoc (a₂⁻¹)];
          exact normal_subgroup.normal _ hab₁ _))),
  mul_assoc := λ a b c, quotient.induction_on₃' a b c
    (λ a b c, congr_arg mk (mul_assoc a b c)),
  one_mul := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (one_mul a)),
  mul_one := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_one a)),
  inv := λ a, quotient.lift_on' a (λ a, ((a⁻¹ : G) : quotient N))
    (λ a b hab, quotient.sound' begin
      show a⁻¹⁻¹ * b⁻¹ ∈ N,
      rw ← mul_inv_rev,
      exact is_subgroup.inv_mem (is_subgroup.mem_norm_comm hab)
    end),
  mul_left_inv := λ a, quotient.induction_on' a
    (λ a, congr_arg mk (mul_left_inv a)) }
attribute [to_additive quotient_add_group.add_group._proof_6] quotient_group.group._proof_6
attribute [to_additive quotient_add_group.add_group._proof_5] quotient_group.group._proof_5
attribute [to_additive quotient_add_group.add_group._proof_4] quotient_group.group._proof_4
attribute [to_additive quotient_add_group.add_group._proof_3] quotient_group.group._proof_3
attribute [to_additive quotient_add_group.add_group._proof_2] quotient_group.group._proof_2
attribute [to_additive quotient_add_group.add_group._proof_1] quotient_group.group._proof_1
attribute [to_additive quotient_add_group.add_group] quotient_group.group
attribute [to_additive quotient_add_group.quotient.equations._eqn_1] quotient_group.quotient.equations._eqn_1
attribute [to_additive quotient_add_group.add_group.equations._eqn_1] quotient_group.group.equations._eqn_1

instance : is_group_hom (mk : G → quotient N) := ⟨λ _ _, rfl⟩
attribute [to_additive quotient_add_group.is_add_group_hom] quotient_group.is_group_hom
attribute [to_additive quotient_add_group.is_add_group_hom.equations._eqn_1] quotient_group.is_group_hom.equations._eqn_1

instance {G : Type*} [comm_group G] (s : set G) [is_subgroup s] : comm_group (quotient s) :=
{ mul_comm := λ a b, quotient.induction_on₂' a b
    (λ a b, congr_arg mk (mul_comm a b)),
  ..@quotient_group.group _ _ s (normal_subgroup_of_comm_group s) }
attribute [to_additive quotient_add_group.add_comm_group._proof_6] quotient_group.comm_group._proof_6
attribute [to_additive quotient_add_group.add_comm_group._proof_5] quotient_group.comm_group._proof_5
attribute [to_additive quotient_add_group.add_comm_group._proof_4] quotient_group.comm_group._proof_4
attribute [to_additive quotient_add_group.add_comm_group._proof_3] quotient_group.comm_group._proof_3
attribute [to_additive quotient_add_group.add_comm_group._proof_2] quotient_group.comm_group._proof_2
attribute [to_additive quotient_add_group.add_comm_group._proof_1] quotient_group.comm_group._proof_1
attribute [to_additive quotient_add_group.add_comm_group] quotient_group.comm_group
attribute [to_additive quotient_add_group.add_comm_group.equations._eqn_1] quotient_group.comm_group.equations._eqn_1

@[simp] lemma coe_one : ((1 : G) : quotient N) = 1 := rfl
@[simp] lemma coe_mul (a b : G) : ((a * b : G) : quotient N) = a * b := rfl
@[simp] lemma coe_inv (a : G) : ((a⁻¹ : G) : quotient N) = a⁻¹ := rfl
@[simp] lemma coe_pow (a : G) (n : ℕ) : ((a ^ n : G) : quotient N) = a ^ n :=
@is_group_hom.pow _ _ _ _ mk _ a n

attribute [to_additive quotient_add_group.coe_zero] coe_one
attribute [to_additive quotient_add_group.coe_add] coe_mul
attribute [to_additive quotient_add_group.coe_neg] coe_inv

@[simp] lemma coe_gpow (a : G) (n : ℤ) : ((a ^ n : G) : quotient N) = a ^ n :=
@is_group_hom.gpow _ _ _ _ mk _ a n

local notation ` Q ` := quotient N

def lift (φ : G → H) [is_group_hom φ] (HN : ∀x∈N, φ x = 1) (q : Q) : H :=
q.lift_on' φ $ assume a b (hab : a⁻¹ * b ∈ N),
(calc φ a = φ a * 1           : by simp
...       = φ a * φ (a⁻¹ * b) : by rw HN (a⁻¹ * b) hab
...       = φ (a * (a⁻¹ * b)) : by rw is_group_hom.mul φ a (a⁻¹ * b)
...       = φ b               : by simp)
attribute [to_additive quotient_add_group.lift._proof_1] lift._proof_1
attribute [to_additive quotient_add_group.lift] lift
attribute [to_additive quotient_add_group.lift.equations._eqn_1] lift.equations._eqn_1

@[simp] lemma lift_mk {φ : G → H} [is_group_hom φ] (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (g : Q) = φ g := rfl
attribute [to_additive quotient_add_group.lift_mk] lift_mk

@[simp] lemma lift_mk' {φ : G → H} [is_group_hom φ] (HN : ∀x∈N, φ x = 1) (g : G) :
  lift N φ HN (mk g : Q) = φ g := rfl
attribute [to_additive quotient_add_group.lift_mk'] lift_mk'

def map (M : set H) [normal_subgroup M] (f : G → H) [is_group_hom f] (h : N ⊆ f ⁻¹' M) :
  quotient N → quotient M :=
begin
  haveI : is_group_hom ((mk : H → quotient M) ∘ f) := is_group_hom.comp _ _,
  refine quotient_group.lift N (mk ∘ f) _,
  assume x hx,
  refine quotient_group.eq.2 _,
  rw [mul_one, is_subgroup.inv_mem_iff],
  exact h hx,
end

attribute [to_additive quotient_add_group.map._proof_1] map._proof_1
attribute [to_additive quotient_add_group.map._proof_2] map._proof_2
attribute [to_additive quotient_add_group.map] map

variables (φ : G → H) [is_group_hom φ] (HN : ∀x∈N, φ x = 1)

instance is_group_hom_quotient_lift  :
  is_group_hom (lift N φ HN) :=
⟨λ q r, quotient.induction_on₂' q r $ λ a b,
  show φ (a * b) = φ a * φ b, from is_group_hom.mul φ a b⟩
attribute [to_additive quotient_add_group.is_add_group_hom_quotient_lift] quotient_group.is_group_hom_quotient_lift
attribute [to_additive quotient_add_group.is_add_group_hom_quotient_lift.equations._eqn_1] quotient_group.is_group_hom_quotient_lift.equations._eqn_1

open function is_group_hom

@[to_additive quotient_add_group.injective_ker_lift]
lemma injective_ker_lift : injective (lift (ker φ) φ $ λ x h, (mem_ker φ).1 h) :=
assume a b, quotient.induction_on₂' a b $ assume a b (h : φ a = φ b), quotient.sound' $
show a⁻¹ * b ∈ ker φ, by rw [mem_ker φ,
  is_group_hom.mul φ, ← h, is_group_hom.inv φ, inv_mul_self]

--@[to_additive quotient_add_group.quotient_ker_equiv_range]
noncomputable def quotient_ker_equiv_range : (quotient (ker φ)) ≃ set.range φ :=
@equiv.of_bijective _ (set.range φ) (λ x, ⟨lift (ker φ) φ
  (by simp [mem_ker]) x, by exact quotient.induction_on' x (λ x, ⟨x, rfl⟩)⟩)
⟨λ a b h, injective_ker_lift _ (subtype.mk.inj h),
  λ ⟨x, y, hy⟩, ⟨mk y, subtype.eq hy⟩⟩

noncomputable def quotient_ker_equiv_of_surjective (hφ : function.surjective φ) :
  (quotient (ker φ)) ≃ H :=
calc (quotient_group.quotient (is_group_hom.ker φ)) ≃ set.range φ : quotient_ker_equiv_range _
... ≃ H : ⟨λ a, a.1, λ b, ⟨b, hφ b⟩, λ ⟨_, _⟩, rfl, λ _, rfl⟩

end quotient_group

namespace quotient_add_group
open is_add_group_hom

variables {G : Type u} [_root_.add_group G] (N : set G) [normal_add_subgroup N] {H : Type v} [_root_.add_group H]
variables (φ : G → H) [_root_.is_add_group_hom φ]

noncomputable def quotient_ker_equiv_range : (quotient (ker φ)) ≃ set.range φ :=
@quotient_group.quotient_ker_equiv_range (multiplicative G) _ (multiplicative H) _ φ _

noncomputable def quotient_ker_equiv_of_surjective (hφ : function.surjective φ) : (quotient (ker φ)) ≃ H :=
@quotient_group.quotient_ker_equiv_of_surjective (multiplicative G) _ (multiplicative H) _ φ _ hφ

attribute [to_additive quotient_add_group.quotient_ker_equiv_range] quotient_group.quotient_ker_equiv_range
attribute [to_additive quotient_add_group.quotient_ker_equiv_of_surjective] quotient_group.quotient_ker_equiv_of_surjective

end quotient_add_group
