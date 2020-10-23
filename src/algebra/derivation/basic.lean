/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.algebra.basic
import group_theory.free_abelian_group

/-!
# Kähler differentials

In this file we define derivations and Kähler differentials.
-/

universes u v w u₁ v₁ w₁

variables (R : Type u) (A : Type v) [comm_ring R] [comm_ring A] [algebra R A]
variables (M : Type w) [add_comm_group M] [module A M]

/-- The derivations to a given module. -/
@[nolint has_inhabited_instance] structure derivation :=
(to_fun : A → M)
(add : ∀ x y, to_fun (x + y) = to_fun x + to_fun y)
(mul : ∀ x y, to_fun (x * y) = x • to_fun y + y • to_fun x)
(algebra : ∀ r : R, to_fun (algebra_map R A r) = 0)

namespace derivation

instance : has_coe_to_fun (derivation R A M) :=
⟨λ D, A → M, derivation.to_fun⟩

instance : has_coe (derivation R A M) (A →+ M) :=
⟨λ f, add_monoid_hom.mk' f f.2⟩

section
variables {R A M} (D : derivation R A M) (r : R) (a b : A)
theorem map_add : D (a + b) = D a + D b := D.add a b
theorem map_zero : D 0 = 0 := (D : A →+ M).map_zero
theorem map_neg : D (-a) = -D a := (D : A →+ M).map_neg a
theorem map_sub : D (a - b) = D a - D b := (D : A →+ M).map_sub a b
theorem map_mul : D (a * b) = a • D b + b • D a := D.mul a b
theorem map_mul_comm : D (a * b) = b • D a + a • D b := (D.mul a b).trans $ add_comm _ _
theorem map_algebra_map : D (algebra_map R A r) = 0 := D.algebra r

@[ext] theorem ext : Π {D1 D2 : derivation R A M}, (∀ a, D1 a = D2 a) → D1 = D2
| ⟨f, _, _, _⟩ ⟨g, _, _, _⟩ H := mk.inj_eq.mpr $ funext H
end

instance : add_comm_group (derivation R A M) :=
by refine
{ add := λ D1 D2, ⟨λ a, D1 a + D2 a,
    λ a1 a2, by rw [D1.map_add, D2.map_add, add_add_add_comm],
    λ a1 a2, by rw [D1.map_mul, D2.map_mul, smul_add, smul_add, add_add_add_comm],
    λ r, by rw [D1.map_algebra_map, D2.map_algebra_map, add_zero]⟩,
  zero := ⟨λ a, 0,
    λ a1 a2, by rw add_zero,
    λ a1 a2, by rw [smul_zero, smul_zero, add_zero],
    λ r, rfl⟩,
  neg := λ D, ⟨λ a, -D a,
    λ a1 a2, by rw [D.map_add, neg_add],
    λ a1 a2, by rw [D.map_mul, neg_add, smul_neg, smul_neg],
    λ r, by rw [D.map_algebra_map, neg_zero]⟩,
  .. };
{ intros, ext, exact add_assoc _ _ _ <|> exact zero_add _ <|>
  exact add_zero _ <|> exact add_left_neg _ <|> exact add_comm _ _ }

instance : module A (derivation R A M) :=
{ smul := λ a D, ⟨λ b, a • D b,
    λ a1 a2, by rw [D.map_add, smul_add],
    λ a1 a2, by rw [D.map_mul, smul_add, smul_smul, smul_smul, mul_comm, mul_smul, mul_comm, mul_smul],
    λ s, by rw [D.map_algebra_map, smul_zero]⟩,
  mul_smul := λ a1 a2 D, ext $ λ b, mul_smul _ _ _,
  one_smul := λ D, ext $ λ b, one_smul A _,
  smul_add := λ a D1 D2, ext $ λ b, smul_add _ _ _,
  smul_zero := λ a, ext $ λ b, smul_zero _,
  add_smul := λ a1 a2 D, ext $ λ b, add_smul _ _ _,
  zero_smul := λ D, ext $ λ b, zero_smul A _ }

section
variables {R A M} (a : A) (D D1 D2 : derivation R A M) (b : A)
@[simp] lemma add_apply : (D1 + D2) b = D1 b + D2 b := rfl
@[simp] lemma zero_apply : (0 : derivation R A M) b = 0 := rfl
@[simp] lemma neg_apply : (-D) b = -(D b) := rfl
@[simp] lemma sub_apply : (D1 - D2) b = D1 b - D2 b := rfl
set_option class.instance_max_depth 41
@[simp] lemma smul_apply : (a • D) b = a • (D b) := rfl
end

variables {R A M}
/-- The composition of a derivation with a linear map as a derivation. -/
def comp {N : Type u₁} [add_comm_group N] [module A N]
  (D : derivation R A M) (f : M →ₗ[A] N) : derivation R A N :=
{ to_fun := λ a, f (D a),
  add := λ a1 a2, by rw [D.map_add, f.map_add],
  mul := λ a1 a2, by rw [D.map_mul, f.map_add, f.map_smul, f.map_smul],
  algebra := λ r, by rw [D.map_algebra_map, f.map_zero] }

@[simp] lemma comp_apply {N : Type u₁} [add_comm_group N] [module A N]
  (D : derivation R A M) (f : M →ₗ[A] N) (x) : D.comp f x = f (D x) := rfl

end derivation

variables (R A)

/-- The relators defining the Kähler module. -/
def Kaehler.relators : set (free_abelian_group (A × A)) :=
{ x : free_abelian_group (A × A) |
  (∃ a b c : A, free_abelian_group.of (a + b, c) - (free_abelian_group.of (a, c) + free_abelian_group.of (b, c)) = x) ∨
  (∃ a b c : A, free_abelian_group.of (a, b + c) - (free_abelian_group.of (a, b) + free_abelian_group.of (a, c)) = x) ∨
  (∃ a b c : A, free_abelian_group.of (a, b * c) - (free_abelian_group.of (a * b, c) + free_abelian_group.of (a * c, b)) = x) ∨
  (∃ a : A, ∃ r : R, free_abelian_group.of (a, algebra_map R A r) = x) }

/-- The Kähler module classifying derivations. -/
@[reducible] def Kaehler : Type v :=
quotient_add_group.quotient $ add_subgroup.closure $ Kaehler.relators R A

namespace Kaehler

instance : add_comm_group (Kaehler R A) := quotient_add_group.add_comm_group _

instance : normal_add_subgroup (add_group.closure (relators R A)) :=
{ normal := λ n hn g, by rwa add_sub_cancel' }

instance : has_scalar A (Kaehler R A) :=
begin
  refine ⟨λ a, quotient_add_group.lift _
    (free_abelian_group.lift $ λ p : A × A, quotient_add_group.mk $ free_abelian_group.of (a * p.1, p.2)) _⟩,
  intros x hx, refine add_subgroup.closure_induction hx _ _ _ _,
  { intros y hy, rcases hy with ⟨b,c,d,rfl⟩ | ⟨b,c,d,rfl⟩ | ⟨b,c,d,rfl⟩ | ⟨b,r,rfl⟩,
    { rw [free_abelian_group.lift.sub, free_abelian_group.lift.add,
          free_abelian_group.lift.of, free_abelian_group.lift.of, free_abelian_group.lift.of],
      refine eq.symm (quotient.sound' _),
      change _ ∈ _, rw [neg_zero, zero_add, mul_add],
      exact add_subgroup.subset_closure (or.inl ⟨_, _, _, rfl⟩) },
    { rw [free_abelian_group.lift.sub, free_abelian_group.lift.add,
          free_abelian_group.lift.of, free_abelian_group.lift.of, free_abelian_group.lift.of],
      refine eq.symm (quotient.sound' _),
      change _ ∈ _, rw [neg_zero, zero_add],
      exact add_subgroup.subset_closure (or.inr $ or.inl ⟨_, _, _, rfl⟩) },
    { rw [free_abelian_group.lift.sub, free_abelian_group.lift.add,
          free_abelian_group.lift.of, free_abelian_group.lift.of, free_abelian_group.lift.of],
      refine eq.symm (quotient.sound' _),
      change _ ∈ _, rw [neg_zero, zero_add, ← mul_assoc, ← mul_assoc],
      exact add_subgroup.subset_closure (or.inr $ or.inr $ or.inl ⟨_, _, _, rfl⟩) },
    { rw free_abelian_group.lift.of,
      refine eq.symm (quotient.sound' _),
      change _ ∈ _, rw [neg_zero, zero_add],
      exact add_subgroup.subset_closure (or.inr $ or.inr $ or.inr ⟨_, _, rfl⟩) } },
  { exact free_abelian_group.lift.zero _ },
  { intros x y ihx ihy, rw [free_abelian_group.lift.add, ihx, ihy, add_zero] },
  { intros x ih, rw [free_abelian_group.lift.neg, ih, neg_zero] }
end

instance : module A (Kaehler R A) :=
begin
  refine { smul := (•), .. },
  { intros x, refine quotient_add_group.induction_on x (λ p, _),
    dsimp only [(•)], rw quotient_add_group.lift_mk',
    refine free_abelian_group.induction_on p rfl _ _ _,
    { rintros ⟨p1, p2⟩, rw [free_abelian_group.lift.of, one_mul] },
    { intros p ih, rw [free_abelian_group.lift.neg, ih], refl },
    { intros p q ihp ihq, rw [free_abelian_group.lift.add, ihp, ihq], refl } },
  { intros a1 a2 x, refine quotient_add_group.induction_on x (λ p, _),
    dsimp only [(•)], simp only [quotient_add_group.lift_mk'],
    refine free_abelian_group.induction_on p rfl _ _ _,
    { rintros ⟨p1, p2⟩, rw [free_abelian_group.lift.of, free_abelian_group.lift.of,
          quotient_add_group.lift_mk', free_abelian_group.lift.of, ← mul_assoc] },
    { intros p ih, rw [free_abelian_group.lift.neg, free_abelian_group.lift.neg, ih], refl },
    { intros p q ihp ihq,
      rw [free_abelian_group.lift.add, free_abelian_group.lift.add, ihp, ihq, add_monoid_hom.map_add], } },
  { intros r x y, exact add_monoid_hom.map_add _ _ _ },
  { intros r, refl },
  { intros r s x, refine quotient_add_group.induction_on x (λ p, _),
    dsimp only [(•)], simp only [quotient_add_group.lift_mk'],
    refine free_abelian_group.induction_on p rfl _ _ _,
    { rintros ⟨p1, p2⟩, rw [free_abelian_group.lift.of, free_abelian_group.lift.of, free_abelian_group.lift.of, add_mul],
      refine eq.symm (quotient.sound' (_ : _ ∈ _)), rw add_comm,
      exact add_subgroup.subset_closure (or.inl ⟨_, _, _, rfl⟩) },
    { intros p ih, rw [free_abelian_group.lift.neg, ih, neg_add], refl },
    { intros p q ihp ihq, rw [free_abelian_group.lift.add, free_abelian_group.lift.add, free_abelian_group.lift.add, ihp, ihq, add_add_add_comm] } },
  { intros x, refine quotient_add_group.induction_on x (λ p, _),
    dsimp only [(•)], simp only [quotient_add_group.lift_mk'],
    refine free_abelian_group.induction_on p rfl _ _ _,
    { rintros ⟨p1, p2⟩, rw [free_abelian_group.lift.of, zero_mul],
      refine quotient.sound' (_ : _ ∈ _), rw add_zero,
      refine add_subgroup.subset_closure (or.inl ⟨0, 0, p2, _⟩),
      rw [← sub_sub, add_zero, sub_self, zero_sub] },
    { intros p ih, rw [free_abelian_group.lift.neg, ih, neg_zero] },
    { intros p q ihp ihq, rw [free_abelian_group.lift.add, ihp, ihq, add_zero] } }
end

/-- The standard derivation to the Kaehler module. -/
def D : derivation R A (Kaehler R A) :=
{ to_fun := λ a, quotient_add_group.mk $ free_abelian_group.of (1, a),
  add := λ a b, eq.symm $ quotient.sound' $ show _ ∈ _,
    by rw add_comm; exact add_subgroup.subset_closure (or.inr $ or.inl ⟨_, _, _, rfl⟩),
  mul := λ a b, by dsimp only [(•)]; simp only [quotient_add_group.lift_mk', free_abelian_group.lift.of, mul_comm _ (1:A)];
    exact eq.symm (quotient.sound' $ add_subgroup.subset_closure $ or.inr $ or.inr $ or.inl ⟨1, a, b, by rw sub_eq_neg_add⟩),
  algebra := λ r, eq.symm $ quotient.sound' $ add_subgroup.subset_closure $ or.inr $ or.inr $ or.inr ⟨1, r, by rw [neg_zero, zero_add]⟩ }

variables {R A}

theorem smul_D (a b : A) : a • D R A b = free_abelian_group.of (a, b) :=
(free_abelian_group.lift.of _ _).trans $ by { erw mul_one, refl }

@[elab_as_eliminator] theorem induction_on {C : Kaehler R A → Prop} (p : Kaehler R A)
  (hd : ∀ a b, C ((a : A) • D R A b)) (ha : ∀ a b, C a → C b → C (a+b)) : C p :=
quotient_add_group.induction_on p $ λ p, free_abelian_group.induction_on p
  (by simpa only [zero_smul] using hd 0 0)
  (λ ⟨a, b⟩, by have := hd a b; rwa smul_D at this)
  (λ ⟨a, b⟩ ih, by have := hd (-a) b; rwa [neg_smul, smul_D] at this)
  (λ _ _, ha _ _)

@[elab_as_eliminator] theorem induction_on' {C : Kaehler R A → Prop} (p : Kaehler R A)
  (hd : ∀ a b, C (quotient_add_group.mk $ free_abelian_group.of (a, b))) (ha : ∀ a b, C a → C b → C (a+b)) : C p :=
induction_on p (λ a b, by rw smul_D; apply hd) ha

end Kaehler

namespace derivation

variables {R A M}

/-- A derivation induces a linear map from the module of Kähler differentials. -/
def factor (D : derivation R A M) : Kaehler R A →ₗ[A] M :=
begin
  refine { to_fun := quotient_add_group.lift _ (free_abelian_group.lift $ λ p : A × A, p.1 • D p.2) $ λ x hx,
    add_subgroup.closure_induction hx
      (λ p hp, _)
      (free_abelian_group.lift.zero _)
      (λ p q ihp ihq, by rw [free_abelian_group.lift.add, ihp, ihq, add_zero])
      (λ p ih, by rw [free_abelian_group.lift.neg, ih, neg_zero]),
  map_add' := add_monoid_hom.map_add _,
  map_smul' := λ a p, _ },
  rcases hp with ⟨a,b,c,rfl⟩|⟨a,b,c,rfl⟩|⟨a,b,c,rfl⟩|⟨a,r,rfl⟩,
  { simp only [free_abelian_group.lift.add, free_abelian_group.lift.sub, free_abelian_group.lift.of, add_smul, sub_self] },
  { simp only [free_abelian_group.lift.add, free_abelian_group.lift.sub, free_abelian_group.lift.of, D.map_add, smul_add, sub_self] },
  { simp only [free_abelian_group.lift.add, free_abelian_group.lift.sub,
            free_abelian_group.lift.of, D.map_mul, smul_add, mul_smul, sub_self] },
  { simp only [free_abelian_group.lift.add, free_abelian_group.lift.sub,
            free_abelian_group.lift.of, D.map_algebra_map, smul_zero, sub_self] },
  exact Kaehler.induction_on p
    (λ b c, by rw [smul_smul, Kaehler.smul_D, quotient_add_group.lift_mk, free_abelian_group.lift.of,
        Kaehler.smul_D, quotient_add_group.lift_mk, free_abelian_group.lift.of, mul_smul])
    (λ q r ihq ihr, by rw [smul_add, add_monoid_hom.map_add, ihq, ihr,
        add_monoid_hom.map_add, smul_add])
end

theorem factor_D (D : derivation R A M) (a : A) : D.factor (Kaehler.D R A a) = D a :=
(free_abelian_group.lift.of _ _).trans $ one_smul _ _

theorem factor_comp (D : derivation R A M) : (Kaehler.D R A).comp D.factor = D :=
ext $ D.factor_D

theorem comp_factor (f : Kaehler R A →ₗ[A] M) : ((Kaehler.D R A).comp f).factor = f :=
linear_map.ext $ λ p, Kaehler.induction_on p
  (λ a b, by simp_rw [linear_map.map_smul, factor_D, comp_apply])
  (λ p q ihp ihq, by rw [f.map_add, linear_map.map_add, ihp, ihq])

/-- The derivations are classified by the Kähler module. -/
def linear_equiv : derivation R A M ≃ₗ[A] (Kaehler R A →ₗ[A] M) :=
{ to_fun := factor,
  inv_fun := (Kaehler.D R A).comp,
  left_inv := λ D, D.factor_comp,
  right_inv := λ f, comp_factor f,
  map_add' := λ D1 D2, linear_map.ext $ λ p, Kaehler.induction_on p
    (λ a b, by rw [linear_map.map_smul, linear_map.map_smul, linear_map.add_apply,
        factor_D, factor_D, factor_D, derivation.add_apply])
    (λ p q ihp ihq, by rw [linear_map.map_add, linear_map.map_add, ihp, ihq]),
  map_smul' := λ a D, linear_map.ext $ λ p, Kaehler.induction_on p
    (λ b c, by rw [linear_map.smul_apply, linear_map.map_smul, linear_map.map_smul,
        factor_D, factor_D, derivation.smul_apply, smul_smul, smul_smul, mul_comm])
    (λ p q ihp ihq, by rw [linear_map.map_add, linear_map.map_add, ihp, ihq]) }

end derivation
