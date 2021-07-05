/-
Copyright (c) 2021 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import algebra.algebra.basic
import algebra.monoid_algebra

/-!
# Representations
Closely following module.basic
-/

/--
Representation of monoid G as a k-module M is a k-linear G-action on M.
-/
class repre
  (k : Type*) (G : Type*) (M : Type*)
  [semiring k] [monoid G] [add_comm_monoid M] [module k M]
extends distrib_mul_action G M :=
(smul_smul : ∀ (g : G) (r : k) (m : M), g • (r • m) = r • (g • m))

/--
Representation obtained from a monoid_hom from G to endomorphisms on M
-/
def of_monoid_hom
  {k : Type*} {G : Type*} {M : Type*}
  [semiring k] [monoid G] [add_comm_monoid M] [module k M]
  (ρ : G →* M →ₗ[k] M) : repre k G M :=
{ to_distrib_mul_action :=
  { to_mul_action :=
    { to_has_scalar := ⟨λ g x, ρ g x⟩,
      one_smul := by simp,
      mul_smul := by simp },
    smul_add := by simp,
    smul_zero := by simp },
  smul_smul := by simp }

section

/--
G-action as an endomorphism.
-/
def linear_map_of_smul
  (k : Type*) (G : Type*) (M : Type*)
  [semiring k] [monoid G] [add_comm_monoid M] [module k M] [repre k G M] (g : G) : M →ₗ[k] M :=
{ to_fun := λ x : M, g • x,
  map_add' := by {intros x y, apply smul_add},
  map_smul' := by {intros r x, apply repre.smul_smul} }

variables
  {k : Type*} {G : Type*} {M : Type*}
  [semiring k] [monoid G] [add_comm_monoid M] [module k M] [repre k G M]

@[simp]
lemma linear_map_of_smul_apply (g : G) (x : M) :
(linear_map_of_smul k G M g : M →ₗ[k] M) x = g • x := rfl

/-
Representation of G as a monoid_hom from G to the monoid of endomorphisms of M.
-/
def to_monoid_hom : G →* M →ₗ[k] M :=
{ to_fun := linear_map_of_smul k G M,
  map_one' := by {ext, simp},
  map_mul' := by {intros g h, ext, simp, apply mul_smul} }

end

@[simp]
lemma mul_smul
  {k : Type*} {G : Type*} {M : Type*}
  [semiring k] [monoid G] [add_comm_monoid M] [module k M] [repre k G M] :
  ∀ (g h : G) (x : M), (g * h) • x = g • h • x := mul_smul

@[simp]
lemma smul_smul2
  {k : Type*} {G : Type*} {M : Type*}
  [semiring k] [monoid G] [add_comm_monoid M] [module k M] [s : repre k G M] :
  ∀ (g : G) (r : k) (m : M), g • (r • m) = r • (g • m) := by {intros, apply s.smul_smul}

protected
theorem repre.subsingleton (k : Type*) (G : Type*) (M : Type*)
  [semiring k] [monoid G] [add_comm_monoid M] [module k M] [repre k G M] [subsingleton k] :
  subsingleton M :=
⟨λ x y, by rw [← one_smul k x, ← one_smul k y, subsingleton.elim (1:k) 0, zero_smul, zero_smul]⟩