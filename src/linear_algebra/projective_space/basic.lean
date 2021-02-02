/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colter MacDonald, Adam Topaz
-/
import tactic
import group_theory.group_action.basic
import algebra.invertible
import linear_algebra

/-!
# Projective spaces

TODO : Add docs

-/

variables (K : Type*) [field K]
variables (V : Type*) [add_comm_group V] [vector_space K V]
variables {W : Type*} [add_comm_group W] [vector_space K W]

/-- The nonzero elements of a vector space. -/
def nonzero := {v : V // v ≠ 0}

variables {K V}

namespace nonzero

instance : has_coe (nonzero V) V := ⟨λ v, v.1⟩

noncomputable instance [nontrivial V] : inhabited (nonzero V) := inhabited.mk $
⟨classical.some $ exists_ne 0, classical.some_spec $ exists_ne 0⟩

lemma coe_nonzero (v : nonzero V) : (v : V) ≠ 0 := v.2

/-- Map a nonzero vector with respect to an injective map. -/
def map {f : V →ₗ[K] W} (inj : function.injective f) : nonzero V → nonzero W := λ v,
{ val := f v,
  property := by { rw ← f.map_zero, exact λ c, coe_nonzero v (inj c) } }

@[simp] lemma coe_map {f : V →ₗ[K] W} {inj : function.injective f} {v : nonzero V} :
  (nonzero.map inj v : W) = f v := rfl

@[ext] lemma ext {v w : nonzero V} : (v : V) = w → v = w :=
by {cases v, cases w, simp}

@[simps]
instance : has_scalar (units K) (nonzero V) :=
{ smul := λ u v, ⟨(u : K) • v, λ c, coe_nonzero v $ by simpa using c⟩ }

instance : mul_action (units K) (nonzero V) :=
{ one_smul := λ x, by tidy,
  mul_smul := λ x y v, nonzero.ext $ by simp [mul_smul] }

lemma is_unit_of_smul_eq {v : V} {w : nonzero V} {a : K} : a • v = w → is_unit a :=
λ h, is_unit_iff_ne_zero.mpr $ λ c, coe_nonzero w $ by simp [← h, c]

end nonzero

variables (K V)
/-- The Projectivization of `V` as a `K` vector space. -/
def proj_space := quotient (mul_action.orbit_rel (units K) (nonzero V))
variables {K V}

namespace proj_space

local attribute [instance] mul_action.orbit_rel

/-- Given a nonzero vector, construct an element in the projectivization of `V`. -/
def mk : nonzero V → proj_space K V := quotient.mk

noncomputable instance [nontrivial V] : inhabited (proj_space K V) := ⟨mk $ default _⟩

lemma mk_eq_mk {v w : nonzero V} : (mk v : proj_space K V) = mk w ↔
  ∃ (u : units K), u • w = v :=
begin
  change quotient.mk _ = quotient.mk _ ↔ _,
  rw quotient.eq,
  change v ∈ mul_action.orbit _ _ ↔ _,
  simp [mul_action.orbit],
end

lemma mk_eq_mk' {v w : nonzero V} : (mk v : proj_space K V) = mk w ↔
  ∃ (u : K), u • (w : V) = v :=
begin
  rw mk_eq_mk,
  split,
  { rintro ⟨u,rfl⟩,
    exact ⟨u,rfl⟩ },
  { rintro ⟨u,hu⟩,
    refine ⟨is_unit.unit (nonzero.is_unit_of_smul_eq hu), nonzero.ext _⟩,
    simp [← hu, is_unit.unit_spec] }
end

/--
Map an element in the projecivization of a vector space with respect to an injective linear map.
-/
def map {f : V →ₗ[K] W} (inj : function.injective f) : proj_space K V → proj_space K W :=
quotient.lift (λ v, quotient.mk $ nonzero.map inj v) $
by {rintros v w ⟨a,rfl⟩, refine quotient.sound ⟨a,nonzero.ext $ by simp⟩}

end proj_space
