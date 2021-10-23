/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import data.polynomial.eval
import ring_theory.ideal.quotient

/-!
# modular equivalence for submodule
-/

open submodule

variables {R : Type*} [ring R]
variables {M : Type*} [add_comm_group M] [module R M] (U U₁ U₂ : submodule R M)
variables {x x₁ x₂ y y₁ y₂ z z₁ z₂ : M}
variables {N : Type*} [add_comm_group N] [module R N] (V V₁ V₂ : submodule R N)

/-- A predicate saying two elements of a module are equivalent modulo a submodule. -/
def smodeq (x y : M) : Prop :=
(submodule.quotient.mk x : U.quotient) = submodule.quotient.mk y

notation x ` ≡ `:50 y ` [SMOD `:50 N `]`:0 := smodeq N x y

variables {U U₁ U₂}

protected lemma smodeq.def : x ≡ y [SMOD U] ↔
  (submodule.quotient.mk x : U.quotient) = submodule.quotient.mk y := iff.rfl

namespace smodeq

lemma sub_mem : x ≡ y [SMOD U] ↔ x - y ∈ U :=
by rw [smodeq.def, submodule.quotient.eq]

@[simp] theorem top : x ≡ y [SMOD (⊤ : submodule R M)] :=
(submodule.quotient.eq ⊤).2 mem_top

@[simp] theorem bot : x ≡ y [SMOD (⊥ : submodule R M)] ↔ x = y :=
by rw [smodeq.def, submodule.quotient.eq, mem_bot, sub_eq_zero]

@[mono] theorem mono (HU : U₁ ≤ U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD U₂] :=
(submodule.quotient.eq U₂).2 $ HU $ (submodule.quotient.eq U₁).1 hxy

@[refl] theorem refl : x ≡ x [SMOD U] := eq.refl _

@[symm] theorem symm (hxy : x ≡ y [SMOD U]) : y ≡ x [SMOD U] := hxy.symm

@[trans] theorem trans (hxy : x ≡ y [SMOD U]) (hyz : y ≡ z [SMOD U]) : x ≡ z [SMOD U] :=
hxy.trans hyz

theorem add (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ + x₂ ≡ y₁ + y₂ [SMOD U] :=
by { rw smodeq.def at hxy₁ hxy₂ ⊢, simp_rw [quotient.mk_add, hxy₁, hxy₂] }

theorem smul (hxy : x ≡ y [SMOD U]) (c : R) : c • x ≡ c • y [SMOD U] :=
by { rw smodeq.def at hxy ⊢, simp_rw [quotient.mk_smul, hxy] }

theorem zero : x ≡ 0 [SMOD U] ↔ x ∈ U :=
by rw [smodeq.def, submodule.quotient.eq, sub_zero]

theorem map (hxy : x ≡ y [SMOD U]) (f : M →ₗ[R] N) : f x ≡ f y [SMOD U.map f] :=
(submodule.quotient.eq _).2 $ f.map_sub x y ▸ mem_map_of_mem $ (submodule.quotient.eq _).1 hxy

theorem comap {f : M →ₗ[R] N} (hxy : f x ≡ f y [SMOD V]) : x ≡ y [SMOD V.comap f] :=
(submodule.quotient.eq _).2 $ show f (x - y) ∈ V,
from (f.map_sub x y).symm ▸ (submodule.quotient.eq _).1 hxy

lemma eval {R : Type*} [comm_ring R] {I : ideal R} {x y : R} (h : x ≡ y [SMOD I])
  (f : polynomial R) : f.eval x ≡ f.eval y [SMOD I] :=
begin
  rw [smodeq.def] at h ⊢,
  show ideal.quotient.mk I (f.eval x) = ideal.quotient.mk I (f.eval y),
  change ideal.quotient.mk I x = ideal.quotient.mk I y at h,
  rw [← polynomial.eval₂_at_apply, ← polynomial.eval₂_at_apply, h],
end

end smodeq
