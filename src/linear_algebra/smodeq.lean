/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import data.polynomial.eval
import ring_theory.ideal.quotient
import group_theory.subgroup.basic

/-!
# modular equivalence for submodule
-/

open submodule
open_locale polynomial

variables {M X : Type*} [add_comm_group M] [set_like X M] [add_subgroup_class X M] (U U₁ U₂ : X)
variables {R : Type*} [ring R] [module R M] (Ug : add_subgroup M) (Us : submodule R M)
variables {x x₁ x₂ y y₁ y₂ z z₁ z₂ : M}
variables {N : Type*} [add_comm_group N] [module R N] (V V₁ V₂ : submodule R N)

/-- A predicate saying two elements of a additive group are equivalent modulo a subgroup. -/
def smodeq (x y : M) : Prop :=
x - y ∈ U

notation x ` ≡ `:50 y ` [SMOD `:50 N `]`:0 := smodeq N x y

variables {U U₁ U₂ Us Ug}

protected lemma smodeq.def : x ≡ y [SMOD U] ↔ x - y ∈ U :=
iff.rfl

namespace smodeq

protected lemma smodeq.iff_coe_eq : x ≡ y [SMOD Ug] ↔
  (x : M ⧸ Ug) = y :=
by { rw [quotient_add_group.eq, ← neg_mem_iff, smodeq.def, neg_add', neg_neg] }

protected lemma smodeq.iff_mkq_eq : x ≡ y [SMOD Us] ↔
  Us.mkq x = Us.mkq y :=
@smodeq.iff_coe_eq _ _ Us.to_add_subgroup x y

@[simp] theorem top_submodule : x ≡ y [SMOD (⊤ : submodule R M)] :=
trivial

@[simp] theorem bot_submodule : x ≡ y [SMOD (⊥ : submodule R M)] ↔ x = y :=
by rw [smodeq.def, mem_bot, sub_eq_zero]

@[mono] theorem mono (HU : U₁ ≤ U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD U₂] :=
HU hxy

@[refl] theorem refl : x ≡ x [SMOD U] := by { rw [smodeq.def, sub_self], exact zero_mem _ }

@[symm] theorem symm (hxy : x ≡ y [SMOD U]) : y ≡ x [SMOD U] :=
by rwa [smodeq.def, ← neg_mem_iff, neg_sub]

@[trans] theorem trans (hxy : x ≡ y [SMOD U]) (hyz : y ≡ z [SMOD U]) : x ≡ z [SMOD U] :=
by { rw smodeq.def, convert add_mem hxy hyz, rw [sub_add, sub_sub_cancel] }

lemma comm : x ≡ y [SMOD U] ↔ y ≡ x [SMOD U] := ⟨symm, symm⟩

theorem add (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) : x₁ + x₂ ≡ y₁ + y₂ [SMOD U] :=
by { rw smodeq.def, convert add_mem hxy₁ hxy₂, rw add_sub_add_comm }

theorem smul (hxy : x ≡ y [SMOD Us]) (c : R) : c • x ≡ c • y [SMOD Us] :=
by { rw smodeq.iff_mkq_eq at hxy ⊢, simp_rw [Us.mkq.map_smul, hxy] }

theorem zero : x ≡ 0 [SMOD U] ↔ x ∈ U :=
by rw [smodeq.def, sub_zero]

lemma congr (hxy₁ : x₁ ≡ y₁ [SMOD U]) (hxy₂ : x₂ ≡ y₂ [SMOD U]) :
  x₁ ≡ x₂ [SMOD U] ↔ y₁ ≡ y₂ [SMOD U] :=
⟨λ e, hxy₁.symm.trans (e.trans hxy₂), λ e, hxy₁.trans (e.trans hxy₂.symm)⟩

lemma mem_iff (hxy : x ≡ y [SMOD U]) : x ∈ U ↔ y ∈ U :=
by { rw [← zero, ← zero], exact congr hxy refl }

theorem map (hxy : x ≡ y [SMOD Us]) (f : M →ₗ[R] N) : f x ≡ f y [SMOD Us.map f] :=
by { rw [smodeq.def, ← map_sub], exact mem_map_of_mem hxy }

theorem comap {f : M →ₗ[R] N} (hxy : f x ≡ f y [SMOD V]) : x ≡ y [SMOD V.comap f] :=
by rwa [smodeq.def, mem_comap, map_sub]

lemma eval {R : Type*} [comm_ring R] {I : ideal R} {x y : R} (h : x ≡ y [SMOD I])
  (f : R[X]) : f.eval x ≡ f.eval y [SMOD I] :=
begin
  rw [smodeq.iff_mkq_eq] at h ⊢,
  show ideal.quotient.mk I (f.eval x) = ideal.quotient.mk I (f.eval y),
  change ideal.quotient.mk I x = ideal.quotient.mk I y at h,
  rw [← polynomial.eval₂_at_apply, ← polynomial.eval₂_at_apply, h],
end

end smodeq
