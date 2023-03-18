/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Patrick Massot
-/

import ring_theory.valuation.basic
import ring_theory.ideal.quotient_operations

/-!
# The valuation on a quotient ring

The support of a valuation `v : valuation R Γ₀` is `supp v`. If `J` is an ideal of `R`
with `h : J ⊆ supp v` then the induced valuation
on R / J = `ideal.quotient J` is `on_quot v h`.

-/

namespace valuation

variables {R Γ₀ : Type*} [comm_ring R] [linear_ordered_comm_monoid_with_zero Γ₀]
variables (v : valuation R Γ₀)

/-- If `hJ : J ⊆ supp v` then `on_quot_val hJ` is the induced function on R/J as a function.
Note: it's just the function; the valuation is `on_quot hJ`. -/
def on_quot_val {J : ideal R} (hJ : J ≤ supp v) :
  R ⧸ J → Γ₀ :=
λ q, quotient.lift_on' q v $ λ a b h,
calc v a = v (b + -(-a + b)) : by simp
     ... = v b             :
      v.map_add_supp b $ (ideal.neg_mem_iff _).2 $ hJ $ quotient_add_group.left_rel_apply.mp h

/-- The extension of valuation v on R to valuation on R/J if J ⊆ supp v -/
def on_quot {J : ideal R} (hJ : J ≤ supp v) :
  valuation (R ⧸ J) Γ₀ :=
{ to_fun := v.on_quot_val hJ,
  map_zero' := v.map_zero,
  map_one'  := v.map_one,
  map_mul'  := λ xbar ybar, quotient.ind₂' v.map_mul xbar ybar,
  map_add_le_max'  := λ xbar ybar, quotient.ind₂' v.map_add xbar ybar }

@[simp] lemma on_quot_comap_eq {J : ideal R} (hJ : J ≤ supp v) :
  (v.on_quot hJ).comap (ideal.quotient.mk J) = v :=
ext $ λ r, rfl

lemma self_le_supp_comap (J : ideal R) (v : valuation (R ⧸ J) Γ₀) :
  J ≤ (v.comap (ideal.quotient.mk J)).supp :=
by { rw [comap_supp, ← ideal.map_le_iff_le_comap], simp }

@[simp] lemma comap_on_quot_eq (J : ideal R) (v : valuation (R ⧸ J) Γ₀) :
  (v.comap (ideal.quotient.mk J)).on_quot (v.self_le_supp_comap J) = v :=
ext $ by { rintro ⟨x⟩, refl }

/-- The quotient valuation on R/J has support supp(v)/J if J ⊆ supp v. -/
lemma supp_quot {J : ideal R} (hJ : J ≤ supp v) :
  supp (v.on_quot hJ) = (supp v).map (ideal.quotient.mk J) :=
begin
  apply le_antisymm,
  { rintro ⟨x⟩ hx,
    apply ideal.subset_span,
    exact ⟨x, hx, rfl⟩ },
  { rw ideal.map_le_iff_le_comap,
    intros x hx, exact hx }
end

lemma supp_quot_supp : supp (v.on_quot le_rfl) = 0 :=
by { rw supp_quot, exact ideal.map_quotient_self _ }

end valuation

namespace add_valuation

variables {R Γ₀ : Type*}
variables [comm_ring R] [linear_ordered_add_comm_monoid_with_top Γ₀]
variables (v : add_valuation R Γ₀)

local attribute [reducible] add_valuation

/-- If `hJ : J ⊆ supp v` then `on_quot_val hJ` is the induced function on R/J as a function.
Note: it's just the function; the valuation is `on_quot hJ`. -/
def on_quot_val {J : ideal R} (hJ : J ≤ supp v) : (R ⧸ J) → Γ₀ := v.on_quot_val hJ

/-- The extension of valuation v on R to valuation on R/J if J ⊆ supp v -/
def on_quot {J : ideal R} (hJ : J ≤ supp v) :
  add_valuation (R ⧸ J) Γ₀ :=
v.on_quot hJ

@[simp] lemma on_quot_comap_eq {J : ideal R} (hJ : J ≤ supp v) :
  (v.on_quot hJ).comap (ideal.quotient.mk J) = v :=
v.on_quot_comap_eq hJ

lemma comap_supp {S : Type*} [comm_ring S] (f : S →+* R) :
  supp (v.comap f) = ideal.comap f v.supp :=
v.comap_supp f

lemma self_le_supp_comap (J : ideal R) (v : add_valuation (R ⧸ J) Γ₀) :
  J ≤ (v.comap (ideal.quotient.mk J)).supp :=
v.self_le_supp_comap J

@[simp] lemma comap_on_quot_eq (J : ideal R) (v : add_valuation (R ⧸ J) Γ₀) :
  (v.comap (ideal.quotient.mk J)).on_quot (v.self_le_supp_comap J) = v :=
v.comap_on_quot_eq J

/-- The quotient valuation on R/J has support supp(v)/J if J ⊆ supp v. -/
lemma supp_quot {J : ideal R} (hJ : J ≤ supp v) :
  supp (v.on_quot hJ) = (supp v).map (ideal.quotient.mk J) :=
v.supp_quot hJ

lemma supp_quot_supp : supp (v.on_quot le_rfl) = 0 :=
v.supp_quot_supp

end add_valuation
