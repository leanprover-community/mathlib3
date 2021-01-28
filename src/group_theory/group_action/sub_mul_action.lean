/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.group_action.basic
import algebra.group_action_hom
import algebra.module.basic
import data.bundled_set
/-!

# Sets invariant to a `mul_action`

In this file we define `sub_mul_action R M`; a subset of a `mul_action M` which is closed with
respect to scalar multiplication.

For most uses, typically `submodule R M` is more powerful.

## Tags

submodule, mul_action
-/

open function

universes u v
variables {R : Type u} {M : Type v}

set_option old_structure_cmd true

/-- A sub_mul_action is a set which is closed under scalar multiplication.  -/
structure sub_mul_action (R : Type u) (M : Type v) [has_scalar R M] : Type v :=
(carrier : set M)
(smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier)

namespace sub_mul_action

variables [has_scalar R M]

instance : is_bundled_set (sub_mul_action R M) :=
{ mem_type := M,
  set_coe' := sub_mul_action.carrier,
  set_coe_inj' := λ a b h, by { cases a, cases b, congr' } }

instance : has_top (sub_mul_action R M) :=
⟨{ carrier := set.univ, smul_mem' := λ _ _ _, set.mem_univ _ }⟩

instance : has_bot (sub_mul_action R M) :=
⟨{ carrier := ∅, smul_mem' := λ c, set.not_mem_empty}⟩

instance : inhabited (sub_mul_action R M) := ⟨⊥⟩

variables (p q : sub_mul_action R M)

variables {p q}

@[ext] theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := is_bundled_set.ext h

end sub_mul_action

namespace sub_mul_action

section has_scalar

variables [has_scalar R M]
variables (p : sub_mul_action R M)
variables {r : R} {x : M}

lemma smul_mem (r : R) (h : x ∈ p) : r • x ∈ p := p.smul_mem' r h

instance : has_scalar R p :=
{ smul := λ c x, ⟨c • x.1, smul_mem _ c x.2⟩ }

variables {p}
@[simp, norm_cast] lemma coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • ↑x := rfl
@[simp, norm_cast] lemma coe_mk (x : M) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : M) = x := rfl
@[simp] lemma coe_mem (x : p) : (x : M) ∈ p := x.2

variables {p}

@[simp] protected lemma eta (x : p) (hx : (x : M) ∈ p) : (⟨x, hx⟩ : p) = x := subtype.eta x hx

variables (p)

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →[R] M :=
by refine {to_fun := coe, ..}; simp [coe_smul]

@[simp] theorem subtype_apply (x : p) : p.subtype x = x := rfl

lemma subtype_eq_val : ((sub_mul_action.subtype p) : p → M) = subtype.val := rfl

end has_scalar

section mul_action

variables [monoid R]

variables [mul_action R M]
variables (p : sub_mul_action R M)
variables {r : R} {x : M}

@[simp] lemma smul_mem_iff' (u : units R) : (u : R) • x ∈ p ↔ x ∈ p :=
⟨λ h, by simpa only [smul_smul, u.inv_mul, one_smul] using p.smul_mem ↑u⁻¹ h, p.smul_mem u⟩

/-- If the scalar product forms a `mul_action`, then the subset inherits this action -/
instance : mul_action R p :=
{ smul := (•),
  one_smul := λ x, subtype.ext $ one_smul _ x,
  mul_smul := λ c₁ c₂ x, subtype.ext $ mul_smul c₁ c₂ x }

end mul_action

section semimodule

variables [semiring R] [add_comm_monoid M]
variables [semimodule R M]
variables (p : sub_mul_action R M)

lemma zero_mem (h : (p : set M).nonempty) : (0 : M) ∈ p :=
let ⟨x, hx⟩ := h in zero_smul R (x : M) ▸ p.smul_mem 0 hx

/-- If the scalar product forms a `semimodule`, and the `sub_mul_action` is not `⊥`, then the
subset inherits the zero. -/
instance [n_empty : nonempty p] : has_zero p :=
{ zero := ⟨0, n_empty.elim $ λ x, p.zero_mem ⟨x, x.prop⟩⟩ }

end semimodule

section add_comm_group

variables [ring R] [add_comm_group M]
variables [semimodule R M]
variables (p p' : sub_mul_action R M)
variables {r : R} {x y : M}

lemma neg_mem (hx : x ∈ p) : -x ∈ p := by { rw ← neg_one_smul R, exact p.smul_mem _ hx }

@[simp] lemma neg_mem_iff : -x ∈ p ↔ x ∈ p :=
⟨λ h, by { rw ←neg_neg x, exact neg_mem _ h}, neg_mem _⟩

instance : has_neg p := ⟨λx, ⟨-x.1, neg_mem _ x.2⟩⟩

@[simp, norm_cast] lemma coe_neg (x : p) : ((-x : p) : M) = -x := rfl

end add_comm_group

end sub_mul_action

namespace sub_mul_action

variables [division_ring R] [add_comm_group M] [module R M]
variables (p : sub_mul_action R M) {r : R} {x y : M}

theorem smul_mem_iff (r0 : r ≠ 0) : r • x ∈ p ↔ x ∈ p :=
p.smul_mem_iff' (units.mk0 r r0)

end sub_mul_action
