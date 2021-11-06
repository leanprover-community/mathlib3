/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.group_action_hom
import algebra.module.basic
import data.set_like.basic
import group_theory.group_action.basic
/-!

# Sets invariant to a `mul_action`

In this file we define `sub_mul_action R M`; a subset of a `mul_action R M` which is closed with
respect to scalar multiplication.

For most uses, typically `submodule R M` is more powerful.

## Main definitions

* `sub_mul_action.mul_action` - the `mul_action R M` transferred to the subtype.
* `sub_mul_action.mul_action'` - the `mul_action S M` transferred to the subtype when
  `is_scalar_tower S R M`.
* `sub_mul_action.is_scalar_tower` - the `is_scalar_tower S R M` transferred to the subtype.

## Tags

submodule, mul_action
-/

open function

universes u u' u'' v
variables {S : Type u'} {T : Type u''} {R : Type u} {M : Type v}

set_option old_structure_cmd true

/-- A sub_mul_action is a set which is closed under scalar multiplication.  -/
structure sub_mul_action (R : Type u) (M : Type v) [has_scalar R M] : Type v :=
(carrier : set M)
(smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier)

namespace sub_mul_action

variables [has_scalar R M]

instance : set_like (sub_mul_action R M) M :=
⟨sub_mul_action.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp] lemma mem_carrier {p : sub_mul_action R M} {x : M} : x ∈ p.carrier ↔ x ∈ (p : set M) :=
iff.rfl

@[ext] theorem ext {p q : sub_mul_action R M} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := set_like.ext h

/-- Copy of a sub_mul_action with a new `carrier` equal to the old one. Useful to fix definitional
equalities.-/
protected def copy (p : sub_mul_action R M) (s : set M) (hs : s = ↑p) : sub_mul_action R M :=
{ carrier := s,
  smul_mem' := hs.symm ▸ p.smul_mem' }

@[simp] lemma coe_copy (p : sub_mul_action R M) (s : set M) (hs : s = ↑p) :
  (p.copy s hs : set M) = s := rfl

lemma copy_eq (p : sub_mul_action R M) (s : set M) (hs : s = ↑p) : p.copy s hs = p :=
set_like.coe_injective hs

instance : has_bot (sub_mul_action R M) :=
⟨{ carrier := ∅, smul_mem' := λ c, set.not_mem_empty}⟩

instance : inhabited (sub_mul_action R M) := ⟨⊥⟩

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

variables (p)

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →[R] M :=
by refine {to_fun := coe, ..}; simp [coe_smul]

@[simp] theorem subtype_apply (x : p) : p.subtype x = x := rfl

lemma subtype_eq_val : ((sub_mul_action.subtype p) : p → M) = subtype.val := rfl

end has_scalar

section mul_action

variables [monoid R] [mul_action R M]

section
variables [has_scalar S R] [has_scalar S M] [is_scalar_tower S R M]
variables (p : sub_mul_action R M)

lemma smul_of_tower_mem (s : S) {x : M} (h : x ∈ p) : s • x ∈ p :=
by { rw [←one_smul R x, ←smul_assoc], exact p.smul_mem _ h }

instance has_scalar' : has_scalar S p :=
{ smul := λ c x, ⟨c • x.1, smul_of_tower_mem _ c x.2⟩ }

instance : is_scalar_tower S R p :=
{ smul_assoc := λ s r x, subtype.ext $ smul_assoc s r ↑x }

@[simp, norm_cast] lemma coe_smul_of_tower (s : S) (x : p) : ((s • x : p) : M) = s • ↑x := rfl

@[simp] lemma smul_mem_iff' {G} [group G] [has_scalar G R] [mul_action G M]
  [is_scalar_tower G R M] (g : G) {x : M} :
  g • x ∈ p ↔ x ∈ p :=
⟨λ h, inv_smul_smul g x ▸ p.smul_of_tower_mem g⁻¹ h, p.smul_of_tower_mem g⟩

end

section
variables [monoid S] [has_scalar S R] [mul_action S M] [is_scalar_tower S R M]
variables (p : sub_mul_action R M)

/-- If the scalar product forms a `mul_action`, then the subset inherits this action -/
instance mul_action' : mul_action S p :=
{ smul := (•),
  one_smul := λ x, subtype.ext $ one_smul _ x,
  mul_smul := λ c₁ c₂ x, subtype.ext $ mul_smul c₁ c₂ x }

instance : mul_action R p := p.mul_action'

end

end mul_action

section module

variables [semiring R] [add_comm_monoid M]
variables [module R M]
variables (p : sub_mul_action R M)

lemma zero_mem (h : (p : set M).nonempty) : (0 : M) ∈ p :=
let ⟨x, hx⟩ := h in zero_smul R (x : M) ▸ p.smul_mem 0 hx

/-- If the scalar product forms a `module`, and the `sub_mul_action` is not `⊥`, then the
subset inherits the zero. -/
instance [n_empty : nonempty p] : has_zero p :=
{ zero := ⟨0, n_empty.elim $ λ x, p.zero_mem ⟨x, x.prop⟩⟩ }

end module

section add_comm_group

variables [ring R] [add_comm_group M]
variables [module R M]
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

variables [division_ring S] [semiring R] [mul_action R M]
variables [has_scalar S R] [mul_action S M] [is_scalar_tower S R M]
variables (p : sub_mul_action R M) {s : S} {x y : M}

theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p :=
p.smul_mem_iff' (units.mk0 s s0)

end sub_mul_action
