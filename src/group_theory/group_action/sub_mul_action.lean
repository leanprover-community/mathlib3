/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.hom.group_action
import algebra.module.basic
import data.set_like.basic
import group_theory.group_action.basic
/-!

# Sets invariant to a `mul_action`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

/-- `smul_mem_class S R M` says `S` is a type of subsets `s ≤ M` that are closed under the
scalar action of `R` on `M`.

Note that only `R` is marked as an `out_param` here, since `M` is supplied by the `set_like`
class instead.
-/
class smul_mem_class (S : Type*) (R : out_param $ Type*) (M : Type*) [has_smul R M]
  [set_like S M] :=
(smul_mem : ∀ {s : S} (r : R) {m : M}, m ∈ s → r • m ∈ s)

/-- `vadd_mem_class S R M` says `S` is a type of subsets `s ≤ M` that are closed under the
additive action of `R` on `M`.

Note that only `R` is marked as an `out_param` here, since `M` is supplied by the `set_like`
class instead.
-/
class vadd_mem_class (S : Type*) (R : out_param $ Type*) (M : Type*) [has_vadd R M]
  [set_like S M] :=
(vadd_mem : ∀ {s : S} (r : R) {m : M}, m ∈ s → r +ᵥ m ∈ s)

attribute [to_additive] smul_mem_class

namespace set_like

variables [has_smul R M] [set_like S M] [hS : smul_mem_class S R M] (s : S)
include hS

open smul_mem_class

/-- A subset closed under the scalar action inherits that action. -/
@[to_additive "A subset closed under the additive action inherits that action.",
priority 900] -- lower priority so other instances are found first
instance has_smul : has_smul R s := ⟨λ r x, ⟨r • x.1, smul_mem r x.2⟩⟩

@[simp, norm_cast, to_additive, priority 900]
-- lower priority so later simp lemmas are used first; to appease simp_nf
protected lemma coe_smul (r : R) (x : s) : (↑(r • x) : M) = r • x := rfl

@[simp, to_additive, priority 900]
-- lower priority so later simp lemmas are used first; to appease simp_nf
lemma mk_smul_mk (r : R) (x : M) (hx : x ∈ s) :
  r • (⟨x, hx⟩ : s) = ⟨r • x, smul_mem r hx⟩ := rfl

@[to_additive] lemma smul_def (r : R) (x : s) : r • x = ⟨r • x, smul_mem r x.2⟩ := rfl

omit hS

@[simp] lemma forall_smul_mem_iff {R M S : Type*} [monoid R] [mul_action R M]
  [set_like S M] [smul_mem_class S R M] {N : S} {x : M} :
  (∀ (a : R), a • x ∈ N) ↔ x ∈ N :=
⟨λ h, by simpa using h 1, λ h a, smul_mem_class.smul_mem a h⟩

end set_like

/-- A sub_mul_action is a set which is closed under scalar multiplication.  -/
structure sub_mul_action (R : Type u) (M : Type v) [has_smul R M] : Type v :=
(carrier : set M)
(smul_mem' : ∀ (c : R) {x : M}, x ∈ carrier → c • x ∈ carrier)

namespace sub_mul_action

variables [has_smul R M]

instance : set_like (sub_mul_action R M) M :=
⟨sub_mul_action.carrier, λ p q h, by cases p; cases q; congr'⟩

instance : smul_mem_class (sub_mul_action R M) R M :=
{ smul_mem := smul_mem' }

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

section has_smul

variables [has_smul R M]
variables (p : sub_mul_action R M)
variables {r : R} {x : M}

lemma smul_mem (r : R) (h : x ∈ p) : r • x ∈ p := p.smul_mem' r h

instance : has_smul R p :=
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

end has_smul

namespace smul_mem_class

variables [monoid R] [mul_action R M] {A : Type*} [set_like A M]
variables [hA : smul_mem_class A R M] (S' : A)

include hA
/-- A `sub_mul_action` of a `mul_action` is a `mul_action`.  -/
@[priority 75] -- Prefer subclasses of `mul_action` over `smul_mem_class`.
instance to_mul_action : mul_action R S' :=
subtype.coe_injective.mul_action coe (set_like.coe_smul S')

/-- The natural `mul_action_hom` over `R` from a `sub_mul_action` of `M` to `M`. -/
protected def subtype : S' →[R] M := ⟨coe,  λ _ _, rfl⟩

@[simp] protected theorem coe_subtype : (smul_mem_class.subtype S' : S' → M) = coe := rfl

end smul_mem_class

section mul_action_monoid

variables [monoid R] [mul_action R M]

section
variables [has_smul S R] [has_smul S M] [is_scalar_tower S R M]
variables (p : sub_mul_action R M)

lemma smul_of_tower_mem (s : S) {x : M} (h : x ∈ p) : s • x ∈ p :=
by { rw [←one_smul R x, ←smul_assoc], exact p.smul_mem _ h }

instance has_smul' : has_smul S p :=
{ smul := λ c x, ⟨c • x.1, smul_of_tower_mem _ c x.2⟩ }

instance : is_scalar_tower S R p :=
{ smul_assoc := λ s r x, subtype.ext $ smul_assoc s r ↑x }

instance is_scalar_tower' {S' : Type*} [has_smul S' R] [has_smul S' S]
  [has_smul S' M] [is_scalar_tower S' R M] [is_scalar_tower S' S M] :
  is_scalar_tower S' S p :=
{ smul_assoc := λ s r x, subtype.ext $ smul_assoc s r ↑x }

@[simp, norm_cast] lemma coe_smul_of_tower (s : S) (x : p) : ((s • x : p) : M) = s • ↑x := rfl

@[simp] lemma smul_mem_iff' {G} [group G] [has_smul G R] [mul_action G M]
  [is_scalar_tower G R M] (g : G) {x : M} :
  g • x ∈ p ↔ x ∈ p :=
⟨λ h, inv_smul_smul g x ▸ p.smul_of_tower_mem g⁻¹ h, p.smul_of_tower_mem g⟩

instance [has_smul Sᵐᵒᵖ R] [has_smul Sᵐᵒᵖ M] [is_scalar_tower Sᵐᵒᵖ R M]
  [is_central_scalar S M] : is_central_scalar S p :=
{ op_smul_eq_smul := λ r x, subtype.ext $ op_smul_eq_smul r x }

end

section

variables [monoid S] [has_smul S R] [mul_action S M] [is_scalar_tower S R M]
variables (p : sub_mul_action R M)

/-- If the scalar product forms a `mul_action`, then the subset inherits this action -/
instance mul_action' : mul_action S p :=
{ smul := (•),
  one_smul := λ x, subtype.ext $ one_smul _ x,
  mul_smul := λ c₁ c₂ x, subtype.ext $ mul_smul c₁ c₂ x }

instance : mul_action R p := p.mul_action'

end


/-- Orbits in a `sub_mul_action` coincide with orbits in the ambient space. -/
lemma coe_image_orbit {p : sub_mul_action R M} (m : p) :
  coe '' mul_action.orbit R m = mul_action.orbit R (m : M) := (set.range_comp _ _).symm

/- -- Previously, the relatively useless :
lemma orbit_of_sub_mul {p : sub_mul_action R M} (m : p) :
  (mul_action.orbit R m : set M) = mul_action.orbit R (m : M) := rfl
-/

/-- Stabilizers in monoid sub_mul_action coincide with stabilizers in the ambient space -/
lemma stabilizer_of_sub_mul.submonoid {p : sub_mul_action R M} (m : p) :
  mul_action.stabilizer.submonoid R m = mul_action.stabilizer.submonoid R (m : M) :=
begin
  ext,
  simp only [mul_action.mem_stabilizer_submonoid_iff,
      ← sub_mul_action.coe_smul, set_like.coe_eq_coe]
end

end mul_action_monoid

section mul_action_group

variables [group R] [mul_action R M]

/-- Stabilizers in group sub_mul_action coincide with stabilizers in the ambient space -/
lemma stabilizer_of_sub_mul {p : sub_mul_action R M} (m : p) :
  mul_action.stabilizer R m = mul_action.stabilizer R (m : M) :=
begin
  rw ← subgroup.to_submonoid_eq,
  exact stabilizer_of_sub_mul.submonoid m,
end

end mul_action_group


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

variables [group_with_zero S] [monoid R] [mul_action R M]
variables [has_smul S R] [mul_action S M] [is_scalar_tower S R M]
variables (p : sub_mul_action R M) {s : S} {x y : M}

theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p :=
p.smul_mem_iff' (units.mk0 s s0)

end sub_mul_action
