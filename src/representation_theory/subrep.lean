/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.direct_sum

open function
open_locale big_operators

set_option old_structure_cmd true

structure subrep
  {k G V : Type*} [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]
  (ρ : representation k G V) extends submodule k V :=
(smulG_mem' : ∀ (g : G) {x : V}, x ∈ carrier → ρ g x ∈ carrier)

structure rep_hom
  {k G V V' : Type*} [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [add_comm_monoid V'] [module k V']
  (ρ : representation k G V) (ρ' : representation k G V') extends V →ₗ[k] V' :=
(smul_comm : ∀ (g : G) (x : V), ρ' g (to_fun x) = to_fun (ρ g x))

namespace subrep
-- Follows algebra.module.submodule.basic
variables
  {k G V : Type*}
  [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]
  {ρ : representation k G V}

instance : set_like (subrep ρ) V :=
{ coe := subrep.carrier,
  coe_injective' := λ p q h, by cases p; cases q; congr' }

instance : add_submonoid_class (subrep ρ) V :=
{ zero_mem := zero_mem',
  add_mem := add_mem' }

@[simp] theorem mem_to_submodule (p : subrep ρ) (x : V) : x ∈ p.to_submodule ↔ x ∈ p :=
iff.rfl

variables {p q : subrep ρ}

@[simp]
lemma mem_mk {S : set V} {x : V} (h₁ h₂ h₃ h₄) : x ∈ (⟨S, h₁, h₂, h₃, h₄⟩ : subrep ρ) ↔ x ∈ S :=
iff.rfl

@[simp] lemma coe_set_mk (S : set V) (h₁ h₂ h₃ h₄) :
  ((⟨S, h₁, h₂, h₃, h₄⟩ : subrep ρ) : set V) = S := rfl

@[simp]
lemma mk_le_mk {S S' : set V} (h₁ h₂ h₃ h₄ h₁' h₂' h₃' h₄') :
  (⟨S, h₁, h₂, h₃, h₄⟩ : subrep ρ) ≤ (⟨S', h₁', h₂', h₃', h₄'⟩ : subrep ρ) ↔ S ⊆ S' := iff.rfl

@[ext] theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := set_like.ext h

/-- Copy of a subrep with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (p : subrep ρ) (s : set V) (hs : s = ↑p) : subrep ρ :=
{ carrier := s,
  zero_mem' := hs.symm ▸ p.zero_mem',
  add_mem' := hs.symm ▸ p.add_mem',
  smul_mem' := hs.symm ▸ p.smul_mem',
  smulG_mem' := hs.symm ▸ p.smulG_mem' }

@[simp] lemma coe_copy (S : subrep ρ) (s : set V) (hs : s = ↑S) :
  (S.copy s hs : set V) = s := rfl

lemma copy_eq (S : subrep ρ) (s : set V) (hs : s = ↑S) : S.copy s hs = S :=
set_like.coe_injective hs

theorem to_submodule_injective :
  injective (to_submodule : subrep ρ → submodule k V) :=
λ p q h, set_like.ext'_iff.2 (show _, from set_like.ext'_iff.1 h)

@[simp] theorem to_submodule_eq : p.to_submodule = q.to_submodule ↔ p = q :=
to_submodule_injective.eq_iff

@[mono] lemma to_submodule_strict_mono :
  strict_mono (to_submodule : subrep ρ → submodule k V) := λ _ _, id

lemma to_submodule_le : p.to_submodule ≤ q.to_submodule ↔ p ≤ q := iff.rfl

@[mono]
lemma to_submodule_mono : monotone (to_submodule : subrep ρ → submodule k V) :=
to_submodule_strict_mono.monotone

@[simp] theorem coe_to_submodule (p : subrep ρ) :
  (p.to_submodule : set V) = p := rfl

-- to_sub_mul_action for the G-action?

end subrep

namespace subrep

section add_comm_monoid

variables
  {k k' G G' V ι : Type*}
  [comm_semiring k] [monoid G] [add_comm_monoid V] [module k V]
  {ρ : representation k G V} {p q : subrep ρ}
  {r : k} {g : G} {x y : V}

variables (p)
@[simp] lemma mem_carrier : x ∈ p.carrier ↔ x ∈ (p : set V) := iff.rfl

@[simp] protected lemma zero_mem : (0 : V) ∈ p := zero_mem _
protected lemma add_mem (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p := add_mem h₁ h₂

lemma smul_mem (r : k) (h : x ∈ p) : r • x ∈ p := p.smul_mem' r h
lemma smul_of_tower_mem [has_scalar k' k] [has_scalar k' V] [is_scalar_tower k' k V]
  (r : k') (h : x ∈ p) : r • x ∈ p :=
p.to_submodule.smul_of_tower_mem r h

lemma smulG_mem (g : G) (h : x ∈ p) : ρ g x ∈ p := p.smulG_mem' g h

protected lemma sum_mem {t : finset ι} {f : ι → V} : (∀c∈t, f c ∈ p) → (∑ i in t, f i) ∈ p :=
sum_mem

lemma sum_smul_mem {t : finset ι} {f : ι → V} (r : ι → k)
    (hyp : ∀ c ∈ t, f c ∈ p) : (∑ i in t, r i • f i) ∈ p :=
sum_mem (λ i hi, smul_mem _ _ (hyp i hi))

lemma sum_smulG_mem {t : finset ι} {f : ι → V} (g : ι → G)
    (hyp : ∀ c ∈ t, f c ∈ p) : (∑ i in t, ρ (g i) (f i) ∈ p) :=
sum_mem (λ i hi, smulG_mem _ _ (hyp i hi))

@[simp] lemma smul_mem_iff' [group G'] [mul_action G' V] [has_scalar G' k] [is_scalar_tower G' k V]
  (g : G') : g • x ∈ p ↔ x ∈ p :=
p.to_submodule.smul_mem_iff' g

instance : has_add p := ⟨λx y, ⟨x.1 + y.1, add_mem x.2 y.2⟩⟩
instance : has_zero p := ⟨⟨0, zero_mem _⟩⟩
instance : inhabited p := ⟨0⟩
instance [has_scalar k' k] [has_scalar k' V] [is_scalar_tower k' k V] :
  has_scalar k' p := ⟨λ c x, ⟨c • x.1, smul_of_tower_mem _ c x.2⟩⟩

instance [has_scalar k' k] [has_scalar k' V] [is_scalar_tower k' k V] : is_scalar_tower k' k p :=
p.to_submodule.is_scalar_tower

instance
  [has_scalar k' k] [has_scalar k' V] [is_scalar_tower k' k V]
  [has_scalar k'ᵐᵒᵖ k] [has_scalar k'ᵐᵒᵖ V] [is_scalar_tower k'ᵐᵒᵖ k V]
  [is_central_scalar k' V] : is_central_scalar k' p :=
p.to_submodule.is_central_scalar

protected lemma nonempty : (p : set V).nonempty := ⟨0, p.zero_mem⟩

@[simp] lemma mk_eq_zero {x} (h : x ∈ p) : (⟨x, h⟩ : p) = 0 ↔ x = 0 := subtype.ext_iff_val

variables {p}
@[simp, norm_cast] lemma coe_eq_zero {x : p} : (x : V) = 0 ↔ x = 0 :=
(set_like.coe_eq_coe : (x : V) = (0 : p) ↔ x = 0)
@[simp, norm_cast] lemma coe_add (x y : p) : (↑(x + y) : V) = ↑x + ↑y := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : p) : V) = 0 := rfl
@[norm_cast] lemma coe_smul (r : k) (x : p) : ((r • x : p) : V) = r • ↑x := rfl
@[simp, norm_cast] lemma coe_smul_of_tower [has_scalar k' k] [has_scalar k' V]
  [is_scalar_tower k' k V] (r : k') (x : p) : ((r • x : p) : V) = r • ↑x := rfl
@[simp, norm_cast] lemma coe_mk (x : V) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : V) = x := rfl
@[simp] lemma coe_mem (x : p) : (x : V) ∈ p := x.2

variables (p)

instance : add_comm_monoid p :=
{ add := (+), zero := 0, .. p.to_submodule.to_add_submonoid.to_add_comm_monoid }

instance module' [semiring k'] [has_scalar k' k] [module k' V] [is_scalar_tower k' k V] :
  module k' p := p.to_submodule.module'
instance : module k p := p.module'

/-- `representation` is not a class -/
def representation' :
  representation k G p :=
begin
  split,
  show G → (↥p →ₗ[k] ↥p),
  { intro g,
    refine linear_map.cod_restrict p.to_submodule (linear_map.dom_restrict (ρ g) p.to_submodule) _,
    simp only [linear_map.dom_restrict_apply, subrep.mem_to_submodule, subrep.coe_mem,
      subrep.smulG_mem, forall_const] },
  { ext,
    simp only [map_one, linear_map.cod_restrict_apply, linear_map.dom_restrict_apply,
      linear_map.one_apply, linear_map.one_apply, set_like.coe_eq_coe, eq_self_iff_true] },
  { intros g g',
    ext,
    simp only [map_mul, linear_map.cod_restrict_apply, linear_map.dom_restrict_apply,
      linear_map.mul_apply, linear_map.mul_apply, linear_map.cod_restrict_apply,
      linear_map.dom_restrict_apply, linear_map.cod_restrict_apply, linear_map.dom_restrict_apply,
      eq_self_iff_true] }
end

instance no_zero_smul_divisors [no_zero_smul_divisors k V] : no_zero_smul_divisors k p :=
⟨λ c x h,
  have c = 0 ∨ (x : V) = 0,
  from eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg coe h),
  this.imp_right (@subtype.ext_iff _ _ x 0).mpr⟩

/-- Embedding of a submodule `p` to the ambient space `M`. -/
protected def subtype : p →ₗ[k] V :=
by refine {to_fun := coe, ..}; simp [coe_smul]

theorem subtype_apply (x : p) : p.subtype x = x := rfl

@[simp] lemma coe_subtype : ((subrep.subtype p) : p → V) = coe := rfl

lemma injective_subtype : injective p.subtype := subtype.coe_injective

/-- Note the `add_submonoid` version of this lemma is called `add_submonoid.coe_finset_sum`. -/
@[simp] lemma coe_sum (x : ι → p) (s : finset ι) : ↑(∑ i in s, x i) = ∑ i in s, (x i : V) :=
p.subtype.map_sum

-- restrict scalars

end add_comm_monoid

section add_comm_group

variables
  {k G V : Type*}
  [comm_ring k] [monoid G] [add_comm_group V] [module k V]
  {ρ : representation k G V} (p : subrep ρ)
  {r : k} {x y : V}

instance : add_subgroup_class (subrep ρ) V :=
{ neg_mem := λ p x, p.to_submodule.neg_mem,
  .. subrep.add_submonoid_class }

protected lemma neg_mem (hx : x ∈ p) : -x ∈ p := neg_mem hx

-- to_add_subgroup

protected lemma sub_mem : x ∈ p → y ∈ p → x - y ∈ p := sub_mem
protected lemma neg_mem_iff : -x ∈ p ↔ x ∈ p := neg_mem_iff
protected lemma add_mem_iff_left : y ∈ p → (x + y ∈ p ↔ x ∈ p) := add_mem_cancel_right
protected lemma add_mem_iff_right : x ∈ p → (x + y ∈ p ↔ y ∈ p) := add_mem_cancel_left
protected lemma coe_neg (x : p) : ((-x : p) : V) = -x := add_subgroup_class.coe_neg _
protected lemma coe_sub (x y : p) : (↑(x - y) : V) = ↑x - ↑y := add_subgroup_class.coe_sub _ _

lemma sub_mem_iff_left (hy : y ∈ p) : (x - y) ∈ p ↔ x ∈ p :=
by rw [sub_eq_add_neg, p.add_mem_iff_left (p.neg_mem hy)]

lemma sub_mem_iff_right (hx : x ∈ p) : (x - y) ∈ p ↔ y ∈ p :=
by rw [sub_eq_add_neg, p.add_mem_iff_right hx, p.neg_mem_iff]

instance : add_comm_group p :=
{ add := (+), zero := 0, neg := has_neg.neg, ..p.to_submodule.to_add_subgroup.to_add_comm_group }

end add_comm_group

-- is domain
-- ordered monoid
-- ordered group

end subrep

namespace subrep

variables
  {k k' G V : Type*}
  [division_ring k'] [comm_semiring k] [monoid G]
  [add_comm_monoid V] [module k V] [has_scalar k' k]
  [module k' V] [is_scalar_tower k' k V]
  {ρ : representation k G V}

variables (p : subrep ρ) {s : k'} {x y : V}

theorem smul_mem_iff (s0 : s ≠ 0) : s • x ∈ p ↔ x ∈ p :=
p.to_submodule.smul_mem_iff s0

end subrep
