/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro

Modules over a ring.
-/

import algebra.ring algebra.big_operators group_theory.subgroup group_theory.group_action
open function

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

-- /-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
-- class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)

-- infixr ` • `:73 := has_scalar.smul

/-- A semimodule is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `α` and an additive monoid of "vectors" `β`,
  connected by a "scalar multiplication" operation `r • x : β`
  (where `r : α` and `x : β`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class semimodule (α : Type u) (β : Type v) [semiring α]
  [add_comm_monoid β] extends distrib_mul_action α β :=
(add_smul : ∀(r s : α) (x : β), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : β, (0 : α) • x = 0)

section semimodule
variables [R:semiring α] [add_comm_monoid β] [semimodule α β] (r s : α) (x y : β)
include R

theorem add_smul : (r + s) • x = r • x + s • x := semimodule.add_smul r s x
variables (α)
@[simp] theorem zero_smul : (0 : α) • x = 0 := semimodule.zero_smul α x

lemma smul_smul : r • s • x = (r * s) • x := (mul_smul _ _ _).symm

instance smul.is_add_monoid_hom {r : α} : is_add_monoid_hom (λ x : β, r • x) :=
{ map_add := smul_add _, map_zero := smul_zero _ }

end semimodule

/-- A module is a generalization of vector spaces to a scalar ring.
  It consists of a scalar ring `α` and an additive group of "vectors" `β`,
  connected by a "scalar multiplication" operation `r • x : β`
  (where `r : α` and `x : β`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class module (α : Type u) (β : Type v) [ring α] [add_comm_group β] extends semimodule α β

structure module.core (α β) [ring α] [add_comm_group β] extends has_scalar α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(add_smul : ∀(r s : α) (x : β), (r + s) • x = r • x + s • x)
(mul_smul : ∀(r s : α) (x : β), (r * s) • x = r • s • x)
(one_smul : ∀x : β, (1 : α) • x = x)

def module.of_core {α β} [ring α] [add_comm_group β] (M : module.core α β) : module α β :=
by letI := M.to_has_scalar; exact
{ zero_smul := λ x,
    have (0 : α) • x + (0 : α) • x = (0 : α) • x + 0, by rw ← M.add_smul; simp,
    add_left_cancel this,
  smul_zero := λ r,
    have r • (0:β) + r • 0 = r • 0 + 0, by rw ← M.smul_add; simp,
    add_left_cancel this,
  ..M }

section module
variables [ring α] [add_comm_group β] [module α β] (r s : α) (x y : β)

@[simp] theorem neg_smul : -r • x = - (r • x) :=
eq_neg_of_add_eq_zero (by rw [← add_smul, add_left_neg, zero_smul])

variables (α)
theorem neg_one_smul (x : β) : (-1 : α) • x = -x := by simp
variables {α}

@[simp] theorem smul_neg : r • (-x) = -(r • x) :=
by rw [← neg_one_smul α, ← mul_smul, mul_neg_one, neg_smul]

theorem smul_sub (r : α) (x y : β) : r • (x - y) = r • x - r • y :=
by simp [smul_add]; rw smul_neg

theorem sub_smul (r s : α) (y : β) : (r - s) • y = r • y - s • y :=
by simp [add_smul]

end module

instance semiring.to_semimodule [r : semiring α] : semimodule α α :=
{ smul := (*),
  smul_add := mul_add,
  add_smul := add_mul,
  mul_smul := mul_assoc,
  one_smul := one_mul,
  zero_smul := zero_mul,
  smul_zero := mul_zero, ..r }

@[simp] lemma smul_eq_mul [semiring α] {a a' : α} : a • a' = a * a' := rfl

instance ring.to_module [r : ring α] : module α α :=
{ ..semiring.to_semimodule }

def is_ring_hom.to_module [ring α] [ring β] (f : α → β) [h : is_ring_hom f] : module α β :=
module.of_core
{ smul := λ r x, f r * x,
  smul_add := λ r x y, by unfold has_scalar.smul; rw [mul_add],
  add_smul := λ r s x, by unfold has_scalar.smul; rw [h.map_add, add_mul],
  mul_smul := λ r s x, by unfold has_scalar.smul; rw [h.map_mul, mul_assoc],
  one_smul := λ x, show f 1 * x = _, by rw [h.map_one, one_mul] }

class is_linear_map (α : Type u) {β : Type v} {γ : Type w}
  [ring α] [add_comm_group β] [add_comm_group γ] [module α β] [module α γ]
  (f : β → γ) : Prop :=
(add  : ∀x y, f (x + y) = f x + f y)
(smul : ∀(c : α) x, f (c • x) = c • f x)

structure linear_map (α : Type u) (β : Type v) (γ : Type w)
  [ring α] [add_comm_group β] [add_comm_group γ] [module α β] [module α γ] :=
(to_fun : β → γ)
(add  : ∀x y, to_fun (x + y) = to_fun x + to_fun y)
(smul : ∀(c : α) x, to_fun (c • x) = c • to_fun x)

infixr ` →ₗ `:25 := linear_map _
notation β ` →ₗ[`:25 α `] ` γ := linear_map α β γ

namespace linear_map

variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables (f g : β →ₗ[α] γ)
include α

instance : has_coe_to_fun (β →ₗ[α] γ) := ⟨_, to_fun⟩

theorem is_linear : is_linear_map α f := {..f}

@[extensionality] theorem ext {f g : β →ₗ[α] γ} (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

theorem ext_iff {f g : β →ₗ[α] γ} : f = g ↔ ∀ x, f x = g x :=
⟨by rintro rfl; simp, ext⟩

@[simp] lemma map_add (x y : β) : f (x + y) = f x + f y := f.add x y

@[simp] lemma map_smul (c : α) (x : β) : f (c • x) = c • f x := f.smul c x

@[simp] lemma map_zero : f 0 = 0 :=
by rw [← zero_smul α, map_smul f 0 0, zero_smul]

instance : is_add_group_hom f := ⟨map_add f⟩

@[simp] lemma map_neg (x : β) : f (- x) = - f x :=
by rw [← neg_one_smul α, map_smul, neg_one_smul]

@[simp] lemma map_sub (x y : β) : f (x - y) = f x - f y :=
by simp [map_neg, map_add]

@[simp] lemma map_sum {ι} {t : finset ι} {g : ι → β} :
  f (t.sum g) = t.sum (λi, f (g i)) :=
(finset.sum_hom f).symm

def comp (f : γ →ₗ[α] δ) (g : β →ₗ[α] γ) : β →ₗ[α] δ := ⟨f ∘ g, by simp, by simp⟩

@[simp] lemma comp_apply (f : γ →ₗ[α] δ) (g : β →ₗ[α] γ) (x : β) : f.comp g x = f (g x) := rfl

def id : β →ₗ[α] β := ⟨id, by simp, by simp⟩

@[simp] lemma id_apply (x : β) : @id α β _ _ _ x = x := rfl

end linear_map

namespace is_linear_map
variables [ring α] [add_comm_group β] [add_comm_group γ]
variables [module α β] [module α γ]
include α

def mk' (f : β → γ) (H : is_linear_map α f) : β →ₗ γ := {to_fun := f, ..H}

@[simp] theorem mk'_apply {f : β → γ} (H : is_linear_map α f) (x : β) :
  mk' f H x = f x := rfl

lemma is_linear_map_neg :
  is_linear_map α (λ (z : β), -z) :=
is_linear_map.mk neg_add (λ x y, (smul_neg x y).symm)

lemma is_linear_map_smul {α R : Type*} [add_comm_group α] [comm_ring R] [module R α] (c : R) :
  is_linear_map R (λ (z : α), c • z) :=
begin
  refine is_linear_map.mk (smul_add c) _,
  intros _ _,
  simp [smul_smul],
  ac_refl
end

--TODO: move
lemma is_linear_map_smul' {α R : Type*} [add_comm_group α] [comm_ring R] [module R α] (a : α) :
  is_linear_map R (λ (c : R), c • a) :=
begin
  refine is_linear_map.mk (λ x y, add_smul x y a) _,
  intros _ _,
  simp [smul_smul]
end

variables {f : β → γ} (lin : is_linear_map α f)
include β γ lin

@[simp] lemma map_zero : f (0 : β) = (0 : γ) :=
by rw [← zero_smul α (0 : β), lin.smul, zero_smul]

@[simp] lemma map_add (x y : β) : f (x + y) = f x + f y :=
by rw [lin.add]

@[simp] lemma map_neg (x : β) : f (- x) = - f x :=
by rw [← neg_one_smul α, lin.smul, neg_one_smul]

@[simp] lemma map_sub (x y : β) : f (x - y) = f x - f y :=
by simp [lin.map_neg, lin.map_add]

end is_linear_map

/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
structure submodule (α : Type u) (β : Type v) [ring α]
  [add_comm_group β] [module α β] : Type v :=
(carrier : set β)
(zero : (0:β) ∈ carrier)
(add : ∀ {x y}, x ∈ carrier → y ∈ carrier → x + y ∈ carrier)
(smul : ∀ (c:α) {x}, x ∈ carrier → c • x ∈ carrier)

namespace submodule
variables [ring α] [add_comm_group β] [add_comm_group γ]
variables [module α β] [module α γ]
variables (p p' : submodule α β)
variables {r : α} {x y : β}

instance : has_coe (submodule α β) (set β) := ⟨submodule.carrier⟩
instance : has_mem β (submodule α β) := ⟨λ x p, x ∈ (p : set β)⟩
@[simp] theorem mem_coe : x ∈ (p : set β) ↔ x ∈ p := iff.rfl

theorem ext' {s t : submodule α β} (h : (s : set β) = t) : s = t :=
by cases s; cases t; congr'

protected theorem ext'_iff {s t : submodule α β}  : (s : set β) = t ↔ s = t :=
⟨ext', λ h, h ▸ rfl⟩

@[extensionality] theorem ext {s t : submodule α β}
  (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := ext' $ set.ext h

@[simp] lemma zero_mem : (0 : β) ∈ p := p.zero

lemma add_mem (h₁ : x ∈ p) (h₂ : y ∈ p) : x + y ∈ p := p.add h₁ h₂

lemma smul_mem (r : α) (h : x ∈ p) : r • x ∈ p := p.smul r h

lemma neg_mem (hx : x ∈ p) : -x ∈ p := by rw ← neg_one_smul α; exact p.smul_mem _ hx

lemma sub_mem (hx : x ∈ p) (hy : y ∈ p) : x - y ∈ p := p.add_mem hx (p.neg_mem hy)

lemma neg_mem_iff : -x ∈ p ↔ x ∈ p :=
⟨λ h, by simpa using neg_mem p h, neg_mem p⟩

lemma add_mem_iff_left (h₁ : y ∈ p) : x + y ∈ p ↔ x ∈ p :=
⟨λ h₂, by simpa using sub_mem _ h₂ h₁, λ h₂, add_mem _ h₂ h₁⟩

lemma add_mem_iff_right (h₁ : x ∈ p) : x + y ∈ p ↔ y ∈ p :=
⟨λ h₂, by simpa using sub_mem _ h₂ h₁, add_mem _ h₁⟩

lemma sum_mem {ι : Type w} [decidable_eq ι] {t : finset ι} {f : ι → β} :
  (∀c∈t, f c ∈ p) → t.sum f ∈ p :=
finset.induction_on t (by simp [p.zero_mem]) (by simp [p.add_mem] {contextual := tt})

instance : has_add p := ⟨λx y, ⟨x.1 + y.1, add_mem _ x.2 y.2⟩⟩
instance : has_zero p := ⟨⟨0, zero_mem _⟩⟩
instance : has_neg p := ⟨λx, ⟨-x.1, neg_mem _ x.2⟩⟩
instance : has_scalar α p := ⟨λ c x, ⟨c • x.1, smul_mem _ c x.2⟩⟩

@[simp] lemma coe_add (x y : p) : (↑(x + y) : β) = ↑x + ↑y := rfl
@[simp] lemma coe_zero : ((0 : p) : β) = 0 := rfl
@[simp] lemma coe_neg (x : p) : ((-x : p) : β) = -x := rfl
@[simp] lemma coe_smul (r : α) (x : p) : ((r • x : p) : β) = r • ↑x := rfl

instance : add_comm_group p :=
by refine {add := (+), zero := 0, neg := has_neg.neg, ..};
  { intros, apply set_coe.ext, simp }

instance submodule_is_add_subgroup : is_add_subgroup (p : set β) :=
{ zero_mem := p.zero,
  add_mem  := p.add,
  neg_mem  := λ _, p.neg_mem }

lemma coe_sub (x y : p) : (↑(x - y) : β) = ↑x - ↑y := by simp

instance : module α p :=
by refine {smul := (•), ..};
   { intros, apply set_coe.ext, simp [smul_add, add_smul, mul_smul] }

protected def subtype : p →ₗ[α] β :=
by refine {to_fun := coe, ..}; simp [coe_smul]

@[simp] theorem subtype_apply (x : p) : p.subtype x = x := rfl

end submodule

@[reducible] def ideal (α : Type u) [comm_ring α] := submodule α α

namespace ideal
variables [comm_ring α] (I : ideal α) {a b : α}

protected lemma zero_mem : (0 : α) ∈ I := I.zero_mem

protected lemma add_mem : a ∈ I → b ∈ I → a + b ∈ I := I.add_mem

lemma neg_mem_iff : -a ∈ I ↔ a ∈ I := I.neg_mem_iff

lemma add_mem_iff_left : b ∈ I → (a + b ∈ I ↔ a ∈ I) := I.add_mem_iff_left

lemma add_mem_iff_right : a ∈ I → (a + b ∈ I ↔ b ∈ I) := I.add_mem_iff_right

protected lemma sub_mem : a ∈ I → b ∈ I → a - b ∈ I := I.sub_mem

lemma mul_mem_left : b ∈ I → a * b ∈ I := I.smul_mem _

lemma mul_mem_right (h : a ∈ I) : a * b ∈ I := mul_comm b a ▸ I.mul_mem_left h

end ideal

/-- A vector space is the same as a module, except the scalar ring is actually
  a field. (This adds commutativity of the multiplication and existence of inverses.)
  This is the traditional generalization of spaces like `ℝ^n`, which have a natural
  addition operation and a way to multiply them by real numbers, but no multiplication
  operation between vectors. -/
class vector_space (α : Type u) (β : Type v) [discrete_field α] [add_comm_group β] extends module α β

instance discrete_field.to_vector_space {α : Type*} [discrete_field α] : vector_space α α :=
{ .. ring.to_module }

/-- Subspace of a vector space. Defined to equal `submodule`. -/
@[reducible] def subspace (α : Type u) (β : Type v)
  [discrete_field α] [add_comm_group β] [vector_space α β] : Type v :=
submodule α β

instance subspace.vector_space {α β}
  {f : discrete_field α} [add_comm_group β] [vector_space α β]
  (p : subspace α β) : vector_space α p := {..submodule.module p}

namespace submodule

variables {R:discrete_field α} [add_comm_group β] [add_comm_group γ]
variables [vector_space α β] [vector_space α γ]
variables (p p' : submodule α β)
variables {r : α} {x y : β}
include R

set_option class.instance_max_depth 36

theorem smul_mem_iff (r0 : r ≠ 0) : r • x ∈ p ↔ x ∈ p :=
⟨λ h, by simpa [smul_smul, inv_mul_cancel r0] using p.smul_mem (r⁻¹) h,
 p.smul_mem r⟩

end submodule

namespace add_comm_monoid
open add_monoid

variables {M : Type*} [add_comm_monoid M]

instance : semimodule ℕ M :=
{ smul := smul,
  smul_add := λ _ _ _, smul_add _ _ _,
  add_smul := λ _ _ _, add_smul _ _ _,
  mul_smul := λ _ _ _, mul_smul _ _ _,
  one_smul := one_smul,
  zero_smul := zero_smul,
  smul_zero := smul_zero }

end add_comm_monoid

namespace add_comm_group

variables {M : Type*} [add_comm_group M]

instance : module ℤ M :=
{ smul := gsmul,
  smul_add := λ _ _ _, gsmul_add _ _ _,
  add_smul := λ _ _ _, add_gsmul _ _ _,
  mul_smul := λ _ _ _, gsmul_mul _ _ _,
  one_smul := one_gsmul,
  zero_smul := zero_gsmul,
  smul_zero := gsmul_zero }

end add_comm_group

def is_add_group_hom.to_linear_map [add_comm_group α] [add_comm_group β]
  (f : α → β) [is_add_group_hom f] : α →ₗ[ℤ] β :=
{ to_fun := f,
  add := is_add_group_hom.map_add f,
  smul := λ i x, int.induction_on i (by rw [zero_smul, zero_smul, is_add_group_hom.map_zero f])
    (λ i ih, by rw [add_smul, add_smul, is_add_group_hom.map_add f, ih, one_smul, one_smul])
    (λ i ih, by rw [sub_smul, sub_smul, is_add_group_hom.map_sub f, ih, one_smul, one_smul]) }
