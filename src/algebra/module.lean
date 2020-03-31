/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro

Modules over a ring.

## Implementation notes


Throughout the `linear_map` section implicit `{}` brackets are often used instead of type class `[]` brackets.
This is done when the instances can be inferred because they are implicit arguments to the type `linear_map`.
When they can be inferred from the type it is faster to use this method than to use type class inference

-/

import algebra.ring algebra.big_operators group_theory.subgroup group_theory.group_action
open function

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

-- /-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
-- class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)

-- infixr ` • `:73 := has_scalar.smul

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A semimodule is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `α` and an additive monoid of "vectors" `β`,
  connected by a "scalar multiplication" operation `r • x : β`
  (where `r : α` and `x : β`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class semimodule (α : Type u) (β : Type v) [semiring α]
  [add_comm_monoid β] extends distrib_mul_action α β :=
(add_smul : ∀(r s : α) (x : β), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : β, (0 : α) • x = 0)
end prio

section semimodule
variables [R:semiring α] [add_comm_monoid β] [semimodule α β] (r s : α) (x y : β)
include R

theorem add_smul : (r + s) • x = r • x + s • x := semimodule.add_smul r s x
variables (α)
@[simp] theorem zero_smul : (0 : α) • x = 0 := semimodule.zero_smul α x

variable {α}

lemma semimodule.eq_zero_of_zero_eq_one (zero_eq_one : (0 : α) = 1) : x = 0 :=
by rw [←one_smul α x, ←zero_eq_one, zero_smul]

instance smul.is_add_monoid_hom (x : β) : is_add_monoid_hom (λ r:α, r • x) :=
{ map_zero := zero_smul _ x,
  map_add := λ r₁ r₂, add_smul r₁ r₂ x }

lemma list.sum_smul {l : list α} {x : β} : l.sum • x = (l.map (λ r, r • x)).sum :=
show (λ r, r • x) l.sum = (l.map (λ r, r • x)).sum,
from (list.sum_hom _ _).symm

lemma multiset.sum_smul {l : multiset α} {x : β} : l.sum • x = (l.map (λ r, r • x)).sum :=
show (λ r, r • x) l.sum = (l.map (λ r, r • x)).sum,
from (multiset.sum_hom _ _).symm

lemma finset.sum_smul {f : γ → α} {s : finset γ} {x : β} :
  s.sum f • x = s.sum (λ r, (f r) • x) :=
show (λ r, r • x) (s.sum f) = s.sum (λ r, (f r) • x),
from (finset.sum_hom _ _).symm

end semimodule

section prio
set_option default_priority 100 -- see Note [default priority]
/-- A module is a generalization of vector spaces to a scalar ring.
  It consists of a scalar ring `α` and an additive group of "vectors" `β`,
  connected by a "scalar multiplication" operation `r • x : β`
  (where `r : α` and `x : β`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class module (α : Type u) (β : Type v) [ring α] [add_comm_group β] extends semimodule α β
end prio

/--
To prove two module structures on a fixed `add_comm_group` agree,
it suffices to check the scalar multiplications agree.
-/
-- We'll later use this to show `module ℤ M` is a subsingleton.
@[ext]
lemma module_ext {R : Type*} [ring R] {M : Type*} [add_comm_group M] (P Q : module R M)
  (w : ∀ (r : R) (m : M), by { haveI := P, exact r • m } = by { haveI := Q, exact r • m }) :
  P = Q :=
begin
  resetI,
  rcases P with ⟨⟨⟨⟨⟨P⟩⟩⟩⟩⟩, rcases Q with ⟨⟨⟨⟨⟨Q⟩⟩⟩⟩⟩, congr,
  funext r m,
  exact w r m,
  all_goals { apply proof_irrel_heq },
end

structure module.core (α β) [ring α] [add_comm_group β] extends has_scalar α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(add_smul : ∀(r s : α) (x : β), (r + s) • x = r • x + s • x)
(mul_smul : ∀(r s : α) (x : β), (r * s) • x = r • s • x)
(one_smul : ∀x : β, (1 : α) • x = x)

/-- Define `module` without proving `zero_smul` and `smul_zero` by using an auxiliary
structure `module.core`. -/
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
by simp [smul_add, sub_eq_add_neg]; rw smul_neg

theorem sub_smul (r s : α) (y : β) : (r - s) • y = r • y - s • y :=
by simp [add_smul, sub_eq_add_neg]

theorem smul_eq_zero {R E : Type*} [division_ring R] [add_comm_group E] [module R E]
  {c : R} {x : E} :
  c • x = 0 ↔ c = 0 ∨ x = 0 :=
⟨λ h, classical.by_cases or.inl
  (λ hc, or.inr $ by rw [← one_smul R x, ← inv_mul_cancel hc, mul_smul, h, smul_zero]),
  λ h, h.elim (λ hc, hc.symm ▸ zero_smul R x) (λ hx, hx.symm ▸ smul_zero c)⟩

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

/-- A ring homomorphism `f : α →+* β` defines a module structure by `r • x = f r * x`. -/
def ring_hom.to_module [ring α] [ring β] (f : α →+* β) : module α β :=
module.of_core
{ smul := λ r x, f r * x,
  smul_add := λ r x y, by unfold has_scalar.smul; rw [mul_add],
  add_smul := λ r s x, by unfold has_scalar.smul; rw [f.map_add, add_mul],
  mul_smul := λ r s x, by unfold has_scalar.smul; rw [f.map_mul, mul_assoc],
  one_smul := λ x, show f 1 * x = _, by rw [f.map_one, one_mul] }

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
notation β ` →ₗ[`:25 α:25 `] `:0 γ:0 := linear_map α β γ

namespace linear_map

variables {rα : ring α} {gβ : add_comm_group β} {gγ : add_comm_group γ} {gδ : add_comm_group δ}
variables {mβ : module α β} {mγ : module α γ} {mδ : module α δ}
variables (f g : β →ₗ[α] γ)
include α mβ mγ

instance : has_coe_to_fun (β →ₗ[α] γ) := ⟨_, to_fun⟩

@[simp] lemma coe_mk (f : β → γ) (h₁ h₂) :
  ((linear_map.mk f h₁ h₂ : β →ₗ[α] γ) : β → γ) = f := rfl

@[simp] lemma to_fun_eq_coe (f : β →ₗ[α] γ) : f.to_fun = ⇑f := rfl

theorem is_linear : is_linear_map α f := {..f}

@[ext] theorem ext {f g : β →ₗ[α] γ} (H : ∀ x, f x = g x) : f = g :=
by cases f; cases g; congr'; exact funext H

theorem ext_iff {f g : β →ₗ[α] γ} : f = g ↔ ∀ x, f x = g x :=
⟨by rintro rfl; simp, ext⟩

@[simp] lemma map_add (x y : β) : f (x + y) = f x + f y := f.add x y

@[simp] lemma map_smul (c : α) (x : β) : f (c • x) = c • f x := f.smul c x

@[simp] lemma map_zero : f 0 = 0 :=
by rw [← zero_smul α, map_smul f 0 0, zero_smul]

instance : is_add_group_hom f := { map_add := map_add f }

/-- convert a linear map to an additive map -/
def to_add_monoid_hom (f : β →ₗ[α] γ) : β →+ γ :=
{ to_fun := f,
  map_zero' := by simp,
  map_add' := by simp, }

@[simp] lemma to_add_monoid_hom_coe (f : β →ₗ[α] γ) :
  ((f.to_add_monoid_hom) : β → γ) = (f : β → γ) := rfl

@[simp] lemma map_neg (x : β) : f (- x) = - f x :=
by rw [← neg_one_smul α, map_smul, neg_one_smul]

@[simp] lemma map_sub (x y : β) : f (x - y) = f x - f y :=
by simp [map_neg, map_add, sub_eq_add_neg]

@[simp] lemma map_sum {ι} {t : finset ι} {g : ι → β} :
  f (t.sum g) = t.sum (λi, f (g i)) :=
(t.sum_hom f).symm

include mδ

/-- Composition of linear maps. -/
def comp (f : γ →ₗ[α] δ) (g : β →ₗ[α] γ) : β →ₗ[α] δ := ⟨f ∘ g, by simp, by simp⟩

@[simp] lemma comp_apply (f : γ →ₗ[α] δ) (g : β →ₗ[α] γ) (x : β) : f.comp g x = f (g x) := rfl

omit mγ mδ
variables [rα] [gβ] [mβ]

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
lemma is_linear_map_smul' {α R : Type*} [add_comm_group α] [ring R] [module R α] (a : α) :
  is_linear_map R (λ (c : R), c • a) :=
begin
  refine is_linear_map.mk (λ x y, add_smul x y a) _,
  intros _ _,
  simp [smul_smul]
end

variables {f : β → γ} (lin : is_linear_map α f)
include β γ lin

lemma map_zero : f (0 : β) = (0 : γ) :=
by rw [← zero_smul α (0 : β), lin.smul, zero_smul]

lemma map_add (x y : β) : f (x + y) = f x + f y :=
by rw [lin.add]

lemma map_neg (x : β) : f (- x) = - f x :=
by rw [← neg_one_smul α, lin.smul, neg_one_smul]

lemma map_sub (x y : β) : f (x - y) = f x - f y :=
by simp [lin.map_neg, lin.map_add, sub_eq_add_neg]

end is_linear_map

abbreviation module.End (R : Type u) (M : Type v)
  [comm_ring R] [add_comm_group M] [module R M] := M →ₗ[R] M

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

@[ext] theorem ext {s t : submodule α β}
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

lemma smul_mem_iff' (u : units α) : (u:α) • x ∈ p ↔ x ∈ p :=
⟨λ h, by simpa only [smul_smul, u.inv_mul, one_smul] using p.smul_mem ↑u⁻¹ h, p.smul_mem u⟩

instance : has_add p := ⟨λx y, ⟨x.1 + y.1, add_mem _ x.2 y.2⟩⟩
instance : has_zero p := ⟨⟨0, zero_mem _⟩⟩
instance : inhabited p := ⟨0⟩
instance : has_neg p := ⟨λx, ⟨-x.1, neg_mem _ x.2⟩⟩
instance : has_scalar α p := ⟨λ c x, ⟨c • x.1, smul_mem _ c x.2⟩⟩

@[simp, move_cast] lemma coe_add (x y : p) : (↑(x + y) : β) = ↑x + ↑y := rfl
@[simp, elim_cast] lemma coe_zero : ((0 : p) : β) = 0 := rfl
@[simp, move_cast] lemma coe_neg (x : p) : ((-x : p) : β) = -x := rfl
@[simp, move_cast] lemma coe_smul (r : α) (x : p) : ((r • x : p) : β) = r • ↑x := rfl
@[simp, elim_cast] lemma coe_mk (x : β) (hx : x ∈ p) : ((⟨x, hx⟩ : p) : β) = x := rfl

@[simp] protected lemma eta (x : p) (hx : (x : β) ∈ p) : (⟨x, hx⟩ : p) = x := subtype.eta x hx

instance : add_comm_group p :=
by refine {add := (+), zero := 0, neg := has_neg.neg, ..};
  { intros, apply set_coe.ext, simp [add_comm, add_left_comm] }

instance submodule_is_add_subgroup : is_add_subgroup (p : set β) :=
{ zero_mem := p.zero,
  add_mem  := p.add,
  neg_mem  := λ _, p.neg_mem }

@[simp, move_cast] lemma coe_sub (x y : p) : (↑(x - y) : β) = ↑x - ↑y := rfl

instance : module α p :=
by refine {smul := (•), ..};
   { intros, apply set_coe.ext, simp [smul_add, add_smul, mul_smul] }

protected def subtype : p →ₗ[α] β :=
by refine {to_fun := coe, ..}; simp [coe_smul]

@[simp] theorem subtype_apply (x : p) : p.subtype x = x := rfl

lemma subtype_eq_val (p : submodule α β) :
  ((submodule.subtype p) : p → β) = subtype.val := rfl

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

/--
Vector spaces are defined as an `abbreviation` for modules,
if the base ring is a field.
(A previous definition made `vector_space` a structure
defined to be `module`.)
This has as advantage that vector spaces are completely transparant
for type class inference, which means that all instances for modules
are immediately picked up for vector spaces as well.
A cosmetic disadvantage is that one can not extend vector spaces an sich,
in definitions such as `normed_space`.
The solution is to extend `module` instead.
-/
library_note "vector space definition"

/-- A vector space is the same as a module, except the scalar ring is actually
  a field. (This adds commutativity of the multiplication and existence of inverses.)
  This is the traditional generalization of spaces like `ℝ^n`, which have a natural
  addition operation and a way to multiply them by real numbers, but no multiplication
  operation between vectors. -/
abbreviation vector_space (α : Type u) (β : Type v) [field α] [add_comm_group β] :=
module α β

instance field.to_vector_space {α : Type*} [field α] : vector_space α α :=
{ .. ring.to_module }

/-- Subspace of a vector space. Defined to equal `submodule`. -/
@[reducible] def subspace (α : Type u) (β : Type v)
  [field α] [add_comm_group β] [vector_space α β] : Type v :=
submodule α β

instance subspace.vector_space {α β}
  {f : field α} [add_comm_group β] [vector_space α β]
  (p : subspace α β) : vector_space α p := {..submodule.module p}

namespace submodule

variables {R : division_ring α} [add_comm_group β] [module α β]
variables (p : submodule α β) {r : α} {x y : β}
include R

set_option class.instance_max_depth 36

theorem smul_mem_iff (r0 : r ≠ 0) : r • x ∈ p ↔ x ∈ p :=
p.smul_mem_iff' (units.mk0 r r0)

end submodule

namespace add_comm_monoid
open add_monoid

variables {M : Type*} [add_comm_monoid M]

/-- The natural ℕ-semimodule structure on any `add_comm_monoid`. -/
-- We don't make this a global instance, as it results in too many instances,
-- and confusing ambiguity in the notation `n • x` when `n : ℕ`.
def nat_semimodule : semimodule ℕ M :=
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

/-- The natural ℤ-module structure on any `add_comm_group`. -/
-- We don't immediately make this a global instance, as it results in too many instances,
-- and confusing ambiguity in the notation `n • x` when `n : ℤ`.
-- We do turn it into a global instance, but only at the end of this file,
-- and I remain dubious whether this is a good idea.
def int_module : module ℤ M :=
{ smul := gsmul,
  smul_add := λ _ _ _, gsmul_add _ _ _,
  add_smul := λ _ _ _, add_gsmul _ _ _,
  mul_smul := λ _ _ _, gsmul_mul _ _ _,
  one_smul := one_gsmul,
  zero_smul := zero_gsmul,
  smul_zero := gsmul_zero }

instance : subsingleton (module ℤ M) :=
begin
  split,
  intros P Q,
  ext,
  -- isn't that lovely: `r • m = r • m`
  have one_smul : by { haveI := P, exact (1 : ℤ) • m } = by { haveI := Q, exact (1 : ℤ) • m },
    begin
      rw [@one_smul ℤ _ _ (by { haveI := P, apply_instance, }) m],
      rw [@one_smul ℤ _ _ (by { haveI := Q, apply_instance, }) m],
    end,
  have nat_smul : ∀ n : ℕ, by { haveI := P, exact (n : ℤ) • m } = by { haveI := Q, exact (n : ℤ) • m },
    begin
      intro n,
      induction n with n ih,
      { erw [zero_smul, zero_smul], },
      { rw [int.coe_nat_succ, add_smul, add_smul],
        erw ih,
        rw [one_smul], }
    end,
  cases r,
  { rw [int.of_nat_eq_coe, nat_smul], },
  { rw [int.neg_succ_of_nat_coe, neg_smul, neg_smul, nat_smul], }
end

end add_comm_group

section
local attribute [instance] add_comm_monoid.nat_semimodule

lemma semimodule.smul_eq_smul (R : Type*) [semiring R]
  {β : Type*} [add_comm_group β] [semimodule R β]
  (n : ℕ) (b : β) : n • b = (n : R) • b :=
begin
  induction n with n ih,
  { rw [nat.cast_zero, zero_smul, zero_smul] },
  { change (n + 1) • b = (n + 1 : R) • b,
    rw [add_smul, add_smul, one_smul, ih, one_smul] }
end

lemma semimodule.add_monoid_smul_eq_smul (R : Type*) [semiring R] {β : Type*} [add_comm_group β]
  [semimodule R β] (n : ℕ) (b : β) : add_monoid.smul n b = (n : R) • b :=
semimodule.smul_eq_smul R n b

lemma nat.smul_def {M : Type*} [add_comm_monoid M] (n : ℕ) (x : M) :
  n • x = add_monoid.smul n x :=
rfl

end

section
local attribute [instance] add_comm_group.int_module

lemma gsmul_eq_smul {M : Type*} [add_comm_group M] (n : ℤ) (x : M) : gsmul n x = n • x := rfl

lemma module.gsmul_eq_smul_cast (R : Type*) [ring R] {β : Type*} [add_comm_group β] [module R β]
  (n : ℤ) (b : β) : gsmul n b = (n : R) • b :=
begin
  cases n,
  { apply semimodule.add_monoid_smul_eq_smul, },
  { dsimp,
    rw semimodule.add_monoid_smul_eq_smul R,
    push_cast,
    rw neg_smul, }
end

lemma module.gsmul_eq_smul {β : Type*} [add_comm_group β] [module ℤ β]
  (n : ℤ) (b : β) : gsmul n b = n • b :=
by rw [module.gsmul_eq_smul_cast ℤ, int.cast_id]

end

-- We prove this without using the `add_comm_group.int_module` instance, so the `•`s here
-- come from whatever the local `module ℤ` structure actually is.
lemma add_monoid_hom.map_int_module_smul
  {α : Type*} {β : Type*} [add_comm_group α] [add_comm_group β]
  [module ℤ α] [module ℤ β] (f : α →+ β) (x : ℤ) (a : α) : f (x • a) = x • f a :=
by simp only [← module.gsmul_eq_smul, f.map_gsmul]

lemma add_monoid_hom.map_int_cast_smul
  {R : Type*} [ring R] {α : Type*} {β : Type*} [add_comm_group α] [add_comm_group β]
  [module R α] [module R β] (f : α →+ β) (x : ℤ) (a : α) : f ((x : R) • a) = (x : R) • f a :=
by simp only [← module.gsmul_eq_smul_cast, f.map_gsmul]

lemma add_monoid_hom.map_nat_cast_smul
  {R : Type*} [semiring R] {α : Type*} {β : Type*} [add_comm_group α] [add_comm_group β]
  [semimodule R α] [semimodule R β] (f : α →+ β) (x : ℕ) (a : α) :
  f ((x : R) • a) = (x : R) • f a :=
by simp only [← semimodule.add_monoid_smul_eq_smul, f.map_smul]

lemma add_monoid_hom.map_rat_cast_smul {R : Type*} [division_ring R] [char_zero R]
  {E : Type*} [add_comm_group E] [module R E] {F : Type*} [add_comm_group F] [module R F]
  (f : E →+ F) (c : ℚ) (x : E) :
  f ((c : R) • x) = (c : R) • f x :=
begin
  have : ∀ (x : E) (n : ℕ), 0 < n → f (((n⁻¹ : ℚ) : R) • x) = ((n⁻¹ : ℚ) : R) • f x,
  { intros x n hn,
    replace hn : (n : R) ≠ 0 := nat.cast_ne_zero.2 (ne_of_gt hn),
    conv_rhs { congr, skip, rw [← one_smul R x, ← mul_inv_cancel hn, mul_smul] },
    rw [f.map_nat_cast_smul, smul_smul, rat.cast_inv, rat.cast_coe_nat,
      inv_mul_cancel hn, one_smul] },
  refine c.num_denom_cases_on (λ m n hn hmn, _),
  rw [rat.mk_eq_div, div_eq_mul_inv, rat.cast_mul, int.cast_coe_nat, mul_smul, mul_smul,
    rat.cast_coe_int, f.map_int_cast_smul, this _ n hn]
end

lemma add_monoid_hom.map_rat_module_smul {E : Type*} [add_comm_group E] [vector_space ℚ E]
  {F : Type*} [add_comm_group F] [module ℚ F] (f : E →+ F) (c : ℚ) (x : E) :
  f (c • x) = c • f x :=
rat.cast_id c ▸ f.map_rat_cast_smul c x

-- We finally turn on these instances globally:
attribute [instance] add_comm_monoid.nat_semimodule add_comm_group.int_module

/-- Reinterpret an additive homomorphism as a `ℤ`-linear map. -/
def add_monoid_hom.to_int_linear_map [add_comm_group α] [add_comm_group β] (f : α →+ β) :
  α →ₗ[ℤ] β :=
⟨f, f.map_add, f.map_int_module_smul⟩

/-- Reinterpret an additive homomorphism as a `ℚ`-linear map. -/
def add_monoid_hom.to_rat_linear_map [add_comm_group α] [vector_space ℚ α]
  [add_comm_group β] [vector_space ℚ β] (f : α →+ β) :
  α →ₗ[ℚ] β :=
⟨f, f.map_add, f.map_rat_module_smul⟩

namespace finset

lemma sum_const' {α : Type*} (R : Type*) [ring R] {β : Type*}
  [add_comm_group β] [module R β] {s : finset α} (b : β) :
  finset.sum s (λ (a : α), b) = (finset.card s : R) • b :=
by rw [finset.sum_const, ← semimodule.smul_eq_smul]; refl

variables {M : Type*} [decidable_linear_ordered_cancel_comm_monoid M]
  {s : finset α} (f : α → M)

theorem exists_card_smul_le_sum (hs : s.nonempty) :
  ∃ i ∈ s, s.card • f i ≤ s.sum f :=
exists_le_of_sum_le hs $ by rw [sum_const, ← nat.smul_def, smul_sum]

theorem exists_card_smul_ge_sum (hs : s.nonempty) :
  ∃ i ∈ s, s.sum f ≤ s.card • f i :=
exists_le_of_sum_le hs $ by rw [sum_const, ← nat.smul_def, smul_sum]

end finset
