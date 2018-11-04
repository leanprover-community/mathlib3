/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl

Modules over a ring.
-/

import algebra.ring algebra.big_operators data.set.lattice
open function

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : out_param $ Type u) (γ : Type v) := (smul : α → γ → γ)

infixr ` • `:73 := has_scalar.smul

/-- A semimodule is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `α` and an additive monoid of "vectors" `β`,
  connected by a "scalar multiplication" operation `r • x : β`
  (where `r : α` and `x : β`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class semimodule (α : out_param $ Type u) (β : Type v) [out_param $ semiring α]
  extends has_scalar α β, add_comm_monoid β :=
(smul_add : ∀r (x y : β), r • (x + y) = r • x + r • y)
(add_smul : ∀r s (x : β), (r + s) • x = r • x + s • x)
(mul_smul : ∀r s (x : β), (r * s) • x = r • s • x)
(one_smul : ∀x : β, (1 : α) • x = x)
(zero_smul : ∀x : β, (0 : α) • x = 0)
(smul_zero {} : ∀r, r • (0 : β) = 0)

section semimodule
variables {R:semiring α} [semimodule α β] {r s : α} {x y : β}
include R

theorem smul_add' : r • (x + y) = r • x + r • y := semimodule.smul_add r x y
theorem add_smul' : (r + s) • x = r • x + s • x := semimodule.add_smul r s x
theorem mul_smul' : (r * s) • x = r • s • x := semimodule.mul_smul r s x
@[simp] theorem one_smul' : (1 : α) • x = x := semimodule.one_smul x
@[simp] theorem zero_smul' : (0 : α) • x = 0 := semimodule.zero_smul x
@[simp] theorem smul_zero' : r • (0 : β) = 0 := semimodule.smul_zero r

lemma smul_smul' : r • s • x = (r * s) • x := mul_smul'.symm

end semimodule

/-- A module is a generalization of vector spaces to a scalar ring.
  It consists of a scalar ring `α` and an additive group of "vectors" `β`,
  connected by a "scalar multiplication" operation `r • x : β`
  (where `r : α` and `x : β`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
class module (α : out_param $ Type u) (β : Type v) [out_param $ ring α]
  extends has_scalar α β, add_comm_group β :=
(smul_add : ∀r (x y : β), r • (x + y) = r • x + r • y)
(add_smul : ∀r s (x : β), (r + s) • x = r • x + s • x)
(mul_smul : ∀r s (x : β), (r * s) • x = r • s • x)
(one_smul : ∀x : β, (1 : α) • x = x)

section module
variables {R:ring α} [module α β] {r s : α} {x y : β}
include R

theorem smul_add : r • (x + y) = r • x + r • y := module.smul_add r x y
theorem add_smul : (r + s) • x = r • x + s • x := module.add_smul r s x
theorem mul_smul : (r * s) • x = r • s • x := module.mul_smul r s x
@[simp] theorem one_smul : (1 : α) • x = x := module.one_smul x

@[simp] theorem zero_smul : (0 : α) • x = 0 :=
have (0 : α) • x + 0 • x = 0 • x + 0, by rw ← add_smul; simp,
add_left_cancel this

@[simp] theorem smul_zero : r • (0 : β) = 0 :=
have r • (0:β) + r • 0 = r • 0 + 0, by rw ← smul_add; simp,
add_left_cancel this

instance module.to_semimodule : semimodule α β :=
{ zero_smul := λ x, zero_smul,
  smul_zero := λ r, smul_zero,
  ..‹module α β› }

@[simp] theorem neg_smul : -r • x = - (r • x) :=
eq_neg_of_add_eq_zero (by rw [← add_smul, add_left_neg, zero_smul])

theorem neg_one_smul (x : β) : (-1 : α) • x = -x := by simp

@[simp] theorem smul_neg : r • (-x) = -(r • x) :=
by rw [← neg_one_smul x, ← mul_smul, mul_neg_one, neg_smul]

theorem smul_sub (r : α) (x y : β) : r • (x - y) = r • x - r • y :=
by simp [smul_add]

theorem sub_smul (r s : α) (y : β) : (r - s) • y = r • y - s • y :=
by simp [add_smul]

lemma smul_smul : r • s • x = (r * s) • x := mul_smul.symm

end module

instance semiring.to_semimodule [r : semiring α] : semimodule α α :=
{ smul := (*),
  smul_add := mul_add,
  add_smul := add_mul,
  mul_smul := mul_assoc,
  one_smul := one_mul,
  zero_smul := zero_mul,
  smul_zero := mul_zero, ..r }

@[simp] lemma smul_eq_mul' [semiring α] {a a' : α} : a • a' = a * a' := rfl

instance ring.to_module [r : ring α] : module α α :=
{ ..semiring.to_semimodule }

@[simp] lemma smul_eq_mul [ring α] {a a' : α} : a • a' = a * a' := rfl

structure is_linear_map {α : Type u} {β : Type v} {γ : Type w} [ring α] [module α β] [module α γ]
  (f : β → γ) : Prop :=
(add  : ∀x y, f (x + y) = f x + f y)
(smul : ∀c x, f (c • x) = c • f x)

namespace is_linear_map
variables [ring α] [module α β] [module α γ] [module α δ]
variables {f g h : β → γ} {r : α} {x y : β}
include α

section
variable (hf : is_linear_map f)
include hf

@[simp] lemma zero : f 0 = 0 :=
calc f 0 = f (0 • 0 : β) : by rw [zero_smul]
     ... = 0 : by rw [hf.smul]; simp

@[simp] lemma neg (x : β) : f (- x) = - f x :=
eq_neg_of_add_eq_zero $ by rw [←hf.add]; simp [hf.zero]

@[simp] lemma sub (x y : β) : f (x - y) = f x - f y :=
by simp [hf.neg, hf.add]

@[simp] lemma sum {ι : Type x} {t : finset ι} {g : ι → β} : f (t.sum g) = t.sum (λi, f (g i)) :=
(finset.sum_hom f hf.zero hf.add).symm

end

lemma comp {g : δ → β} (hf : is_linear_map f) (hg : is_linear_map g) : is_linear_map (f ∘ g) :=
by refine {..}; simp [(∘), hg.add, hf.add, hg.smul, hf.smul]

lemma id : is_linear_map (id : β → β) :=
by refine {..}; simp

lemma inverse {f : γ → β} {g : β → γ}
  (hf : is_linear_map f) (h₁ : left_inverse g f) (h₂ : right_inverse g f): is_linear_map g :=
⟨assume x y,
  have g (f (g (x + y))) = g (f (g x + g y)),
    by rw [h₂ (x + y), hf.add, h₂ x, h₂ y],
  by rwa [h₁ (g (x + y)), h₁ (g x + g y)] at this,
assume a b,
  have g (f (g (a • b))) = g (f (a • g b)),
    by rw [h₂ (a • b), hf.smul, h₂ b],
  by rwa [h₁ (g (a • b)), h₁ (a • g b)] at this ⟩

lemma map_zero : is_linear_map (λb, 0 : β → γ) :=
by refine {..}; simp

lemma map_neg (hf : is_linear_map f) : is_linear_map (λb, - f b) :=
by refine {..}; simp [hf.add, hf.smul]

lemma map_add (hf : is_linear_map f) (hg : is_linear_map g) : is_linear_map (λb, f b + g b) :=
by refine {..}; simp [hg.add, hf.add, hg.smul, hf.smul, smul_add]

lemma map_sum [decidable_eq δ] {t : finset δ} {f : δ → β → γ} :
  (∀d∈t, is_linear_map (f d)) → is_linear_map (λb, t.sum $ λd, f d b) :=
finset.induction_on t (by simp [map_zero]) (by simp [map_add] {contextual := tt})

lemma map_sub (hf : is_linear_map f) (hg : is_linear_map g) : is_linear_map (λb, f b - g b) :=
by refine {..}; simp [hg.add, hf.add, hg.smul, hf.smul, smul_add]

lemma map_smul_right {α : Type u} {β : Type v} {γ : Type w} [comm_ring α] [module α β] [module α γ]
  {f : β → γ} {r : α} (hf : is_linear_map f) :
  is_linear_map (λb, r • f b) :=
by refine {..}; simp [hf.add, hf.smul, smul_add, smul_smul, mul_comm]

lemma map_smul_left {f : γ → α} (hf : is_linear_map f) : is_linear_map (λb, f b • x) :=
by refine {..}; simp [hf.add, hf.smul, add_smul, smul_smul]

end is_linear_map

/-- A submodule of a module is one which is closed under vector operations.
  This is a sufficient condition for the subset of vectors in the submodule
  to themselves form a module. -/
class is_submodule {α : Type u} {β : Type v} [ring α] [module α β] (p : set β) : Prop :=
(zero_ : (0:β) ∈ p)
(add_  : ∀ {x y}, x ∈ p → y ∈ p → x + y ∈ p)
(smul : ∀ c {x}, x ∈ p → c • x ∈ p)

namespace is_submodule
variables [ring α] [module α β] [module α γ]
variables {p p' : set β} [is_submodule p] [is_submodule p']
variables {r : α}
include α

section
variables {x y : β}

lemma zero : (0 : β) ∈ p := is_submodule.zero_ α p

lemma add : x ∈ p → y ∈ p → x + y ∈ p := is_submodule.add_ α

lemma neg (hx : x ∈ p) : -x ∈ p := by rw ← neg_one_smul x; exact smul _ hx

lemma sub (hx : x ∈ p) (hy : y ∈ p) : x - y ∈ p := add hx (neg hy)

lemma sum {ι : Type w} [decidable_eq ι] {t : finset ι} {f : ι → β} :
  (∀c∈t, f c ∈ p) → t.sum f ∈ p :=
finset.induction_on t (by simp [zero]) (by simp [add] {contextual := tt})

lemma smul_ne_0 {a : α} {b : β} (h : a ≠ 0 → b ∈ p) : a • b ∈ p :=
classical.by_cases
  (assume : a = 0, by simp [this, zero])
  (assume : a ≠ 0, by simp [h this, smul])

instance single_zero : is_submodule ({0} : set β) :=
by refine {..}; by simp {contextual := tt}

instance univ : is_submodule (set.univ : set β) :=
by refine {..}; by simp {contextual := tt}

instance image {f : β → γ} (hf : is_linear_map f) : is_submodule (f '' p) :=
{ is_submodule .
  zero_ := ⟨0, zero, hf.zero⟩,
  add_  := assume c₁ c₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩,
    ⟨b₁ + b₂, add hb₁ hb₂, by simp [eq₁, eq₂, hf.add]⟩,
  smul  := assume a c ⟨b, hb, eq⟩, ⟨a • b, smul a hb, by simp [hf.smul, eq]⟩ }

instance range {f : β → γ} (hf : is_linear_map f) : is_submodule (set.range f) :=
by rw [← set.image_univ]; exact is_submodule.image hf

instance preimage {f : γ → β} (hf : is_linear_map f) : is_submodule (f ⁻¹' p) :=
by refine {..}; simp [hf.zero, hf.add, hf.smul, zero, add, smul] {contextual:=tt}

instance add_submodule : is_submodule {z | ∃x∈p, ∃y∈p', z = x + y} :=
{ is_submodule .
  zero_ := ⟨0, zero, 0, zero, by simp⟩,
  add_  := assume b₁ b₂ ⟨x₁, hx₁, y₁, hy₁, eq₁⟩ ⟨x₂, hx₂, y₂, hy₂, eq₂⟩,
    ⟨x₁ + x₂, add hx₁ hx₂, y₁ + y₂, add hy₁ hy₂, by simp [eq₁, eq₂]⟩,
  smul  := assume a b ⟨x, hx, y, hy, eq⟩,
    ⟨a • x, smul _ hx, a • y, smul _ hy, by simp [eq, smul_add]⟩ }

lemma Inter_submodule {ι : Sort w} {s : ι → set β} (h : ∀i, is_submodule (s i)) :
  is_submodule (⋂i, s i) :=
by refine {..}; simp [zero, add, smul] {contextual := tt}

instance Inter_submodule' {ι : Sort w} {s : ι → set β} [h : ∀i, is_submodule (s i)] :
  is_submodule (⋂i, s i) :=
Inter_submodule h

instance sInter_submodule {s : set (set β)} [hs : ∀t∈s, is_submodule t] : is_submodule (⋂₀ s) :=
by rw set.sInter_eq_bInter; exact Inter_submodule (assume t, Inter_submodule $ hs t)

instance inter_submodule : is_submodule (p ∩ p') :=
suffices is_submodule (⋂₀ {p, p'} : set β), by simpa [set.inter_comm],
@is_submodule.sInter_submodule α β _ _ {p, p'} $
  by simp [or_imp_distrib, ‹is_submodule p›, ‹is_submodule p'›] {contextual := tt}

end

end is_submodule

section comm_ring

theorem is_submodule.eq_univ_of_contains_unit {α : Type u} [comm_ring α] (S : set α) [is_submodule S]
  (x y : α) (hx : x ∈ S) (h : y * x = 1) : S = set.univ :=
set.ext $ λ z, ⟨λ hz, trivial, λ hz, calc
    z = z * (y * x) : by simp [h]
  ... = (z * y) * x : eq.symm $ mul_assoc z y x
  ... ∈ S : is_submodule.smul (z * y) hx⟩

theorem is_submodule.univ_of_one_mem {α : Type u} [comm_ring α] (S : set α) [is_submodule S] :
  (1:α) ∈ S → S = set.univ :=
λ h, set.ext $ λ z, ⟨λ hz, trivial, λ hz, by simpa using (is_submodule.smul z h : z * 1 ∈ S)⟩

end comm_ring

/-- A vector space is the same as a module, except the scalar ring is actually
  a field. (This adds commutativity of the multiplication and existence of inverses.)
  This is the traditional generalization of spaces like `ℝ^n`, which have a natural
  addition operation and a way to multiply them by real numbers, but no multiplication
  operation between vectors. -/
class vector_space (α : out_param $ Type u) (β : Type v) [out_param $ field α] extends module α β

/-- Subspace of a vector space. Defined to equal `is_submodule`. -/
@[reducible] def subspace {α : Type u} {β : Type v} [field α] [vector_space α β] (p : set β) :
  Prop :=
is_submodule p
