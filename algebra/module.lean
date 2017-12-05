/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl

Modules over a ring.
-/

import algebra.ring algebra.big_operators data.set.basic
open function

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

lemma set.sInter_eq_Inter {s : set (set α)} : (⋂₀ s) = (⋂i ∈ s, i) :=
set.ext $ by simp

class has_scalar (α : inout Type u) (γ : Type v) := (smul : α → γ → γ)

infixr ` • `:73 := has_scalar.smul

class module (α : inout Type u) (β : Type v) [inout ring α]
  extends has_scalar α β, add_comm_group β :=
(smul_add : ∀r (x y : β), r • (x + y) = r • x + r • y)
(add_smul : ∀r s (x : β), (r + s) • x = r • x + s • x)
(mul_smul : ∀r s (x : β), (r * s) • x = r • s • x)
(one_smul : ∀x : β, (1 : α) • x = x)

section module
variables [ring α] [module α β] {r s : α} {x y : β}

theorem smul_add : r • (x + y) = r • x + r • y := module.smul_add r x y
theorem add_smul : (r + s) • x = r • x + s • x := module.add_smul r s x
theorem mul_smul : (r * s) • x = r • s • x :=  module.mul_smul r s x
@[simp] theorem one_smul : (1 : α) • x = x := module.one_smul _ x

@[simp] theorem zero_smul : (0 : α) • x = 0 :=
have (0 : α) • x + 0 • x = 0 • x + 0, by rw ← add_smul; simp,
add_left_cancel this

@[simp] theorem smul_zero : r • (0 : β) = 0 :=
have r • (0:β) + r • 0 = r • 0 + 0, by rw ← smul_add; simp,
add_left_cancel this

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

instance ring.to_module [r : ring α] : module α α :=
{ smul := (*),
  smul_add := mul_add,
  add_smul := add_mul,
  mul_smul := mul_assoc,
  one_smul := one_mul, ..r }

@[simp] lemma smul_eq_mul [ring α] {a a' : α} : a • a' = a * a' := rfl

structure is_linear_map {α : Type u} {β : Type v} {γ : Type w} [ring α] [module α β] [module α γ]
  (f : β → γ) : Prop :=
(add  : ∀x y, f (x + y) = f x + f y)
(smul : ∀c x, f (c • x) = c • f x)

attribute [simp] is_linear_map.add is_linear_map.smul

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

@[simp] lemma sum {ι : Type w} {t : finset ι} {g : ι → β} : f (t.sum g) = t.sum (λi, f (g i)) :=
(finset.sum_hom f hf.zero hf.add).symm

end

lemma comp {g : δ → β} (hf : is_linear_map f) (hg : is_linear_map g) : is_linear_map (f ∘ g) :=
by refine {..}; simp [(∘), hg.add, hf.add, hg.smul, hf.smul]

lemma id : is_linear_map (id : β → β) :=
by refine {..}; simp

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

lemma map_smul_left {f : β → α} (hf : is_linear_map f) : is_linear_map (λb, f b • x) :=
by refine {..}; simp [hf.add, hf.smul, add_smul, smul_smul]

end is_linear_map

class is_submodule {α : Type u} {β : Type v} [ring α] [module α β] (p : set β) : Prop :=
(zero_ : (0:β) ∈ p)
(add_  : ∀ {x y}, x ∈ p → y ∈ p → x + y ∈ p)
(smul  : ∀ c {x}, x ∈ p → c • x ∈ p)

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
by rw [set.sInter_eq_Inter]; exact Inter_submodule (assume t, Inter_submodule $ hs t)

instance inter_submodule : is_submodule (p ∩ p') :=
suffices is_submodule (⋂₀ {p, p'} : set β), by simpa,
@is_submodule.sInter_submodule α β _ _ {p, p'} $
  by simp [or_imp_distrib, ‹is_submodule p›, ‹is_submodule p'›] {contextual := tt}

end

section subtype
variables {x y : {x : β // x ∈ p}}

instance : has_add {x : β // x ∈ p} := ⟨λ ⟨x, px⟩ ⟨y, py⟩, ⟨x + y, add px py⟩⟩
instance : has_zero {x : β // x ∈ p} := ⟨⟨0, zero⟩⟩
instance : has_neg {x : β // x ∈ p} := ⟨λ ⟨x, hx⟩, ⟨-x, neg hx⟩⟩
instance : has_scalar α {x : β // x ∈ p} := ⟨λ c ⟨x, hx⟩, ⟨c • x, smul c hx⟩⟩

@[simp] lemma add_val  : (x + y).val = x.val + y.val := by cases x; cases y; refl
@[simp] lemma zero_val : (0 : {x : β // x ∈ p}).val = 0 := rfl
@[simp] lemma neg_val  : (-x).val = -x.val := by cases x; refl
@[simp] lemma smul_val : (r • x).val = r • x.val := by cases x; refl

instance : module α {x : β // x ∈ p} :=
by refine {add := (+), zero := 0, neg := has_neg.neg, smul := (•), ..};
  { intros, apply subtype.eq,
    simp [smul_add, add_smul, mul_smul] }

lemma sub_val : (x - y).val = x.val - y.val := by simp

lemma is_linear_map_subtype_val {f : γ → {x : β // x ∈ p}} (hf : is_linear_map f) :
  is_linear_map (λb, (f b).val) :=
by refine {..}; simp [hf.add, hf.smul]

lemma is_linear_map_subtype_mk {f : γ → β} (hf : is_linear_map f) {h : ∀c, f c ∈ p} :
  is_linear_map (λc, ⟨f c, h c⟩ : γ → {x : β // x ∈ p}) :=
by refine {..}; intros; apply subtype.eq; simp [hf.add, hf.smul]

end subtype

section quotient

variables (s : set β) [hs : is_submodule s]
include s hs

def quotient_rel : setoid β :=
⟨λb₁ b₂, b₁ - b₂ ∈ s,
  assume b, by simp [zero],
  assume b₁ b₂ hb,
  have - (b₁ - b₂) ∈ s, from is_submodule.neg hb,
  by simpa using this,
  assume b₁ b₂ b₃ hb₁₂ hb₂₃,
  have (b₁ - b₂) + (b₂ - b₃) ∈ s, from add hb₁₂ hb₂₃,
  by simpa using this⟩

local attribute [instance] quotient_rel

def quotient : Type v := quotient (quotient_rel s)

local notation ` Q ` := quotient s

instance quotient.has_zero : has_zero Q := ⟨⟦ 0 ⟧⟩

instance quotient.has_add : has_add Q :=
⟨λa b, quotient.lift_on₂ a b (λa b, ⟦a + b⟧) $
  assume a₁ a₂ b₁ b₂ (h₁ : a₁ - b₁ ∈ s) (h₂ : a₂ - b₂ ∈ s),
  quotient.sound $
  have (a₁ - b₁) + (a₂ - b₂) ∈ s, from add h₁ h₂,
  show (a₁ + a₂) - (b₁ + b₂) ∈ s, by simpa⟩

instance quotient.has_neg : has_neg Q :=
⟨λa, quotient.lift_on a (λa, ⟦- a⟧) $ assume a b (h : a - b ∈ s),
  quotient.sound $
  have - (a - b) ∈ s, from neg h,
  show (-a) - (-b) ∈ s, by simpa⟩

instance quotient.has_scalar : has_scalar α Q :=
⟨λa b, quotient.lift_on b (λb, ⟦a • b⟧) $ assume b₁ b₂ (h : b₁ - b₂ ∈ s),
  quotient.sound $
  have a • (b₁ - b₂) ∈ s, from is_submodule.smul a h,
  show a • b₁ - a • b₂ ∈ s, by simpa [smul_add]⟩

instance quotient.module : module α Q :=
{ module .
  zero := 0,
  add  := (+),
  neg  := has_neg.neg,
  smul := (•),
  add_assoc    := assume a b c, quotient.induction_on₃ a b c $ assume a b c, quotient.sound $
    by simp,
  add_comm     := assume a b, quotient.induction_on₂ a b $ assume a b, quotient.sound $
    by simp,
  add_zero     := assume a, quotient.induction_on a $ assume a, quotient.sound $
    by simp,
  zero_add     := assume a, quotient.induction_on a $ assume a, quotient.sound $
    by simp,
  add_left_neg := assume a, quotient.induction_on a $ assume a, quotient.sound $
    by simp,
  one_smul     := assume a, quotient.induction_on a $ assume a, quotient.sound $
    by simp,
  mul_smul     := assume a b c, quotient.induction_on c $ assume c, quotient.sound $
    by simp [mul_smul],
  smul_add     := assume a b c, quotient.induction_on₂ b c $ assume b c, quotient.sound $
    by simp [smul_add],
  add_smul     := assume a b c, quotient.induction_on c $ assume c, quotient.sound $
    by simp [add_smul] }

instance quotient.inhabited : inhabited Q := ⟨0⟩

lemma is_linear_map_quotient_mk : @is_linear_map _ _ Q _ _ _ (λb, ⟦b⟧ : β → Q) :=
by refine {..}; intros; refl

def quotient.lift {f : β → γ} (hf : is_linear_map f) (h : ∀x∈s, f x = 0) (b : Q) : γ :=
b.lift_on f $ assume a b (hab : a - b ∈ s),
  have f a - f b = 0, by rw [←hf.sub]; exact h _ hab,
  show f a = f b, from eq_of_sub_eq_zero this

lemma is_linear_map_quotient_lift {f : β → γ} {h : ∀x y, x - y ∈ s → f x = f y}
  (hf : is_linear_map f) : is_linear_map (λq:Q, quotient.lift_on q f h) :=
⟨assume b₁ b₂, quotient.induction_on₂ b₁ b₂ $ assume b₁ b₂, hf.add b₁ b₂,
  assume a b, quotient.induction_on b $ assume b, hf.smul a b⟩

lemma quotient.injective_lift [is_submodule s] {f : β → γ} (hf : is_linear_map f)
  (hs : s = {x | f x = 0}) : injective (quotient.lift s hf $ le_of_eq hs) :=
assume a b, quotient.induction_on₂ a b $ assume a b (h : f a = f b), quotient.sound $
  have f (a - b) = 0, by rw [hf.sub]; simp [h],
  show a - b ∈ s, from hs.symm ▸ this

end quotient

end is_submodule

def linear_map {α : Type u} (β : Type v) (γ : Type w) [ring α] [module α β] [module α γ] :=
subtype (@is_linear_map α β γ _ _ _)

namespace linear_map

variables [ring α] [module α β] [module α γ]
variables {r : α} {A B C : linear_map β γ} {x y : β}
include α

instance : has_coe_to_fun (linear_map β γ) := ⟨_, subtype.val⟩

theorem ext (h : ∀ x, A x = B x) : A = B := subtype.eq $ funext h

lemma is_linear_map_coe : is_linear_map A := A.property

@[simp] lemma map_add  : A (x + y) = A x + A y := is_linear_map_coe.add x y
@[simp] lemma map_smul : A (r • x) = r • A x := is_linear_map_coe.smul r x
@[simp] lemma map_zero : A 0 = 0 := is_linear_map_coe.zero
@[simp] lemma map_neg  : A (-x) = -A x := is_linear_map_coe.neg _
@[simp] lemma map_sub  : A (x - y) = A x - A y := is_linear_map_coe.sub _ _

/- kernel -/

def ker (A : linear_map β γ) : set β := {y | A y = 0}

section ker

@[simp] lemma mem_ker : x ∈ A.ker ↔ A x = 0 := iff.rfl

theorem ker_of_map_eq_map (h : A x = A y) : x - y ∈ A.ker :=
by rw [mem_ker, map_sub]; exact sub_eq_zero_of_eq h

theorem inj_of_trivial_ker (H : A.ker ⊆ {0}) (h : A x = A y) : x = y :=
eq_of_sub_eq_zero $ set.eq_of_mem_singleton $ H $ ker_of_map_eq_map h

variables (α A)

instance ker.is_submodule : is_submodule A.ker :=
{ zero_ := map_zero,
  add_ := λ x y HU HV, by rw mem_ker at *; simp [HU, HV, mem_ker],
  smul := λ r x HV, by rw mem_ker at *; simp [HV] }

theorem sub_ker (HU : x ∈ A.ker) (HV : y ∈ A.ker) : x - y ∈ A.ker :=
is_submodule.sub HU HV

end ker

/- image -/

def im (A : linear_map β γ) : set γ := {x | ∃ y, A y = x}

@[simp] lemma mem_im {A : linear_map β γ} {z : γ} :
  z ∈ A.im ↔ ∃ y, A y = z := iff.rfl

instance im.is_submodule : is_submodule A.im :=
{ zero_ := ⟨0, map_zero⟩,
  add_ := λ a b ⟨x, hx⟩ ⟨y, hy⟩, ⟨x + y, by simp [hx, hy]⟩,
  smul := λ r a ⟨x, hx⟩, ⟨r • x, by simp [hx]⟩ }

section add_comm_group

instance : has_add (linear_map β γ) := ⟨λhf hg, ⟨_, hf.2.map_add hg.2⟩⟩
instance : has_zero (linear_map β γ) := ⟨⟨_, is_linear_map.map_zero⟩⟩
instance : has_neg (linear_map β γ) := ⟨λhf, ⟨_, hf.2.map_neg⟩⟩

@[simp] lemma add_app : (A + B) x = A x + B x := rfl
@[simp] lemma zero_app : (0 : linear_map β γ) x = 0 := rfl
@[simp] lemma neg_app : (-A) x = -A x := rfl

instance : add_comm_group (linear_map β γ) :=
by refine {add := (+), zero := 0, neg := has_neg.neg, ..}; { intros, apply ext, simp }

end add_comm_group

end linear_map

namespace linear_map
variables [comm_ring α] [module α β] [module α γ]

instance : has_scalar α (linear_map β γ) := ⟨λr f, ⟨λb, r • f b, f.2.map_smul_right⟩⟩

@[simp] lemma smul_app {r : α} {x : β} {A : linear_map β γ} : (r • A) x = r • (A x) := rfl

variables (α β γ)

instance : module α (linear_map β γ) :=
by refine {smul := (•), ..linear_map.add_comm_group, ..};
  { intros, apply ext, simp [smul_add, add_smul, mul_smul] }

end linear_map

namespace module
variables [ring α] [module α β]
include α

instance : has_one (linear_map β β) := ⟨⟨id, is_linear_map.id⟩⟩
instance : has_mul (linear_map β β) := ⟨λf g, ⟨_, is_linear_map.comp f.2 g.2⟩⟩

@[simp] lemma one_app (x : β) : (1 : linear_map β β) x = x := rfl
@[simp] lemma mul_app (A B : linear_map β β) (x : β) : (A * B) x = A (B x) := rfl

variables (α β)

instance endomorphism_ring : ring (linear_map β β) :=
by refine {mul := (*), one := 1, ..linear_map.add_comm_group, ..};
  { intros, apply linear_map.ext, simp }

def general_linear_group := units (linear_map β β)

end module

class vector_space (α : inout Type u) (β : Type v) [field α] extends module α β

@[reducible] def subspace {α : Type u} {β : Type v} [field α] [vector_space α β] (p : set β) :
  Prop :=
is_submodule p
