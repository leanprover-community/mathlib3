/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad

Modules over a ring.
-/

import algebra.ring

universes u v

class has_scalar (α : inout Type u) (γ : Type v) := (smul : α → γ → γ)

infixl ` • `:73 := has_scalar.smul

class module (α : inout Type u) (β : Type v) [ring α] extends has_scalar α β, add_comm_group β :=
(smul_left_distrib  : ∀r (x y : β), r • (x + y) = r • x + r • y)
(smul_right_distrib : ∀r s (x : β), (r + s) • x = r • x + s • x)
(mul_smul           : ∀r s (x : β), (r * s) • x = r • (s • x))
(one_smul           : ∀x : β, (1 : α) • x = x)

section module
variables {α : Type u} {β : Type v} [ring α] [module α β]
variables {a b c : α} {u v w : β}

theorem smul_left_distrib : a • (u + v) = a • u + a • v := module.smul_left_distrib a u v
theorem smul_right_distrib : (a + b) • u = a • u + b • u := module.smul_right_distrib a b u
theorem mul_smul : (a * b) • u = a • (b • u) :=  module.mul_smul a b u
@[simp] theorem one_smul : (1 : α) • u = u := module.one_smul _ u

@[simp] theorem zero_smul : (0 : α) • u = 0 :=
have (0 : α) • u + 0 • u = 0 • u + 0, by rewrite [←smul_right_distrib]; simp,
add_left_cancel this

@[simp] theorem smul_zero : a • (0 : β) = 0 :=
have a • (0:β) + a • 0 = a • 0 + 0, by rewrite [←smul_left_distrib]; simp,
add_left_cancel this

@[simp] theorem neg_smul : (-a) • u = - (a • u) :=
eq_neg_of_add_eq_zero (by rewrite [←smul_right_distrib, add_left_neg, zero_smul])

@[simp] theorem smul_neg : a • (-u) = -(a • u) :=
calc a • (-u) = a • (-(1 • u)) : by simp
  ... = (a * -1) • u : by rw [←neg_smul, mul_smul]; simp
  ... = -(a • u) : by rw [mul_neg_eq_neg_mul_symm]; simp

theorem smul_sub_left_distrib (a : α) (u v : β) : a • (u - v) = a • u - a • v :=
by simp [smul_left_distrib]

theorem sub_smul_right_distrib (a b : α) (v : β) : (a - b) • v = a • v - b • v :=
by simp [smul_right_distrib]

lemma smul_smul : a • (b • u) = (a * b) • u := mul_smul.symm

end module

instance ring.to_module {α : Type u} [r : ring α] : module α α :=
{ r with
  smul := λa b, a * b,
  smul_left_distrib := assume a b c, mul_add _ _ _,
  smul_right_distrib := assume a b c, add_mul _ _ _,
  mul_smul := assume a b c, mul_assoc _ _ _,
  one_smul := assume a, one_mul _ }

lemma eq_zero_of_add_self_eq {α : Type} [add_comm_group α]
{a : α} (H : a + a = a) : a = 0 :=
add_left_cancel (by {rw add_zero, exact H})


class submodule (R : Type) (M : Type) [ring R] [module R M] (p : set M) :=
(add : ∀ {u v}, u ∈ p → v ∈ p → u + v ∈ p)
(zero : (0:M) ∈ p)
(neg : ∀ {v}, v ∈ p → -v ∈ p)
(smul : ∀ c {v}, v ∈ p → c • v ∈ p)

namespace submodule

variables (R : Type) {M : Type} [ring R] [module R M]
variables {p : set M} [submodule R M p]
variables {c d : R} (u v w : {x : M // x ∈ p})

include R

protected def add' : {x : M // x ∈ p} → {x : M // x ∈ p} → {x : M // x ∈ p}
| ⟨v₁, p₁⟩ ⟨v₂, p₂⟩ := ⟨v₁ + v₂, add R p₁ p₂⟩

protected def neg' : {x : M // x ∈ p} → {x : M // x ∈ p}
| ⟨v, p⟩ := ⟨-v, neg R p⟩

protected def smul' : R → {x : M // x ∈ p} → {x : M // x ∈ p}
| c ⟨v, p⟩ := ⟨c • v, smul c p⟩

instance : has_add {x : M // x ∈ p} := ⟨submodule.add' R⟩
instance : has_zero {x : M // x ∈ p} := ⟨⟨0, zero R p⟩⟩
instance : has_neg {x : M // x ∈ p} := ⟨submodule.neg' R⟩
instance : has_scalar R {x : M // x ∈ p} := ⟨submodule.smul' R⟩

@[simp] lemma add_val : (u + v).val = u.val + v.val := by cases u; cases v; refl
@[simp] lemma zero_val : (0 : {x : M // x ∈ p}).val = 0 := rfl
@[simp] lemma neg_val : (-v).val = -v.val := by cases v; refl
@[simp] lemma smul_val : (c • v).val = c • v.val := by cases v; refl

lemma sub {u v : M} (HU : u ∈ p) (HV : v ∈ p) : u - v ∈ p := add R HU (neg R HV)

variables (R M p)

instance : module R {x : M // x ∈ p} :=
{ add                := (+),
  add_assoc          := λ u v w, subtype.eq (by simp [add_assoc]),
  zero               := 0,
  zero_add           := λ v, subtype.eq (by simp [zero_add]),
  add_zero           := λ v, subtype.eq (by simp [add_zero]),
  neg                := has_neg.neg,
  add_left_neg       := λ v, subtype.eq (by simp [add_left_neg]),
  add_comm           := λ u v, subtype.eq (by simp [add_comm]),
  smul               := (•),
  smul_left_distrib  := λ c u v, subtype.eq (by simp [smul_left_distrib]),
  smul_right_distrib := λ c u v, subtype.eq (by simp [smul_right_distrib]),
  mul_smul           := λ c d v, subtype.eq (by simp [mul_smul]),
  one_smul           := λ v, subtype.eq (by simp [one_smul]) }

instance : has_coe (submodule R M p) (module R {x : M // x ∈ p}) := ⟨λ s, submodule.module R M p⟩

end submodule


structure linear_map (R M N : Type) [ring R] [module R M] [module R N] :=
(T : M → N)
(map_add : ∀ u v, T (u+v) = T u + T v)
(map_smul : ∀ (c:R) v, T (c • v) = c • (T v))

namespace linear_map

variables {R M N : Type}

section basic

variables [ring R] [module R M] [module R N]
variables {c d : R} {A B C : linear_map R M N} {u v : M}

instance : has_coe_to_fun (linear_map R M N) := ⟨_, T⟩

@[simp] lemma map_add_app : A (u+v) = A u + A v := A.map_add u v
@[simp] lemma map_smul_app : A (c•v) = c • (A v) := A.map_smul c v

theorem ext (HAB : ∀ v, A v = B v) : A = B :=
by {cases A, cases B, congr, exact funext HAB}

@[simp] lemma map_zero : A 0 = 0 :=
begin
  have := eq.symm (map_add A 0 0),
  rw [add_zero] at this,
  exact eq_zero_of_add_self_eq this
end

@[simp] lemma map_neg : A (-v) = -(A v) :=
eq_neg_of_add_eq_zero (by {rw [←map_add_app], simp})

@[simp] lemma map_sub : A (u-v) = A u - A v := by simp

end basic


@[simp] def ker [ring R] [module R M] [module R N]
  (A : linear_map R M N) : set M := {v | A v = 0}

namespace ker

variables [ring R] [module R M] [module R N]
variables {c d : R} {A : linear_map R M N} {u v : M}

@[simp] lemma mem_ker : v ∈ A.ker ↔ A v = 0 := iff.rfl

theorem ker_of_map_eq_map (Huv : A u = A v) : u-v ∈ A.ker :=
by {rw [mem_ker,map_sub], exact sub_eq_zero_of_eq Huv}

theorem inj_of_trivial_ker (H: ∀ v, A.ker v → v = 0) (Huv: A u = A v) : u = v :=
eq_of_sub_eq_zero (H _ (ker_of_map_eq_map Huv))

variables (R A)

instance : submodule R M A.ker :=
{ add  := λ u v HU HV, by {rw [mem_ker] at *, simp [HU,HV]},
  zero := map_zero,
  neg  := λ v HV, by {rw [mem_ker] at *, simp [HV]},
  smul := λ c v HV, by {rw [mem_ker] at *, simp [HV]} }

theorem sub_ker (HU : u ∈ A.ker) (HV : v ∈ A.ker) : u - v ∈ A.ker :=
submodule.sub R HU HV

end ker


@[simp] def im [ring R] [module R M] [module R N]
  (A : linear_map R M N) : set N := {w | ∃ v, A v = w}

namespace im

variables [ring R] [module R M] [module R N]
variables {c d : R} {A : linear_map R M N} (u v w : N)

@[simp] lemma mem_im : w ∈ A.im ↔ ∃ v, A v = w := ⟨id, id⟩

theorem add_im (HU : u ∈ A.im) (HV : v ∈ A.im) : u + v ∈ A.im :=
begin
  unfold im at *,
  cases HU with x hx,
  cases HV with y hy,
  existsi (x + y),
  simp [hx, hy]
end

theorem zero_im : (0:N) ∈ A.im := ⟨0, map_zero⟩

theorem neg_im (HV : v ∈ A.im) : -v ∈ A.im :=
begin
  unfold im at *,
  cases HV with y hy,
  existsi (-y),
  simp [hy]
end

theorem smul_im (c : R) (v : N) (HV : v ∈ A.im) : c • v ∈ A.im :=
begin
  unfold im at *,
  cases HV with y hy,
  existsi (c • y),
  simp [hy]
end

variables (R A)

instance : submodule R N A.im :=
{ add  := add_im,
  zero := zero_im,
  neg  := neg_im,
  smul := smul_im }

end im


section add_comm_group

variables [ring R] [module R M] [module R N]
variables {c d : R} {A B C : linear_map R M N} {u v : M}

protected def add : linear_map R M N → linear_map R M N → linear_map R M N
| ⟨T₁, a₁, s₁⟩ ⟨T₂, a₂, s₂⟩ :=
{ T        := λ v, T₁ v + T₂ v,
  map_add  := λ u v, by simp [a₁, a₂],
  map_smul := λ c v, by simp [smul_left_distrib, s₁, s₂] }

protected def neg : linear_map R M N → linear_map R M N
| ⟨T, a, s⟩ :=
{ T        := (λ v, -(T v)),
  map_add  := λ u v, by simp [a],
  map_smul := λ c v, by simp [s] }

instance : has_add (linear_map R M N) := ⟨linear_map.add⟩

instance : has_zero (linear_map R M N) := ⟨
{ T        := λ v, 0,
  map_add  := λ u v, by simp,
  map_smul := λ c v, by simp }⟩

instance : has_neg (linear_map R M N) := ⟨linear_map.neg⟩

@[simp] lemma add_app : (A + B) v = A v + B v := by cases A; cases B; refl
@[simp] lemma zero_app : (0:linear_map R M N) v = 0 := rfl
@[simp] lemma neg_app : (-A) v = -(A v) := by cases A; refl

instance : add_comm_group (linear_map R M N) :=
{ add                 := (+),
  add_assoc           := λ A B C, ext (λ v, by simp [add_assoc]),
  zero                := 0,
  zero_add            := λ A, ext (λ v, by simp [zero_add]),
  add_zero            := λ A, ext (λ v, by simp [add_zero]),
  neg                 := has_neg.neg,
  add_left_neg        := λ A, ext (λ v, by simp [add_left_neg]),
  add_comm            := λ A B, ext (λ v, by simp [add_comm]) }

end add_comm_group


section Hom

variables [comm_ring R] [module R M] [module R N]
variables {c d : R} {A B C : linear_map R M N} {u v : M}

protected def smul : R → linear_map R M N → linear_map R M N
| c ⟨T, a, s⟩ :=
{ T        := λ v, c • T v,
  map_add  := λ u v, by simp [smul_left_distrib,a],
  map_smul := λ k v, by simp [smul_smul,s] }

instance : has_scalar R (linear_map R M N) := ⟨linear_map.smul⟩

@[simp] lemma smul_app : (c • A) v = c • (A v) := by cases A; refl

variables (R M N)

instance : module R (linear_map R M N) :=
{ linear_map.add_comm_group with
  smul               := (•),
  smul_left_distrib  := λ c A B, ext (λ v, by simp [module.smul_left_distrib]),
  smul_right_distrib := λ c d A, ext (λ v, by simp [module.smul_right_distrib]),
  mul_smul           := λ c d A, ext (λ v, by simp [module.mul_smul]),
  one_smul           := λ A, ext (λ v, by simp [module.one_smul]) }

end Hom

end linear_map


namespace module

variables (R M : Type)

def dual [comm_ring R] [module R M] := module R (linear_map R M R)

variables {R M}
variables [ring R] [module R M]
variables {A B C : linear_map R M M} {v : M}

protected def mul : linear_map R M M → linear_map R M M → linear_map R M M
| ⟨T₁, a₁, s₁⟩ ⟨T₂, a₂, s₂⟩ :=
{ T        := T₁ ∘ T₂,
  map_add  := λ u v, by simp [function.comp, a₂, a₁],
  map_smul := λ c v, by simp [function.comp, s₂, s₁] }

def id : linear_map R M M := ⟨id, λ u v, rfl, λ u v, rfl⟩

instance : has_mul (linear_map R M M) := ⟨module.mul⟩

@[simp] lemma id_app : (id : linear_map R M M) v = v := rfl
@[simp] lemma comp_app : (A * B) v = A (B v) := by cases A; cases B; refl

variables (A B C)

@[simp] lemma comp_id : A * id = A := linear_map.ext (λ v, by simp)
@[simp] lemma id_comp : id * A = A := linear_map.ext (λ v, by simp)
theorem comp_assoc : (A * B) * C = A * (B * C) := linear_map.ext (λ v, by simp)
theorem comp_add : A * (B + C) = A * B + A * C := linear_map.ext (λ v, by simp)
theorem add_comp : (A + B) * C = A * C + B * C := linear_map.ext (λ v, by simp)

variables (R M)

def endomorphism_ring : ring (linear_map R M M) :=
{ linear_map.add_comm_group with
  mul             := (*),
  mul_assoc       := comp_assoc,
  one             := id,
  one_mul         := id_comp,
  mul_one         := comp_id,
  left_distrib    := comp_add,
  right_distrib   := add_comp }

def general_linear_group [ring R] [module R M] :=
by have := endomorphism_ring R M; exact units (linear_map R M M)

end module
