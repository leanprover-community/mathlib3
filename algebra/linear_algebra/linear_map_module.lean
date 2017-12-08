/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau

Type of linear functions
-/
import algebra.linear_algebra.basic

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}


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

-- declaring this an instance breaks `real.lean` with reaching max. instance resolution depth
def endomorphism_ring : ring (linear_map β β) :=
by refine {mul := (*), one := 1, ..linear_map.add_comm_group, ..};
  { intros, apply linear_map.ext, simp }

def general_linear_group :=
@units (linear_map β β) (@ring.to_semiring _ (endomorphism_ring α β))

end module
