/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau

Subtype construction of sub modules.
-/
import algebra.linear_algebra.basic

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
variables [ring α] [module α β] [module α γ] {p : set β} [is_submodule p]
variables {r : α} {x y : {x : β // x ∈ p}}
include α

open is_submodule

instance : has_add {x : β // x ∈ p} := ⟨λ ⟨x, px⟩ ⟨y, py⟩, ⟨x + y, add px py⟩⟩
instance : has_zero {x : β // x ∈ p} := ⟨⟨0, zero⟩⟩
instance : has_neg {x : β // x ∈ p} := ⟨λ ⟨x, hx⟩, ⟨-x, neg hx⟩⟩
instance : has_scalar α {x : β // x ∈ p} := ⟨λ c ⟨x, hx⟩, ⟨c • x, smul c hx⟩⟩

@[simp] lemma add_val : (x + y).val = x.val + y.val := by cases x; cases y; refl
@[simp] lemma zero_val : (0 : {x : β // x ∈ p}).val = 0 := rfl
@[simp] lemma neg_val : (-x).val = -x.val := by cases x; refl
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
