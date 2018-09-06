/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau

Subtype construction of sub modules.
-/
import linear_algebra.basic

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
variables [ring α] [module α β] [module α γ] {p : set β} [is_submodule p]
variables {r : α} {x y : {x : β // x ∈ p}}

open is_submodule

section
include α

instance : has_add {x : β // x ∈ p} := ⟨λx y, ⟨x.1 + y.1, add x.2 y.2⟩⟩
instance : has_zero {x : β // x ∈ p} := ⟨⟨0, zero⟩⟩
instance : has_neg {x : β // x ∈ p} := ⟨λx, ⟨-x.1, neg x.2⟩⟩
instance : has_scalar α {x : β // x ∈ p} := ⟨λ c x, ⟨c • x.1, smul c x.2⟩⟩

@[simp] lemma add_val : (x + y).val = x.val + y.val := rfl
@[simp] lemma zero_val : (0 : {x : β // x ∈ p}).val = 0 := rfl
@[simp] lemma neg_val : (-x).val = -x.val := rfl
@[simp] lemma smul_val : (r • x).val = r • x.val := rfl

instance : add_comm_group {x : β // x ∈ p} :=
by refine {add := (+), zero := 0, neg := has_neg.neg, ..};
  { intros, apply subtype.eq, simp }

instance {α β} {r : ring α} [module α β] {p : set β} [is_submodule p] : module α {x : β // x ∈ p} :=
by refine {add := (+), smul := (•), ..@subtype.add_comm_group α β _ _ _ _, ..};
  { intros, apply subtype.eq,
    simp [smul_add, add_smul, mul_smul],
    try { exact smul_add <|> exact add_smul <|> exact mul_smul <|> exact one_smul } }

instance {α β} {f : field α} [vector_space α β] {p : set β} [is_submodule p] :
  vector_space α {x : β // x ∈ p} :=
{ .. @subtype.module α β (@comm_ring.to_ring α (@field.to_comm_ring α f)) _ p _ }

@[simp] lemma sub_val : (x - y).val = x.val - y.val := by simp

lemma is_linear_map_subtype_val {f : γ → {x : β // x ∈ p}} (hf : is_linear_map f) :
  is_linear_map (λb, (f b).val) :=
by refine {..}; simp [hf.add, hf.smul]

lemma is_linear_map_subtype_mk (f : γ → β) (hf : is_linear_map f) (h : ∀c, f c ∈ p) :
  is_linear_map (λc, ⟨f c, h c⟩ : γ → {x : β // x ∈ p}) :=
by refine {..}; intros; apply subtype.eq; simp [hf.add, hf.smul]

instance {s t : set β} [is_submodule s] [is_submodule t] :
  is_submodule (@subtype.val β (λx, x ∈ s) ⁻¹' t) :=
is_submodule.preimage (is_linear_map_subtype_val is_linear_map.id)

end