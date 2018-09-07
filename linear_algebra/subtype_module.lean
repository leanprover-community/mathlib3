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
variables {r : α} {x y : p}

open set

namespace is_submodule
include α

instance : has_add p := ⟨λx y, ⟨x.1 + y.1, add x.2 y.2⟩⟩
instance : has_zero p := ⟨⟨0, zero⟩⟩
instance : has_neg p := ⟨λx, ⟨-x.1, neg x.2⟩⟩
instance : has_scalar α p := ⟨λ c x, ⟨c • x.1, smul c x.2⟩⟩

@[simp] lemma coe_add : (↑(x + y) : β) = ↑x + ↑y := rfl
@[simp] lemma coe_zero : ((0 : p) : β) = 0 := rfl
@[simp] lemma coe_neg : ((-x : p) : β) = -x := rfl
@[simp] lemma coe_smul : ((r • x : p) : β) = r • ↑x := rfl

instance : add_comm_group p :=
by refine {add := (+), zero := 0, neg := has_neg.neg, ..};
  { intros, apply set_coe.ext, simp }

instance {α β} {r : ring α} [m : module α β] {p : set β} [h : is_submodule p] : module α p :=
begin
  refine {smul := (•), ..@is_submodule.add_comm_group α β r m p h, ..};
  { intros, apply set_coe.ext,
    simp [smul_add, add_smul, mul_smul],
    try { exact smul_add <|> exact add_smul <|> exact mul_smul <|> exact one_smul } }
end

instance {α β} {f : field α} [vector_space α β] {p : set β} [is_submodule p] :
  vector_space α {x : β // x ∈ p} :=
{ .. @is_submodule.module α β (@comm_ring.to_ring α (@field.to_comm_ring α f)) _ p _ }

@[simp] lemma sub_val : (↑(x - y) : β) = ↑x - ↑y := by simp

lemma is_linear_map_coe (s : set β) [is_submodule s] : is_linear_map (coe : s → β) :=
by refine {..}; simp [coe_smul]

-- should this be in the root namespace?
lemma is_linear_map_subtype_val {f : γ → p} (hf : is_linear_map f) : is_linear_map (λb, (f b).val) :=
(is_linear_map_coe p).comp hf

-- should this be in the root namespace?
lemma is_linear_map_subtype_mk (f : γ → β) (hf : is_linear_map f) (h : ∀c, f c ∈ p) :
  is_linear_map (λc, ⟨f c, h c⟩ : γ → {x : β // x ∈ p}) :=
by refine {..}; intros; apply set_coe.ext; simp [hf.add, hf.smul]

instance {s t : set β} [is_submodule s] [is_submodule t] : is_submodule (coe ⁻¹' t) :=
is_submodule.preimage (is_linear_map_coe s)

end is_submodule

