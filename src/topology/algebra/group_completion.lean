/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Completion of topological groups:
-/
import topology.uniform_space.completion topology.algebra.uniform_group
noncomputable theory

section group
open uniform_space Cauchy filter set
variables {α : Type*} [uniform_space α]

instance [has_zero α] : has_zero (completion α) := ⟨(0 : α)⟩
instance [has_neg α] : has_neg (completion α) := ⟨completion.map (λa, -a : α → α)⟩
instance [has_add α] : has_add (completion α) := ⟨completion.map₂ (+)⟩

lemma coe_zero [has_zero α] : ((0 : α) : completion α) = 0 := rfl
end group

namespace uniform_space.completion
section uniform_add_group
open uniform_space uniform_space.completion
variables {α : Type*} [uniform_space α] [add_group α] [uniform_add_group α]

lemma coe_neg (a : α) : ((- a : α) : completion α) = - a :=
(map_coe uniform_continuous_neg' a).symm

lemma coe_add (a b : α) : ((a + b : α) : completion α) = a + b :=
(map₂_coe_coe a b (+) uniform_continuous_add').symm

instance : add_group (completion α) :=
{ zero_add     := assume a, completion.induction_on a
   (is_closed_eq (continuous_map₂ continuous_const continuous_id) continuous_id)
    (assume a, show 0 + (a : completion α) = a, by rw [← coe_zero, ← coe_add, zero_add]),
  add_zero     := assume a, completion.induction_on a
    (is_closed_eq (continuous_map₂ continuous_id continuous_const) continuous_id)
    (assume a, show (a : completion α) + 0 = a, by rw [← coe_zero, ← coe_add, add_zero]),
  add_left_neg := assume a, completion.induction_on a
    (is_closed_eq (continuous_map₂ completion.continuous_map continuous_id) continuous_const)
    (assume a, show - (a : completion α) + a = 0, by rw [← coe_neg, ← coe_add, add_left_neg, coe_zero]),
  add_assoc    := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_map₂
        (continuous_map₂ continuous_fst (continuous_snd.comp continuous_fst)) (continuous_snd.comp continuous_snd))
      (continuous_map₂ continuous_fst
        (continuous_map₂ (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd))))
    (assume a b c, show (a : completion α) + b + c = a + (b + c),
      by repeat { rw [← coe_add] }; rw [add_assoc]),
  .. completion.has_zero, .. completion.has_neg, ..completion.has_add }

instance : uniform_add_group (completion α) :=
⟨ (uniform_continuous.prod_mk uniform_continuous_fst
  (uniform_continuous_snd.comp uniform_continuous_map)).comp (uniform_continuous_map₂' (+))  ⟩

instance is_add_group_hom_coe : is_add_group_hom (coe : α → completion α) :=
⟨ coe_add ⟩

variables {β : Type*} [uniform_space β] [add_group β] [uniform_add_group β]

lemma is_add_group_hom_extension  [complete_space β] [separated β]
  {f : α → β} [is_add_group_hom f] (hf : continuous f) : is_add_group_hom (completion.extension f) :=
have hf : uniform_continuous f, from uniform_continuous_of_continuous hf,
⟨assume a b, completion.induction_on₂ a b
  (is_closed_eq
    (continuous_add'.comp continuous_extension)
    (continuous_add (continuous_fst.comp continuous_extension) (continuous_snd.comp continuous_extension)))
  (assume a b, by rw [← coe_add, extension_coe hf, extension_coe hf, extension_coe hf, is_add_group_hom.map_add f])⟩

lemma is_add_group_hom_map [add_group β] [uniform_add_group β]
  {f : α → β} [is_add_group_hom f] (hf : continuous f) : is_add_group_hom (completion.map f) :=
is_add_group_hom_extension (hf.comp (continuous_coe _))

section instance_max_depth
-- TODO: continuous_add requires some long proofs through
-- uniform_add_group / topological_add_group w.r.t prod / completion etc
set_option class.instance_max_depth 52

lemma is_add_group_hom_prod [add_group β] [uniform_add_group β] :
  is_add_group_hom (@completion.prod α β _ _) :=
⟨assume ⟨a₁, a₂⟩ ⟨b₁, b₂⟩,
  begin
    refine completion.induction_on₄ a₁ a₂ b₁ b₂ (is_closed_eq _ _) _,
    { refine continuous.comp _ uniform_continuous_prod.continuous,
      refine continuous_add _ _,
      exact continuous.prod_mk (continuous_fst.comp continuous_fst) (continuous_fst.comp continuous_snd),
      exact continuous.prod_mk (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd) },
    { refine continuous_add _ _,
      refine continuous.comp _ uniform_continuous_prod.continuous,
      exact continuous.prod_mk (continuous_fst.comp continuous_fst) (continuous_fst.comp continuous_snd),
      refine continuous.comp _ uniform_continuous_prod.continuous,
      exact continuous.prod_mk (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd) },
    { assume a b c d,
      show completion.prod (↑a + ↑c, ↑b + ↑d) = completion.prod (↑a, ↑b) + completion.prod (↑c, ↑d),
      rw [← coe_add, ← coe_add, prod_coe_coe, prod_coe_coe, prod_coe_coe, ← coe_add],
      refl }
  end⟩

end instance_max_depth

instance {α : Type*} [uniform_space α] [add_comm_group α] [uniform_add_group α] : add_comm_group (completion α) :=
{ add_comm  := assume a b, completion.induction_on₂ a b
    (is_closed_eq (continuous_map₂ continuous_fst continuous_snd) (continuous_map₂ continuous_snd continuous_fst))
    (assume x y, by { change ↑x + ↑y = ↑y + ↑x, rw [← coe_add, ← coe_add, add_comm]}),
  .. completion.add_group }
end uniform_add_group


end uniform_space.completion
