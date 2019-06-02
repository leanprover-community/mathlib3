/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Theory of topological rings with uniform structure.
-/

import topology.algebra.group_completion topology.algebra.ring

open classical set lattice filter topological_space add_comm_group
local attribute [instance] classical.prop_decidable
noncomputable theory

namespace uniform_space.completion
open dense_embedding uniform_space
variables (α : Type*) [ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] [separated α]

instance is_Z_bilin_mul : is_Z_bilin (λp:α×α, p.1 * p.2) :=
⟨assume a a' b, add_mul a a' b, assume a b b', mul_add a b b'⟩

instance : has_one (completion α) := ⟨(1:α)⟩

instance : has_mul (completion α) :=
⟨λa b, extend (dense_embedding_coe.prod dense_embedding_coe)
  ((coe : α → completion α) ∘ (λp:α×α, p.1 * p.2)) (a, b)⟩

lemma coe_one : ((1 : α) : completion α) = 1 := rfl

lemma continuous_mul' : continuous (λp:completion α×completion α, p.1 * p.2) :=
suffices continuous $ extend (dense_embedding_coe.prod dense_embedding_coe) $
  ((coe : α → completion α) ∘ (λp:α×α, p.1 * p.2)),
{ convert this, ext ⟨a, b⟩, refl },
extend_Z_bilin dense_embedding_coe dense_embedding_coe ((continuous_coe α).comp continuous_mul')

section rules
variables {α}
lemma coe_mul (a b : α) : ((a * b : α) : completion α) = a * b :=
eq.symm (extend_e_eq (dense_embedding_coe.prod dense_embedding_coe) (a, b))

lemma continuous_mul {β : Type*} [topological_space β] {f g : β → completion α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, f b * g b) :=
(continuous_mul' α).comp (continuous.prod_mk hf hg)
end rules

instance : ring (completion α) :=
{ one_mul       := assume a, completion.induction_on a
    (is_closed_eq (continuous_mul continuous_const continuous_id) continuous_id)
    (assume a, by rw [← coe_one, ← coe_mul, one_mul]),
  mul_one       := assume a, completion.induction_on a
    (is_closed_eq (continuous_mul continuous_id continuous_const) continuous_id)
    (assume a, by rw [← coe_one, ← coe_mul, mul_one]),
  mul_assoc     := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_mul (continuous_mul continuous_fst (continuous_fst.comp continuous_snd))
        (continuous_snd.comp continuous_snd))
      (continuous_mul continuous_fst
        (continuous_mul (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul, mul_assoc]),
  left_distrib  := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_mul continuous_fst (continuous_add
        (continuous_fst.comp continuous_snd)
        (continuous_snd.comp continuous_snd)))
      (continuous_add
        (continuous_mul continuous_fst (continuous_fst.comp continuous_snd))
        (continuous_mul continuous_fst (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ←coe_add, mul_add]),
  right_distrib := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_mul (continuous_add continuous_fst
        (continuous_fst.comp continuous_snd)) (continuous_snd.comp continuous_snd))
      (continuous_add
        (continuous_mul continuous_fst (continuous_snd.comp continuous_snd))
        (continuous_mul (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ←coe_add, add_mul]),
  ..completion.add_comm_group, ..completion.has_mul α, ..completion.has_one α }

instance is_ring_hom_coe : is_ring_hom (coe : α → completion α) :=
⟨coe_one α, assume a b, coe_mul a b, assume a b, coe_add a b⟩
universe u
instance is_ring_hom_extension
  {β : Type u} [uniform_space β] [ring β] [uniform_add_group β] [topological_ring β]
    [complete_space β] [separated β]
  {f : α → β} [is_ring_hom f] (hf : continuous f) :
  is_ring_hom (completion.extension f) :=
have hf : uniform_continuous f, from uniform_continuous_of_continuous hf,
{ map_one := by rw [← coe_one, extension_coe hf, is_ring_hom.map_one f],
  map_add := assume a b, completion.induction_on₂ a b
    (is_closed_eq
      (continuous_extension.comp continuous_add')
      (continuous_add (continuous_extension.comp continuous_fst) (continuous_extension.comp continuous_snd)))
    (assume a b,
      by rw [← coe_add, extension_coe hf, extension_coe hf, extension_coe hf, is_add_group_hom.map_add f]),
  map_mul := assume a b, completion.induction_on₂ a b
    (is_closed_eq
      (continuous_extension.comp (continuous_mul' α))
      (_root_.continuous_mul (continuous_extension.comp continuous_fst) (continuous_extension.comp continuous_snd)))
    (assume a b,
      by rw [← coe_mul, extension_coe hf, extension_coe hf, extension_coe hf, is_ring_hom.map_mul f]) }

end uniform_space.completion


namespace uniform_space
variables {α : Type*}
lemma ring_sep_rel (α) [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  separation_setoid α = submodule.quotient_rel (ideal.closure ⊥) :=
setoid.ext $ assume x y, group_separation_rel x y

lemma ring_sep_quot (α) [r : comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  quotient (separation_setoid α) = (⊥ : ideal α).closure.quotient :=
by rw [@ring_sep_rel α r]; refl

def sep_quot_equiv_ring_quot (α)
  [r : comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  quotient (separation_setoid α) ≃ (⊥ : ideal α).closure.quotient :=
quotient.congr (equiv.refl α) $ assume x y, group_separation_rel x y

/- TODO: use a form of transport a.k.a. lift definition a.k.a. transfer -/
instance [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  comm_ring (quotient (separation_setoid α)) :=
by rw ring_sep_quot α; apply_instance

instance [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  topological_ring (quotient (separation_setoid α)) :=
begin
  convert topological_ring_quotient (⊥ : ideal α).closure,
  { apply ring_sep_rel },
  { dsimp [topological_ring_quotient_topology, quotient.topological_space, to_topological_space],
    congr,
    apply ring_sep_rel,
    apply ring_sep_rel },
  { apply ring_sep_rel },
  { simp [uniform_space.comm_ring] },
end

end uniform_space
