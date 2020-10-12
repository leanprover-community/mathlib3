/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Completion of topological groups:
-/
import topology.uniform_space.completion
import topology.algebra.uniform_group
noncomputable theory

universes u v

section group
open uniform_space Cauchy filter set
variables {α : Type u} [uniform_space α]

instance [has_zero α] : has_zero (completion α) := ⟨(0 : α)⟩
instance [has_neg α] : has_neg (completion α) := ⟨completion.map (λa, -a : α → α)⟩
instance [has_add α] : has_add (completion α) := ⟨completion.map₂ (+)⟩

-- TODO: switch sides once #1103 is fixed
@[norm_cast]
lemma uniform_space.completion.coe_zero [has_zero α] : ((0 : α) : completion α) = 0 := rfl
end group

namespace uniform_space.completion
section uniform_add_group
open uniform_space uniform_space.completion
variables {α : Type*} [uniform_space α] [add_group α] [uniform_add_group α]

@[norm_cast]
lemma coe_neg (a : α) : ((- a : α) : completion α) = - a :=
(map_coe uniform_continuous_neg a).symm

@[norm_cast]
lemma coe_add (a b : α) : ((a + b : α) : completion α) = a + b :=
(map₂_coe_coe a b (+) uniform_continuous_add).symm

instance : add_group (completion α) :=
{ zero_add     := assume a, completion.induction_on a
   (is_closed_eq (continuous_map₂ continuous_const continuous_id) continuous_id)
    (assume a, show 0 + (a : completion α) = a, by rw_mod_cast zero_add),
  add_zero     := assume a, completion.induction_on a
    (is_closed_eq (continuous_map₂ continuous_id continuous_const) continuous_id)
    (assume a, show (a : completion α) + 0 = a, by rw_mod_cast add_zero),
  add_left_neg := assume a, completion.induction_on a
    (is_closed_eq (continuous_map₂ completion.continuous_map continuous_id) continuous_const)
    (assume a, show - (a : completion α) + a = 0, by { rw_mod_cast add_left_neg, refl }),
  add_assoc    := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_map₂
        (continuous_map₂ continuous_fst (continuous_fst.comp continuous_snd)) (continuous_snd.comp continuous_snd))
      (continuous_map₂ continuous_fst
        (continuous_map₂ (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
    (assume a b c, show (a : completion α) + b + c = a + (b + c),
      by repeat { rw_mod_cast add_assoc }),
  .. completion.has_zero, .. completion.has_neg, ..completion.has_add }

instance : uniform_add_group (completion α) :=
⟨(uniform_continuous_map₂ (+)).bicompl uniform_continuous_id uniform_continuous_map⟩

/-- Embedding of a uniform additive group into its completion as an `add_monoid_hom`. -/
def coe_add_hom : α →+ completion α := add_monoid_hom.mk' coe coe_add

@[simp] lemma coe_coe_add_hom : ⇑(coe_add_hom : α →+ completion α) = coe := rfl

instance {α : Type u} [uniform_space α] [add_comm_group α] [uniform_add_group α] :
  add_comm_group (completion α) :=
{ add_comm  := assume a b, completion.induction_on₂ a b
    (is_closed_eq (continuous_map₂ continuous_fst continuous_snd)
      (continuous_map₂ continuous_snd continuous_fst))
    (assume x y, by { change ↑x + ↑y = ↑y + ↑x, rw [← coe_add, ← coe_add, add_comm]}),
  .. completion.add_group }
end uniform_add_group

end uniform_space.completion

open uniform_space uniform_space.completion

variables {G H : Type*} [uniform_space G] [add_group G] [uniform_add_group G]
  [uniform_space H] [add_group H] [uniform_add_group H]

/-- Extend an additive monoid homomorphism with a complete separated codimain to the
completion of the codomain. -/
def add_monoid_hom.uniform_extension [complete_space H] [separated_space H] (f : G →+ H)
  (hf : continuous f) : completion G →+ H :=
add_monoid_hom.mk' (completion.extension f) $
have hf : uniform_continuous f, from f.uniform_continuous_of_continuous hf,
assume a b, completion.induction_on₂ a b
(is_closed_eq
  (continuous_extension.comp continuous_add)
  ((continuous_extension.comp continuous_fst).add (continuous_extension.comp continuous_snd)))
(assume a b, by rw_mod_cast [extension_coe hf, extension_coe hf, extension_coe hf, f.map_add])

@[simp] lemma add_monoid_hom.coe_uniform_extension [complete_space H] [separated_space H]
  (f : G →+ H) (hf : continuous f) :
  ⇑(f.uniform_extension hf) = completion.extension f :=
rfl

/-- A uniform continuous additive monoid homomorphism between uniform additive groups
defined a uniform continuous additive monoid homomorphism between their completions. -/
def add_monoid_hom.map_uniform_extension (f : G →+ H) (hf : continuous f) :
  completion G →+ completion H :=
(coe_add_hom.comp f).uniform_extension $ (continuous_coe _).comp hf
