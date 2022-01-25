/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import algebra.group.hom_instances
import topology.uniform_space.completion
import topology.algebra.uniform_group

/-!
# Completion of topological groups:

This files endows the completion of a topological abelian group with a group structure.
More precisely the instance `uniform_space.completion.add_group` builds an abelian group structure
on the completion of an abelian group endowed with a compatible uniform structure.
Then the instance `uniform_space.completion.uniform_add_group` proves this group structure is
compatible with the completed uniform structure. The compatibility condition is `uniform_add_group`.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous group morphisms.

* `add_monoid_hom.extension`: extends a continuous group morphism from `G`
  to a complete separated group `H` to `completion G`.
* `add_monoid_hom.completion`: promotes a continuous group morphism
  from `G` to `H` into a continuous group morphism
  from `completion G` to `completion H`.
-/

noncomputable theory

universes u v

section group
open uniform_space Cauchy filter set
variables {α : Type u} [uniform_space α]

instance [has_zero α] : has_zero (completion α) := ⟨(0 : α)⟩
instance [has_neg α] : has_neg (completion α) := ⟨completion.map (λa, -a : α → α)⟩
instance [has_add α] : has_add (completion α) := ⟨completion.map₂ (+)⟩
instance [has_sub α] : has_sub (completion α) := ⟨completion.map₂ has_sub.sub⟩

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
lemma coe_sub (a b : α) : ((a - b : α) : completion α) = a - b :=
(map₂_coe_coe a b has_sub.sub uniform_continuous_sub).symm

@[norm_cast]
lemma coe_add (a b : α) : ((a + b : α) : completion α) = a + b :=
(map₂_coe_coe a b (+) uniform_continuous_add).symm

instance : add_monoid (completion α) :=
{ zero_add     := assume a, completion.induction_on a
   (is_closed_eq (continuous_map₂ continuous_const continuous_id) continuous_id)
    (assume a, show 0 + (a : completion α) = a, by rw_mod_cast zero_add),
  add_zero     := assume a, completion.induction_on a
    (is_closed_eq (continuous_map₂ continuous_id continuous_const) continuous_id)
    (assume a, show (a : completion α) + 0 = a, by rw_mod_cast add_zero),
  add_assoc    := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_map₂
        (continuous_map₂ continuous_fst (continuous_fst.comp continuous_snd))
        (continuous_snd.comp continuous_snd))
      (continuous_map₂ continuous_fst
        (continuous_map₂
          (continuous_fst.comp continuous_snd)
          (continuous_snd.comp continuous_snd))))
    (assume a b c, show (a : completion α) + b + c = a + (b + c),
      by repeat { rw_mod_cast add_assoc }),
  .. completion.has_zero, .. completion.has_neg, ..completion.has_add, .. completion.has_sub }

instance : sub_neg_monoid (completion α) :=
{ sub_eq_add_neg := λ a b, completion.induction_on₂ a b
    (is_closed_eq (continuous_map₂ continuous_fst continuous_snd)
      (continuous_map₂ continuous_fst (continuous_map.comp continuous_snd)))
   (λ a b, by exact_mod_cast congr_arg coe (sub_eq_add_neg a b)),
  .. completion.add_monoid, .. completion.has_neg, .. completion.has_sub }

instance : add_group (completion α) :=
{ add_left_neg := assume a, completion.induction_on a
    (is_closed_eq (continuous_map₂ completion.continuous_map continuous_id) continuous_const)
    (assume a, show - (a : completion α) + a = 0, by { rw_mod_cast add_left_neg, refl }),
  .. completion.sub_neg_monoid }

instance : uniform_add_group (completion α) :=
⟨uniform_continuous_map₂ has_sub.sub⟩

/-- The map from a group to its completion as a group hom. -/
@[simps] def to_compl : α →+ completion α :=
{ to_fun := coe,
  map_add' := coe_add,
  map_zero' := coe_zero }

lemma continuous_to_compl : continuous (to_compl : α → completion α) :=
continuous_coe α

variables {β : Type v} [uniform_space β] [add_group β] [uniform_add_group β]

instance {α : Type u} [uniform_space α] [add_comm_group α] [uniform_add_group α] :
  add_comm_group (completion α) :=
{ add_comm  := assume a b, completion.induction_on₂ a b
    (is_closed_eq (continuous_map₂ continuous_fst continuous_snd)
      (continuous_map₂ continuous_snd continuous_fst))
    (assume x y, by { change ↑x + ↑y = ↑y + ↑x, rw [← coe_add, ← coe_add, add_comm]}),
  .. completion.add_group }

end uniform_add_group

end uniform_space.completion

section add_monoid_hom
variables {α β : Type*} [uniform_space α] [add_group α] [uniform_add_group α]
                        [uniform_space β] [add_group β] [uniform_add_group β]

open uniform_space uniform_space.completion

/-- Extension to the completion of a continuous group hom. -/
def add_monoid_hom.extension [complete_space β] [separated_space β] (f : α →+ β)
  (hf : continuous f) : completion α →+ β :=
have hf : uniform_continuous f, from uniform_continuous_of_continuous hf,
{ to_fun := completion.extension f,
  map_zero' := by rw [← coe_zero, extension_coe hf, f.map_zero],
  map_add' := assume a b, completion.induction_on₂ a b
  (is_closed_eq
    (continuous_extension.comp continuous_add)
    ((continuous_extension.comp continuous_fst).add (continuous_extension.comp continuous_snd)))
  (λ a b, by rw_mod_cast [extension_coe hf, extension_coe hf, extension_coe hf,
    f.map_add]) }

lemma add_monoid_hom.extension_coe [complete_space β] [separated_space β] (f : α →+ β)
  (hf : continuous f) (a : α) : f.extension hf a = f a :=
extension_coe (uniform_continuous_of_continuous hf) a

@[continuity]
lemma add_monoid_hom.continuous_extension [complete_space β] [separated_space β] (f : α →+ β)
  (hf : continuous f) : continuous (f.extension hf) :=
continuous_extension

/-- Completion of a continuous group hom, as a group hom. -/
def add_monoid_hom.completion (f : α →+ β) (hf : continuous f) : completion α →+ completion β :=
(to_compl.comp f).extension (continuous_to_compl.comp hf)

@[continuity]
lemma add_monoid_hom.continuous_completion (f : α →+ β)
  (hf : continuous f) : continuous (f.completion hf : completion α → completion β) :=
continuous_map

lemma add_monoid_hom.completion_coe (f : α →+ β)
  (hf : continuous f) (a : α) : f.completion hf a = f a :=
map_coe (uniform_continuous_of_continuous hf) a

lemma add_monoid_hom.completion_zero : (0 : α →+ β).completion continuous_const = 0 :=
begin
  ext x,
  apply completion.induction_on x,
  { apply is_closed_eq ((0 : α →+ β).continuous_completion continuous_const),
    simp [continuous_const] },
  { intro a,
    simp [(0 : α →+ β).completion_coe continuous_const, coe_zero] }
end

lemma add_monoid_hom.completion_add {γ : Type*} [add_comm_group γ] [uniform_space γ]
  [uniform_add_group γ] (f g : α →+ γ) (hf : continuous f) (hg : continuous g) :
  (f + g).completion (hf.add hg) = f.completion hf + g.completion hg :=
begin
  have hfg := hf.add hg,
  ext x,
  apply completion.induction_on x,
  { exact is_closed_eq ((f+g).continuous_completion hfg)
    ((f.continuous_completion hf).add (g.continuous_completion hg)) },
  { intro a,
    simp [(f+g).completion_coe hfg, coe_add, f.completion_coe hf, g.completion_coe hg] }
end

end add_monoid_hom
