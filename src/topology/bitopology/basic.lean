/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import topology.separation

/-!
# Bitopological spaces
-/

open filter
open_locale filter topological_space

variables {α β : Type*}

class bitopological_space (α : Type*) :=
(top_fst top_snd : topological_space α)

/-- The first topology of a bitopological space. -/
def top_fst (α : Type*) : Type* := α

/-- The second topology of a bitopological space. -/
def top_snd (α : Type*) : Type* := α

/-- The "identity" equivalence between `α` and `top_fst α`. -/
def to_top_fst : α ≃ top_fst α := equiv.refl _

/-- The "identity" equivalence between 'α' and 'top_scd α'. -/
def to_top_snd : α ≃ top_snd α := equiv.refl _

/-- The "identity" equivalence between `top_fst α` and `α`. -/
def of_top_fst : top_fst α ≃ α := equiv.refl _

/-- The "identity" equivalence between `top_snd α` and `α`. -/
def of_top_snd : top_snd α ≃ α := equiv.refl _

instance [bitopological_space α] : topological_space (top_fst α) :=
@bitopological_space.top_fst α _

instance [bitopological_space α] : topological_space (top_snd α) :=
@bitopological_space.top_snd α _

/-- A function between bitopological spaces is bicontinuous if it is both continuous between the
first topologies and between the second topologies. -/
structure bicontinuous [bitopological_space α] [bitopological_space β] (f : α → β) : Prop :=
(continuous_fst : continuous (to_top_fst ∘ f ∘ of_top_fst))
(continuous_snd : continuous (to_top_snd ∘ f ∘ of_top_snd))

/-- A bitopological space is bi-Hausdorff if for any two distinct points there exist
disjoint open subsets in each topology containing the respective point. -/
class bi_t2_space (α : Type*) [bitopological_space α] : Prop :=
(bi_t2 (x y : α) : x ≠ y → ∃ (u v : set α), is_open (of_top_fst ⁻¹' u) ∧ is_open (of_top_snd ⁻¹' v)
  ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅)

/-- NEEDS WORK A set `s` is bicompact if for every nontrivial filter `f` that contains `s`,
    there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def is_bicompact (s : set α) : Prop := sorry

/-- -/
class bicompact_space (α : Type*) [bitopological_space α] : Prop :=
(bicompact_univ : is_bicompact (set.univ : set α))

/-- -/
class bizero_dim (α : Type*) [bitopological_space α] : Prop :=
(stuff : true)

instance topological_space.to_bitopological_space [topological_space α] : bitopological_space α :=
⟨‹topological_space α›, ‹topological_space α›⟩

instance t2_space.to_bi_t2_space [topological_space α] [t2_space α] : bi_t2_space α :=
⟨λ x y h, t2_separation h⟩

instance compact_space.to_bicompact_space [topological_space α] [compact_space α] :
  bicompact_space α :=
sorry

instance zero_dim.to_bizero_dim [topological_space α] : bizero_dim α :=
sorry

instance : bi_t2_space punit := by apply_instance
