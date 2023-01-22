/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.filter.seq
import control.traversable.instances

/-!
-/

open set
open_locale filter

namespace filter

universe u
variables {α β γ : Type u}

-- this section needs to be before applicative, otherwise the wrong instance will be chosen

instance : applicative filter := { map := @filter.map, seq := @filter.seq }

lemma seq_eq_filter_seq (f : filter (α → β)) (g : filter α) : f <*> g = seq f g := rfl

instance : alternative filter :=
{ failure := λ α, ⊥,
  orelse  := λ α x y, x ⊔ y }

instance : is_lawful_applicative (filter : Type u → Type u) :=
{ pure_seq_eq_map := λ α β, pure_seq_eq_map,
  map_pure        := λ α β, map_pure,
  seq_pure        := λ α β, seq_pure,
  seq_assoc       := λ α β γ, seq_assoc }

instance : is_comm_applicative (filter : Type u → Type u) :=
⟨λ α β f g, prod_map_seq_comm f g⟩

open list

lemma sequence_mono :
  ∀ (as bs : list (filter α)), forall₂ (≤) as bs → sequence as ≤ sequence bs
| []        []        forall₂.nil         := le_rfl
| (a :: as) (b :: bs) (forall₂.cons h hs) := seq_mono (map_mono h) (sequence_mono as bs hs)

variables {f : β → filter α} {s : γ → set α}

lemma mem_traverse :
  ∀ (fs : list β) (us : list γ), forall₂ (λ b c, s c ∈ f b) fs us → traverse s us ∈ traverse f fs
| []        []        forall₂.nil         := mem_pure.2 $ mem_singleton _
| (f :: fs) (u :: us) (forall₂.cons h hs) := seq_mem_seq (image_mem_map h) (mem_traverse fs us hs)

lemma mem_traverse_iff (fs : list β) (t : set (list α)) :
  t ∈ traverse f fs ↔
    (∃ us : list (set α), forall₂ (λ b (s : set α), s ∈ f b) fs us ∧ sequence us ⊆ t) :=
begin
  split,
  { induction fs generalizing t,
    case nil { simp only [sequence, mem_pure, imp_self, forall₂_nil_left_iff,
      exists_eq_left, set.pure_def, singleton_subset_iff, traverse_nil] },
    case cons : b fs ih t
    { intro ht,
      rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩,
      rcases ih v hv with ⟨us, hus, hu'⟩,
      exact ⟨cons ⁻¹' u :: us, forall₂.cons hu hus,
        (set.seq_mono (image_preimage_subset _ _) hu').trans ht⟩ } },
  { rintro ⟨us, hus, hs⟩,
    exact mem_of_superset (mem_traverse _ _ hus) hs }
end

end filter
