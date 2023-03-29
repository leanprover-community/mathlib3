/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.set.image
import data.list.basic
import data.fin.basic

/-!
# Lemmas about `list`s and `set.range`

In this file we prove lemmas about range of some operations on lists.
-/

open list
variables {α β : Type*} (l : list α)

namespace set

lemma range_list_map (f : α → β) : range (map f) = {l | ∀ x ∈ l, x ∈ range f} :=
begin
  refine subset.antisymm (range_subset_iff.2 $ λ l, forall_mem_map_iff.2 $ λ y _, mem_range_self _)
    (λ l hl, _),
  induction l with a l ihl, { exact ⟨[], rfl⟩ },
  rcases ihl (λ x hx, hl x $ subset_cons _ _ hx) with ⟨l, rfl⟩,
  rcases hl a (mem_cons_self _ _) with ⟨a, rfl⟩,
  exact ⟨a :: l, map_cons _ _ _⟩
end

lemma range_list_map_coe (s : set α) : range (map (coe : s → α)) = {l | ∀ x ∈ l, x ∈ s} :=
by rw [range_list_map, subtype.range_coe]

@[simp] lemma range_list_nth_le : range (λ k : fin l.length, l.nth_le k k.2) = {x | x ∈ l} :=
begin
  ext x,
  rw [mem_set_of_eq, mem_iff_nth_le],
  exact ⟨λ ⟨⟨n, h₁⟩, h₂⟩, ⟨n, h₁, h₂⟩, λ ⟨n, h₁, h₂⟩, ⟨⟨n, h₁⟩, h₂⟩⟩
end

lemma range_list_nth : range l.nth = insert none (some '' {x | x ∈ l}) :=
begin
  rw [← range_list_nth_le, ← range_comp],
  refine (range_subset_iff.2 $ λ n, _).antisymm (insert_subset.2 ⟨_, _⟩),
  exacts [(le_or_lt l.length n).imp nth_eq_none_iff.2 (λ hlt, ⟨⟨_, _⟩, (nth_le_nth hlt).symm⟩),
    ⟨_, nth_eq_none_iff.2 le_rfl⟩, range_subset_iff.2 $ λ k, ⟨_, nth_le_nth _⟩]
end

@[simp] lemma range_list_nthd (d : α) : range (λ n, l.nthd n d) = insert d {x | x ∈ l} :=
calc range (λ n, l.nthd n d) = (λ o : option α, o.get_or_else d) '' range l.nth :
  by simp only [← range_comp, (∘), nthd_eq_get_or_else_nth]
... = insert d {x | x ∈ l} :
  by simp only [range_list_nth, image_insert_eq, option.get_or_else, image_image, image_id']

@[simp]
lemma range_list_inth [inhabited α] (l : list α) : range l.inth = insert default {x | x ∈ l} :=
range_list_nthd l default

end set

/-- If each element of a list can be lifted to some type, then the whole list can be lifted to this
type. -/
instance list.can_lift (c) (p) [can_lift α β c p] :
  can_lift (list α) (list β) (list.map c) (λ l, ∀ x ∈ l, p x) :=
{ prf  := λ l H,
    begin
      rw [← set.mem_range, set.range_list_map],
      exact λ a ha, can_lift.prf a (H a ha),
    end}
