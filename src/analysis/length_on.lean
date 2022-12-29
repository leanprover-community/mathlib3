import data.real.ennreal
import topology.metric_space.emetric_space
import .for_mathlib
import data.finset.sort
import topology.instances.ennreal

open emetric nnreal set ennreal

namespace function

section length_on

variables {α β : Type*} [pseudo_emetric_space α]
variables (f : β → α)

-- This definition yields a messy term and troubles down the road!
/-@[simp] def length_on : list β → ennreal
| list.nil := 0
| (list.cons _ list.nil) := 0
| (a::b::l) := edist (f a) (f b) + (length_on (b::l))
-/

-- definition 'length_on' depends on 'ennreal.canonically_ordered_comm_semiring
-- so says lean
noncomputable def length_on : list β → ennreal :=
list.rec 0
  (λ (a : β) (l : list β) (ih : ennreal),
      list.rec 0 (λ (b : β) (l : list β) (ih' : ennreal), edist (f a) (f b) + ih) l)

lemma length_on_nil : f.length_on list.nil = 0 := rfl
lemma length_on_singleton (a : β) : f.length_on [a] = 0 := rfl
lemma length_on_cons_cons (a b : β) (l : list β) :
  f.length_on (a::b::l) = edist (f a) (f b) + f.length_on (b::l) := rfl

lemma length_on_pair (a b : β) : f.length_on [a, b] = edist (f a) (f b) :=
by simp only [length_on_cons_cons, length_on_singleton, add_zero]

lemma length_on_append_cons_cons :
   ∀ (l : list β) (a b : β), f.length_on (l ++ [a, b]) = f.length_on (l ++ [a]) + edist (f a) (f b)
| [] a b := by
  { simp only [length_on, list.nil_append, add_zero, zero_add], }
| [x] a b := by
  { simp only [length_on, list.singleton_append, add_zero], }
| (x :: y :: l) a b := by
  { simp only [length_on_cons_cons, list.cons_append, add_assoc],
    congr,
    simp only [←list.cons_append],
    apply length_on_append_cons_cons, }

lemma length_on_le_length_on_cons (c : β) : ∀ (l : list β), f.length_on l ≤ (f.length_on $ c :: l)
| [] := by { rw [length_on, le_zero_iff], }
| (a::l) := self_le_add_left _ _

lemma length_on_drop_second_cons_le :
  ∀ (a b : β) (l : list β), f.length_on (a :: l) ≤ f.length_on (a :: b :: l)
| _ _ []  := by
  { apply length_on_le_length_on_cons, }
| a b (c::l) := by
  { simp only [length_on, ←add_assoc],
    apply add_le_add_right (edist_triangle _ _ _) (f.length_on (c :: l)), }

lemma length_on_append : ∀ l l', f.length_on l + f.length_on l' ≤ f.length_on (l ++ l')
| [] l' := by
  { rw [list.nil_append, length_on, zero_add], exact le_refl (f.length_on l'), }
| [a] l' := by
  { rw [list.singleton_append, length_on, zero_add],
    apply length_on_le_length_on_cons, }
| (a :: b :: l) l' := by
  { rw [list.cons_append, length_on, add_assoc],
    refine add_le_add_left (length_on_append (b::l) l') _, }

lemma length_on_reverse : ∀ (l : list β), f.length_on l.reverse = f.length_on l
| [] := rfl
| [a] := rfl
| (a :: b :: l) := by
  { simp only [length_on_append_cons_cons, ←length_on_reverse (b :: l), list.reverse_cons,
               list.append_assoc, list.singleton_append, length_on_cons_cons],
    rw [add_comm, edist_comm], }

lemma length_on_map {γ : Type*} (φ : γ → β) :
  ∀ (l : list γ), f.length_on (l.map φ) = (f ∘ φ).length_on l
| [] := by { simp only [length_on_nil, list.map_nil], }
| [a] := by { simp only [length_on_singleton, list.map], }
| (a :: b :: l)  := by
  { simp only [length_on_cons_cons, list.map, comp_app, ←length_on_map (b::l)], }

lemma length_on_le_append_singleton_append :
  ∀ (l : list β) (x : β) (l' : list β), f.length_on (l ++ l') ≤ f.length_on (l ++ [x] ++ l')
| [] x l' := f.length_on_le_length_on_cons _ _
| [a] x l' := f.length_on_drop_second_cons_le _ _ _
| (a :: b :: l) x l' := by
  { change a :: b :: l ++ l' with a :: b :: (l ++ l'),
    change a :: b :: l ++ [x] ++ l' with a :: b :: (l ++ [x] ++ l'),
    rw [length_on],
    apply add_le_add_left _ (edist (f a) (f b)),
    exact length_on_le_append_singleton_append (b :: l) x l', }

lemma length_on_append_singleton_append :
  ∀ (l : list β) (x : β) (l' : list β),
    f.length_on (l ++ [x] ++ l') = f.length_on (l ++ [x]) + f.length_on ([x] ++ l')
| [] x l' := by { rw [length_on, list.nil_append, zero_add], }
| [a] x l' := by
  { simp only [length_on, list.singleton_append, list.cons_append, add_zero, eq_self_iff_true,
               list.nil_append], }
| (a :: b :: l) x l' := by
  { simp only [length_on_cons_cons, list.cons_append, list.append_assoc, list.singleton_append,
               add_assoc],
    congr,
    simp_rw [←list.cons_append b l, ←@list.singleton_append _ x l',←list.append_assoc],
    exact length_on_append_singleton_append (b::l) x l', }

lemma length_on_mono' :
  ∀ {l l' : list β}, l <+ l' → ∀ x, f.length_on (x::l) ≤ f.length_on (x::l')
| _ _ list.sublist.slnil             x := by { rw [length_on, le_zero_iff], }
| _ _ (list.sublist.cons  l₁ l₂ a s) x :=
  (f.length_on_drop_second_cons_le x a l₁).trans $ add_le_add_left (length_on_mono' s a) _
| _ _ (list.sublist.cons2 l₁ l₂ a s) x := add_le_add_left (length_on_mono' s a) _

lemma length_on_mono : ∀ {l l' : list β}, l <+ l' → f.length_on l ≤ f.length_on l'
| _ _ list.sublist.slnil             := by { rw [length_on, le_zero_iff], }
| _ _ (list.sublist.cons  l₁ l₂ a s) :=
  (f.length_on_le_length_on_cons a l₁).trans $ f.length_on_mono' s a
| _ _ (list.sublist.cons2 l₁ l₂ a s) := f.length_on_mono' s a

lemma edist_le_length_on_of_mem {a b : β} {l : list β} (al : a ∈ l) (bl : b ∈ l) :
  edist (f a) (f b) ≤ f.length_on l :=
begin
  rcases l.pair_mem_list al bl with rfl|ab|ba,
  { rw [edist_self (f a)], exact zero_le', },
  { rw [←length_on_pair], exact f.length_on_mono ab, },
  { rw [edist_comm, ←length_on_pair], exact f.length_on_mono ba, }
end

lemma length_on_congr {f g : β → α} {l : list β} (h : ∀ x ∈ l, f x = g x) :
  f.length_on l = g.length_on l := sorry


lemma length_on_destutter' [decidable_eq β] :
  ∀ (a : β) (l : list β), f.length_on (l.destutter' (≠) a) = f.length_on (a::l) := sorry
/- | a [] := by simp only [length_on_nil, length_on_singleton, list.destutter'_nil]
| a [b] := by
  { by_cases h : a = b,
    { cases h,
      simp only [length_on_pair, length_on_singleton, list.destutter'_singleton, ne.def,
                 eq_self_iff_true, not_true, if_false, edist_self],   },
    { replace h : a ≠ b := h,
      simp only [list.destutter'_cons_pos _ h, list.destutter'_nil], }, }
| a (b::c::l) := by
  { by_cases h : a = b,
  { cases h,
      simp only [length_on_cons_cons, list.destutter'_cons_neg, ne.def, eq_self_iff_true, not_true,
               not_false_iff, edist_self, zero_add],
      rw [length_on_destutter' a (c::l), length_on_cons_cons], },
    { replace h : a ≠ b := h,
      simp only [list.destutter'_cons_pos _ h],
      by_cases h' : b = c,
      { cases h',
        have : list.destutter' (ne) b (b::l) = list.destutter' (ne) b l, by {simp,},
        rw this,
        simp [length_on_cons_cons],
      rw length_on_cons_cons, } } }

lemma length_on_destutter [decidable_eq β] :
  ∀ (l : list β), f.length_on (l.destutter (≠)) = f.length_on l
| [] := by simp only [list.destutter_nil]
| (a::l) := f.length_on_destutter' a l
-/


section finset

variables [linear_order β] {r s t : finset β} (st : s ⊆ t)

noncomputable def length_on_finset (s : finset β) := f.length_on (s.sort (≤))

lemma length_on_finset_mono : f.length_on_finset s ≤ f.length_on_finset t := sorry

end finset

end length_on

end function
