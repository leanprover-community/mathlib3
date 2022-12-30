import data.real.ennreal
import topology.metric_space.emetric_space
import .for_mathlib
import data.finset.sort
import topology.instances.ennreal

open emetric nnreal set ennreal

namespace function

section length_on

variables {E α : Type*} [pseudo_emetric_space E]
variables (f : α → E)

-- This definition yields a messy term and troubles down the road!
/-@[simp] def length_on : list α → ennreal
| list.nil := 0
| (list.cons _ list.nil) := 0
| (a::b::l) := edist (f a) (f b) + (length_on (b::l))
-/

-- definition 'length_on' depends on 'ennreal.canonically_ordered_comm_semiring
-- so says lean
noncomputable def length_on : list α → ennreal :=
list.rec 0
  (λ (a : α) (l : list α) (ih : ennreal),
      list.rec 0 (λ (b : α) (l : list α) (ih' : ennreal), edist (f a) (f b) + ih) l)

lemma length_on_nil : f.length_on list.nil = 0 := rfl
lemma length_on_singleton (a : α) : f.length_on [a] = 0 := rfl
lemma length_on_cons_cons (a b : α) (l : list α) :
  f.length_on (a::b::l) = edist (f a) (f b) + f.length_on (b::l) := rfl

lemma length_on_pair (a b : α) : f.length_on [a, b] = edist (f a) (f b) :=
by simp only [length_on_cons_cons, length_on_singleton, add_zero]

lemma length_on_eq_zip_sum :
  ∀ (l : list α), f.length_on l = (list.zip_with (λ x y, edist (f x) (f y)) l l.tail).sum
| [] := by simp [length_on_nil]
| [a] := by simp [length_on_singleton]
| (a::b::l) := by simp [length_on_cons_cons, length_on_eq_zip_sum (b::l)]

lemma length_on_append_cons_cons :
   ∀ (l : list α) (a b : α), f.length_on (l ++ [a, b]) = f.length_on (l ++ [a]) + edist (f a) (f b)
| [] a b := by
  { simp only [length_on, list.nil_append, add_zero, zero_add], }
| [x] a b := by
  { simp only [length_on, list.singleton_append, add_zero], }
| (x :: y :: l) a b := by
  { simp only [length_on_cons_cons, list.cons_append, add_assoc],
    congr,
    simp only [←list.cons_append],
    apply length_on_append_cons_cons, }

lemma length_on_le_length_on_cons (c : α) : ∀ (l : list α), f.length_on l ≤ (f.length_on $ c :: l)
| [] := by { rw [length_on, le_zero_iff], }
| (a::l) := self_le_add_left _ _

lemma length_on_drop_second_cons_le :
  ∀ (a b : α) (l : list α), f.length_on (a :: l) ≤ f.length_on (a :: b :: l)
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

lemma length_on_reverse : ∀ (l : list α), f.length_on l.reverse = f.length_on l
| [] := rfl
| [a] := rfl
| (a :: b :: l) := by
  { simp only [length_on_append_cons_cons, ←length_on_reverse (b :: l), list.reverse_cons,
               list.append_assoc, list.singleton_append, length_on_cons_cons],
    rw [add_comm, edist_comm], }

lemma length_on_map {γ : Type*} (φ : γ → α) :
  ∀ (l : list γ), f.length_on (l.map φ) = (f ∘ φ).length_on l
| [] := by { simp only [length_on_nil, list.map_nil], }
| [a] := by { simp only [length_on_singleton, list.map], }
| (a :: b :: l)  := by
  { simp only [length_on_cons_cons, list.map, comp_app, ←length_on_map (b::l)], }

lemma length_on_le_append_singleton_append :
  ∀ (l : list α) (x : α) (l' : list α), f.length_on (l ++ l') ≤ f.length_on (l ++ [x] ++ l')
| [] x l' := f.length_on_le_length_on_cons _ _
| [a] x l' := f.length_on_drop_second_cons_le _ _ _
| (a :: b :: l) x l' := by
  { change a :: b :: l ++ l' with a :: b :: (l ++ l'),
    change a :: b :: l ++ [x] ++ l' with a :: b :: (l ++ [x] ++ l'),
    rw [length_on],
    apply add_le_add_left _ (edist (f a) (f b)),
    exact length_on_le_append_singleton_append (b :: l) x l', }

lemma length_on_append_singleton_append :
  ∀ (l : list α) (x : α) (l' : list α),
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
  ∀ {l l' : list α}, l <+ l' → ∀ x, f.length_on (x::l) ≤ f.length_on (x::l')
| _ _ list.sublist.slnil             x := by { rw [length_on, le_zero_iff], }
| _ _ (list.sublist.cons  l₁ l₂ a s) x :=
  (f.length_on_drop_second_cons_le x a l₁).trans $ add_le_add_left (length_on_mono' s a) _
| _ _ (list.sublist.cons2 l₁ l₂ a s) x := add_le_add_left (length_on_mono' s a) _

lemma length_on_mono : ∀ {l l' : list α}, l <+ l' → f.length_on l ≤ f.length_on l'
| _ _ list.sublist.slnil             := by { rw [length_on, le_zero_iff], }
| _ _ (list.sublist.cons  l₁ l₂ a s) :=
  (f.length_on_le_length_on_cons a l₁).trans $ f.length_on_mono' s a
| _ _ (list.sublist.cons2 l₁ l₂ a s) := f.length_on_mono' s a

lemma edist_le_length_on_of_mem {a b : α} {l : list α} (al : a ∈ l) (bl : b ∈ l) :
  edist (f a) (f b) ≤ f.length_on l :=
begin
  rcases l.pair_mem_list al bl with rfl|ab|ba,
  { rw [edist_self (f a)], exact zero_le', },
  { rw [←length_on_pair], exact f.length_on_mono ab, },
  { rw [edist_comm, ←length_on_pair], exact f.length_on_mono ba, }
end

lemma length_on_congr {f g : α → E} :
  ∀ {l : list α} (h : ∀ x ∈ l, f x = g x), f.length_on l = g.length_on l
| [] h := by simp only [length_on_nil]
| [a] h := by simp only [length_on_singleton]
| (a::b::l) h := by
  { have al : a ∈ a::b::l, by simp only [list.mem_cons_iff, eq_self_iff_true, true_or],
    have bl : b ∈ a::b::l, by simp only [list.mem_cons_iff, eq_self_iff_true, true_or, or_true],
    simp only [length_on_cons_cons, h _ al, h _ bl,
               @length_on_congr (b::l) (λ x xl', h _ (or.inr xl'))], }

lemma length_on_const : ∀ {l : list α} (hc : ∀ x y ∈ l, f x = f y), f.length_on l = 0
| [] h := by simp only [length_on_nil]
| [a] h := by simp only [length_on_singleton]
| (a::b::l) h := by
  { have al : a ∈ a::b::l, by simp only [list.mem_cons_iff, eq_self_iff_true, true_or],
    have bl : b ∈ a::b::l, by simp only [list.mem_cons_iff, eq_self_iff_true, true_or, or_true],
    simp only [length_on_cons_cons, h _ al _ bl, edist_self, add_zero,
               @length_on_const (b::l) (λ x xl' y yl', h _ (or.inr xl') _ (or.inr yl'))], }

end length_on

end function
