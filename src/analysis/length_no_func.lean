import data.real.ennreal
import topology.metric_space.emetric_space
import data.finset.sort
import topology.instances.ennreal

open emetric nnreal set ennreal

open_locale big_operators

variables {E : Type*} [pseudo_emetric_space E]

namespace list


@[protected]
noncomputable def edist : list E → ennreal :=
list.rec 0
  (λ (a : E) (l : list E) (ih : ennreal),
      list.rec 0 (λ (b : E) (l : list E) (ih' : ennreal), edist a b + ih) l)


lemma edist_nil : edist (@list.nil E) = 0 := rfl
lemma edist_singleton (a : E) : edist [a] = 0 := rfl
lemma edist_cons_cons (a b : E) (l : list E) :
  edist (a::b::l) = edist a b + edist (b::l) := rfl

lemma edist_pair (a b : E) : edist [a, b] = edist a b :=
by simp only [edist_cons_cons, edist_singleton, add_zero]

lemma edist_eq_zip_sum :
  ∀ (l : list E), edist l = (list.zip_with (λ x y, edist x y) l l.tail).sum
| [] := by simp [edist_nil]
| [a] := by simp [edist_singleton]
| (a::b::l) := by simp [edist_cons_cons, edist_eq_zip_sum (b::l)]

lemma edist_append_cons_cons :
   ∀ (l : list E) (a b : E), edist (l ++ [a, b]) = edist (l ++ [a]) + edist a b
| [] a b := by
  { simp only [list.edist, list.nil_append, add_zero, zero_add], }
| [x] a b := by
  { simp only [list.edist, list.singleton_append, add_zero], }
| (x :: y :: l) a b := by
  { simp only [edist_cons_cons, list.cons_append, add_assoc],
    congr,
    simp only [←list.cons_append],
    apply edist_append_cons_cons, }

lemma edist_le_edist_cons (c : E) : ∀ (l : list E), edist l ≤ (edist $ c :: l)
| [] := by { rw [list.edist, le_zero_iff], }
| (a::l) := self_le_add_left _ _

lemma edist_drop_second_cons_le :
  ∀ (a b : E) (l : list E), edist (a :: l) ≤ edist (a :: b :: l)
| _ _ []  := by
  { apply edist_le_edist_cons, }
| a b (c::l) := by
  { simp only [list.edist, ←add_assoc],
    apply add_le_add_right (edist_triangle _ _ _) (edist (c :: l)), }

lemma edist_append : ∀ (l l' : list E), edist l + edist l' ≤ edist (l ++ l')
| [] l' := by
  { rw [list.nil_append, list.edist, zero_add], exact le_refl (edist l'), }
| [a] l' := by
  { rw [list.singleton_append, list.edist, zero_add],
    apply edist_le_edist_cons, }
| (a :: b :: l) l' := by
  { rw [list.cons_append, list.edist, add_assoc],
    refine add_le_add_left (edist_append (b::l) l') _, }

lemma edist_reverse : ∀ (l : list E), edist l.reverse = edist l
| [] := rfl
| [a] := rfl
| (a :: b :: l) := by
  { simp only [edist_append_cons_cons, ←edist_reverse (b :: l), list.reverse_cons,
               list.append_assoc, list.singleton_append, edist_cons_cons],
    rw [add_comm, edist_comm], }

lemma edist_le_append_singleton_append :
  ∀ (l : list E) (x : E) (l' : list E), edist (l ++ l') ≤ edist (l ++ [x] ++ l')
| [] x l' := edist_le_edist_cons _ _
| [a] x l' := edist_drop_second_cons_le _ _ _
| (a :: b :: l) x l' := by
  { change a :: b :: l ++ l' with a :: b :: (l ++ l'),
    change a :: b :: l ++ [x] ++ l' with a :: b :: (l ++ [x] ++ l'),
    rw [list.edist],
    apply add_le_add_left _ (edist a b),
    exact edist_le_append_singleton_append (b :: l) x l', }

lemma edist_append_singleton_append :
  ∀ (l : list E) (x : E) (l' : list E),
    edist (l ++ [x] ++ l') = edist (l ++ [x]) + edist ([x] ++ l')
| [] x l' := by { rw [list.edist, list.nil_append, zero_add], }
| [a] x l' := by
  { simp only [list.edist, list.singleton_append, list.cons_append, add_zero, eq_self_iff_true,
               list.nil_append], }
| (a :: b :: l) x l' := by
  { simp only [edist_cons_cons, list.cons_append, list.append_assoc, list.singleton_append,
               add_assoc],
    congr,
    simp_rw [←list.cons_append b l, ←@list.singleton_append _ x l',←list.append_assoc],
    exact edist_append_singleton_append (b::l) x l', }

lemma edist_mono' :
  ∀ {l l' : list E}, l <+ l' → ∀ x, edist (x::l) ≤ edist (x::l')
| _ _ list.sublist.slnil             x := by { rw [list.edist, le_zero_iff], }
| _ _ (list.sublist.cons  l₁ l₂ a s) x :=
  (edist_drop_second_cons_le x a l₁).trans $ add_le_add_left (edist_mono' s a) _
| _ _ (list.sublist.cons2 l₁ l₂ a s) x := add_le_add_left (edist_mono' s a) _

lemma edist_mono : ∀ {l l' : list E}, l <+ l' → edist l ≤ edist l'
| _ _ list.sublist.slnil             := by { rw [list.edist, le_zero_iff], }
| _ _ (list.sublist.cons  l₁ l₂ a s) :=
  (edist_le_edist_cons a l₁).trans $ edist_mono' s a
| _ _ (list.sublist.cons2 l₁ l₂ a s) := edist_mono' s a


-- for mathlib?
lemma pair_mem_list {β : Type*} {a b : β} :
  ∀ (l : list β), a ∈ l → b ∈ l → a = b ∨ [a,b] <+ l ∨ [b,a] <+ l
| [] al bl := by { simpa only [list.not_mem_nil] using al, }
| (x::l) al bl := by
  { simp only [list.mem_cons_iff] at al bl, cases al; cases bl,
    { left, exact al.trans bl.symm, },
    { rw al, right, left, apply list.sublist.cons2,
      simpa only [list.singleton_sublist] using bl, },
    { rw bl, right,  right, apply list.sublist.cons2,
      simpa only [list.singleton_sublist] using al, },
    { rcases pair_mem_list l al bl with h|ab|ba,
      { left, exact h, },
      { right, left, apply list.sublist.cons, exact ab, },
      { right, right, apply list.sublist.cons, exact ba, }, }, }

lemma edist_le_edist_of_mem {a b : E} {l : list E} (al : a ∈ l) (bl : b ∈ l) :
  edist a b ≤ edist l :=
begin
  rcases l.pair_mem_list al bl with rfl|ab|ba,
  { rw [edist_self a], exact zero_le', },
  { rw [←edist_pair], exact edist_mono ab, },
  { rw [edist_comm, ←edist_pair], exact edist_mono ba, }
end

lemma edist_const : ∀ {l : list E} (hc : ∀ x y ∈ l, x = y), edist l = 0
| [] h := by simp only [edist_nil]
| [a] h := by simp only [edist_singleton]
| (a::b::l) h := by
  { have al : a ∈ a::b::l, by simp only [list.mem_cons_iff, eq_self_iff_true, true_or],
    have bl : b ∈ a::b::l, by simp only [list.mem_cons_iff, eq_self_iff_true, true_or, or_true],
    simp only [edist_cons_cons, h _ al _ bl, edist_self, add_zero,
               @edist_const (b::l) (λ x xl' y yl', h _ (or.inr xl') _ (or.inr yl'))], }


-- mathlib?
lemma pairwise.rel_first_of_mem_cons {α : Type u_1} {R : α → α → Prop} (hR : reflexive R)
  {x y : α } {l : list α} (hl : (x::l).pairwise R) (hy : y ∈ x::l) : R x y := sorry

lemma edist_of_triangles_eq :
  ∀ {l : list E} {a b : E} (hl : list.chain (λ x y, edist x y + edist y b = edist x b) a l),
    l.edist ≤ edist a b
| [] a b hl := by simp [edist_nil]
| [x] a b hl := by simp [edist_singleton]
| (x::y::l) a b hl :=
begin
  simp only [chain_cons] at hl,
  calc (x::y::l).edist
     = edist x y + (y::l).edist : edist_cons_cons _ _ _
  ...≤ edist x y + edist y b    : add_le_add_left (@edist_of_triangles_eq (y::l) y b _) _
  ...= edist x b                : hl.2.1
  ...≤ edist a x + edist x b    : self_le_add_left _ _
  ...= edist a b                : hl.1,
  constructor,
  simp only [edist_self, zero_add],
  exact hl.2.2,
end

-- mathlib?
lemma _root_.real.edist_triangle_eq_of_aligned {a b c : ℝ} (ab : a ≤ b) (bc : b ≤ c) :
  edist a b + edist b c = edist a c := sorry

lemma edist_of_monotone_le_real :
  ∀ {l : list ℝ} (hl : l.pairwise (≤)) {a b : ℝ} (hab : ∀ x ∈ l, a ≤ x ∧ x ≤ b),
  l.edist ≤ edist a b :=
begin
  rintro l hl a b hab,
  apply edist_of_triangles_eq,
  revert a b hl,
  induction l,
  { simp only [pairwise.nil, not_mem_nil, forall_const, chain.nil], },
  { rintro a b hl hab,
    simp only [pairwise_cons] at hl,
    exact chain.cons
      (_root_.real.edist_triangle_eq_of_aligned (hab l_hd (or.inl rfl)).left (hab l_hd (or.inl rfl)).right)
      (l_ih hl.right (λ (x : ℝ) (xl : x ∈ l_tl), ⟨hl.left x xl, (hab x (or.inr xl)).right⟩))},
end

end list


noncomputable def function.evariation_on {α : Type*} [linear_order α] (f : α → E) (s : set α) :=
⨆ l ∈ {l : list α | l.pairwise (≤) ∧ ∀ ⦃x⦄, x ∈ l → x ∈ s}, (l.map f).edist
