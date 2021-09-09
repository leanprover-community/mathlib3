/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.multiset.basic

/-!
# Sections of a multiset
-/

namespace multiset
variables {α : Type*}

section sections

/--
The sections of a multiset of multisets `s` consists of all those multisets
which can be put in bijection with `s`, so each element is an member of the corresponding multiset.
-/
def sections (s : multiset (multiset α)) : multiset (multiset α) :=
multiset.rec_on s {0} (λs _ c, s.bind $ λa, c.map (multiset.cons a))
  (assume a₀ a₁ s pi, by simp [map_bind, bind_bind a₀ a₁, cons_swap])

@[simp] lemma sections_zero : sections (0 : multiset (multiset α)) = {0} :=
rfl

@[simp] lemma sections_cons (s : multiset (multiset α)) (m : multiset α) :
  sections (m ::ₘ s) = m.bind (λa, (sections s).map (multiset.cons a)) :=
rec_on_cons m s

lemma coe_sections : ∀(l : list (list α)),
  sections ((l.map (λl:list α, (l : multiset α))) : multiset (multiset α)) =
    ((l.sections.map (λl:list α, (l : multiset α))) : multiset (multiset α))
| [] := rfl
| (a :: l) :=
  begin
    simp,
    rw [← cons_coe, sections_cons, bind_map_comm, coe_sections l],
    simp [list.sections, (∘), list.bind]
  end

@[simp] lemma sections_add (s t : multiset (multiset α)) :
  sections (s + t) = (sections s).bind (λm, (sections t).map ((+) m)) :=
multiset.induction_on s (by simp)
  (assume a s ih, by simp [ih, bind_assoc, map_bind, bind_map, -add_comm])

lemma mem_sections {s : multiset (multiset α)} :
  ∀{a}, a ∈ sections s ↔ s.rel (λs a, a ∈ s) a :=
multiset.induction_on s (by simp)
  (assume a s ih a',
    by simp [ih, rel_cons_left, -exists_and_distrib_left, exists_and_distrib_left.symm, eq_comm])

lemma card_sections {s : multiset (multiset α)} : card (sections s) = prod (s.map card) :=
multiset.induction_on s (by simp) (by simp {contextual := tt})

lemma prod_map_sum [comm_semiring α] {s : multiset (multiset α)} :
  prod (s.map sum) = sum ((sections s).map prod) :=
multiset.induction_on s (by simp)
  (assume a s ih, by simp [ih, map_bind, sum_map_mul_left, sum_map_mul_right])

end sections

end multiset
