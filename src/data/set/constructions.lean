import tactic
import data.finset.basic

variables {α : Type*} (S : set (set α))

structure has_finite_inter :=
(univ_mem : set.univ ∈ S)
(inter_mem {s t} : s ∈ S → t ∈ S → s ∩ t ∈ S)

namespace has_finite_inter

inductive finite_inter_closure : set (set α)
| basic {s} : s ∈ S → finite_inter_closure s
| univ : finite_inter_closure set.univ
| inter {s t} : finite_inter_closure s → finite_inter_closure t → finite_inter_closure (s ∩ t)

def finite_inter_closure_has_finite_inter : has_finite_inter (finite_inter_closure S) :=
{ univ_mem := finite_inter_closure.univ,
  inter_mem := λ _ _, finite_inter_closure.inter }
  
variable {S}
lemma finite_inter_mem (cond : has_finite_inter S) (F : finset (set α)) :
  ↑F ⊆ S → ⋂₀ (↑F : set (set α)) ∈ S :=
begin
  classical,
  refine finset.induction_on F (λ _, _) _,
  { suffices : set.univ ∈ S, by simpa,
    apply cond.univ_mem },
  { intros a s h1 h2 h3,
    suffices : a ∩ ⋂₀ ↑s ∈ S, by simpa,
    apply cond.inter_mem,
    { apply h3, simp },
    { apply h2, intros x hx, apply h3, 
      suffices : x = a ∨ x ∈ s, by simpa,
      right, assumption } }
end

lemma finite_inter_closure_insert {A : set α} (cond : has_finite_inter S) 
  (P ∈ finite_inter_closure (insert A S)) : P ∈ S ∨ ∃ Q ∈ S, P = A ∩ Q :=
begin
  induction H,
  { cases H_a,
    { right,
      use set.univ,
      refine ⟨cond.univ_mem,_⟩,
      simpa},
    { left, assumption } },
  { left, exact cond.univ_mem },
  { rcases H_ih_a with (h | ⟨Q,hQ,rfl⟩),
    { rcases H_ih_a_1 with (i | ⟨R,hR,rfl⟩),
      { left,
        apply cond.inter_mem,
        assumption' },
      { right,
        use H_s ∩ R,
        split,
        { apply cond.inter_mem, assumption' },
        { finish } } },
    { rcases H_ih_a_1 with (i | ⟨R,hR,rfl⟩),
      { right,
        use Q ∩ H_t,
        split,
        { apply cond.inter_mem, assumption' },
        { finish } },
      { right,
        use Q ∩ R,
        split,
        { apply cond.inter_mem, assumption' },
        { tidy } } } },
end

end has_finite_inter
