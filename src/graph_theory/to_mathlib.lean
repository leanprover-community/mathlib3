import data.finset
import data.fin_enum
import algebra.big_operators

section move_this
variables {X : Type*} {Y : Type*} [decidable_eq X] [decidable_eq Y]

lemma finset.map_disjoint (f : X ↪ Y) (s t : finset X) :
  disjoint (s.map f) (t.map f) ↔ disjoint s t :=
begin
  simp only [finset.disjoint_iff_ne, finset.mem_map,
    exists_prop, exists_imp_distrib, and_imp],
  split,
  { rintros h x hxs _ hxt rfl, exact h _ x hxs rfl _ x hxt rfl rfl },
  { rintros h _ x₁ hxs rfl _ x₂ hxt rfl,
    apply f.inj'.ne, solve_by_elim }
end

def finset_with_card_of_injective_fn {k : ℕ} (f : fin k → X) (i : function.injective f) :
  {s : finset X // s.card = k} :=
⟨finset.univ.map ⟨f, i⟩, (by simp)⟩

variables {M : Type*} [ordered_comm_monoid M] (s : finset X)

lemma finset.sum_le (f : X → M) {m : M} (hm : ∀ x ∈ s, f x ≤ m) :
  s.sum f ≤ (add_monoid.smul s.card m) :=
begin
  rw ← finset.sum_const,
  exact finset.sum_le_sum hm,
end

end move_this
