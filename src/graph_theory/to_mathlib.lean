import data.finset
import data.fin_enum

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

end move_this
