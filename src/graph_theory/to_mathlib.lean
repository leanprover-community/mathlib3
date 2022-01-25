import algebra.big_operators.order
import data.fin_enum
import data.finset.lattice
import measure_theory.probability_mass_function.basic

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

@[simp]
lemma finset.powerset_univ (X : Type*) [fintype X] :
  (finset.univ : finset X).powerset = finset.univ :=
by simp only [finset.eq_univ_iff_forall, finset.mem_powerset, finset.subset_univ, forall_const]

section classical
open_locale classical

noncomputable def pmf.binomial (X : Type*) [fintype X] (p : nnreal) (hp : p ≤ 1) : pmf (finset X) :=
⟨λ s, p ^ s.card * (1 - p) ^ (fintype.card X - s.card),
begin
  have p_add : p + (1 - p) = 1,
  { rw add_comm, exact nnreal.sub_add_cancel_of_le hp },
  have := finset.sum_pow_mul_eq_add_pow p (1 - p) (finset.univ : finset X),
  rw [p_add, one_pow, finset.powerset_univ, finset.card_univ] at this,
  conv { congr, skip, rw ← this },
  apply has_sum_fintype,
end⟩

end classical

end move_this
