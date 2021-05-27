import data.real.basic
import combinatorics.simple_graph.basic
import analysis.special_functions.exp_log
import analysis.special_functions.pow

section

open_locale big_operators
open finset fintype

universe u

def equitable_on {α : Type*} (s : set α) (f : α → ℕ) : Prop :=
  ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₁ ≤ f a₂ → f a₂ - f a₁ ≤ 1

@[simp]
lemma equitable_on_empty {α : Type*} (f : α → ℕ) :
  equitable_on ∅ f :=
by simp [equitable_on]

lemma equitable_on_iff {α : Type*} (s : set α) (f : α → ℕ) :
  equitable_on s f ↔ ∀ ⦃a₁ a₂⦄, a₁ ∈ s → a₂ ∈ s → f a₂ - f a₁ ≤ 1 :=
begin
  split,
  { intros hf a₁ a₂ ha₁ ha₂,
    cases le_total (f a₁) (f a₂),
    { apply hf ha₁ ha₂ h },
    rw nat.sub_eq_zero_of_le h,
    apply zero_le_one },
  { intros hf a₁ a₂ ha₁ ha₂ _,
    apply hf ha₁ ha₂ }
end

variables {V : Type u}

namespace simple_graph
variables [decidable_eq V] (G : simple_graph V) [decidable_rel G.adj]

def edges_pair_finset (U W : finset V) : finset (V × V) :=
(U.product W).filter (λ e, G.adj e.1 e.2)

lemma mem_edges_pair_finset (U W : finset V) (x : V × V) :
  x ∈ G.edges_pair_finset U W ↔ x.1 ∈ U ∧ x.2 ∈ W ∧ G.adj x.1 x.2 :=
by simp [edges_pair_finset, and_assoc]

lemma mem_edges_pair_finset' (U W : finset V) (x y : V) :
  (x, y) ∈ G.edges_pair_finset U W ↔ x ∈ U ∧ y ∈ W ∧ G.adj x y :=
mem_edges_pair_finset _ _ _ _

def edges_count_finset (U W : finset V) : ℕ :=
(G.edges_pair_finset U W).card

lemma edges_count_finset_symm (U W : finset V) :
  G.edges_count_finset U W = G.edges_count_finset W U :=
begin
  apply finset.card_congr (λ (i : V × V) hi, (i.2, i.1)) _ _ _,
  { rintro ⟨i, j⟩ h,
    simp only [mem_edges_pair_finset'] at h ⊢,
    rwa [G.edge_symm, and.left_comm] },
  { rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h₁ h₂ h,
    rcases h,
    refl },
  rintro ⟨i₁, j₁⟩ h,
  refine ⟨⟨j₁, i₁⟩, _, rfl⟩,
  simp only [mem_edges_pair_finset'] at h ⊢,
  rwa [G.edge_symm, and.left_comm],
end

def edges_count : sym2 (finset V) → ℕ :=
quotient.lift (function.uncurry (edges_count_finset G))
  (by { rintros _ _ ⟨_, _⟩, { refl }, apply edges_count_finset_symm })

noncomputable def density_pair (U W : finset V) : ℝ :=
G.edges_count_finset U W / (U.card * W.card)

lemma density_pair_symm (U W : finset V) : G.density_pair U W = G.density_pair W U :=
begin
  rw [density_pair, mul_comm, edges_count_finset_symm],
  refl
end

lemma density_pair_nonneg (U W : finset V) :
  0 ≤ G.density_pair U W :=
begin
  rw [density_pair],
  apply div_nonneg,
  { norm_cast,
    exact nat.zero_le _ },
  norm_cast,
  apply mul_nonneg,
  exact nat.zero_le _,
  exact nat.zero_le _,
end

lemma density_pair_le_one (U W : finset V) :
  G.density_pair U W ≤ 1 :=
begin
  rw density_pair,
  norm_cast,
  refine div_le_one_of_le _ (nat.cast_nonneg _),
  norm_cast,
  rw [edges_count_finset, edges_pair_finset, ←finset.card_product],
  exact finset.card_filter_le _ _,
end

noncomputable def density_sym2 : sym2 (finset V) → ℝ :=
quotient.lift (function.uncurry (density_pair G))
  (by { rintros _ _ ⟨_, _⟩, { refl }, apply density_pair_symm })

lemma density_sym2_le_one (s : sym2 (finset V)) :
  G.density_sym2 s ≤ 1 :=
begin
  apply quotient.induction_on s,
  rintro xy,
  apply density_pair_le_one,
end

lemma density_sym2_nonneg (s : sym2 (finset V)) :
  0 ≤ G.density_sym2 s :=
begin
  apply quotient.induction_on s,
  rintro xy,
  apply density_pair_nonneg,
end

def is_uniform (ε : ℝ) (U W : finset V) : Prop :=
∀ U', U' ⊆ U → ∀ W', W' ⊆ W → ε * U.card ≤ U'.card → ε * W.card ≤ W'.card →
abs (density_pair G U' W' - density_pair G U W) < ε

lemma is_uniform_symmetric (ε : ℝ) : symmetric (is_uniform G ε) :=
begin
  intros U W h W' hW' U' hU' hW hU,
  rw density_pair_symm _ W',
  rw density_pair_symm _ W,
  apply h _ hU' _ hW' hU hW,
end

def is_uniform_sym2 (ε : ℝ) : sym2 (finset V) → Prop :=
sym2.from_rel (is_uniform_symmetric G ε)

end simple_graph

structure equipartition (V : Type u) [decidable_eq V] :=
(parts : finset (finset V))
(disjoint : ∀ (a₁ a₂ ∈ parts) x, x ∈ a₁ → x ∈ a₂ → a₁ = a₂)
(covering : ∀ v, ∃ (a ∈ parts), v ∈ a) -- TODO: add a lemma saying the union is everything
(sizes : equitable_on (parts : set (finset V)) finset.card)

namespace equipartition
variables [decidable_eq V] (P : equipartition V)
open_locale classical

def size : ℕ := card P.parts

def pair_in_partition :
  sym2 (finset V) → Prop :=
quotient.lift (λ (ij : finset V × finset V), ij.1 ∈ P.parts ∧ ij.2 ∈ P.parts)
  (by { rintros _ _ ⟨_, _⟩, { refl }, ext, apply and_comm })

variables (G : simple_graph V) [decidable_rel G.adj]

noncomputable def non_uniform_parts [fintype V] (ε : ℝ) :
  finset (sym2 (finset V)) :=
univ.filter (λ a, pair_in_partition P a ∧ ¬a.is_diag ∧ ¬G.is_uniform_sym2 ε a)

def is_uniform [fintype V] (ε : ℝ) : Prop :=
((P.non_uniform_parts G ε).card : ℝ) ≤ ε * P.size.choose 2

noncomputable def index [fintype V] (P : equipartition V) : ℝ :=
(∑ (i : sym2 (finset V)), if i.is_diag then 0 else (G.density_sym2 i)^2) / P.size ^ 2

theorem index_le_half [fintype V] (P : equipartition V) :
  P.index G ≤ 1/2 :=
begin
  rw [equipartition.index],
  rw le_div_iff,
  rw div_mul_eq_mul_div,
  apply div_le_of_nonneg_of_le_mul,
  { exact pow_nonneg (nat.cast_nonneg _) _ },
  { exact zero_le_one },
  {
    rw [finset.sum_ite, finset.sum_const_zero, zero_add, one_mul],
    have : (∑ (x : sym2 (finset V)) in univ.filter (λ (x : sym2 (finset V)), ¬x.is_diag),
      G.density_sym2 x ^ 2) ≤ (univ.filter (λ (x : sym2 (finset V)), ¬x.is_diag)).card,
    { rw [finset.card_eq_sum_ones, sum_nat_cast, nat.cast_one],
      apply finset.sum_le_sum,
      rintro s _,
      rw [sq, ←abs_le_one_iff_mul_self_le_one, abs_eq_self.2 (G.density_sym2_nonneg _)],
      exact G.density_sym2_le_one _ },
    sorry
  },
  exact zero_lt_two,
end

end equipartition

def exp_bound : ℕ → ℕ := λ n, n * 4^n
/-def iterate_exp (t : ℕ) : ℕ → ℕ
| 0 := t
| (j+1) := iterate_exp j * 4^iterate_exp j-/

/-- An explicit bound in Szemeredi's regularity lemma. -/
noncomputable def szemeredi_bound (ε : ℝ) (l : ℕ) : ℕ :=
let t : ℕ := (max l (ceil (real.log (100 / ε^5) / real.log 4) + 1).nat_abs),
    N : ℕ := exp_bound^[(ceil (4 * ε^(-5 : ℝ))).nat_abs] t
 in N * 16^N

open_locale classical
variables [decidable_eq V] [fintype V] (G : simple_graph V) [decidable_rel G.adj]

/--
The work-horse of SRL. This says that if we have an equipartition which is *not* uniform, then we
can make a (much bigger) equipartition with a higher index.
(This is helpful since the index is bounded by a constant, so this process eventually terminates
and gives a uniform equipartition).
-/
theorem increment (P : equipartition V) (ε : ℝ) (h₁ : P.size * 16^P.size ≤ card V)
  (h₂ : 100 < ε^5 * 4^P.size) (hP : ¬P.is_uniform G ε) :
  ∃ (Q : equipartition V), Q.size = exp_bound P.size ∧ P.index G + ε^5 / 8 ≤ Q.index G :=
begin
  sorry
end

/-- Effective Szemeredi's regularity lemma: For any sufficiently big graph, there is a uniform
equipartition of bounded size (where the bound does not depend on the graph). -/
theorem szemeredi_regularity (ε : ℝ) (hε₁ : 0 < ε) (hε₂ : ε < 1) (l : ℕ) (hG : l ≤ card V) :
  ∃ (P : equipartition V), l ≤ P.size ∧ P.size ≤ szemeredi_bound ε l ∧ P.is_uniform G ε :=
sorry

end
