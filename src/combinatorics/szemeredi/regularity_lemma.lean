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

structure equipartition (V : Type u) [decidable_eq V] :=
(parts : finset (finset V))
(disjoint : ∀ (a₁ a₂ ∈ parts) x, x ∈ a₁ → x ∈ a₂ → a₁ = a₂)
(covering : ∀ v, ∃ (a ∈ parts), v ∈ a) -- TODO: add a lemma saying the union is everything
(sizes : equitable_on (parts : set (finset V)) finset.card)

variables [decidable_eq V]

def equipartition.size (P : equipartition V) : ℕ := card P.parts

variables (G : simple_graph V) [decidable_rel G.adj]

def edges_pair_finset (U W : finset V) : finset (V × V) :=
(U.product W).filter (λ e, G.adj e.1 e.2)

lemma mem_edges_pair_finset (U W : finset V) (x : V × V) :
  x ∈ edges_pair_finset G U W ↔ x.1 ∈ U ∧ x.2 ∈ W ∧ G.adj x.1 x.2 :=
by simp [edges_pair_finset, and_assoc]

lemma mem_edges_pair_finset' (U W : finset V) (x y : V) :
  (x, y) ∈ edges_pair_finset G U W ↔ x ∈ U ∧ y ∈ W ∧ G.adj x y :=
mem_edges_pair_finset _ _ _ _

def edges_count_finset (U W : finset V) : ℕ :=
(edges_pair_finset G U W).card

lemma edges_count_finset_symm (U W : finset V) :
  edges_count_finset G U W = edges_count_finset G W U :=
begin
  apply finset.card_congr (λ (i : V × V) hi, (i.2, i.1)) _ _ _,
  { rintro ⟨i, j⟩ h,
    simp only [mem_edges_pair_finset'] at h ⊢,
    rwa [G.edge_symm, and.left_comm] },
  { rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h₁ h₂ h,
    rcases h,
    refl },
  { rintro ⟨i₁, j₁⟩ h,
    refine ⟨⟨j₁, i₁⟩, _, rfl⟩,
    { simp only [mem_edges_pair_finset'] at h ⊢,
      rwa [G.edge_symm, and.left_comm] } }
end

def edges_count : sym2 (finset V) → ℕ :=
quotient.lift (function.uncurry (edges_count_finset G))
  (by { rintros _ _ ⟨_, _⟩, { refl }, apply edges_count_finset_symm })

noncomputable def density_pair (U W : finset V) : ℝ :=
edges_count_finset G U W / (U.card * W.card)

lemma density_pair_symm (U W : finset V) : density_pair G U W = density_pair G W U :=
begin
  rw [density_pair, mul_comm, edges_count_finset_symm],
  refl
end

noncomputable def density_sym2 : sym2 (finset V) → ℝ :=
quotient.lift (function.uncurry (density_pair G))
  (by { rintros _ _ ⟨_, _⟩, { refl }, apply density_pair_symm })

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

open_locale classical

def pair_in_partition (P : equipartition V) :
  sym2 (finset V) → Prop :=
quotient.lift (λ (ij : finset V × finset V), ij.1 ∈ P.parts ∧ ij.2 ∈ P.parts)
  (by { rintros _ _ ⟨_, _⟩, { refl }, ext, apply and_comm })

noncomputable def equipartition.non_uniform_parts [fintype V] (P : equipartition V) (ε : ℝ) :
  finset (sym2 (finset V)) :=
univ.filter (λ a, pair_in_partition P a ∧ ¬a.is_diag ∧ ¬is_uniform_sym2 G ε a)

def equipartition.is_uniform [fintype V] (P : equipartition V) (ε : ℝ) : Prop :=
((P.non_uniform_parts G ε).card : ℝ) ≤ ε * P.size.choose 2

def iterate_exp (t : ℕ) : ℕ → ℕ
| 0 := t
| (j+1) := iterate_exp j * 4^iterate_exp j

/-- An explicit bound in Szemeredi's regularity lemma. -/
noncomputable def szemeredi_bound (ε : ℝ) (l : ℕ) : ℕ :=
let t : ℕ := (max l (ceil (real.log (100 / ε^5) / real.log 4) + 1).nat_abs),
    N : ℕ := iterate_exp t (ceil (4 * ε^(-5 : ℝ))).nat_abs
 in N * 16^N

noncomputable def equipartition.index [fintype V] (P : equipartition V) : ℝ :=
P.size ^ (-2 : ℝ) * ∑ (i : sym2 (finset V)), if i.is_diag then 0 else (density_sym2 G i)^2

/-- Effective Szemeredi's regularity lemma: For any sufficiently big graph, there is a uniform
equipartition of bounded size (where the bound does not depend on the graph). -/
theorem szemeredi_regularity (ε : ℝ) (hε₁ : 0 < ε) (hε₂ : ε < 1) (l : ℕ)
  {V : Type u} (G : simple_graph V) [fintype V] (hG : l ≤ card V) :
  ∃ (P : equipartition V), l ≤ P.size ∧ P.size ≤ szemeredi_bound ε l ∧ P.is_uniform G ε :=
sorry

end
