import data.real.basic
import combinatorics.simple_graph.basic
import analysis.special_functions.exp_log
import analysis.special_functions.pow

section

open_locale big_operators
open finset fintype

universe u

lemma prod_quotient_sym2_not_diag {α : Type u} [decidable_eq α] (s : finset α) :
  (finset.filter (λ (a : sym2 α), ¬a.is_diag) (finset.image quotient.mk (s.product s))).card =
    s.card.choose 2 :=
begin
  let ordered_pairs : finset (α × α) := (s.product s).filter (λ (x : α × α), ¬(x.1 = x.2)),
  have : ordered_pairs.card = s.card * (s.card - 1),
  { rw [nat.mul_sub_left_distrib, mul_one],
    change finset.card (finset.filter _ _) = _,
    rw [finset.filter_not, card_sdiff (filter_subset _ _), finset.card_product],
    congr' 1,
    refine finset.card_congr (λ (x : _ × _) _, x.1) _ _ _,
    { rintro ⟨x, y⟩ h,
      simp only [mem_filter, mem_product] at h,
      apply h.1.1 },
    { simp only [true_and, prod.forall, mem_filter, mem_product],
      rintro a b ⟨x, y⟩ ⟨⟨_, _⟩, rfl⟩ ⟨_, rfl : x = y⟩ (rfl : a = x),
      refl },
    { simp only [exists_prop, mem_filter, imp_self, exists_and_distrib_right, implies_true_iff,
        exists_eq_right, exists_eq_right', and_self, prod.exists, mem_product] } },
  rw [nat.choose_two_right, ←this],
  symmetry,
  apply nat.div_eq_of_eq_mul_right (show 0 < 2, by norm_num),
  have : ∀ x ∈ ordered_pairs,
    quotient.mk x ∈ ((s.product s).image quotient.mk).filter (λ (a : sym2 α), ¬a.is_diag),
  { rintro ⟨x, y⟩ hx,
    simp only [mem_image, exists_prop, mem_filter, sym2.is_diag_iff_proj_eq, sym2.eq_iff,
      prod.exists, mem_product],
    simp only [mem_filter, mem_product] at hx,
    refine ⟨⟨_, _, hx.1, or.inl ⟨rfl, rfl⟩⟩, hx.2⟩ },
  rw [card_eq_sum_card_fiberwise this, finset.sum_const_nat, mul_comm],
  refine quotient.ind _,
  rintro ⟨x, y⟩ hxy,
  simp only [mem_image, exists_prop, mem_filter, sym2.is_diag_iff_proj_eq, sym2.eq_iff,
    prod.exists, mem_product] at hxy,
  have : x ∈ s ∧ y ∈ s,
  { rcases hxy with ⟨⟨x, y, ⟨_, _⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, _⟩;
    refine ⟨‹_›, ‹_›⟩ },
  have : filter (λ (z : α × α), ⟦z⟧ = ⟦(x, y)⟧) ordered_pairs = ({(x,y), (y,x)} : finset _),
  { ext ⟨x₁, y₁⟩,
    simp only [true_and, mem_filter, mem_insert, mem_product, mem_singleton, sym2.eq_iff,
      and_iff_right_iff_imp, prod.mk.inj_iff],
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩),
    { refine ⟨‹_›, hxy.2⟩, },
    refine ⟨⟨this.2, this.1⟩, ne.symm hxy.2⟩ },
  rw [this, card_insert_of_not_mem, card_singleton],
  simp only [not_and, prod.mk.inj_iff, mem_singleton],
  rintro rfl,
  apply hxy.2
end

lemma card_sym2_not_diag {α : Type u} [decidable_eq α] [fintype α] :
  (univ.filter (λ (a : sym2 α), ¬a.is_diag)).card = (card α).choose 2 :=
prod_quotient_sym2_not_diag (univ : finset α)

lemma sym2.injective {α : Type u} : function.injective (sym2.diag : α → sym2 α) :=
begin
  rintro x y (h : ⟦_⟧ = ⟦_⟧),
  rw sym2.eq_iff at h,
  simpa using h
end

lemma card_sym2 {α : Type u} [decidable_eq α] [fintype α] :
  card (sym2 α) = card α * (card α + 1) / 2 :=
begin
  have : univ.filter (λ (x : sym2 α), x.is_diag) = univ.image sym2.diag,
  { ext,
    simp [sym2.is_diag] },
  rw [←finset.card_univ, ←filter_union_filter_neg_eq sym2.is_diag (univ : finset (sym2 α)),
    card_disjoint_union, this, card_image_of_injective _ sym2.injective, card_sym2_not_diag,
    nat.choose_two_right, finset.card_univ, add_comm, ←nat.triangle_succ, nat.succ_sub_one,
    mul_comm],
  rw disjoint_iff_inter_eq_empty,
  apply filter_inter_filter_neg_eq,
end

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
  intros hf a₁ a₂ ha₁ ha₂ _,
  apply hf ha₁ ha₂
end

namespace simple_graph
variables {V : Type u} [decidable_eq V] (G : simple_graph V) [decidable_rel G.adj]

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
  refine div_le_one_of_le _ (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)),
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
variables {V : Type u} [decidable_eq V] (P : equipartition V)

/-lemma Union_eq_univ : (⋃ (s : finset V) (s ∈ P.parts), s) : set V) = set.univ :=
begin

end-/

protected def size : ℕ := card P.parts

def distinct_unordered_pairs [fintype V] (P : equipartition V) :
  finset (sym2 (finset V)) :=
((P.parts.product P.parts).image quotient.mk).filter (λ (a : sym2 _), ¬a.is_diag)

lemma mem_distinct_unordered_pairs [fintype V] (P : equipartition V)
  (U W : finset V) :
  ⟦(U, W)⟧ ∈ P.distinct_unordered_pairs ↔ U ∈ P.parts ∧ W ∈ P.parts ∧ U ≠ W :=
begin
  rw [equipartition.distinct_unordered_pairs, finset.mem_filter],
  simp only [mem_image, exists_prop, sym2.is_diag_iff_proj_eq, sym2.eq_iff, prod.exists,
    mem_product],
  split,
  { rintro ⟨⟨U, W, ⟨hU, hW⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩, _⟩;
    exact ⟨‹_›, ‹_›, ‹_›⟩ },
  { rintro ⟨h₁, h₂, h₃⟩,
    exact ⟨⟨_, _, ⟨h₁, h₂⟩, or.inl ⟨rfl, rfl⟩⟩, h₃⟩ }
end

lemma distinct_unordered_pairs_size [fintype V] (P : equipartition V) :
  P.distinct_unordered_pairs.card = P.size.choose 2 :=
by rw [distinct_unordered_pairs, equipartition.size, prod_quotient_sym2_not_diag]

variables (G : simple_graph V)
open_locale classical

noncomputable def non_uniform_parts [fintype V] (ε : ℝ) :
  finset (sym2 (finset V)) :=
P.distinct_unordered_pairs.filter (λ a, ¬G.is_uniform_sym2 ε a)

--doesn't work TODO: make a MWE
--#print non_uniform_parts

def is_uniform [fintype V] (ε : ℝ) : Prop :=
((P.non_uniform_parts G ε).card : ℝ) ≤ ε * P.size.choose 2

noncomputable def index [fintype V] (P : equipartition V) : ℝ :=
(∑ (i : sym2 (finset V)), if i.is_diag then 0 else (G.density_sym2 i)^2) / P.size ^ 2

theorem index_le_half [fintype V] (P : equipartition V) :
  P.index G ≤ 1/2 :=
begin
  rw [equipartition.index, le_div_iff, div_mul_eq_mul_div],
  apply div_le_of_nonneg_of_le_mul,
  { exact pow_nonneg (nat.cast_nonneg _) _ },
  { exact zero_le_one },
  { rw [finset.sum_ite, finset.sum_const_zero, zero_add, one_mul],
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

/-! ### Discrete and dummy equipartitions -/

@[simps]
def discrete_equipartition (V : Type*) [decidable_eq V] [fintype V] : equipartition V :=
{ parts := finset.univ.image singleton,
  disjoint :=
  begin
    simp only [mem_image, mem_univ, exists_true_left, exists_imp_distrib],
    rintro a₁ a₂ i ⟨⟩ rfl j ⟨⟩ rfl k,
    simp only [mem_singleton],
    rintro rfl rfl,
    refl
  end,
  covering := λ v, ⟨{v}, by simp, by simp⟩,
  sizes := λ a b,
  begin
    simp only [set.image_univ, set.mem_range, coe_univ, exists_imp_distrib, coe_image],
    rintro _ rfl _ rfl,
    simp only [implies_true_iff, zero_le', card_singleton],
  end }

namespace discrete_equipartition
variables {V : Type u} [decidable_eq V] [fintype V] (G : simple_graph V)

protected lemma size : (discrete_equipartition V).size = card V :=
begin
  change finset.card (finset.univ.image _) = _,
  rw [finset.card_image_of_injective, finset.card_univ],
  intros i j k,
  rwa singleton_inj at k,
end

open equipartition -- used for `rw non_uniform_parts at hUW`. Shouldn't be though...

lemma non_uniform_parts {ε : ℝ} (hε : 0 < ε) :
  (discrete_equipartition V).non_uniform_parts G ε = ∅ :=
begin
  rw eq_empty_iff_forall_not_mem,
  intro x,
  apply quotient.induction_on x,
  rintro ⟨U, W⟩ hUW,
  rw [non_uniform_parts, finset.mem_filter, mem_distinct_unordered_pairs,
    discrete_equipartition_parts, mem_image, mem_image] at hUW, --problem with `non_uniform_parts`
  apply hUW.2,
  rintro U' (hU' : U' ⊆ U) W' (hW' : W' ⊆ W) (hU : ε * U.card ≤ _) (hW : ε * W.card ≤ _),
  obtain ⟨⟨x, _, rfl⟩, ⟨y, _, rfl⟩, t⟩ := hUW.1,
  rw [card_singleton, nat.cast_one, mul_one] at hU hW,
  obtain rfl | rfl := finset.subset_singleton_iff.1 hU',
  { rw [finset.card_empty, nat.cast_zero] at hU,
    exfalso,
    exact hε.not_le hU },
  obtain rfl | rfl := finset.subset_singleton_iff.1 hW',
  { rw [finset.card_empty, nat.cast_zero] at hW,
    exfalso,
    exact hε.not_le hW },
  rw [sub_self, abs_zero],
  exact hε,
end

def is_uniform {ε : ℝ} (hε : 0 < ε) :
  (discrete_equipartition V).is_uniform G ε :=
begin
  rw [is_uniform, discrete_equipartition.size, discrete_equipartition.non_uniform_parts _ hε,
    finset.card_empty, nat.cast_zero],--problem with `is_uniform`
  exact mul_nonneg hε.le (nat.cast_nonneg _),
end

end discrete_equipartition

/-- Arbitrary equipartition into `n` parts -/
@[simps]
def dummy_equipartition (V : Type*) [decidable_eq V] [fintype V] (n : ℕ) : equipartition V :=
{ parts := finset.univ.image singleton,
  disjoint :=
  begin
    simp only [mem_image, mem_univ, exists_true_left, exists_imp_distrib],
    rintro a₁ a₂ i ⟨⟩ rfl j ⟨⟩ rfl k,
    simp only [mem_singleton],
    rintro rfl rfl,
    refl
  end,
  covering := λ v, ⟨{v}, by simp, by simp⟩,
  sizes := λ a b,
  begin
    simp only [set.image_univ, set.mem_range, coe_univ, exists_imp_distrib, coe_image],
    rintro _ rfl _ rfl,
    simp only [implies_true_iff, zero_le', card_singleton],
  end }

protected lemma dummy_equipartition.size {V : Type u} [decidable_eq V] [fintype V] {n : ℕ} :
  (dummy_equipartition V n).size = n :=
begin
  sorry,
end

/-! ### The actual proof -/

def exp_bound : ℕ → ℕ := λ n, n * 4^n

lemma le_exp_bound (n : ℕ) :
  n ≤ exp_bound n :=
nat.le_mul_of_pos_right (pow_pos (by norm_num) n)

/-- An explicit bound in Szemeredi's regularity lemma. -/
noncomputable def szemeredi_bound (ε : ℝ) (l : ℕ) : ℕ :=
let t : ℕ := max l (⌈real.log (100 / ε^5) / real.log 4⌉ + 1).nat_abs,
    N : ℕ := exp_bound^[⌈4 * ε^(-5 : ℝ)⌉.nat_abs] t
 in N * 16^N

open_locale classical
variables {V : Type u} [fintype V] (G : simple_graph V)
include G

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

open discrete_equipartition

--have the problem that I must prove stuff (namely the equivalent of `hl`) while defining data
/-/-- The equipartition refinement operation -/
def szemeredi_equipartition {ε : ℝ} {l : ℕ} (hl : 100 < ε ^ 5 * 4^l) : ℕ → equipartition V
| 0       := dummy_equipartition V l
| (n + 1) := dite ((szemeredi_equipartition n).size * 16 ^ (szemeredi_equipartition n).size ≤ card V)
  begin
    intro h,
    have := increment G (szemeredi_equipartition n) ε h,
  end
  (λ _, discrete_equipartition V) --this can probably be changed to something smarter-/

/-- Effective Szemeredi's regularity lemma: For any sufficiently big graph, there is a uniform
equipartition of bounded size (where the bound does not depend on the graph). -/
theorem szemeredi_regularity {ε : ℝ} (hε₁ : 0 < ε) (hε₂ : ε < 1) (l : ℕ) (hG : l ≤ card V) :
  ∃ (P : equipartition V), l ≤ P.size ∧ P.size ≤ szemeredi_bound ε l ∧ P.is_uniform G ε :=
begin
  cases le_total (card V) (szemeredi_bound ε l),
  { use discrete_equipartition V,
    sorry
    --rw discrete_equipartition.size, --beurk, again the same problem
    --exact ⟨hG, h, discrete_partition.is_uniform G hε₁⟩
    },
  --use szemeredi_equipartition ???,
  sorry
end

end
