import combinatorics.simple_graph.ramsey
import order.partition.finpartition
import data.finset.locally_finite
import analysis.special_functions.explicit_stirling
import analysis.asymptotics.asymptotics
import data.complex.exponential_bounds

open finset
namespace simple_graph

open_locale big_operators
open fintype (card)

variables {V : Type*} {G G₁ G₂ : simple_graph V}

lemma card_filter_not_diag {α : Type*} [fintype α] [decidable_eq α] :
  (finset.univ.filter (λ a : sym2 α, ¬ sym2.is_diag a)).card = (card α).choose 2 :=
by rw [←sym2.card_subtype_not_diag, fintype.card_subtype]

lemma edge_set_top :
  (⊤ : simple_graph V).edge_set = {a : sym2 V | ¬ sym2.is_diag a} :=
begin
  ext e,
  induction e using sym2.induction_on with x y,
  simp,
end

@[simp] lemma edge_finset_bot' [decidable_eq V]
  [fintype (edge_set (⊥ : simple_graph V))] :
  (⊥ : simple_graph V).edge_finset = ∅ :=
by simp [edge_finset]

@[simp] lemma edge_finset_sup' [decidable_eq V]
  [fintype (edge_set G₁)] [fintype (edge_set G₂)] [fintype (edge_set (G₁ ⊔ G₂))]:
  (G₁ ⊔ G₂).edge_finset = G₁.edge_finset ∪ G₂.edge_finset :=
by simp [edge_finset]

@[simp] lemma edge_finset_inf' [decidable_eq V]
  [fintype (edge_set G₁)] [fintype (edge_set G₂)] [fintype (edge_set (G₁ ⊓ G₂))] :
  (G₁ ⊓ G₂).edge_finset = G₁.edge_finset ∩ G₂.edge_finset :=
by simp [edge_finset]

@[simp] lemma edge_finset_sdiff' [decidable_eq V]
  [fintype (edge_set G₁)] [fintype (edge_set G₂)] [fintype (edge_set (G₁ \ G₂))] :
  (G₁ \ G₂).edge_finset = G₁.edge_finset \ G₂.edge_finset :=
by simp [edge_finset]

lemma edge_finset_top [fintype V] [decidable_eq V] :
  (⊤ : simple_graph V).edge_finset = univ.filter (λ a : sym2 V, ¬ sym2.is_diag a) :=
begin
  refine coe_injective _,
  rw [coe_edge_finset, edge_set_top, coe_filter_univ],
end

lemma edge_finset_top_card [fintype V] [decidable_eq V] :
  (⊤ : simple_graph V).edge_finset.card = (card V).choose 2 :=
by rw [edge_finset_card, card_top_edge_set]

lemma edge_finset_card_le [fintype V] [fintype G.edge_set] :
  G.edge_finset.card ≤ (card V).choose 2 :=
begin
  classical,
  rw [←edge_finset_top_card],
  exact card_le_of_subset (edge_finset_mono le_top),
end

lemma compl_edge_set_eq : edge_set Gᶜ = {x : sym2 V | ¬x.is_diag} \ edge_set G :=
by rw [←edge_set_top, ←edge_set_sdiff, top_sdiff]

lemma compl_edge_set_eq' : edge_set G = {x : sym2 V | ¬x.is_diag} \ edge_set Gᶜ :=
by rw [←edge_set_top, ←edge_set_sdiff, top_sdiff, compl_compl]

lemma compl_edge_finset_eq [fintype V] [decidable_eq V] [fintype G.edge_set] [fintype Gᶜ.edge_set] :
  Gᶜ.edge_finset = univ.filter (λ a : sym2 V, ¬ sym2.is_diag a) \ G.edge_finset :=
begin
  refine coe_injective _,
  rw [coe_edge_finset, coe_sdiff, coe_edge_finset, coe_filter_univ, compl_edge_set_eq],
end

lemma compl_edge_finset_eq'
  [fintype V] [decidable_eq V] [fintype G.edge_set] [fintype Gᶜ.edge_set] :
  G.edge_finset = univ.filter (λ a : sym2 V, ¬ sym2.is_diag a) \ Gᶜ.edge_finset :=
begin
  refine coe_injective _,
  rw [coe_edge_finset, coe_sdiff, coe_edge_finset, coe_filter_univ, compl_edge_set_eq'],
end

lemma card_compl_edge_finset_eq
  [fintype V] [fintype G.edge_set] [fintype Gᶜ.edge_set] :
  Gᶜ.edge_finset.card = (card V).choose 2 - G.edge_finset.card :=
begin
  classical,
  rw [compl_edge_finset_eq, card_sdiff, card_filter_not_diag],
  simp only [subset_iff, mem_edge_finset, mem_filter, mem_univ, true_and],
  apply not_is_diag_of_mem_edge_set
end

lemma card_edge_finset_eq_sub_compl'
  [fintype V] [fintype G.edge_set] [fintype Gᶜ.edge_set] :
  G.edge_finset.card = (card V).choose 2 - Gᶜ.edge_finset.card :=
begin
  classical,
  rw [compl_edge_finset_eq', card_sdiff, card_filter_not_diag],
  simp only [subset_iff, mem_edge_finset, mem_filter, mem_univ, true_and],
  apply not_is_diag_of_mem_edge_set
end

variables [fintype V] {p : ℝ} {s : finset (sym2 V)}

def weighting_aux (p : ℝ) (s : finset (sym2 V)) : ℝ :=
p ^ s.card * (1 - p) ^ ((card V).choose 2 - s.card)

lemma weighting_aux_pos (hp₀ : 0 < p) (hp₁ : p < 1) : 0 < weighting_aux p s :=
mul_pos (pow_pos hp₀ _) (pow_pos (sub_pos_of_lt hp₁) _)

def weighting (V : Type*) [fintype V] (p : ℝ) (G : simple_graph V) [fintype G.edge_set] :
  ℝ := weighting_aux p G.edge_finset

lemma weighting_pos [fintype G.edge_set] (hp₀ : 0 < p) (hp₁ : p < 1) :
  0 < weighting V p G :=
weighting_aux_pos hp₀ hp₁

lemma weighting_eq [fintype G.edge_set] [fintype Gᶜ.edge_set] :
  weighting V p G = p ^ G.edge_finset.card * (1 - p) ^ Gᶜ.edge_finset.card :=
by rw [weighting, weighting_aux, card_compl_edge_finset_eq]

lemma weighting_compl [fintype G.edge_set] [fintype Gᶜ.edge_set] :
  weighting V (1 - p) Gᶜ = weighting V p G :=
begin
  rw [weighting, weighting, weighting_aux, weighting_aux, sub_sub_self,
    ←card_edge_finset_eq_sub_compl', ←card_compl_edge_finset_eq, mul_comm],
end

lemma disj_union_inj_left {α : Type*} {s t₁ t₂ : finset α}
  {hst₁ : disjoint s t₁} {hst₂ : disjoint s t₂} :
  disj_union s t₁ hst₁ = disj_union s t₂ hst₂ → t₁ = t₂ :=
begin
  intro h,
  ext i,
  wlog h' : i ∈ t₁,
  { simp only [h', false_iff],
    intro h'',
    apply h',
    exact (this h.symm i h'').1 h'' },
  simp only [h', true_iff],
  have : i ∈ s.disj_union t₁ hst₁,
  { rw mem_disj_union,
    exact or.inr h' },
  rw [h, mem_disj_union] at this,
  exact this.resolve_left (finset.disjoint_right.1 hst₁ h'),
end

lemma disj_union_inj_right {α : Type*} {s₁ s₂ t : finset α}
  {hst₁ : disjoint s₁ t} {hst₂ : disjoint s₂ t} :
  disj_union s₁ t hst₁ = disj_union s₂ t hst₂ → s₁ = s₂ :=
begin
  intro h,
  rw [disj_union_comm s₁, disj_union_comm s₂] at h,
  exact disj_union_inj_left h,
end

local attribute [instance] fintype.to_locally_finite_order

section

open_locale classical

lemma weighting_aux_sum_between [decidable_eq V] (H₁ H₂ : simple_graph V) (h : H₁ ≤ H₂) :
  ∑ G in finset.Icc H₁ H₂, weighting V p G =
    p ^ H₁.edge_finset.card * (1 - p) ^ H₂ᶜ.edge_finset.card :=
begin
  simp only [weighting],
  rw ←finset.sum_image,
  swap,
  { simp },
  have h₁ : (Icc H₁ H₂).image (λ G, G.edge_finset) =
    (H₁ᶜ ⊓ H₂).edge_finset.powerset.image (λ s, s ∪ H₁.edge_finset),
  { ext s,
    simp only [mem_image, mem_powerset, mem_Icc, exists_prop, compl_sup, edge_set_inf,
      set.subset_to_finset, set.subset_inter_iff, and_assoc, compl_compl],
    split,
    { rintro ⟨G, hG₁, hG₂, rfl⟩,
      refine ⟨(G \ H₁).edge_finset, _, _, _⟩,
      { rw [coe_edge_finset, sdiff_eq, edge_set_subset_edge_set],
        exact inf_le_right },
      { rw [coe_edge_finset, edge_set_subset_edge_set],
        exact sdiff_le.trans hG₂ },
      rwa [←edge_finset_sup', ←coe_inj, coe_edge_finset, coe_edge_finset, sdiff_sup_cancel] },
    rintro ⟨s, hs₁, hs₂, rfl⟩,
    refine ⟨from_edge_set s ⊔ H₁, le_sup_right, sup_le _ h, _⟩,
    { exact (from_edge_set_mono hs₂).trans_eq (from_edge_set_edge_set _) },
    rw [←coe_inj, coe_union, coe_edge_finset, coe_edge_finset, edge_set_sup,
      edge_set_from_edge_set, sdiff_eq_left.2],
    rw set.disjoint_left,
    intros e he,
    exact not_is_diag_of_mem_edge_set _ (hs₁ he) },
  rw [h₁, finset.sum_image],
  swap,
  { simp only [edge_finset_inf', mem_powerset, subset_inter_iff, and_imp, compl_edge_finset_eq,
      subset_sdiff],
    rintro G - hG₁ hG₂ G' - hG'₁ hG'₂ h',
    rw [←disj_union_eq_union _ _ hG₁, ←disj_union_eq_union _ _ hG'₁] at h',
    exact disj_union_inj_right h' },
  have h₂ : ∀ x ∈ (H₁ᶜ ⊓ H₂).edge_finset.powerset, disjoint x H₁.edge_finset,
  { intro x,
    simp only [edge_finset_inf', mem_powerset, subset_inter_iff, compl_edge_finset_eq, subset_sdiff,
      implies_true_iff, and_imp, and_assoc] {contextual := tt} },
  simp only [weighting_aux],
  have : (H₁ᶜ ⊓ H₂).edge_finset.card + H₁.edge_finset.card = H₂.edge_finset.card,
  { rw [←card_union_eq, ←edge_finset_sup'],
    congr' 1,
    { rwa [←coe_inj, coe_edge_finset, coe_edge_finset, inf_comm, ←sdiff_eq, sdiff_sup_cancel] },
    rw [←disjoint_coe, coe_edge_finset, coe_edge_finset, set.disjoint_iff_inter_eq_empty,
      ←edge_set_inf, @inf_comm _ _ H₁ᶜ, inf_assoc, compl_inf_eq_bot, inf_bot_eq, edge_set_bot] },
  have h₃ : (H₁ᶜ ⊓ H₂).edge_finset.card = H₂.edge_finset.card - H₁.edge_finset.card,
  { rw [←this, nat.add_sub_cancel] },
  have :
    (p ^ H₁.edge_finset.card * (1 - p) ^ H₂ᶜ.edge_finset.card) *
      (∑ x in (H₁ᶜ ⊓ H₂).edge_finset.powerset,
        p ^ x.card * (1 - p) ^ ((H₁ᶜ ⊓ H₂).edge_finset.card - x.card)) =
          (p ^ H₁.edge_finset.card * (1 - p) ^ H₂ᶜ.edge_finset.card),
  { rw [finset.sum_pow_mul_eq_add_pow p (1 - p) (H₁ᶜ ⊓ H₂).edge_finset, add_sub_cancel'_right,
      one_pow, mul_one] },
  rw [←this, mul_comm, sum_mul],
  refine sum_congr rfl (λ x hx, _),
  rw [mul_mul_mul_comm, ←pow_add, ←pow_add, card_union_eq (h₂ x hx)],
  congr' 2,
  rw [h₃, card_compl_edge_finset_eq, tsub_tsub, add_comm, add_comm (_ - _), tsub_add_tsub_cancel],
  { apply edge_finset_card_le },
  rw [add_comm, ←card_union_eq (h₂ x hx)],
  refine card_le_of_subset _,
  rw [mem_powerset, edge_finset_inf, subset_inter_iff] at hx,
  exact union_subset hx.2 (edge_finset_subset_edge_finset.2 h),
end

lemma sum_weighting : ∑ G, weighting V p G = 1 :=
begin
  have : Icc (⊥ : simple_graph V) ⊤ = finset.univ,
  { rw [←coe_inj, coe_Icc, set.Icc_bot_top, coe_univ] },
  rw [←this, weighting_aux_sum_between ⊥ ⊤ bot_le, edge_finset_bot', edge_finset_card],
  simp only [compl_top, edge_set_bot, set.empty_card, card_empty, pow_zero, pow_zero, mul_one],
end

end

lemma card_edge_set_map {V V' : Type*} (f : V ↪ V') (G : simple_graph V)
  [fintype (edge_set G)] [fintype (edge_set (G.map f))] :
  card (G.map f).edge_set = card G.edge_set :=
begin
  let f' := simple_graph.embedding.map_edge_set (embedding.map f G),
  have : function.bijective f',
  { refine ⟨f'.injective, _⟩,
    rintro ⟨x, hx⟩,
    induction x using sym2.induction_on with x y,
    simp only [embedding.map_edge_set_apply, set_coe.exists, sym2.exists, mem_edge_set, exists_prop,
      subtype.ext_iff, hom.map_edge_set_coe, rel_embedding.coe_coe_fn, embedding.map_apply,
      function.embedding.to_fun_eq_coe, subtype.coe_mk, sym2.map_pair_eq],
    simp only [mem_edge_set, map_adj] at hx,
    obtain ⟨x, y, huv, rfl, rfl⟩ := hx,
    exact ⟨x, y, huv, rfl⟩ },
  exact (fintype.card_of_bijective this).symm,
end

def clique_on (G : simple_graph V) (s : set V) : Prop :=
spanning_coe (⊤ : simple_graph s) ≤ G

def indep_on (G : simple_graph V) (t : set V) : Prop :=
G ≤ (spanning_coe (⊤ : simple_graph t))ᶜ

lemma clique_on_compl (s : set V) : clique_on Gᶜ s ↔ indep_on G s :=
by rw [clique_on, indep_on, le_compl_comm]

lemma indep_on_iff {t : set V} : indep_on G t ↔ disjoint G (spanning_coe (⊤ : simple_graph t)) :=
by rw [indep_on, le_compl_iff_disjoint_right]

instance decidable_adj_map {V' : Type*} [decidable_eq V'] {G : simple_graph V}
  [decidable_rel G.adj] {f : V ↪ V'} : decidable_rel (G.map f).adj :=
λ x y, decidable_of_iff' _ (G.map_adj f _ _)

lemma card_edge_set_spanning_coe_top [decidable_eq V] (s : finset V) :
  fintype.card (spanning_coe (⊤ : simple_graph s)).edge_set = s.card.choose 2 :=
begin
  rw [card_edge_set_map, card_top_edge_set],
  change (fintype.card (s : Type*)).choose 2 = _,
  rw fintype.card_coe,
end

instance decidable_le {H : simple_graph V} [decidable_rel G.adj] [decidable_rel H.adj] :
  decidable (G ≤ H) :=
fintype.decidable_forall_fintype

instance decidable_pred_clique_on [decidable_eq V] [decidable_rel G.adj] :
  decidable_pred (λ s : finset V, clique_on G s) :=
λ s, simple_graph.decidable_le

instance decidable_pred_indep_on [decidable_eq V] [decidable_rel G.adj] :
  decidable_pred (λ s : finset V, indep_on G s) :=
λ s, simple_graph.decidable_le

lemma le.def {G H : simple_graph V} : G ≤ H ↔ ∀ ⦃x y : V⦄, G.adj x y → H.adj x y := iff.rfl

lemma fin.fin_two_eq_zero_iff_ne_one {x : fin 2} : x = 0 ↔ x ≠ 1 :=
begin
  revert x,
  rw fin.forall_fin_two,
  simp
end

lemma clique_on_monochromatic_of {K : Type*} (C : top_edge_labelling V K) (k : K) (m : set V) :
  clique_on (C.label_graph k) m ↔ C.monochromatic_of m k :=
begin
  simp only [clique_on, top_edge_labelling.monochromatic_of, le.def, map_adj, set_coe.exists,
    top_edge_labelling.label_graph_adj, function.embedding.coe_subtype, subtype.coe_mk, top_adj,
    ne.def, subtype.mk_eq_mk, forall_exists_index, and_imp],
  split,
  { intros h x hx y hy h',
    obtain ⟨_, z⟩ := h x hx y hy h' rfl rfl,
    exact z },
  { rintro h x y a ha b hb hab rfl rfl,
    exact ⟨hab, h ha hb _⟩ },
end

lemma label_graph_fin_two_compl (C : top_edge_labelling V (fin 2)) :
  (C.label_graph 1)ᶜ = C.label_graph 0 :=
begin
  classical,
  rw [←label_graph_to_edge_labelling C, to_edge_labelling_label_graph,
    to_edge_labelling_label_graph_compl],
end

lemma indep_on_monochromatic_of (C : top_edge_labelling V (fin 2)) (m : set V) :
  indep_on (C.label_graph 1) m ↔ C.monochromatic_of m 0 :=
by rw [←clique_on_compl, label_graph_fin_two_compl, clique_on_monochromatic_of]

def number_of_cliques [decidable_eq V] (G : simple_graph V) [decidable_rel G.adj] (k : ℕ) : ℕ :=
((univ.powerset_len k).filter (λ (s : finset V), G.clique_on s)).card

def number_of_indeps [decidable_eq V] (G : simple_graph V) [decidable_rel G.adj] (l : ℕ) : ℕ :=
((univ.powerset_len l).filter (λ (s : finset V), G.indep_on s)).card

lemma number_of_cliques_compl [decidable_eq V] [decidable_rel G.adj] [decidable_rel Gᶜ.adj]
  {k : ℕ} :
  number_of_cliques Gᶜ k = number_of_indeps G k :=
begin
  rw [number_of_cliques, number_of_indeps],
  simp only [clique_on_compl],
end

def number_of_things [decidable_eq V] (G : simple_graph V) [decidable_rel G.adj] (k l : ℕ) : ℕ :=
G.number_of_cliques k + G.number_of_indeps l

section

open_locale classical

lemma weighted_number_cliques [decidable_eq V] {k : ℕ} :
  ∑ G, weighting V p G * G.number_of_cliques k = ((card V).choose k) * p ^ k.choose 2 :=
begin
  simp_rw [number_of_cliques, card_eq_sum_ones, nat.cast_sum, nat.cast_one, sum_filter, mul_sum,
    @sum_comm _ (finset V), mul_boole, ←sum_filter],
  rw [←nsmul_eq_mul, ←card_univ, ←card_powerset_len, ←sum_const],
  refine sum_congr rfl _,
  intros x hx,
  have :
    univ.filter (λ a : simple_graph V, a.clique_on x) = Icc (spanning_coe (⊤ : simple_graph x)) ⊤,
  { ext G,
    simp only [mem_filter, mem_univ, true_and, mem_Icc, le_top, and_true, clique_on] },
  rw [this],
  have : ∑ (G : simple_graph V) in _, weighting V p G = _ :=
    weighting_aux_sum_between (spanning_coe (⊤ : simple_graph x)) ⊤ le_top,
  rw [edge_finset_card, edge_finset_card] at this,
  simp only [compl_top, edge_set_bot, set.empty_card', pow_zero, mul_one] at this,
  convert this using 2,
  { congr' 1 },
  refine eq.symm _,
  convert (card_edge_set_spanning_coe_top x).trans _ using 1,
  { convert fintype.card_congr' _,
    refl },
  rw mem_powerset_len_univ_iff at hx,
  rw hx
end

lemma weighted_number_indeps [decidable_eq V] {k : ℕ} :
  ∑ G, weighting V p G * G.number_of_indeps k = ((card V).choose k) * (1 - p) ^ k.choose 2 :=
begin
  simp only [←number_of_cliques_compl],
  simp only [←@weighting_compl _ _ _ p],
  rw ←weighted_number_cliques,
  refine (sum_bij' (λ G _, Gᶜ) (λ _ _, mem_univ _) _ (λ G _, Gᶜ) (λ _ _, mem_univ _) _ _),
  { intros a ha,
    refine congr_arg2 (*) _ _,
    { congr' 1, },
    { refine congr_arg _ _,
      change finset.card _ = finset.card _,
      refine congr_arg _ _,
      ext i,
      refine mem_filter.trans _,
      rw mem_filter } },
  { intros a ha,
    rw compl_compl },
  { intros a ha,
    rw compl_compl },
end

lemma weighted_number_things [decidable_eq V] {k l : ℕ} :
  ∑ G, weighting V p G * G.number_of_things k l =
    (card V).choose k * p ^ k.choose 2 + (card V).choose l * (1 - p) ^ l.choose 2 :=
by simp only [number_of_things, nat.cast_add, mul_add, sum_add_distrib, weighted_number_cliques,
  weighted_number_indeps]

end

lemma basic_bound {k l : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < 1)
  (hV : ((card V).choose k : ℝ) * p ^ k.choose 2 + (card V).choose l * (1 - p) ^ l.choose 2 < 1) :
  ∃ (G : simple_graph V),
    (∀ X : finset V, X.card = k → ¬ G.clique_on X) ∧
    (∀ X : finset V, X.card = l → ¬ G.indep_on X) :=
begin
  letI := classical.dec_eq V,
  by_contra',
  refine hV.not_le _,
  rw [←weighted_number_things, ←@sum_weighting V _ p],
  refine sum_le_sum _,
  intros i hi,
  refine le_mul_of_one_le_right _ _,
  swap,
  { rw [nat.one_le_cast, number_of_things, nat.succ_le_iff, add_pos_iff, number_of_cliques,
      number_of_indeps, card_pos, card_pos, filter_nonempty_iff, filter_nonempty_iff],
    simp only [exists_prop, mem_powerset_len_univ_iff, or_iff_not_imp_left, not_exists, not_and],
    exact this _ },
  letI := classical.dec_rel i.adj,
  exact (weighting_pos hp hp').le,
end

lemma basic_ramsey_bound {k l n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < 1)
  (hV : (n.choose k : ℝ) * p ^ k.choose 2 + n.choose l * (1 - p) ^ l.choose 2 < 1) :
  n < ramsey_number ![k, l] :=
begin
  let V := fin n,
  rw ←fintype.card_fin n,
  rw ←fintype.card_fin n at hV,
  rw [←not_le, ramsey_number_pair_swap, ramsey_number_le_iff, is_ramsey_valid_iff_eq],
  intros h,
  obtain ⟨G, hG₁, hG₂⟩ := basic_bound hp hp' hV,
  letI := classical.dec_rel G.adj,
  let C := G.to_edge_labelling,
  obtain ⟨m, hm⟩ := h C,
  rw [fin.exists_fin_two, matrix.cons_val_zero, matrix.cons_val_one, matrix.head_cons,
    ←indep_on_monochromatic_of, ←clique_on_monochromatic_of, to_edge_labelling_label_graph] at hm,
  cases hm,
  { exact hG₂ m hm.2.symm hm.1 },
  { exact hG₁ m hm.2.symm hm.1 }
end

open real

lemma sq_div_four_le_choose_two {k : ℕ} (hk : 2 ≤ k) : (k ^ 2 / 4 : ℝ) ≤ k.choose 2 :=
begin
  rw [nat.cast_choose_two, sq, mul_div_assoc, mul_div_assoc],
  refine mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
  have : (2 : ℝ) ≤ k := by exact_mod_cast hk,
  linarith,
end

-- meant to be used when p *very* small
lemma basic_off_diagonal_ramsey_bound {k l n : ℕ} {p : ℝ} (hp : 0 < p) (hp' : p < 1)
  (hk : 2 ≤ k) (hl : 2 ≤ l)
  (hV : (n : ℝ) ^ k * p ^ (k ^ 2 / 4 : ℝ) + n ^ l * exp (-p * l ^ 2 / 4) < 1) :
  n < ramsey_number ![k, l] :=
begin
  refine basic_ramsey_bound hp hp' (hV.trans_le' (add_le_add _ _)),
  { refine mul_le_mul _ _ (by positivity) (by positivity),
    { refine (nat.choose_le_pow _ _).trans _,
      refine div_le_self (by positivity) _,
      rw [nat.one_le_cast, nat.succ_le_iff],
      exact nat.factorial_pos _ },
    { rw ←rpow_nat_cast,
      exact rpow_le_rpow_of_exponent_ge hp hp'.le (sq_div_four_le_choose_two hk) } },
  { refine mul_le_mul _ _ _ (by positivity),
    { refine (nat.choose_le_pow _ _).trans _,
      refine div_le_self (by positivity) _,
      rw [nat.one_le_cast, nat.succ_le_iff],
      exact nat.factorial_pos _ },
    { refine (pow_le_pow_of_le_left (by linarith) (one_sub_le_exp_minus_of_pos hp.le) _).trans _,
      rw [←rpow_nat_cast, ←exp_one_rpow, ←rpow_mul (exp_pos _).le, exp_one_rpow, exp_le_exp,
        mul_div_assoc],
      refine mul_le_mul_of_nonpos_left _ (by simpa using hp.le),
      exact sq_div_four_le_choose_two hl },
    exact pow_nonneg (by linarith) _ }
end

lemma basic_diagonal_ramsey_bound {k n : ℕ} (hV : (n.choose k : ℝ) * 2 ^ (1 - k.choose 2 : ℝ) < 1) :
  n < diagonal_ramsey k :=
begin
  refine basic_ramsey_bound (show 0 < (2 : ℝ)⁻¹, by norm_num) (by norm_num) _,
  norm_num1,
  rwa [one_div, ←two_mul, ←real.rpow_nat_cast, mul_left_comm, real.inv_rpow, ←real.rpow_neg,
    mul_comm (2 : ℝ), ←real.rpow_add_one, add_comm, ←sub_eq_add_neg];
  norm_num1
end

lemma diagonal_ramsey_bound_refined_aux {n k : ℕ} (hk : k ≠ 0)
  (hn : (n : ℝ) ≤ (exp 1 * sqrt 2)⁻¹ * 2 ^ (- 1 / k : ℝ) * k * (sqrt 2) ^ k) :
  n < diagonal_ramsey k :=
begin
  refine basic_diagonal_ramsey_bound _,
  have : (n : ℝ) ^ k ≤ 2 ^ (-1 : ℝ) * ((sqrt 2) ^ (k - 1 : ℝ)) ^ k * (k / exp 1) ^ k,
  { refine (pow_le_pow_of_le_left (nat.cast_nonneg _) hn _).trans_eq _,
    rw [mul_inv, mul_right_comm _ (sqrt 2)⁻¹, mul_right_comm _ (sqrt 2)⁻¹, mul_assoc,
      ←rpow_neg_one (sqrt 2), ←rpow_nat_cast (sqrt 2), ←rpow_add, neg_add_eq_sub, mul_pow,
      mul_comm (exp 1)⁻¹, mul_right_comm, mul_assoc, ←div_eq_mul_inv, mul_pow, ←rpow_nat_cast,
      ←rpow_mul, div_mul_cancel, mul_right_comm],
    { positivity },
    { positivity },
    { positivity } },
  rw [←div_le_iff _, ←div_pow, div_div_eq_mul_div, mul_comm] at this,
  swap,
  { positivity },
  rcases eq_or_ne n 0 with rfl | hn',
  { cases k,
    { simpa using hk },
    rw [nat.choose_zero_succ, nat.cast_zero, zero_mul],
    norm_num1 },
  refine (mul_lt_mul_of_pos_right (choose_upper_bound_of_pos hn' hk) (by positivity)).trans_le _,
  refine (mul_le_mul_of_nonneg_right this (by positivity)).trans_eq _,
  rw [←rpow_div_two_eq_sqrt, ←rpow_nat_cast, ←rpow_mul, ←rpow_add, ←rpow_add, nat.cast_choose_two],
  { ring_nf, rw rpow_zero },
  { norm_num1 },
  { norm_num1 },
  { norm_num1 },
  { norm_num1 },
end

lemma diagonal_ramsey_bound_refined {k : ℕ} (hk : k ≠ 0) :
  (exp 1 * sqrt 2)⁻¹ * 2 ^ (- 1 / k : ℝ) * k * (sqrt 2) ^ k < diagonal_ramsey k :=
begin
  have hk' : 0 ≤ (exp 1 * sqrt 2)⁻¹ * 2 ^ (-1 / k : ℝ) * k * sqrt 2 ^ k,
  { positivity },
  rw ←nat.floor_lt hk',
  exact diagonal_ramsey_bound_refined_aux hk (nat.floor_le hk'),
end

lemma diagonal_ramsey_bound_refined_again {k : ℕ} (hk : k ≠ 0) :
  (exp 1 * sqrt 2)⁻¹ * (1 - log 2 / k) * k * (sqrt 2) ^ k < diagonal_ramsey k :=
begin
  refine (diagonal_ramsey_bound_refined hk).trans_le' _,
  refine mul_le_mul_of_nonneg_right _ (by positivity),
  refine mul_le_mul_of_nonneg_right _ (by positivity),
  refine mul_le_mul_of_nonneg_left _ (by positivity),
  refine (one_sub_le_exp_minus_of_pos _).trans_eq _,
  { refine div_nonneg (log_nonneg (by norm_num1)) (nat.cast_nonneg _) },
  rw [rpow_def_of_pos, neg_div, mul_neg, mul_one_div],
  norm_num1
end

lemma e_times_sqrt_two_plus_log_two_gt_four : 4 < exp 1 * sqrt 2 + log 2 :=
by { have : 1.4 < sqrt 2, { rw lt_sqrt; norm_num }, nlinarith [log_two_gt_d9, exp_one_gt_d9] }

lemma e_times_sqrt_two_plus_log_two_lt_five : exp 1 * sqrt 2 + log 2 < 5 :=
begin
  have : sqrt 2 < 1.5, { rw sqrt_lt; norm_num },
  nlinarith [log_two_lt_d9, exp_one_lt_d9, exp_one_gt_d9],
end

lemma diagonal_ramsey_bound_simpler_aux {k : ℕ} (hk' : exp 1 * sqrt 2 + log 2 ≤ k):
  sqrt 2 ^ k < diagonal_ramsey k :=
begin
  have : k ≠ 0,
  { have := e_times_sqrt_two_plus_log_two_gt_four.trans_le hk',
    rw [←nat.cast_one, ←nat.cast_bit0, ←nat.cast_bit0, nat.cast_lt] at this,
    rw ←pos_iff_ne_zero,
    exact this.trans_le' (by norm_num) },
  refine (diagonal_ramsey_bound_refined_again this).trans_le' _,
  refine le_mul_of_one_le_left (by positivity) _,
  rwa [mul_assoc, one_sub_mul, div_mul_cancel, inv_mul_eq_div, one_le_div, le_sub_iff_add_le],
  { positivity },
  { positivity },
end

lemma diagonal_ramsey_lower_bound_simpler {k : ℕ} (hk : 2 ≤ k) : sqrt 2 ^ k ≤ diagonal_ramsey k :=
begin
  cases le_total (exp 1 * sqrt 2 + log 2) k,
  { exact (diagonal_ramsey_bound_simpler_aux h).le },
  replace h := h.trans_lt e_times_sqrt_two_plus_log_two_lt_five,
  norm_cast at h,
  interval_cases k,
  { rw [sq_sqrt, diagonal_ramsey_two, nat.cast_two], exact zero_le_two },
  { rw [diagonal_ramsey_three, nat.cast_bit0, nat.cast_bit1, nat.cast_one],
    refine (abs_le_of_sq_le_sq' _ (by norm_num)).2,
    rw [←pow_mul, pow_mul', sq_sqrt];
    norm_num },
  rw [bit0_eq_two_mul 2, pow_mul, ←bit0_eq_two_mul, sq_sqrt, diagonal_ramsey_four];
  norm_num
end

section

open filter

lemma little_o_ramsey_bound :
  ∃ f : ℕ → ℝ, f =o[at_top] (λ _, 1 : _ → ℝ) ∧
    ∀ k, (1 + f k) * k / (sqrt 2 * exp 1) * (sqrt 2) ^ k ≤ diagonal_ramsey k :=
begin
  refine ⟨λ k, -log 2 / k, _, λ k, _⟩,
  { rw asymptotics.is_o_one_iff,
    exact tendsto_const_div_at_top_nhds_0_nat _ },
  rcases eq_or_ne k 0 with rfl | hk,
  { simp },
  refine (diagonal_ramsey_bound_refined_again hk).le.trans_eq' _,
  rw [neg_div, ←sub_eq_add_neg, div_eq_mul_inv, mul_comm (sqrt 2), mul_comm (_ * _) (_⁻¹),
    ←mul_assoc],
end

lemma slightly_off_diagonal_lower_ramsey :
  ∃ c : ℝ, 0 < c ∧ ∀ᶠ l : ℕ in at_top, ∀ k, l ≤ k →
    real.exp (c * l ^ (3 / 4 : ℝ) * log k) ≤ ramsey_number ![k, ⌊(l : ℝ) ^ (3 / 4 : ℝ)⌋₊] :=
begin

end

end

end simple_graph
