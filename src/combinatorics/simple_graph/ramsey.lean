import combinatorics.simple_graph.degree_sum
import data.finite.card
import data.finset.pairwise
import data.sym.card
import data.fin.basic
import algebra.big_operators.order
import data.dfinsupp.well_founded
import tactic.fin_cases
import data.fin.vec_notation
import algebra.big_operators.fin
import number_theory.legendre_symbol.quadratic_char
import field_theory.finite.basic
import data.fin.tuple.sort
import algebra.char_p.pi
import data.nat.choose.central

namespace simple_graph
variables {V V' : Type*} {G : simple_graph V} {K K' : Type*}

open fintype (card)
open finset

section

theorem exists_even_degree [fintype V] [decidable_rel G.adj] (hV : odd (card V)) :
  ∃ v : V, even (G.degree v) :=
begin
  have := even_card_odd_degree_vertices G,
  have : univ.filter (λ (v : V), odd (G.degree v)) ≠ univ,
  { rw [←card_lt_iff_ne_univ, lt_iff_le_and_ne],
    refine ⟨card_le_univ _, _⟩,
    intro h,
    rw [h, nat.even_iff_not_odd] at this,
    exact this hV },
  rw [ne.def, filter_eq_self] at this,
  simpa using this
end

lemma central_binom_monotone : monotone nat.central_binom :=
λ n m h, (nat.choose_le_choose n (nat.mul_le_mul_left 2 h)).trans (nat.choose_le_central_binom _ _)

end

def edge_labelling (G : simple_graph V) (K : Type*) := G.edge_set → K

instance [decidable_eq V] [fintype G.edge_set] [fintype K] : fintype (edge_labelling G K) :=
pi.fintype
instance [nonempty K] : nonempty (edge_labelling G K) := pi.nonempty
instance [inhabited K] : inhabited (edge_labelling G K) := pi.inhabited _
instance [subsingleton K] : subsingleton (edge_labelling G K) := pi.subsingleton
instance [unique K] : unique (edge_labelling G K) := pi.unique

instance [subsingleton V] : is_empty (edge_set G) :=
begin
  split,
  rintro ⟨i, hi⟩,
  induction i using sym2.induction_on with i j,
  simp only [mem_edge_set] at hi,
  cases hi.ne (subsingleton.elim _ _)
end

instance edge_labelling.unique_of_subsingleton [subsingleton V] : unique (edge_labelling G K) :=
pi.unique_of_is_empty _

abbreviation top_edge_labelling (V : Type*) (K : Type*) :=
edge_labelling (⊤ : simple_graph V) K

def top_edge_set_equiv : (⊤ : simple_graph V).edge_set ≃ {a : sym2 V // ¬a.is_diag} :=
equiv.subtype_equiv_right $ λ i, sym2.induction_on i $ λ x y, iff.rfl

lemma card_top_edge_set [decidable_eq V] [fintype V] :
  card (⊤ : simple_graph V).edge_set = (card V).choose 2 :=
by rw [fintype.card_congr top_edge_set_equiv, sym2.card_subtype_not_diag]

lemma card_edge_labelling [decidable_eq V] [fintype V] [fintype K] :
  card (top_edge_labelling V K) = card K ^ (card V).choose 2 :=
fintype.card_fun.trans (by rw card_top_edge_set)

def top_edge_labelling.get (C : top_edge_labelling V K) (x y : V)
  (h : x ≠ y . tactic.assumption) : K :=
C ⟨⟦(x, y)⟧, by simp [h]⟩

variables {C : top_edge_labelling V K}

lemma top_edge_labelling.get_swap (x y : V) (h : x ≠ y) :
  C.get y x h.symm = C.get x y :=
by simp only [top_edge_labelling.get, sym2.eq_swap]

lemma top_edge_labelling.ext_get {C C' : top_edge_labelling V K}
  (h : ∀ x y, x ≠ y → C.get x y = C'.get x y) :
  C = C' :=
begin
  ext ⟨e, he⟩,
  induction e using sym2.induction_on,
  exact h _ _ he,
end

def top_edge_labelling.comp_right (C : top_edge_labelling V K) (f : K → K') :
  top_edge_labelling V K' := f ∘ C

def top_edge_labelling.pullback (C : top_edge_labelling V K) (f : V' ↪ V) :
  top_edge_labelling V' K :=
C ∘ (embedding.complete_graph f).map_edge_set

@[simp] lemma top_edge_labelling.pullback_apply {f : V' ↪ V} (e) :
  C.pullback f e = C ((embedding.complete_graph f).map_edge_set e) := rfl

@[simp] lemma top_edge_labelling.pullback_get {f : V' ↪ V} (x y) (h : x ≠ y) :
  (C.pullback f).get x y = C.get (f x) (f y) (by simpa) := rfl

@[simp] lemma top_edge_labelling.comp_right_apply (f : K → K') (e) : C.comp_right f e = f (C e) :=
rfl
@[simp] lemma top_edge_labelling.comp_right_get (f : K → K') (x y) (h : x ≠ y) :
  (C.comp_right f).get x y = f (C.get x y) := rfl

def top_edge_labelling.mk (f : Π x y : V, x ≠ y → K)
  (f_symm : ∀ (x y : V) (H : x ≠ y), f y x H.symm = f x y H) :
  top_edge_labelling V K :=
λ i, subtype.rec_on i $ λ e,
begin
  refine quotient.hrec_on e (λ xy, f xy.1 xy.2) _,
  rintro ⟨a, b⟩ ⟨c, d⟩ ⟨⟩,
  { refl },
  ext,
  { simp only [mem_edge_set, top_adj, ne.def, eq_iff_iff, not_iff_not],
    exact comm },
  intros h₁ h₂ h,
  exact heq_of_eq (f_symm _ _ _),
end

lemma top_edge_labelling.mk_get (f : Π x y : V, x ≠ y → K) (f_symm) (x y : V) (h : x ≠ y) :
  (top_edge_labelling.mk f f_symm).get x y = f x y h :=
rfl

def top_edge_labelling.monochromatic_of (C : top_edge_labelling V K) (m : set V) (c : K) : Prop :=
∀ ⦃x⦄, x ∈ m → ∀ ⦃y⦄, y ∈ m → x ≠ y → C.get x y = c

lemma top_edge_labelling.monochromatic_of_iff_pairwise [decidable_eq V] (C : top_edge_labelling V K)
  {m : set V} {c : K} :
  C.monochromatic_of m c ↔ m.pairwise (λ x y, if h : x = y then true else C.get x y = c) :=
forall₅_congr (λ x hx y hy h, by simp [h])

def edge_labelling.label_graph (C : edge_labelling G K) (k : K) : simple_graph V :=
simple_graph.from_edge_set {e | ∃ (h : e ∈ G.edge_set), C ⟨e, h⟩ = k}

def edge_labelling.label_graph_adj {C : edge_labelling G K} {k : K} (x y : V) :
  (C.label_graph k).adj x y ↔ ∃ H : G.adj x y, C ⟨⟦(x, y)⟧, H⟩ = k :=
begin
  rw edge_labelling.label_graph,
  simp only [mem_edge_set, from_edge_set_adj, set.mem_set_of_eq, ne.def],
  apply and_iff_left_of_imp _,
  rintro ⟨h, -⟩,
  exact h.ne,
end

instance [decidable_rel G.adj] [decidable_eq K] (k : K) {C : edge_labelling G K} :
  decidable_rel (C.label_graph k).adj :=
λ x y, decidable_of_iff' _ (edge_labelling.label_graph_adj _ _)

@[simp] lemma top_edge_labelling.label_graph_adj {C : top_edge_labelling V K} {k : K} (x y : V) :
  (C.label_graph k).adj x y ↔ ∃ H : x ≠ y, C.get x y = k :=
by { rw [edge_labelling.label_graph_adj], simpa }

lemma edge_labelling.label_graph_le (C : edge_labelling G K) {k : K} : C.label_graph k ≤ G :=
begin
  intros x y,
  rw edge_labelling.label_graph_adj,
  rintro ⟨h, -⟩,
  exact h
end

lemma edge_set_eq_empty_iff {G : simple_graph V} : G.edge_set = ∅ ↔ G = ⊥ :=
by rw [←edge_set_bot, edge_set_inj]

lemma disjoint_edge_set {G H : simple_graph V} : disjoint G.edge_set H.edge_set ↔ disjoint G H :=
by rw [set.disjoint_iff_inter_eq_empty, disjoint_iff, ←edge_set_inf, edge_set_eq_empty_iff]

lemma disjoint_left {G H : simple_graph V} : disjoint G H ↔ (∀ x y, G.adj x y → ¬ H.adj x y) :=
by simp only [←disjoint_edge_set, set.disjoint_left, sym2.forall, mem_edge_set]

lemma edge_labelling.pairwise_disjoint {C : edge_labelling G K} :
  set.pairwise_disjoint (set.univ : set K) C.label_graph :=
begin
  intros k₁ hk₁ k₂ hk₂ h,
  simp only [function.on_fun, disjoint_left, edge_labelling.label_graph_adj, not_exists,
    forall_exists_index],
  rintro x y h rfl h',
  exact h
end

lemma edge_labelling.supr_label_graph (C : edge_labelling G K) : (⨆ k : K, C.label_graph k) = G :=
begin
  ext x y,
  simp only [supr_adj, edge_labelling.label_graph_adj],
  split,
  { rintro ⟨k, h, rfl⟩,
    exact h },
  intro h,
  exact ⟨_, h, rfl⟩,
end

@[simp] lemma adj_sup_iff {ι V : Type*} {s : finset ι} {f : ι → simple_graph V} {x y : V} :
  (s.sup f).adj x y ↔ ∃ i ∈ s, (f i).adj x y :=
begin
  induction s using finset.cons_induction_on with a s has ih,
  { simp },
  { simp [or_and_distrib_right, exists_or_distrib, ih] },
end

lemma edge_labelling.sup_label_graph [fintype K] (C : edge_labelling G K) :
  univ.sup C.label_graph = G :=
begin
  refine eq.trans _ C.supr_label_graph,
  ext x y,
  simp,
end

def to_edge_labelling (G : simple_graph V) [decidable_rel G.adj] :
  top_edge_labelling V (fin 2) :=
top_edge_labelling.mk (λ x y _, if G.adj x y then 1 else 0) (λ x y h, by simp only [G.adj_comm])

@[simp] lemma to_edge_labelling_get {G : simple_graph V} [decidable_rel G.adj]
  {x y : V} (H : x ≠ y) : G.to_edge_labelling.get x y = if G.adj x y then 1 else 0 :=
rfl

lemma to_edge_labelling_label_graph (G : simple_graph V) [decidable_rel G.adj] :
  G.to_edge_labelling.label_graph 1 = G :=
by { ext x y, simpa [imp_false] using G.ne_of_adj }

lemma to_edge_labelling_label_graph_compl (G : simple_graph V) [decidable_rel G.adj] :
  G.to_edge_labelling.label_graph 0 = Gᶜ :=
by { ext x y, simp [imp_false] }

lemma fin.fin_two_eq_zero_of_ne_one {x : fin 2} (hx : x ≠ 1) : x = 0 :=
begin
  revert x,
  rw fin.forall_fin_two,
  simp
end

lemma label_graph_to_edge_labelling [decidable_eq V] (C : top_edge_labelling V (fin 2)) :
  (C.label_graph 1).to_edge_labelling = C :=
begin
  refine top_edge_labelling.ext_get _,
  intros x y h,
  simp only [h, ne.def, not_false_iff, to_edge_labelling_get, top_edge_labelling.label_graph_adj,
    exists_true_left],
  split_ifs,
  { rw h_1 },
  exact (fin.fin_two_eq_zero_of_ne_one h_1).symm,
end

instance [decidable_eq K] [decidable_eq V] (C : top_edge_labelling V K)
  (m : finset V) (c : K) : decidable (C.monochromatic_of m c) :=
decidable_of_iff' _ C.monochromatic_of_iff_pairwise

variables {m : set V} {c : K}

@[simp] lemma monochromatic_of_empty : C.monochromatic_of ∅ c.

@[simp] lemma monochromatic_of_singleton {x : V} : C.monochromatic_of {x} c :=
by simp [top_edge_labelling.monochromatic_of]

lemma monochromatic_finset_singleton {x : V} : C.monochromatic_of ({x} : finset V) c :=
by simp [top_edge_labelling.monochromatic_of]

lemma monochromatic_subsingleton (hm : set.subsingleton m) : C.monochromatic_of m c :=
λ x hx y hy h, by cases h (hm hx hy)

lemma monochromatic_subsingleton_colours [subsingleton K] : C.monochromatic_of m c :=
λ x hx y hy h, subsingleton.elim _ _

lemma top_edge_labelling.monochromatic_of.comp_right (e : K → K') (h : C.monochromatic_of m c) :
  (C.comp_right e).monochromatic_of m (e c) :=
λ x hx y hy h', by rw [top_edge_labelling.comp_right_get, h hx hy h']

lemma top_edge_labelling.monochromatic_of_injective (e : K → K') (he : function.injective e) :
  (C.comp_right e).monochromatic_of m (e c) ↔ C.monochromatic_of m c :=
forall₅_congr (λ x hx y hy h', by simp [he.eq_iff])

lemma top_edge_labelling.monochromatic_of.subset {m' : set V} (h' : m' ⊆ m)
  (h : C.monochromatic_of m c) : C.monochromatic_of m' c :=
λ x hx y hy h'', h (h' hx) (h' hy) h''

lemma top_edge_labelling.monochromatic_of.image {C : top_edge_labelling V' K} {f : V ↪ V'}
  (h : (C.pullback f).monochromatic_of m c) : C.monochromatic_of (f '' m) c :=
by simpa [top_edge_labelling.monochromatic_of]

lemma top_edge_labelling.monochromatic_of.map {C : top_edge_labelling V' K} {f : V ↪ V'}
  {m : finset V} (h : (C.pullback f).monochromatic_of m c) : C.monochromatic_of (m.map f) c :=
by simpa [top_edge_labelling.monochromatic_of]

lemma top_edge_labelling.monochromatic_of_insert {x : V} (hx : x ∉ m) :
  C.monochromatic_of (insert x m) c ↔
    C.monochromatic_of m c ∧ ∀ y ∈ m, C.get x y (H.ne_of_not_mem hx).symm = c :=
begin
  split,
  { intro h,
    exact ⟨h.subset (by simp), λ y hy, h (set.mem_insert _ _) (set.mem_insert_of_mem _ hy) _⟩ },
  classical,
  rintro ⟨h₁, h₂⟩,
  simp only [top_edge_labelling.monochromatic_of, ne.def, set.mem_insert_iff, forall_eq_or_imp,
    eq_self_iff_true, not_true, is_empty.forall_iff, true_and],
  refine ⟨λ _ hy _, h₂ _ hy, λ y hy, ⟨λ _, _, λ z hz, h₁ hy hz⟩⟩,
  rw top_edge_labelling.get_swap,
  exact h₂ y hy,
end

open top_edge_labelling

def is_ramsey_valid (V : Type*) (n : K → ℕ) : Prop :=
∀ C : top_edge_labelling V K, ∃ (m : finset V) c, C.monochromatic_of m c ∧ n c ≤ m.card

lemma is_ramsey_valid.empty_colours [is_empty K] {n : K → ℕ} : is_ramsey_valid (fin 2) n :=
λ C, is_empty_elim (C.get 0 1 (by norm_num))

lemma is_ramsey_valid.exists_zero_of_is_empty [is_empty V] {n : K → ℕ} (h : is_ramsey_valid V n) :
  ∃ c, n c = 0 :=
let ⟨m, c, hm, hc⟩ := h (is_empty.elim (by simp)) in ⟨c, by simpa [subsingleton.elim m ∅] using hc⟩

lemma is_ramsey_valid_of_zero {n : K → ℕ} (c : K) (hc : n c = 0) : is_ramsey_valid V n :=
λ C, ⟨∅, c, by simp, by simp [hc]⟩

lemma is_ramsey_valid_of_exists_zero (n : K → ℕ) (h : ∃ c, n c = 0) : is_ramsey_valid V n :=
let ⟨c, hc⟩ := h in is_ramsey_valid_of_zero _ hc

lemma is_ramsey_valid.mono_right {n n' : K → ℕ} (h : n ≤ n') (h' : is_ramsey_valid V n') :
  is_ramsey_valid V n :=
λ C, let ⟨m, c, hc, hm⟩ := h' C in ⟨m, c, hc, hm.trans' (h _)⟩

lemma is_ramsey_valid_iff_eq {n : K → ℕ} :
  is_ramsey_valid V n ↔
    ∀ C : top_edge_labelling V K, ∃ (m : finset V) c, C.monochromatic_of m c ∧ n c = m.card :=
begin
  refine forall_congr (λ C, _),
  rw [exists_comm, @exists_comm (finset V)],
  refine exists_congr (λ c, _),
  split,
  { rintro ⟨a, ha, ha'⟩,
    obtain ⟨b, hb, hb'⟩ := exists_smaller_set a _ ha',
    exact ⟨b, ha.subset hb, hb'.symm⟩ },
  { rintro ⟨a, ha, ha'⟩,
    exact ⟨_, ha, ha'.le⟩ }
end

lemma is_ramsey_valid_iff_embedding_aux {n : K → ℕ} (c : K) :
  (∃ (m : finset V), C.monochromatic_of m c ∧ n c = m.card) ↔
    nonempty ((⊤ : simple_graph (fin (n c))) ↪g C.label_graph c) :=
begin
  split,
  { rintro ⟨m, hm, hm'⟩,
    have : fintype.card m = n c,
    { rw [fintype.card_coe, hm'] },
    classical,
    obtain ⟨e⟩ := fintype.trunc_equiv_fin_of_card_eq this,
    refine ⟨⟨e.symm.to_embedding.trans (function.embedding.subtype _), _⟩⟩,
    intros a b,
    simp only [ne.def, function.embedding.trans_apply, equiv.coe_to_embedding,
      function.embedding.coe_subtype, label_graph_adj, top_adj, ←subtype.ext_iff,
      embedding_like.apply_eq_iff_eq],
    split,
    { rintro ⟨h, -⟩,
      exact h },
    intro h,
    exact ⟨h, hm (e.symm a).prop (e.symm b).prop _⟩ },
  rintro ⟨f⟩,
  refine ⟨(univ : finset (fin (n c))).map f.to_embedding, _, _⟩,
  { rw monochromatic_of,
    simp only [ne.def, rel_embedding.inj, coe_map, rel_embedding.coe_fn_to_embedding, set.mem_image,
      coe_univ, set.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff'],
    intros x y h,
    have : (⊤ : simple_graph (fin (n c))).adj x y := h,
    simpa [←f.map_rel_iff, h] using this },
  rw [card_map, card_fin],
end

-- pretty good chance this is a better definition...
-- it also generalises better to induced ramsey numbers
lemma is_ramsey_valid_iff_embedding {n : K → ℕ} :
  is_ramsey_valid V n ↔
    ∀ C : top_edge_labelling V K,
      ∃ c : K, nonempty ((⊤ : simple_graph (fin (n c))) ↪g C.label_graph c) :=
begin
  rw is_ramsey_valid_iff_eq,
  refine forall_congr (λ C, _),
  rw exists_comm,
  simp only [is_ramsey_valid_iff_embedding_aux],
end

lemma is_ramsey_valid.embedding {n : K → ℕ} (f : V ↪ V') (h' : is_ramsey_valid V n) :
  is_ramsey_valid V' n :=
λ C, let ⟨m', c, hc, hm'⟩ := h' (C.pullback f) in ⟨m'.map f, c,
by simpa only [coe_map] using hc.image, hm'.trans_eq (card_map _).symm⟩

lemma is_ramsey_valid.card_fin [fintype V] {N : ℕ} {n : K → ℕ} (h : N ≤ card V)
  (h' : is_ramsey_valid (fin N) n) : is_ramsey_valid V n :=
h'.embedding ((fin.cast_le h).to_embedding.trans (fintype.equiv_fin V).symm)

lemma is_ramsey_valid.equiv_left (n : K → ℕ) (f : V ≃ V') :
  is_ramsey_valid V n ↔ is_ramsey_valid V' n :=
⟨λ h, h.embedding f, λ h, h.embedding f.symm⟩

lemma is_ramsey_valid.equiv_right {n : K → ℕ} (f : K' ≃ K) (h : is_ramsey_valid V n) :
  is_ramsey_valid V (n ∘ f) :=
λ C, let ⟨m, c, hm, hc⟩ := h (C.comp_right f) in
⟨m, f.symm c, by rwa [←monochromatic_of_injective f f.injective, f.apply_symm_apply],
  by simpa using hc⟩

lemma is_ramsey_valid_equiv_right {n : K → ℕ} (f : K' ≃ K) :
  is_ramsey_valid V (n ∘ f) ↔ is_ramsey_valid V n :=
⟨λ h, by { convert h.equiv_right f.symm, ext, simp }, λ h, h.equiv_right _⟩

instance [decidable_eq K] [fintype K] [decidable_eq V] [fintype V] (n : K → ℕ) :
  decidable (is_ramsey_valid V n) :=
fintype.decidable_forall_fintype

lemma ramsey_base [nonempty V] {n : K → ℕ} (hn : ∃ k, n k ≤ 1) :
  is_ramsey_valid V n :=
begin
  inhabit V,
  obtain ⟨k, hk⟩ := hn,
  exact λ C, ⟨{arbitrary V}, k, monochromatic_finset_singleton, by simpa using hk⟩,
end

lemma ramsey_base' [fintype V] (n : K → ℕ) (hn : ∃ k, n k ≤ 1) (hV : 1 ≤ card V) :
  is_ramsey_valid V n :=
@ramsey_base _ _ (fintype.card_pos_iff.1 hV) _ hn

lemma is_ramsey_valid_min [fintype V] [nonempty K] {n : K → ℕ} {n' : ℕ} (h : is_ramsey_valid V n)
  (hn : ∀ k, n' ≤ n k) : n' ≤ card V :=
let ⟨m, h, h', hm⟩ := h (classical.arbitrary (top_edge_labelling V K))
in (hn _).trans (hm.trans (finset.card_le_univ m))

lemma is_ramsey_valid_unique [fintype V] [unique K] {n : K → ℕ} (hV : n default ≤ card V) :
  is_ramsey_valid V n :=
λ C, ⟨univ, default, monochromatic_subsingleton_colours, by simpa⟩

lemma is_ramsey_valid.remove_twos {n : K → ℕ} (h : is_ramsey_valid V n) :
  is_ramsey_valid V (λ (k : {k : K // n k ≠ 2}), n k) :=
begin
  casesI is_empty_or_nonempty V with hV hV,
  { obtain ⟨c, hc⟩ := h.exists_zero_of_is_empty,
    exact is_ramsey_valid_of_zero ⟨c, by simp [hc]⟩ hc },
  by_cases h' : ∃ k, n k ≤ 1,
  { obtain ⟨k, hk⟩ := h',
    refine ramsey_base ⟨⟨k, _⟩, hk⟩,
    linarith },
  simp only [not_exists, not_le, nat.lt_iff_add_one_le] at h',
  intro C,
  obtain ⟨m, c, hm, hc⟩ := h (C.comp_right subtype.val),
  have : 1 < m.card := (h' c).trans hc,
  rw finset.one_lt_card_iff at this,
  obtain ⟨a, b, ha, hb, hab⟩ := this,
  have : subtype.val (C.get a b hab) = c := hm ha hb hab,
  refine ⟨m, _, _, hc.trans_eq' (congr_arg n this)⟩,
  rwa [←monochromatic_of_injective _ subtype.val_injective, this],
end

lemma is_ramsey_valid.of_remove_twos {n : K → ℕ}
  (h : is_ramsey_valid V (λ (k : {k : K // n k ≠ 2}), n k)) :
  is_ramsey_valid V n :=
begin
  intro C,
  classical,
  by_cases h'' : ∃ (x y : V) (H : x ≠ y), n (C.get x y) = 2,
  { obtain ⟨x, y, H, hxy⟩ := h'',
    have : x ∉ ({y} : set V) := by simpa,
    refine ⟨({x, y} : finset V), C.get x y, _, _⟩,
    { rw [coe_pair, monochromatic_of_insert this],
      refine ⟨monochromatic_of_singleton, _⟩,
      simp only [set.mem_singleton_iff],
      rintro _ rfl,
      refl },
    rw [hxy, card_doubleton H] },
  push_neg at h'',
  let C' : top_edge_labelling V {k : K // n k ≠ 2} :=
    top_edge_labelling.mk (λ x y h, ⟨C.get x y, h'' _ _ h⟩) _,
  swap,
  { intros x y h,
    ext,
    dsimp,
    exact get_swap _ _ _ },
  obtain ⟨m, c, hm, hc⟩ := h C',
  refine ⟨m, c, _, hc⟩,
  intros x hx y hy h,
  exact subtype.ext_iff.1 (hm hx hy h),
end

lemma is_ramsey_valid_iff_remove_twos (n : K → ℕ) :
  is_ramsey_valid V (λ (k : {k : K // n k ≠ 2}), n k) ↔ is_ramsey_valid V n :=
⟨is_ramsey_valid.of_remove_twos, is_ramsey_valid.remove_twos⟩

lemma is_ramsey_valid_two {n : K → ℕ} {n' : K' → ℕ} (f : K' → K)
  (hf : ∀ x : K', n' x ≠ 2 → n (f x) ≠ 2)
  (hf_inj : ∀ x y : K', n' x ≠ 2 → n' y ≠ 2 → f x = f y → x = y)
  (hf_surj : ∀ x : K, n x ≠ 2 → ∃ y : K', n' y ≠ 2 ∧ f y = x)
  (hf_comm : ∀ x : K', n' x ≠ 2 → n (f x) = n' x) :
  is_ramsey_valid V n' ↔ is_ramsey_valid V n :=
begin
  let e : {k // n' k ≠ 2} → {k // n k ≠ 2} := λ k, ⟨f k, hf _ k.prop⟩,
  have he : function.injective e :=
    λ a b h, subtype.ext (hf_inj _ _ a.prop b.prop (subtype.ext_iff.1 h)),
  have he' : function.surjective e,
  { rintro ⟨i, hi⟩,
    simpa using hf_surj i hi },
  rw [←is_ramsey_valid_iff_remove_twos n, ←is_ramsey_valid_iff_remove_twos n',
    ←is_ramsey_valid_equiv_right (equiv.of_bijective e ⟨he, he'⟩)],
  congr' 2,
  ext ⟨k, hk⟩,
  exact (hf_comm _ hk).symm,
end

lemma neighbor_set_bot {x : V} : (⊥ : simple_graph V).neighbor_set x = ∅ :=
by { ext y, simp }

lemma neighbor_set_top {x : V} : (⊤ : simple_graph V).neighbor_set x = {x}ᶜ :=
by { ext y, rw [mem_neighbor_set, top_adj, set.mem_compl_singleton_iff, ne_comm] }

lemma neighbor_set_sup {G H : simple_graph V} {x : V} :
  (G ⊔ H).neighbor_set x = G.neighbor_set x ∪ H.neighbor_set x :=
by { ext y, simp }

lemma neighbor_set_inf {G H : simple_graph V} {x : V} :
  (G ⊓ H).neighbor_set x = G.neighbor_set x ∩ H.neighbor_set x :=
by { ext y, simp only [mem_neighbor_set, inf_adj, set.mem_inter_iff] }

lemma neighbor_set_supr {ι : Type*} {s : ι → simple_graph V} {x : V} :
  (⨆ i, s i).neighbor_set x = ⋃ i, (s i).neighbor_set x :=
by { ext y, simp }

lemma neighbor_set_infi {ι : Type*} [nonempty ι] {s : ι → simple_graph V} {x : V} :
  (⨅ i, s i).neighbor_set x = ⋂ i, (s i).neighbor_set x :=
begin
  ext y,
  simp only [mem_neighbor_set, infi_adj, ne.def, set.infi_eq_Inter, set.mem_Inter,
    and_iff_left_iff_imp],
  intro h,
  inhabit ι,
  exact (h default).ne,
end

lemma neighbor_set_disjoint {G H : simple_graph V} {x : V} (h : disjoint G H) :
  disjoint (G.neighbor_set x) (H.neighbor_set x) :=
by rw [set.disjoint_iff_inter_eq_empty, ←neighbor_set_inf, h.eq_bot, neighbor_set_bot]

section

-- variables [fintype V] [decidable_eq V] -- probably a more refined assumption is better

instance {V : Type*} {x : V} : is_empty ((⊥ : simple_graph V).neighbor_set x) :=
  subtype.is_empty_false

lemma neighbor_finset_bot {x : V} : (⊥ : simple_graph V).neighbor_finset x = ∅ :=
by { ext y, simp }

lemma neighbor_finset_top [fintype V] [decidable_eq V] {x : V} :
  (⊤ : simple_graph V).neighbor_finset x = {x}ᶜ :=
by { ext y, rw [mem_neighbor_finset, top_adj, finset.mem_compl, mem_singleton, ne_comm] }

lemma neighbor_finset_sup [decidable_eq V] {G H : simple_graph V} {x : V}
  [fintype ((G ⊔ H).neighbor_set x)] [fintype (G.neighbor_set x)] [fintype (H.neighbor_set x)] :
  (G ⊔ H).neighbor_finset x = G.neighbor_finset x ∪ H.neighbor_finset x :=
by { ext y, simp }

lemma neighbor_finset_inf [decidable_eq V] {G H : simple_graph V} {x : V}
  [fintype ((G ⊓ H).neighbor_set x)] [fintype (G.neighbor_set x)] [fintype (H.neighbor_set x)] :
  (G ⊓ H).neighbor_finset x = G.neighbor_finset x ∩ H.neighbor_finset x :=
by { ext y, simp }

instance _root_.finset.decidable_rel_sup
  {ι V : Type*} {s : finset ι} {f : ι → simple_graph V} [Π i, decidable_rel (f i).adj] :
  decidable_rel (s.sup f).adj :=
λ x y, decidable_of_iff' _ adj_sup_iff

lemma neighbor_finset_supr [decidable_eq V] {ι : Type*} {s : finset ι} {f : ι → simple_graph V}
  {x : V} [Π i, fintype ((f i).neighbor_set x)] [fintype ((s.sup f).neighbor_set x)] :
  (s.sup f).neighbor_finset x = s.bUnion (λ i, (f i).neighbor_finset x) :=
by { ext y, simp }

@[simp] lemma coe_neighbor_finset {G : simple_graph V} {x : V} [fintype (G.neighbor_set x)] :
  (G.neighbor_finset x : set V) = G.neighbor_set x :=
by rw [neighbor_finset_def, set.coe_to_finset]

lemma neighbor_finset_disjoint {G H : simple_graph V} {x : V}
  [fintype (G.neighbor_set x)] [fintype (H.neighbor_set x)] (h : disjoint G H) :
  disjoint (G.neighbor_finset x) (H.neighbor_finset x) :=
by { rw [←disjoint_coe, coe_neighbor_finset, coe_neighbor_finset], exact neighbor_set_disjoint h }

end

open_locale big_operators

variables [decidable_eq K] [fintype K] [decidable_eq K'] [fintype K'] {n : K → ℕ}

theorem ramsey_fin_induct_aux {V : Type*} [decidable_eq V]
  {n : K → ℕ} (N : K → ℕ) {C : top_edge_labelling V K}
  (m : K → finset V) (x : V)
  (hN : ∀ k, is_ramsey_valid (fin (N k)) (function.update n k (n k - 1)))
  (hx : ∀ k, x ∉ m k) (h : ∃ k, N k ≤ (m k).card)
  (hm : ∀ k (y : V) (hy : y ∈ m k), C.get x y (ne_of_mem_of_not_mem hy (hx k)).symm = k) :
  ∃ (m : finset V) c, C.monochromatic_of m c ∧ n c ≤ m.card :=
begin
  classical,
  obtain ⟨k, hk⟩ := h,
  have : is_ramsey_valid (m k) (function.update n k (n k - 1)) := (hN k).card_fin (by simp [hk]),
  obtain ⟨m', k', hm', hk'⟩ := this (C.pullback (function.embedding.subtype _)),
  rcases ne_or_eq k k' with hk | rfl,
  { exact ⟨_, _, hm'.map, by simpa [hk.symm] using hk'⟩ },
  have : x ∉ (m'.map (function.embedding.subtype _) : set V),
  { simp [hx k] },
  refine ⟨insert (x : V) (m'.map (function.embedding.subtype _)), k, _, _⟩,
  { rw [coe_insert, top_edge_labelling.monochromatic_of_insert this],
    refine ⟨hm'.map, λ y hy, _⟩,
    generalize_proofs,
    simp only [mem_neighbor_finset, mem_coe, mem_map, function.embedding.coe_subtype, exists_prop,
      subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right,
      top_edge_labelling.label_graph_adj] at hy,
    obtain ⟨hy, _⟩ := hy,
    exact hm _ _ hy, },
  rw [card_insert_of_not_mem this, card_map, ←tsub_le_iff_right],
  rwa function.update_same at hk',
end

theorem ramsey_fin_induct (n : K → ℕ) (N : K → ℕ)
  (hN : ∀ k, is_ramsey_valid (fin (N k)) (function.update n k (n k - 1))) :
  is_ramsey_valid (fin (∑ k, (N k - 1) + 2)) n :=
begin
  by_cases h : ∃ k, n k ≤ 1,
  { refine ramsey_base' _ h _,
    rw [fintype.card_fin],
    exact (nat.le_add_left _ _).trans' (by simp) },
  push_neg at h,
  have hN' : ∀ k, 1 ≤ N k,
  { intro k,
    by_contra',
    haveI : is_empty (fin (N k)),
    { rw [←fintype.card_eq_zero_iff, fintype.card_fin],
      simpa only [nat.lt_one_iff] using this },
    obtain ⟨k', hk'⟩ := (hN k).exists_zero_of_is_empty,
    rcases eq_or_ne k k' with rfl | hk,
    { simp only [function.update_same, tsub_eq_zero_iff_le] at hk',
      exact hk'.not_lt (h _) },
    rw function.update_noteq hk.symm at hk',
    simpa only [not_lt_zero'] using (h k').trans_eq hk' },
  classical,
  set V := fin (∑ k, (N k - 1) + 2),
  intro C,
  let x : V := 0,
  let m : K → finset V := λ k, neighbor_finset (C.label_graph k) x,
  have : univ.bUnion m = {x}ᶜ,
  { simp only [←finset.coe_inj, coe_bUnion, mem_coe, mem_univ, set.Union_true, coe_compl,
      coe_singleton, m, coe_neighbor_finset],
    rw [←neighbor_set_supr, edge_labelling.supr_label_graph C, neighbor_set_top] },
  have e : ∑ k, (m k).card = ∑ k, (N k - 1) + 1,
  { rw [←card_bUnion, this, card_compl, ←card_univ, card_fin, card_singleton, nat.add_succ_sub_one],
    rintro x hx y hy h,
    refine neighbor_finset_disjoint _,
    exact edge_labelling.pairwise_disjoint (by simp) (by simp) h },
  have : ∃ k, N k - 1 < (m k).card,
  { by_contra',
    have : ∑ k, (m k).card ≤ ∑ k, (N k - 1) := sum_le_sum (λ k _, this k),
    rw [e] at this,
    simpa only [add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero] using this },
  obtain ⟨k, hk⟩ := this,
  rw [tsub_lt_iff_right (hN' _), nat.lt_add_one_iff] at hk,
  refine ramsey_fin_induct_aux _ m x hN _ ⟨k, hk⟩ _,
  { simp },
  { simp },
end

theorem ramsey_fin_exists (n : K → ℕ) :
  ∃ N, is_ramsey_valid (fin N) n :=
begin
  refine @well_founded_lt.induction _ _ _ (λ a, ∃ N, is_ramsey_valid (fin N) a) n _,
  clear n,
  intros n ih,
  by_cases h : ∃ k, n k = 0,
  { exact ⟨0, is_ramsey_valid_of_exists_zero _ h⟩ },
  push_neg at h,
  dsimp at ih,
  have : ∀ k, function.update n k (n k - 1) < n,
  { simp only [update_lt_self_iff],
    intro k,
    exact nat.pred_lt (h k) },
  have := λ k, ih _ (this k),
  choose N hN using this,
  exact ⟨_, ramsey_fin_induct _ _ hN⟩,
end

@[to_additive]
lemma mul_le_cancellable.mul {α : Type*} [has_le α] [semigroup α] {a b : α}
  (ha : mul_le_cancellable a) (hb : mul_le_cancellable b) :
  mul_le_cancellable (a * b) :=
begin
  intros x y h,
  rw [mul_assoc, mul_assoc] at h,
  exact hb (ha h),
end

@[to_additive]
lemma mul_le_cancellable.of_mul_left {α : Type*} [has_le α] [semigroup α]
  [covariant_class α α (*) (≤)] {a b : α} (hab : mul_le_cancellable (a * b)) :
  mul_le_cancellable b :=
begin
  intros x y h,
  apply hab,
  rw [mul_assoc, mul_assoc],
  exact mul_le_mul_left' h a,
end

lemma sum_tsub {α β : Type*} [add_comm_monoid β] [partial_order β] [has_exists_add_of_le β]
  [covariant_class β β (+) (≤)] [contravariant_class β β (+) (≤)] [has_sub β] [has_ordered_sub β]
  (s : finset α) {f g : α → β} (hfg : ∀ x ∈ s, g x ≤ f x):
  ∑ x in s, (f x - g x) = ∑ x in s, f x - ∑ x in s, g x :=
eq_tsub_of_add_eq $ by rw [←finset.sum_add_distrib];
  exact finset.sum_congr rfl (λ x hx, tsub_add_cancel_of_le $ hfg _ hx)

-- hn can be weakened but it's just a nontriviality assumption
lemma ramsey_fin_induct' (n : K → ℕ) (N : K → ℕ)
  (hn : ∀ k, 2 ≤ n k) (hN : ∀ k, is_ramsey_valid (fin (N k)) (function.update n k (n k - 1))) :
  is_ramsey_valid (fin (∑ k, N k + 2 - card K)) n :=
begin
  have hN' : ∀ k, 1 ≤ N k,
  { intro k,
    by_contra',
    haveI : is_empty (fin (N k)),
    { rw [←fintype.card_eq_zero_iff, fintype.card_fin],
      simpa only [nat.lt_one_iff] using this },
    obtain ⟨k', hk'⟩ := (hN k).exists_zero_of_is_empty,
    rcases eq_or_ne k k' with rfl | hk,
    { simp only [function.update_same, tsub_eq_zero_iff_le] at hk',
      exact hk'.not_lt (hn _) },
    rw function.update_noteq hk.symm at hk',
    simpa only [le_zero_iff] using (hn k').trans_eq hk' },
  have h : ∀ x : K, x ∈ (univ : finset K) → 1 ≤ N x,
  { simpa using hN' },
  have := ramsey_fin_induct n N hN,
  rwa [sum_tsub _ h, tsub_add_eq_add_tsub, ←fintype.card_eq_sum_ones] at this,
  exact sum_le_sum h,
end

open matrix (vec_cons)

lemma function.update_head {α : Type*} {i : ℕ} {x y : α} {t : fin i → α} :
  function.update (vec_cons x t) 0 y = vec_cons y t :=
begin
  rw [function.funext_iff, fin.forall_fin_succ],
  refine ⟨rfl, λ j, _⟩,
  rw function.update_noteq,
  { simp only [vec_cons, fin.cons_succ] },
  exact fin.succ_ne_zero j
end

lemma function.update_one {α : Type*} {i : ℕ} {x y z : α} {t : fin i → α} :
  function.update (vec_cons x (vec_cons y t)) 1 z = vec_cons x (vec_cons z t) :=
begin
  simp only [function.funext_iff, fin.forall_fin_succ],
  refine ⟨rfl, rfl, λ j, _⟩,
  rw function.update_noteq,
  { simp only [vec_cons, fin.cons_succ] },
  exact (fin.succ_injective _).ne (fin.succ_ne_zero _),
end

lemma function.update_two {α : Type*} {i : ℕ} {w x y z : α} {t : fin i → α} :
  function.update (vec_cons w (vec_cons x (vec_cons y t))) 2 z =
    vec_cons w (vec_cons x (vec_cons z t)) :=
begin
  simp only [function.funext_iff, fin.forall_fin_succ],
  refine ⟨rfl, rfl, rfl, λ j, _⟩,
  rw function.update_noteq,
  { simp only [vec_cons, fin.cons_succ] },
  exact (fin.succ_injective _).ne ((fin.succ_injective _).ne (fin.succ_ne_zero _))
end

theorem ramsey_fin_induct_two {i j Ni Nj : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j)
  (hi' : is_ramsey_valid (fin Ni) ![i - 1, j])
  (hj' : is_ramsey_valid (fin Nj) ![i, j - 1]) :
  is_ramsey_valid (fin (Ni + Nj)) ![i, j] :=
begin
  have : ∑ z : fin 2, ![Ni, Nj] z + 2 - card (fin 2) = Ni + Nj,
  { simp },
  have h := ramsey_fin_induct' ![i, j] ![Ni, Nj] _ _,
  { rwa this at h },
  { rw fin.forall_fin_two,
    exact ⟨hi, hj⟩ },
  { rw [fin.forall_fin_two, function.update_head, function.update_one],
    exact ⟨hi', hj'⟩ },
end

theorem ramsey_fin_induct_two_evens {i j Ni Nj : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j)
  (hNi : even Ni) (hNj : even Nj)
  (hi' : is_ramsey_valid (fin Ni) ![i - 1, j])
  (hj' : is_ramsey_valid (fin Nj) ![i, j - 1]) :
  is_ramsey_valid (fin (Ni + Nj - 1)) ![i, j] :=
begin
  have hNi' : 1 ≤ Ni,
  { by_contra',
    haveI : is_empty (fin Ni),
    { rw [←fintype.card_eq_zero_iff, fintype.card_fin],
      simpa only [nat.lt_one_iff] using this },
    obtain ⟨k', hk'⟩ := hi'.exists_zero_of_is_empty,
    revert k',
    simp only [fin.forall_fin_two, imp_false, matrix.cons_val_zero, tsub_eq_zero_iff_le, not_le,
      matrix.cons_val_one, matrix.head_cons],
    exact ⟨hi, by linarith⟩ },
  have hNj' : 1 ≤ Nj,
  { by_contra',
    haveI : is_empty (fin Nj),
    { rw [←fintype.card_eq_zero_iff, fintype.card_fin],
      simpa only [nat.lt_one_iff] using this },
    obtain ⟨k', hk'⟩ := hj'.exists_zero_of_is_empty,
    revert k',
    simp only [fin.forall_fin_two, imp_false, matrix.cons_val_zero, tsub_eq_zero_iff_le, not_le,
      matrix.cons_val_one, matrix.head_cons],
    exact ⟨by linarith, hj⟩ },
  have : odd (card (fin (Ni + Nj - 1))),
  { rw [fintype.card_fin, nat.odd_sub (le_add_right hNi')],
    simp [hNi, hNj] with parity_simps },
  intro C,
  obtain ⟨x, hx⟩ := @exists_even_degree (fin (Ni + Nj - 1)) (C.label_graph 0) _ _ this,
  let m : fin 2 → finset (fin (Ni + Nj - 1)) := λ k, neighbor_finset (C.label_graph k) x,
  change even (m 0).card at hx,
  have : univ.bUnion m = {x}ᶜ,
  { simp only [←finset.coe_inj, coe_bUnion, mem_coe, mem_univ, set.Union_true, coe_compl,
      coe_singleton, m, coe_neighbor_finset],
    rw [←neighbor_set_supr, edge_labelling.supr_label_graph C, neighbor_set_top] },
  have e : ∑ k, (m k).card = Ni + Nj - 2,
  { rw [←card_bUnion, this, card_compl, ←card_univ, card_fin, card_singleton, nat.sub_sub],
    rintro x hx y hy h,
    refine neighbor_finset_disjoint _,
    exact edge_labelling.pairwise_disjoint (by simp) (by simp) h },
  have : Ni ≤ (m 0).card ∨ Nj ≤ (m 1).card,
  { have : (m 0).card + 1 ≠ Ni,
    { intro h,
      rw [←h] at hNi,
      simpa [hx] with parity_simps using hNi },
    rw [eq_tsub_iff_add_eq_of_le (add_le_add hNi' hNj'), fin.sum_univ_two] at e,
    by_contra' h',
    rw [nat.lt_iff_add_one_le, nat.lt_iff_add_one_le, le_iff_lt_or_eq, or_iff_left this,
      nat.lt_iff_add_one_le, add_assoc] at h',
    have := add_le_add h'.1 h'.2,
    rw [add_add_add_comm, ←add_assoc, e] at this,
    simpa only [add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero] using this },
  refine ramsey_fin_induct_aux ![Ni, Nj] m x _ (by simp) _ _,
  { rw [fin.forall_fin_two, function.update_head, function.update_one],
    exact ⟨hi', hj'⟩ },
  { rwa fin.exists_fin_two },
  { rw [fin.forall_fin_two],
    simp only [mem_neighbor_finset, label_graph_adj, forall_exists_index, imp_self,
      implies_true_iff, and_self] }
end

theorem ramsey_fin_induct_three {i j k Ni Nj Nk : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (hk : 2 ≤ k)
  (hi' : is_ramsey_valid (fin Ni) ![i - 1, j, k])
  (hj' : is_ramsey_valid (fin Nj) ![i, j - 1, k])
  (hk' : is_ramsey_valid (fin Nk) ![i, j, k - 1]) :
  is_ramsey_valid (fin (Ni + Nj + Nk - 1)) ![i, j, k] :=
begin
  have : (∑ (k : fin 3), ![Ni, Nj, Nk] k + 2 - card (fin 3)) = (Ni + Nj + Nk - 1),
  { rw [fintype.card_fin, nat.succ_sub_succ_eq_sub, fin.sum_univ_three],
    refl },
  have h := ramsey_fin_induct' ![i, j, k] ![Ni, Nj, Nk] _ _,
  { rwa this at h },
  { rw [fin.forall_fin_succ, fin.forall_fin_two],
    exact ⟨hi, hj, hk⟩ },
  { rw [fin.forall_fin_succ, fin.forall_fin_two, function.update_head, fin.succ_zero_eq_one',
      fin.succ_one_eq_two', function.update_one, function.update_two],
    exact ⟨hi', hj', hk'⟩ }
end

variables {N : ℕ} [fintype V]

def ramsey_number (n : K → ℕ) : ℕ := nat.find (ramsey_fin_exists n)

lemma ramsey_number_spec_fin (n : K → ℕ) : is_ramsey_valid (fin (ramsey_number n)) n :=
nat.find_spec (ramsey_fin_exists n)

lemma ramsey_number_spec (h : ramsey_number n ≤ card V) : is_ramsey_valid V n :=
(ramsey_number_spec_fin n).card_fin h

lemma ramsey_number_min_fin (hN : is_ramsey_valid (fin N) n) : ramsey_number n ≤ N :=
nat.find_min' (ramsey_fin_exists n) hN

lemma ramsey_number_min (hN : is_ramsey_valid V n) : ramsey_number n ≤ card V :=
ramsey_number_min_fin (hN.embedding (fintype.equiv_fin V).to_embedding)

lemma ramsey_number_le_iff : ramsey_number n ≤ card V ↔ is_ramsey_valid V n :=
⟨ramsey_number_spec, ramsey_number_min⟩

lemma ramsey_number_le_iff_fin : ramsey_number n ≤ N ↔ is_ramsey_valid (fin N) n :=
⟨λ h, (ramsey_number_spec_fin n).embedding (fin.cast_le h).to_embedding, ramsey_number_min_fin⟩

lemma ramsey_number_eq_of (h : is_ramsey_valid (fin (N + 1)) n) (h' : ¬ is_ramsey_valid (fin N) n) :
  ramsey_number n = N + 1 :=
by { rw ←ramsey_number_le_iff_fin at h h', exact h.antisymm (lt_of_not_le h') }

lemma ramsey_number_congr [decidable_eq K'] [fintype K'] {n' : K' → ℕ}
  (h : ∀ N, is_ramsey_valid (fin N) n ↔ is_ramsey_valid (fin N) n') :
  ramsey_number n = ramsey_number n' :=
(ramsey_number_min_fin ((h _).2 (ramsey_number_spec_fin _))).antisymm
  (ramsey_number_min_fin ((h _).1 (ramsey_number_spec_fin _)))

lemma ramsey_number_equiv [decidable_eq K'] [fintype K'] (f : K' ≃ K) :
  ramsey_number (n ∘ f) = ramsey_number n :=
ramsey_number_congr (λ _, is_ramsey_valid_equiv_right f)

lemma ramsey_number_first_swap {i : ℕ} (x y : ℕ) (t : fin i → ℕ) :
  ramsey_number (vec_cons x (vec_cons y t)) = ramsey_number (vec_cons y (vec_cons x t)) :=
begin
  have : vec_cons x (vec_cons y t) ∘ equiv.swap 0 1 = vec_cons y (vec_cons x t),
  { rw [function.funext_iff],
    simp only [fin.forall_fin_succ],
    refine ⟨rfl, rfl, λ j, _⟩,
    simp only [vec_cons, fin.cons_succ, function.comp_apply],
    rw [equiv.swap_apply_of_ne_of_ne, fin.cons_succ, fin.cons_succ],
    { exact fin.succ_ne_zero _ },
    exact (fin.succ_injective _).ne (fin.succ_ne_zero _) },
  rw [←this, ramsey_number_equiv],
end

lemma ramsey_number_pair_swap (x y : ℕ) : ramsey_number ![x, y] = ramsey_number ![y, x] :=
by rw ramsey_number_first_swap

lemma ramsey_number.eq_zero_iff : ramsey_number n = 0 ↔ ∃ c, n c = 0 :=
begin
  rw [←le_zero_iff, ramsey_number_le_iff_fin],
  exact ⟨λ h, h.exists_zero_of_is_empty, is_ramsey_valid_of_exists_zero _⟩,
end

lemma ramsey_number.exists_zero_of_eq_zero (h : ramsey_number n = 0) : ∃ c, n c = 0 :=
ramsey_number.eq_zero_iff.1 h

lemma ramsey_number_exists_zero (c : K) (hc : n c = 0) : ramsey_number n = 0 :=
ramsey_number.eq_zero_iff.2 ⟨c, hc⟩

lemma ramsey_number_pos : 0 < ramsey_number n ↔ (∀ c, n c ≠ 0) :=
by rw [pos_iff_ne_zero, ne.def, ramsey_number.eq_zero_iff, not_exists]

lemma ramsey_number_le_one (hc : ∃ c, n c ≤ 1) : ramsey_number n ≤ 1 :=
by { rw ramsey_number_le_iff_fin, exact ramsey_base hc }

lemma ramsey_number_ge_min [nonempty K] (i : ℕ) (hk : ∀ k, i ≤ n k) : i ≤ ramsey_number n :=
(is_ramsey_valid_min (ramsey_number_spec_fin n) hk).trans_eq (card_fin _)

lemma exists_le_of_ramsey_number_le [nonempty K] (i : ℕ) (hi : ramsey_number n ≤ i) :
  ∃ k, n k ≤ i :=
by { contrapose! hi, exact ramsey_number_ge_min (i + 1) hi }

@[simp] lemma ramsey_number_empty [is_empty K] : ramsey_number n = 2 :=
begin
  refine ramsey_number_eq_of _ _,
  { exact is_ramsey_valid.empty_colours },
  simp [is_ramsey_valid],
end

lemma ramsey_number_nil : ramsey_number ![] = 2 := ramsey_number_empty

lemma exists_le_one_of_ramsey_number_le_one (hi : ramsey_number n ≤ 1) : ∃ k, n k ≤ 1 :=
begin
  haveI : nonempty K,
  { rw ←not_is_empty_iff,
    introI,
    rw ramsey_number_empty at hi,
    norm_num at hi },
  exact exists_le_of_ramsey_number_le _ hi,
end

lemma ramsey_number_eq_one (hc : ∃ c, n c = 1) (hc' : ∀ c, n c ≠ 0) : ramsey_number n = 1 :=
begin
  obtain ⟨c, hc⟩ := hc,
  refine (ramsey_number_le_one ⟨c, hc.le⟩).antisymm _,
  rwa [nat.succ_le_iff, ramsey_number_pos],
end

lemma ramsey_number_eq_one_iff : (∃ c, n c = 1) ∧ (∀ c, n c ≠ 0) ↔ ramsey_number n = 1 :=
begin
  split,
  { rintro ⟨h₁, h₂⟩,
    exact ramsey_number_eq_one h₁ h₂ },
  intro h,
  have : ramsey_number n ≠ 0,
  { rw h, simp },
  rw [ne.def, ramsey_number.eq_zero_iff, not_exists] at this,
  obtain ⟨k, hk⟩ := exists_le_one_of_ramsey_number_le_one h.le,
  refine ⟨⟨k, hk.antisymm _⟩, this⟩,
  rw [nat.succ_le_iff, pos_iff_ne_zero],
  exact this _
end

lemma ramsey_number_unique_colour [unique K] : ramsey_number n = n default :=
begin
  refine le_antisymm (ramsey_number_min_fin (is_ramsey_valid_unique (by simp))) _,
  refine ramsey_number_ge_min _ (λ k, _),
  rw subsingleton.elim default k,
end

@[simp] lemma ramsey_number_singleton {i : ℕ} : ramsey_number ![i] = i :=
by rw [ramsey_number_unique_colour, matrix.cons_val_fin_one]

lemma ramsey_number.mono {n n' : K → ℕ} (h : n ≤ n') : ramsey_number n ≤ ramsey_number n' :=
by { rw [ramsey_number_le_iff_fin], exact (ramsey_number_spec_fin _).mono_right h }

lemma ramsey_number.mono_two {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
  ramsey_number ![a, c] ≤ ramsey_number ![b, d] :=
ramsey_number.mono (by { rw [pi.le_def, fin.forall_fin_two], exact ⟨hab, hcd⟩ })

lemma ramsey_number_monotone {i : ℕ} : monotone (ramsey_number : (fin i → ℕ) → ℕ) :=
λ _ _ h, ramsey_number.mono h

lemma ramsey_number_remove_two {n : K → ℕ} {n' : K' → ℕ} (f : K' → K)
  (hf : ∀ x : K', n' x ≠ 2 → n (f x) ≠ 2)
  (hf_inj : ∀ x y : K', n' x ≠ 2 → n' y ≠ 2 → f x = f y → x = y)
  (hf_surj : ∀ x : K, n x ≠ 2 → ∃ y : K', n' y ≠ 2 ∧ f y = x)
  (hf_comm : ∀ x : K', n' x ≠ 2 → n (f x) = n' x) :
  ramsey_number n' = ramsey_number n :=
ramsey_number_congr (λ N, is_ramsey_valid_two f hf hf_inj hf_surj hf_comm)

@[simp] lemma ramsey_number_cons_two {i : ℕ} {n : fin i → ℕ} :
  ramsey_number (matrix.vec_cons 2 n) = ramsey_number n :=
by { refine (ramsey_number_remove_two fin.succ _ _ _ _).symm; simp [fin.forall_fin_succ] }

@[simp] lemma ramsey_number_cons_zero {i : ℕ} {n : fin i → ℕ} :
  ramsey_number (matrix.vec_cons 0 n) = 0 :=
ramsey_number_exists_zero 0 (by simp)

lemma ramsey_number_cons_one_of_one_le {i : ℕ} {n : fin i → ℕ} (h : ∀ k, n k ≠ 0) :
  ramsey_number (matrix.vec_cons 1 n) = 1 :=
begin
  refine ramsey_number_eq_one ⟨0, rfl⟩ _,
  rw fin.forall_fin_succ,
  simpa using h,
end

lemma ramsey_number_one_succ {i : ℕ} : ramsey_number ![1, i+1] = 1 :=
ramsey_number_cons_one_of_one_le (by simp)

lemma ramsey_number_succ_one {i : ℕ} : ramsey_number ![i+1, 1] = 1 :=
by rw [ramsey_number_pair_swap, ramsey_number_one_succ]

lemma ramsey_number_two_left {i : ℕ} : ramsey_number ![2, i] = i := by simp
@[simp] lemma ramsey_number_two_right {i : ℕ} : ramsey_number ![i, 2] = i :=
by rw [ramsey_number_pair_swap, ramsey_number_two_left]

-- if the condition `h` fails, we find a stronger bound from previous results
-- cf `ramsey_number_le_one`
lemma ramsey_number_multicolour_bound (h : ∀ k, 2 ≤ n k) :
  ramsey_number n ≤ ∑ k, ramsey_number (function.update n k (n k - 1)) + 2 - card K :=
begin
  rw ramsey_number_le_iff_fin,
  exact ramsey_fin_induct' _ _ h (λ k, ramsey_number_spec_fin _),
end

-- if the conditions `hi` or `hj` fail, we find a stronger bound from previous results
-- cf `ramsey_number_le_one`
lemma ramsey_number_two_colour_bound_aux {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
  ramsey_number ![i, j] ≤ ramsey_number ![i - 1, j] + ramsey_number ![i, j - 1] :=
begin
  rw ramsey_number_le_iff_fin,
  refine ramsey_fin_induct_two hi hj _ _;
  exact ramsey_number_spec_fin _
end

lemma ramsey_number_two_colour_bound (i j : ℕ) (hij : i ≠ 1 ∨ j ≠ 1) :
  ramsey_number ![i, j] ≤ ramsey_number ![i - 1, j] + ramsey_number ![i, j - 1] :=
begin
  wlog h : i ≤ j,
  { refine (ramsey_number_pair_swap _ _).trans_le ((this _ _ hij.symm (le_of_not_le h)).trans _),
    rw [ramsey_number_pair_swap, add_comm, add_le_add_iff_right, ramsey_number_pair_swap] },
  rcases i with (_ | _ | _),
  { simp },
  { rcases j with (_ | _ | _),
    { simp },
    { simpa using hij },
    rw [ramsey_number_one_succ, nat.sub_self, ramsey_number_cons_zero, zero_add,
      nat.succ_sub_succ_eq_sub, nat.sub_zero, ramsey_number_one_succ] },
  have : 2 ≤ i + 2, { simp },
  exact ramsey_number_two_colour_bound_aux this (this.trans h),
end

-- a slightly odd shaped bound to make it more practical for explicit computations
lemma ramsey_number_two_colour_bound_even {i j} (Ni Nj : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j)
  (hNi : ramsey_number ![i - 1, j] ≤ Ni) (hNj : ramsey_number ![i, j - 1] ≤ Nj)
  (hNi' : even Ni) (hNj' : even Nj) :
  ramsey_number ![i, j] ≤ Ni + Nj - 1 :=
begin
  rw ramsey_number_le_iff_fin at ⊢ hNi hNj,
  exact ramsey_fin_induct_two_evens hi hj hNi' hNj' hNi hNj,
end

-- if the conditions `hi`, `hj` or `hk` fail, we find a stronger bound from previous results
-- cf `ramsey_number_le_one`
lemma ramsey_number_three_colour_bound {i j k : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) (hk : 2 ≤ k) :
  ramsey_number ![i, j, k] ≤
    ramsey_number ![i - 1, j, k] + ramsey_number ![i, j - 1, k] +
      ramsey_number ![i, j, k - 1] - 1 :=
begin
  rw ramsey_number_le_iff_fin,
  refine ramsey_fin_induct_three hi hj hk _ _ _;
  exact ramsey_number_spec_fin _
end

def diagonal_ramsey (k : ℕ) : ℕ := ramsey_number ![k, k]
lemma diagonal_ramsey.def {k : ℕ} : diagonal_ramsey k = ramsey_number ![k, k] := rfl

@[simp] lemma diagonal_ramsey_zero : diagonal_ramsey 0 = 0 := ramsey_number_cons_zero
@[simp] lemma diagonal_ramsey_one : diagonal_ramsey 1 = 1 :=
by rw [diagonal_ramsey.def, ramsey_number_one_succ]
@[simp] lemma diagonal_ramsey_two : diagonal_ramsey 2 = 2 :=
by rw [diagonal_ramsey.def, ramsey_number_cons_two, ramsey_number_singleton]
lemma diagonal_ramsey_monotone : monotone diagonal_ramsey :=
λ n m hnm, ramsey_number.mono_two hnm hnm

section paley

variables {F : Type*} [field F] [fintype F]

lemma symmetric_is_square (hF : card F % 4 ≠ 3) :
  symmetric (λ x y : F, is_square (x - y)) :=
λ _ _ h, by simpa using h.mul (finite_field.is_square_neg_one_iff.2 hF)

/--
The definition should only be used if card F % 4 ≠ 3. If this condition fails, the graph is ⊤.
-/
def {u} paley_graph (F : Type*) [field F] [fintype F] : simple_graph F :=
{ adj := λ x y, x ≠ y ∧ (is_square (x - y) ∨ card F % 4 = 3),
  symm :=
  begin
    rintro x y ⟨h₁, h₂⟩,
    refine ⟨h₁.symm, _⟩,
    rw or_iff_not_imp_right,
    intro h,
    exact symmetric_is_square h (h₂.resolve_right h),
  end,
  loopless := λ _ h, h.1 rfl }

lemma paley_graph_adj' {x y : F} :
  (paley_graph F).adj x y ↔ x ≠ y ∧ (is_square (x - y) ∨ card F % 4 = 3) :=
iff.rfl

instance paley_decidable [decidable_eq F] :
  decidable_rel (paley_graph F).adj :=
λ x y, decidable_of_iff' _ paley_graph_adj'

lemma paley_graph_adj (hF : card F % 4 ≠ 3) {x y : F} :
  (paley_graph F).adj x y ↔ x ≠ y ∧ is_square (x - y) :=
and_congr_right' (or_iff_left hF)

lemma is_square_sub_of_paley_graph_adj (hF : card F % 4 ≠ 3)  {x y : F}
  (h : (paley_graph F).adj x y) : is_square (x - y) :=
((paley_graph_adj hF).1 h).2
-- and_congr_right' (or_iff_left hF)

@[simps] def rotate (x : F) : paley_graph F ≃g paley_graph F :=
{ to_equiv := equiv.add_left x,
  map_rel_iff' := λ a b, by simp only [paley_graph_adj', equiv.coe_add_left, ne.def, add_right_inj,
    add_sub_add_left_eq_sub] }

/-- The graph automorphism rescaling the Paley graph by a square. -/
@[simps]
def rescale (x : F) (hx : is_square x) (hx' : x ≠ 0) :
  paley_graph F ≃g paley_graph F :=
{ to_equiv := (units.mk0 x hx').mul_left,
  map_rel_iff' :=
  begin
    intros a b,
    simp only [paley_graph],
    simp only [hx', units.mul_left_apply, units.coe_mk0, ne.def, mul_eq_mul_left_iff, or_false,
      not_and, and.congr_right_iff, not_false_iff, forall_true_left] {contextual := tt},
    intro h,
    have : a - b ≠ 0, { rwa sub_ne_zero },
    refine or_congr_left' _,
    haveI : decidable_eq F := classical.dec_eq F,
    rw ←quadratic_char_one_iff_is_square hx' at hx,
    rw [←not_iff_not, ←mul_sub, ←quadratic_char_neg_one_iff_not_is_square, map_mul, hx, one_mul,
      quadratic_char_neg_one_iff_not_is_square],
  end }

/-- The graph isomorphism witnessing that the Paley graph is self complementary. -/
@[simps]
def self_compl (hF : card F % 4 ≠ 3)
  (x : F) (hx : ¬ is_square x) : (paley_graph F)ᶜ ≃g paley_graph F :=
have hx' : x ≠ 0, from λ h, hx (h.symm ▸ is_square_zero F),
{ to_equiv := (units.mk0 x hx').mul_left,
  map_rel_iff' :=
  begin
    intros a b,
    rw [paley_graph_adj hF, compl_adj, paley_graph_adj hF],
    simp only [hx', units.mul_left_apply, units.coe_mk0, ne.def, mul_eq_mul_left_iff, or_false,
      not_and, and.congr_right_iff, not_false_iff, forall_true_left] {contextual := tt},
    intro h,
    have : a - b ≠ 0,
    { rwa sub_ne_zero },
    classical,
    rw ←quadratic_char_neg_one_iff_not_is_square at hx,
    rw [iff_not_comm, ←mul_sub, ←quadratic_char_neg_one_iff_not_is_square, map_mul, hx,
      ←quadratic_char_one_iff_is_square this, neg_mul, one_mul, neg_inj],
  end }

def paley_labelling (F : Type*) [field F] [fintype F] [decidable_eq F] :
  top_edge_labelling F (fin 2) := to_edge_labelling (paley_graph F)

-- smaller `k` don't need the paley construction
lemma no_paley_mono_set [decidable_eq F] {k : ℕ} (hF : card F % 4 = 1)
  (h : ∃ (m : finset F) c, (paley_labelling F).monochromatic_of m c ∧ k + 2 = m.card) :
  ∃ (m : finset F), m.card = k ∧ (0 : F) ∉ m ∧ (1 : F) ∉ m ∧
    (∀ x ∈ m, is_square x) ∧ (∀ x ∈ m, is_square (x - 1 : F)) ∧
      (m : set F).pairwise (λ x y, is_square (y - x)) :=
begin
  have card_not_three_mod_four : card F % 4 ≠ 3,
  { rw hF, simp only [ne.def, nat.one_eq_bit1, nat.one_ne_zero, not_false_iff]},
  have card_one_mod_two : card F % 2 = 1,
  { rw [←nat.mod_mod_of_dvd (card F) (show 2 ∣ 4, by norm_num), hF, nat.one_mod] },
  have : ∃ x : F, ¬ is_square x,
  { apply finite_field.exists_nonsquare,
    rwa [ne.def, finite_field.even_card_iff_char_two, nat.mod_two_ne_zero] },
  rw [exists_comm] at h,
  simp only [is_ramsey_valid_iff_embedding_aux] at h,
  rw [fin.exists_fin_two, paley_labelling, to_edge_labelling_label_graph,
    to_edge_labelling_label_graph_compl] at h,
  have : nonempty ((⊤ : simple_graph (fin (k + 2))) ↪g paley_graph F),
  { rcases h with ⟨⟨h⟩⟩ | h,
    { obtain ⟨x, hx⟩ := this,
      exact ⟨h.trans (self_compl card_not_three_mod_four x hx).to_rel_embedding⟩ },
    exact h },
  have : ∃ f : (⊤ : simple_graph (fin (k + 2))) ↪g paley_graph F, f 0 = 0,
  { obtain ⟨f⟩ := this,
    exact ⟨f.trans (rotate (- f 0)).to_rel_embedding, by simp⟩ },
  have : ∃ f : (⊤ : simple_graph (fin (k + 2))) ↪g paley_graph F, f 0 = 0 ∧ f 1 = 1,
  { obtain ⟨f, hf⟩ := this,
    have hf1 : is_square (f 1),
    { suffices : (paley_graph F).adj (f 1) (f 0),
      { rw [paley_graph_adj card_not_three_mod_four, hf, sub_zero] at this,
        exact this.2 },
      rw f.map_rel_iff,
      simp only [top_adj, ne.def, fin.one_eq_zero_iff, nat.succ_succ_ne_one, not_false_iff] },
    have hf2 : f 1 ≠ 0,
    { rw [←hf, ne.def, rel_embedding.inj],
      simp only [fin.one_eq_zero_iff, nat.succ_succ_ne_one, not_false_iff] },
    refine ⟨f.trans (rescale (f 1) hf1 hf2).symm.to_rel_embedding, _⟩,
    simp only [hf2, hf, rel_iso.to_rel_embedding_eq_coe, embedding.coe_comp, rel_iso.coe_coe_fn,
      function.comp_app, rescale_symm_apply, units.coe_inv, units.coe_mk0, mul_zero,
      eq_self_iff_true, inv_mul_cancel, ne.def, not_false_iff, and_self] },
  have hss : symmetric (λ x y : F, is_square (y - x)),
  { intros x y h,
    exact symmetric_is_square card_not_three_mod_four h },
  suffices : ∃ m : finset F, k = m.card ∧ (0 : F) ∉ m ∧ (1 : F) ∉ m ∧
    (insert (0 : F) (insert (1 : F) (m : set F))).pairwise (λ x y, is_square (y - x)),
  { obtain ⟨m, hm_card, hm₀, hm₁, hm₂⟩ := this,
    rw [set.pairwise_insert_of_symmetric_of_not_mem hss,
      set.pairwise_insert_of_symmetric_of_not_mem hss] at hm₂,
    simp only [mem_coe, set.mem_insert_iff, sub_zero, forall_eq_or_imp, is_square_one,
      true_and] at hm₂,
    { exact ⟨m, hm_card.symm, hm₀, hm₁, hm₂.2, hm₂.1.2, hm₂.1.1⟩ },
    { exact hm₁ },
    simp only [hm₀, set.mem_insert_iff, zero_ne_one, mem_coe, or_self, not_false_iff] },
  simp only [←coe_insert],
  obtain ⟨f, hf₀, hf₁⟩ := this,
  have : ({0, 1} : finset F) ⊆ finset.map f.to_embedding univ,
  { rw [insert_subset, singleton_subset_iff, ←hf₀, ←hf₁],
    exact ⟨mem_map_of_mem _ (by simp), mem_map_of_mem _ (by simp)⟩ },
  refine ⟨(univ : finset (fin (k + 2))).map f.to_embedding \ {0, 1}, _, _, _, _⟩,
  { rw [card_sdiff, card_map, card_doubleton, card_fin, nat.add_sub_cancel],
    { simp only [ne.def, zero_ne_one, not_false_iff] },
    exact this },
  { simp only [mem_sdiff, mem_insert, eq_self_iff_true, mem_singleton, zero_ne_one, or_false,
      not_true, and_false, not_false_iff] },
  { simp only [mem_sdiff, mem_insert, one_ne_zero, mem_singleton, eq_self_iff_true, false_or,
      not_true, and_false, not_false_iff]},
  rw [insert_eq, insert_eq, ←union_assoc, ←insert_eq, union_comm, sdiff_union_of_subset this],
  simp only [set.pairwise, mem_coe, mem_map, exists_prop, mem_univ, true_and, forall_exists_index,
    ne.def, rel_embedding.coe_fn_to_embedding, forall_apply_eq_imp_iff', rel_embedding.inj],
  intros x y h,
  exact is_square_sub_of_paley_graph_adj card_not_three_mod_four (f.map_rel_iff.2 (ne.symm h)),
end

-- lemma is_square_fin_5 : ∀ (x : fin 5), is_square x → x ∈ ({0, 1, 4} : set (fin 5)) :=
-- begin
--   -- simp only [is_square, set.mem_insert_iff, set.mem_singleton_iff, forall_exists_index,
--   --   forall_eq_apply_imp_iff'],
--   -- intro x,
--   -- fin_cases x;
--   -- norm_num
-- end

-- #lint

lemma card_non_zero_square_non_square {F : Type*} [fintype F] [field F] [decidable_eq F]
  (hF : ring_char F ≠ 2) :
  (univ.filter (λ x : F, x ≠ 0 ∧ is_square x)).card = card F / 2 ∧
  (univ.filter (λ x : F, ¬ is_square x)).card = card F / 2 :=
begin
  have : (univ.filter (λ x : F, ¬ is_square x)) = (univ.filter (λ x : F, x ≠ 0 ∧ ¬ is_square x)),
  { refine filter_congr _,
    simp [not_imp_not] {contextual := tt} },
  rw this,
  have cf := quadratic_char_sum_zero hF,
  simp only [quadratic_char_apply, quadratic_char_fun] at cf,
  rw [sum_ite, sum_const_zero, zero_add, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
    mul_neg, mul_one, mul_one, add_neg_eq_zero, nat.cast_inj, filter_filter, filter_filter] at cf,
  rw [←cf, and_self],
  have : (univ.filter (λ x : F, x ≠ 0 ∧ is_square x)) ∪
    (univ.filter (λ x : F, x ≠ 0 ∧ ¬ is_square x)) ∪ {0} = univ,
  { simp only [←filter_or, ←and_or_distrib_left, em, and_true, filter_ne'],
    rw [union_comm, ←insert_eq, insert_erase],
    exact mem_univ _ },
  have h' := congr_arg finset.card this,
  rw [card_disjoint_union, card_disjoint_union, card_singleton, card_univ, ←cf, ←two_mul,
    ←bit0_eq_two_mul, ←bit1] at h',
  { rw [←h', nat.bit1_div_two] },
  { rw finset.disjoint_left,
    simp {contextual := tt} },
  { simp },
end

lemma card_square (F : Type*) [fintype F] [field F] (hF : ring_char F ≠ 2) :
  ((univ : finset F).filter is_square).card = card F / 2 + 1 :=
begin
  rw [←(card_non_zero_square_non_square hF).1],
  simp only [and_comm, ←filter_filter, filter_ne'],
  rw card_erase_add_one,
  simp
end

lemma paley_five_bound : ¬ is_ramsey_valid (zmod 5) ![3, 3] :=
begin
  haveI : fact (nat.prime 5) := ⟨by norm_num⟩,
  classical,
  rw is_ramsey_valid_iff_eq,
  intro h,
  specialize h (paley_labelling (zmod 5)),
  have : ∃ (m : finset (zmod 5)) (c : fin 2),
    (paley_labelling (zmod 5)).monochromatic_of m c ∧ 3 = m.card,
  { simpa only [fin.exists_fin_two] using h },
  have := no_paley_mono_set (by norm_num) this,
  simp only [card_eq_one, ←exists_and_distrib_right, @exists_comm (finset (zmod 5)), exists_eq_left,
    mem_singleton, forall_eq, coe_singleton, set.pairwise_singleton, and_true] at this,
  revert this,
  dec_trivial,
end

lemma paley_seventeen_helper :
  ∀ (a : zmod 17), a ≠ 0 → a ≠ 1 → is_square a → is_square (a - 1) → a = 2 ∨ a = 9 ∨ a = 16 :=
by dec_trivial

lemma paley_seventeen_bound : ¬ is_ramsey_valid (zmod 17) ![4, 4] :=
begin
  haveI : fact (nat.prime 17) := ⟨by norm_num⟩,
  classical,
  rw is_ramsey_valid_iff_eq,
  intro h,
  specialize h (paley_labelling (zmod 17)),
  have : ∃ (m : finset (zmod 17)) (c : fin 2),
    (paley_labelling (zmod 17)).monochromatic_of m c ∧ 4 = m.card,
  { simpa only [fin.exists_fin_two] using h },
  have := no_paley_mono_set (by norm_num) this,
  simp only [card_eq_two, ←exists_and_distrib_right, and_assoc, ne.def, exists_eq_left, mem_insert,
    @exists_comm (finset (zmod 17)), exists_and_distrib_left, mem_singleton, forall_eq_or_imp,
    forall_eq, coe_pair, not_or_distrib, @eq_comm (zmod 17) 0, @eq_comm (zmod 17) 1] at this,
  obtain ⟨a, b, hab, ha₀, hb₀, ha₁, hb₁, ha, hb, ha₁', hb₁', h⟩ := this,
  rw set.pairwise_insert_of_symmetric_of_not_mem at h,
  rotate,
  { intros x y h,
    exact symmetric_is_square (by norm_num) h },
  { exact hab },
  simp only [set.pairwise_singleton, set.mem_singleton_iff, forall_eq, true_and] at h,
  have : a = 2 ∨ a = 9 ∨ a = 16 := paley_seventeen_helper a ha₀ ha₁ ha ha₁',
  have : b = 2 ∨ b = 9 ∨ b = 16 := paley_seventeen_helper b hb₀ hb₁ hb hb₁',
  clear ha₀ ha₁ ha ha₁' hb₀ hb₁ hb hb₁',
  revert h hab,
  revert a b,
  dec_trivial,
end

end paley

lemma diagonal_ramsey_three : diagonal_ramsey 3 = 6 :=
begin
  refine le_antisymm _ _,
  { exact (ramsey_number_two_colour_bound 3 3 (by norm_num)).trans_eq (by simp) },
  rw [←not_lt, nat.lt_succ_iff, ←zmod.card 5, diagonal_ramsey.def, ramsey_number_le_iff],
  exact paley_five_bound
end

lemma ramsey_number_three_four_upper : ramsey_number ![3, 4] ≤ 9 :=
begin
  refine (ramsey_number_two_colour_bound_even 4 6 _ _ _ _ _ _).trans_eq _,
  { norm_num },
  { norm_num },
  { norm_num },
  { rw [nat.succ_sub_succ_eq_sub, tsub_zero, ←diagonal_ramsey, diagonal_ramsey_three] },
  { norm_num },
  { norm_num },
  { norm_num },
end

lemma diagonal_ramsey_four : diagonal_ramsey 4 = 18 :=
begin
  refine le_antisymm _ _,
  { refine (ramsey_number_two_colour_bound 4 4 (by norm_num)).trans _,
    simp only [nat.succ_sub_succ_eq_sub, tsub_zero],
    rw ramsey_number_pair_swap 4,
    linarith [ramsey_number_three_four_upper] },
  rw [←not_lt, nat.lt_succ_iff, ←zmod.card 17, diagonal_ramsey.def, ramsey_number_le_iff],
  exact paley_seventeen_bound
end

lemma ramsey_number_three_four : ramsey_number ![3, 4] = 9 :=
begin
  refine eq_of_le_of_not_lt ramsey_number_three_four_upper _,
  intro h,
  have : diagonal_ramsey 4 ≤ 16,
  { refine (ramsey_number_two_colour_bound 4 4 (by norm_num)).trans _,
    simp only [nat.succ_sub_succ_eq_sub, tsub_zero],
    rw ramsey_number_pair_swap 4,
    linarith only [h] },
  rw diagonal_ramsey_four at this,
  norm_num at this,
end

section

def parts : fin 3 → finset (fin 4 → zmod 2) :=
![{(![1, 1, 0, 0]), (![0, 0, 1, 1]), (![1, 0, 0, 1]), (![1, 1, 1, 0]), (![1, 0, 0, 0])},
  {(![1, 0, 1, 0]), (![0, 1, 0, 1]), (![0, 1, 1, 0]), (![1, 1, 0, 1]), (![0, 1, 0, 0])},
  {(![0, 0, 0, 1]), (![0, 0, 1, 0]), (![0, 1, 1, 1]), (![1, 0, 1, 1]), (![1, 1, 1, 1])}]

lemma parts_property : ∀ i : fin 3, ∀ x y ∈ parts i, x + y ∉ parts i := by dec_trivial.
lemma parts_cover : ∀ i : fin 4 → zmod 2, i ≠ 0 → ∃ j, i ∈ parts j := by dec_trivial.
lemma parts_disjoint :
  ∀ (i : fin 4 → zmod 2) (j : fin 3), i ∈ parts j → ∀ k : fin 3, i ∈ parts k → j = k :=
dec_trivial

lemma parts_get_aux : ∀ i : fin 4 → zmod 2, i ≠ 0 →
  ∃! j, j ∈ (univ : finset (fin 3)) ∧ i ∈ parts j :=
begin
  intros i hi,
  obtain ⟨j, hj⟩ := parts_cover i hi,
  exact ⟨j, ⟨mem_univ _, hj⟩, λ k hk, parts_disjoint _ _ hk.2 _ hj⟩,
end

lemma parts_pair_get_aux : ∀ i j : fin 4 → zmod 2, i ≠ j →
  ∃! k, k ∈ (univ : finset (fin 3)) ∧ i - j ∈ parts k :=
λ i j hij, parts_get_aux _ (sub_ne_zero_of_ne hij)

def parts_pair_get (i j : fin 4 → zmod 2) (hij : i ≠ j) : fin 3 :=
finset.choose _ _ (parts_pair_get_aux i j hij)

lemma parts_pair_get_spec {i j : fin 4 → zmod 2} (hij : i ≠ j) :
  i - j ∈ parts (parts_pair_get i j hij) :=
finset.choose_property _ _ (parts_pair_get_aux i j hij)

lemma parts_pair_get_spec' {i j : fin 4 → zmod 2} {c : fin 3} {hij : i ≠ j}
  (h : parts_pair_get i j hij = c) : i + j ∈ parts c :=
by { rw [←h, ←char_two.sub_eq_add], exact parts_pair_get_spec _ }

lemma parts_pair_get_symm (i j : fin 4 → zmod 2) (hij : i ≠ j) :
  parts_pair_get j i hij.symm = parts_pair_get i j hij :=
begin
  have : i - j = j - i,
  { rw [char_two.sub_eq_add, char_two.sub_eq_add, add_comm] },
  refine parts_disjoint (j - i) _ (parts_pair_get_spec hij.symm) _ _,
  rw ←this,
  exact parts_pair_get_spec hij
end

def clebsch_colouring : top_edge_labelling (fin 4 → zmod 2) (fin 3) :=
top_edge_labelling.mk parts_pair_get parts_pair_get_symm

lemma clebsch_bound : ¬ is_ramsey_valid (fin 4 → zmod 2) ![3, 3, 3] :=
begin
  rw is_ramsey_valid_iff_eq,
  push_neg,
  refine ⟨clebsch_colouring, _⟩,
  rintro m c hm hc,
  have : m.card = 3,
  { clear hm,
    revert c,
    simp only [fin.forall_fin_succ, fin.forall_fin_two, matrix.cons_val_zero, fin.succ_zero_eq_one',
      matrix.cons_val_one, matrix.head_cons, fin.succ_one_eq_two', and_self, eq_comm, imp_self,
      matrix.cons_vec_bit0_eq_alt0, matrix.cons_vec_append, matrix.empty_vec_append,
      matrix.cons_vec_alt0] },
  clear hc,
  rw card_eq_three at this,
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := this,
  have hxyz : x ∉ ({y, z} : set (fin 4 → zmod 2)), { simp [hxy, hxz] },
  have hyz' : y ∉ ({z} : set (fin 4 → zmod 2)), { simp [hyz] },
  simp only [coe_insert, coe_pair, monochromatic_of_insert hxyz, monochromatic_of_insert hyz',
    set.mem_singleton_iff, set.mem_insert_iff, monochromatic_of_singleton, true_and,
    clebsch_colouring, top_edge_labelling.mk_get] at hm,
  have hyz'' := parts_pair_get_spec' (hm.1 _ rfl),
  have hxy'' := parts_pair_get_spec' (hm.2 _ (or.inl rfl)),
  have hxz'' := parts_pair_get_spec' (hm.2 _ (or.inr rfl)),
  apply parts_property _ _ hxz'' _ hyz'',
  rwa [←char_two.sub_eq_add, add_sub_add_right_eq_sub, char_two.sub_eq_add],
end

end

lemma ramsey_number_three_three_three : ramsey_number ![3, 3, 3] = 17 :=
begin
  refine le_antisymm _ _,
  { refine (ramsey_number_three_colour_bound (nat.le_succ _) (nat.le_succ _)
      (nat.le_succ _)).trans _,
    rw [nat.succ_sub_succ_eq_sub, tsub_zero, ramsey_number_first_swap 3],
    have : ramsey_number ![3, 3, 2] = ramsey_number ![2, 3, 3],
    { have : ![2, 3, 3] ∘ ⇑(fin_rotate 3) = ![3, 3, 2],
      { dec_trivial },
      rw [←this, ramsey_number_equiv] },
    rw [this, ramsey_number_cons_two, ←diagonal_ramsey, diagonal_ramsey_three] },
  rw [←not_lt, nat.lt_succ_iff],
  have := clebsch_bound,
  rw [←ramsey_number_le_iff, fintype.card_fun, zmod.card, fintype.card_fin] at this,
  exact this
end

lemma ramsey_number_le_choose : ∀ (i j : ℕ), ramsey_number ![i, j] ≤ (i + j - 2).choose (i - 1)
| 0 _ := by simp
| _ 0 := by { rw [ramsey_number_pair_swap, ramsey_number_cons_zero], exact zero_le' }
| 1 (j+1) := by rw [ramsey_number_one_succ, nat.choose_zero_right]
| (i+1) 1 := by rw [ramsey_number_succ_one, nat.succ_sub_succ_eq_sub, nat.choose_self]
| (i+2) (j+2) :=
  begin
    refine (ramsey_number_two_colour_bound_aux (nat.le_add_left _ _) (nat.le_add_left _ _)).trans _,
    rw [nat.add_succ_sub_one, nat.add_succ_sub_one, ←add_assoc, nat.add_sub_cancel],
    refine (add_le_add (ramsey_number_le_choose _ _) (ramsey_number_le_choose _ _)).trans _,
    rw [add_add_add_comm, nat.add_sub_cancel, ←add_assoc, nat.add_sub_cancel, add_add_add_comm,
      add_right_comm i 2, nat.choose_succ_succ (i + j + 1) i],
    refl,
  end

lemma diagonal_ramsey_le_central_binom (i : ℕ) : diagonal_ramsey i ≤ (i - 1).central_binom :=
(ramsey_number_le_choose i i).trans_eq
  (by rw [nat.central_binom_eq_two_mul_choose, nat.mul_sub_left_distrib, mul_one, two_mul])

lemma diagonal_ramsey_le_central_binom' (i : ℕ) : diagonal_ramsey i ≤ i.central_binom :=
(diagonal_ramsey_le_central_binom _).trans (central_binom_monotone (nat.sub_le _ _))

section

lemma nat.choose_le_two_pow {n k : ℕ} : n.choose k ≤ 2 ^ n :=
begin
  cases le_or_lt k n,
  { rw ←nat.sum_range_choose n,
    refine single_le_sum (λ _ _, zero_le') _,
    rwa mem_range_succ_iff },
  rw nat.choose_eq_zero_of_lt h,
  exact zero_le'
end

lemma asc_le_pow_mul_factorial {s t : ℕ} : t.asc_factorial s ≤ s.factorial * (t + 1) ^ s :=
begin
  induction s with s ih,
  { simp },
  rw [nat.asc_factorial_succ, nat.factorial_succ, pow_succ, mul_mul_mul_comm],
  refine nat.mul_le_mul _ ih,
  rw [add_comm t, add_one_mul, mul_add_one, add_assoc],
  simp,
end

lemma choose_add_le_pow_left (s t : ℕ) : (s + t).choose s ≤ (t + 1) ^ s :=
begin
  rw [add_comm, nat.choose_eq_asc_factorial_div_factorial],
  exact nat.div_le_of_le_mul asc_le_pow_mul_factorial,
end

lemma choose_le_pow_left (s t : ℕ) : s.choose t ≤ (s + 1 - t) ^ t :=
begin
  cases le_or_lt t s,
  { obtain ⟨s, rfl⟩ := exists_add_of_le h,
    refine (choose_add_le_pow_left t s).trans _,
    rw [add_assoc, nat.add_sub_cancel_left] },
  rw nat.choose_eq_zero_of_lt h,
  exact zero_le'
end

end

lemma ramsey_number_pair_le_two_pow {i j : ℕ} : ramsey_number ![i, j] ≤ 2 ^ (i + j - 2) :=
(ramsey_number_le_choose _ _).trans nat.choose_le_two_pow

lemma ramsey_number_pair_le_two_pow' {i j : ℕ} : ramsey_number ![i, j] ≤ 2 ^ (i + j) :=
ramsey_number_pair_le_two_pow.trans (pow_le_pow one_le_two (nat.sub_le _ _))

lemma diagonal_ramsey_le_four_pow_sub_one {i : ℕ} : diagonal_ramsey i ≤ 4 ^ (i - 1) :=
ramsey_number_pair_le_two_pow.trans_eq
  (by rw [(show 4 = 2 ^ 2, from rfl), ←pow_mul, nat.mul_sub_left_distrib, two_mul, mul_one])

lemma diagonal_ramsey_le_four_pow {i : ℕ} : diagonal_ramsey i ≤ 4 ^ i :=
diagonal_ramsey_le_four_pow_sub_one.trans (pow_le_pow (by norm_num) (nat.sub_le _ _))

/-- A good bound when i is small and j is large. For `i = 1, 2` this is equality (as long as
`j ≠ 0`), and for `i = 3` it is the best possible polynomial upper bound. -/
lemma ramsey_number_le_right_pow_left (i j : ℕ) : ramsey_number ![i, j] ≤ j ^ (i - 1) :=
begin
  rcases nat.eq_zero_or_pos j with rfl | hj,
  { rw [ramsey_number_pair_swap, ramsey_number_cons_zero],
    exact zero_le' },
  refine (ramsey_number_le_choose i j).trans _,
  refine (nat.choose_le_choose _ add_tsub_add_le_tsub_add_tsub).trans _,
  refine (choose_add_le_pow_left _ _).trans_eq _,
  rw nat.sub_add_cancel hj,
end

/-- A simplification of `ramsey_number_le_right_pow_left` which is more convenient for asymptotic
reasoning. -/
lemma ramsey_number_le_right_pow_left' {i j : ℕ} : ramsey_number ![i, j] ≤ j ^ i :=
(ramsey_number_le_right_pow_left (i + 1) j).trans' $ ramsey_number.mono_two (by simp) le_rfl

end simple_graph
