import combinatorics.simple_graph.basic
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

namespace simple_graph
variables {V V' : Type*} {G : simple_graph V} {K K' : Type*}

open fintype (card)
open finset

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

instance finset.decidable_rel_sup
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
  have : is_ramsey_valid (m k) (function.update n k (n k - 1)) := (hN k).card_fin (by simp [hk]),
  obtain ⟨m', k', hm', hk'⟩ := this (C.pullback (function.embedding.subtype _)),
  rcases ne_or_eq k k' with hk | rfl,
  { exact ⟨_, _, hm'.map, by simpa [hk.symm] using hk'⟩ },
  have : x ∉ (m'.map (function.embedding.subtype _) : set V),
  { simp },
  refine ⟨insert x (m'.map (function.embedding.subtype _)), k, _, _⟩,
  { rw [coe_insert, top_edge_labelling.monochromatic_of_insert this],
    refine ⟨hm'.map, λ y hy, _⟩,
    generalize_proofs,
    simp only [mem_neighbor_finset, mem_coe, mem_map, function.embedding.coe_subtype, exists_prop,
      subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right,
      top_edge_labelling.label_graph_adj] at hy,
    obtain ⟨⟨_, t⟩, _⟩ := hy,
    exact t },
  rw [card_insert_of_not_mem this, card_map, ←tsub_le_iff_right],
  rwa function.update_same at hk',
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

lemma ramsey_number_pair_swap (x y : ℕ) : ramsey_number ![x, y] = ramsey_number ![y, x] :=
begin
  have : ![x, y] ∘ equiv.swap 0 1 = ![y, x],
  { ext i,
    fin_cases i;
    simp },
  rw [←this, ramsey_number_equiv],
end

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
lemma ramsey_number_two_colour_bound {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j) :
  ramsey_number ![i, j] ≤ ramsey_number ![i - 1, j] + ramsey_number ![i, j - 1] :=
begin
  rw ramsey_number_le_iff_fin,
  refine ramsey_fin_induct_two hi hj _ _;
  exact ramsey_number_spec_fin _
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

@[simp] lemma diagonal_ramsey_three_upper : diagonal_ramsey 3 ≤ 6 :=
begin
  rw diagonal_ramsey.def,
  refine (ramsey_number_two_colour_bound _ _).trans_eq (by simp);
  norm_num,
end

section paley

variables {F : Type*} [field F] [fintype F]

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
    simpa only [mul_neg, mul_one, neg_sub]
      using (h₂.resolve_right h).mul (finite_field.is_square_neg_one_iff.2 h),
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
lemma no_paley_mono_set {k : ℕ} (hF : card F % 4 = 1)
  {h : ∃ (m : finset F) c, (paley_labelling F).monochromatic_of m c ∧ k + 2 = m.card} :
  false :=
begin
  have card_not_three_mod_four : card F % 4 ≠ 3,
  { rw hF, simp },
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


end

example : 1 = 1 :=
begin

end


-- lemma is_ramsey_valid_paley_labelling_aux {n : ℕ} :
  -- nonempty ((⊤ : simple_graph (fin n)) ↪g paley_graph F) ↔

end paley

-- lemma is_ramsey_valid_iff_embedding_aux {n : K → ℕ} (c : K) :
--   (∃ (m : finset V), C.monochromatic_of m c ∧ n c = m.card) ↔
--     nonempty ((⊤ : simple_graph (fin (n c))) ↪g C.label_graph c) :=

-- lemma is_ramsey_valid_iff_embedding {n : K → ℕ} :
--   is_ramsey_valid V n ↔
--     ∀ C : top_edge_labelling V K,
--       ∃ c : K, nonempty ((⊤ : simple_graph (fin (n c))) ↪g C.label_graph c) :=

-- def bad_five_colouring : top_edge_labelling (zmod 5) (fin 2) :=
-- top_edge_labelling.mk
--   (λ x y _, if y - x = 1 ∨ x - y = 1 then 0 else 1)
--   (by { intros x y h, simp only [or_comm] })

-- lemma diagonal_ramsey_three_lower : 5 < diagonal_ramsey 3 :=
-- begin
--   rw [←not_le, diagonal_ramsey.def, ←zmod.card 5, ramsey_number_le_iff, is_ramsey_valid_iff_eq],
--   -- ramsey_number_le_iff, is_ramsey_valid],
--   simp only [not_forall, not_exists, not_and, not_le, fin.succ_one_eq_two'],
--   refine ⟨bad_five_colouring, _⟩,
-- end

-- ramsey_fin_induct :
--   ∀ {K : Type u_5} [_inst_1 : decidable_eq K] [_inst_2 : fintype K] (n N : K → ℕ),
--     (∀ (k : K), is_ramsey_valid (fin (N k)) (function.update n k (n k - 1))) →
--     is_ramsey_valid (fin (∑ (k : K), (N k - 1) + 2)) n

-- lemma ramsey_number_multicolour_bound

end simple_graph
