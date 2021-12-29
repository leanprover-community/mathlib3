/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.subgraph
import data.finset.interval
import data.sym.card

/-!
# Stuff that belongs in mathlib

## TODO

`finset.sym` forms a Galois connection between `finset α` and `finset (sym α n)`. Similar for
`finset.sym2`.
-/

open finset

variables {α β : Type*} {G : simple_graph α}

namespace sym2

lemma out_fst_mem (e : sym2 α) : e.out.1 ∈ e := ⟨e.out.2, by rw [prod.mk.eta, e.out_eq]⟩
lemma out_snd_mem (e : sym2 α) : e.out.2 ∈ e := ⟨e.out.1, by rw [eq_swap, prod.mk.eta, e.out_eq]⟩

lemma ball {p : α → Prop} {a b : α} : (∀ c ∈ ⟦(a, b)⟧, p c) ↔ p a ∧ p b :=
begin
  refine ⟨λ h, ⟨h _ $ mem_mk_left _ _, h _ $ mem_mk_right _ _⟩, λ h c hc, _⟩,
  obtain rfl | rfl := sym2.mem_iff.1 hc,
  { exact h.1 },
  { exact h.2 }
end

end sym2

lemma subtype.coe_inj {p : α → Prop} {a b : subtype p} : (a : α) = b ↔ a = b :=
subtype.coe_injective.eq_iff

namespace sym
variables {n : ℕ} {s t : sym α n} {a b : α}

instance : has_coe (sym α n) (multiset α) := coe_subtype

lemma coe_injective : function.injective (coe : sym α n → multiset α) := subtype.coe_injective

lemma coe_inj : s.val = t.val ↔ s = t := subtype.coe_inj

lemma coe_repeat : (repeat a n : multiset α) = multiset.repeat a n := rfl

@[simp] lemma mem_repeat : b ∈ repeat a n ↔ n ≠ 0 ∧ b = a := multiset.mem_repeat

lemma eq_repeat_iff : s = repeat a n ↔ ∀ b ∈ s, b = a :=
begin
  rw [subtype.ext_iff, coe_repeat],
  convert multiset.eq_repeat',
  exact s.2.symm,
end

end sym

namespace finset

lemma disjoint_filter_filter_neg [decidable_eq α] (s : finset α) (p : α → Prop) [decidable_pred p] :
  disjoint (s.filter p) (s.filter $ λ a, ¬ p a) :=
disjoint_filter.2 $ λ a _, not_not.2

@[simp] lemma diag_union_off_diag [decidable_eq α] (s : finset α) :
  s.diag ∪ s.off_diag = s.product s :=
filter_union_filter_neg_eq _ _

@[simp] lemma disjoint_diag_off_diag [decidable_eq α] (s : finset α) : disjoint s.diag s.off_diag :=
disjoint_filter_filter_neg _ _

lemma is_diag_mk_of_mem_diag {s : finset α} [decidable_eq α] {a : α × α} (h : a ∈ s.diag) :
  sym2.is_diag ⟦a⟧ :=
(sym2.is_diag_iff_proj_eq _).2 ((mem_diag _ _).1 h).2

lemma not_is_diag_mk_of_mem_off_diag {s : finset α} [decidable_eq α] {a : α × α}
  (h : a ∈ s.off_diag) :
  ¬ sym2.is_diag ⟦a⟧ :=
by { rw sym2.is_diag_iff_proj_eq, exact ((mem_off_diag _ _).1 h).2.2 }

@[simp] lemma product_eq_empty {s : finset α} {t : finset β} : s.product t = ∅ ↔ s = ∅ ∨ t = ∅ :=
by rw [←not_nonempty_iff_eq_empty, nonempty_product, not_and_distrib, not_nonempty_iff_eq_empty,
  not_nonempty_iff_eq_empty]

section sym2
variables [decidable_eq α]

/-- Lifts a finset to `sym2 α`. `s.sym2` is the finset of all pairs with elements in `s`. -/
protected def sym2 (s : finset α) : finset (sym2 α) := (s.product s).image quotient.mk

variables {s t : finset α} {e : sym2 α} {a b : α}

@[simp] lemma mem_sym2_iff : e ∈ s.sym2 ↔ ∀ a ∈ e, a ∈ s :=
begin
  refine mem_image.trans
    ⟨_, λ h, ⟨e.out, mem_product.2 ⟨h _ e.out_fst_mem, h _ e.out_snd_mem⟩, e.out_eq⟩⟩,
  rintro ⟨⟨a, b⟩, h, rfl⟩,
  rw sym2.ball,
  rwa mem_product at h,
end

lemma mk_mem_sym2_iff : ⟦(a, b)⟧ ∈ s.sym2 ↔ a ∈ s ∧ b ∈ s := by rw [mem_sym2_iff, sym2.ball]

@[simp] lemma sym2_empty : (∅ : finset α).sym2 = ∅ := rfl

@[simp] lemma sym2_eq_empty : s.sym2 = ∅ ↔ s = ∅ :=
by rw [finset.sym2, image_eq_empty, product_eq_empty, or_self]

@[simp] lemma sym2_nonempty : s.sym2.nonempty ↔ s.nonempty :=
by rw [finset.sym2, nonempty.image_iff, nonempty_product, and_self]

alias sym2_nonempty ↔ _ finset.nonempty.sym2

attribute [protected] finset.nonempty.sym2

@[simp] lemma sym2_univ [fintype α] : (univ : finset α).sym2 = univ := rfl

@[simp] lemma sym2_singleton (a : α) : ({a} : finset α).sym2 = {sym2.diag a} :=
by rw [finset.sym2, singleton_product_singleton, image_singleton, sym2.diag]

@[simp] lemma diag_mem_sym2_iff : sym2.diag a ∈ s.sym2 ↔ a ∈ s :=
mk_mem_sym2_iff.trans $ and_self _

@[simp] lemma sym2_mono (h : s ⊆ t) : s.sym2 ⊆ t.sym2 :=
begin
  intros e he,
  rw mem_sym2_iff at ⊢ he,
  exact λ a ha, h (he _ ha),
end

lemma image_diag_union_image_off_diag :
  s.diag.image quotient.mk ∪ s.off_diag.image quotient.mk = s.sym2 :=
by { rw [←image_union, diag_union_off_diag], refl }

/-- **Stars and bars** for the case `n = 2`. -/
lemma card_sym2 (s : finset α) : s.sym2.card = s.card * (s.card + 1) / 2 :=
begin
  rw [←image_diag_union_image_off_diag, card_union_eq, sym2.card_image_diag,
    sym2.card_image_off_diag, nat.choose_two_right, add_comm, ←nat.triangle_succ, nat.succ_sub_one,
    mul_comm],
  rintro e he,
  rw [inf_eq_inter, mem_inter, mem_image, mem_image] at he,
  obtain ⟨⟨a, ha, rfl⟩, b, hb, hab⟩ := he,
  refine not_is_diag_mk_of_mem_off_diag hb _,
  rw hab,
  exact is_diag_mk_of_mem_diag ha,
end

end sym2

section sym
variables [decidable_eq α] {s t : finset α} {n : ℕ} {m : sym α n} {a b : α}

/-- Lifts a finset to `sym α n`. `s.sym n` is the finset of all unordered tuples of cardinality `n`
with elements in `s`. -/
protected def sym (s : finset α) : Π n, finset (sym α n)
| 0       := {∅}
| (n + 1) := s.sup $ λ a, (sym n).image $ _root_.sym.cons a

@[simp] lemma sym_zero : s.sym 0 = {∅} := rfl
@[simp] lemma sym_succ : s.sym (n + 1) = s.sup (λ a, (s.sym n).image $ sym.cons a) := rfl

@[simp] lemma mem_sym_iff : m ∈ s.sym n ↔ ∀ a ∈ m, a ∈ s :=
begin
  induction n with n ih,
  { refine mem_singleton.trans ⟨_, λ _, sym.eq_nil_of_card_zero _⟩,
    rintro rfl,
    exact λ a ha, ha.elim },
  refine mem_sup.trans  ⟨_, λ h, _⟩,
  { rintro ⟨a, ha, he⟩ b hb,
    rw mem_image at he,
    obtain ⟨e, he, rfl⟩ := he,
    rw sym.mem_cons at hb,
    obtain rfl | hb := hb,
    { exact ha },
    { exact ih.1 he _ hb } },
  { obtain ⟨a, m, rfl⟩ := m.exists_eq_cons_of_succ,
    exact ⟨a, h _ $ sym.mem_cons_self _ _,
      mem_image_of_mem _ $ ih.2 $ λ b hb, h _ $ sym.mem_cons_of_mem hb⟩ }
end
.
@[simp] lemma sym_empty (n : ℕ) : (∅ : finset α).sym (n + 1) = ∅ := rfl

lemma repeat_mem_sym (ha : a ∈ s) (n : ℕ) : sym.repeat a n ∈ s.sym n :=
mem_sym_iff.2 $ λ b hb, by rwa (sym.mem_repeat.1 hb).2

protected lemma nonempty.sym (h : s.nonempty) (n : ℕ) : (s.sym n).nonempty :=
let ⟨a, ha⟩ := h in ⟨_, repeat_mem_sym ha n⟩

@[simp] lemma sym_singleton (a : α) (n : ℕ) : ({a} : finset α).sym n = {sym.repeat a n} :=
eq_singleton_iff_nonempty_unique_mem.2 ⟨(singleton_nonempty _).sym n,
  λ s hs, sym.eq_repeat_iff.2 $ λ b hb, eq_of_mem_singleton $ mem_sym_iff.1 hs _ hb⟩

lemma eq_empty_of_sym_eq_empty (h : s.sym n = ∅) : s = ∅ :=
begin
  rw ←not_nonempty_iff_eq_empty at ⊢ h,
  exact λ hs, h (hs.sym _),
end

@[simp] lemma sym_eq_empty : s.sym n = ∅ ↔ n ≠ 0 ∧ s = ∅ :=
begin
  cases n,
  { exact iff_of_false (singleton_ne_empty _) (λ h, (h.1 rfl).elim) },
  { refine ⟨λ h, ⟨n.succ_ne_zero, eq_empty_of_sym_eq_empty h⟩, _⟩,
    rintro ⟨_, rfl⟩,
    exact sym_empty _ }
end

@[simp] lemma sym_nonempty : (s.sym n).nonempty ↔ n = 0 ∨ s.nonempty :=
by simp_rw [nonempty_iff_ne_empty, ne.def, sym_eq_empty, not_and_distrib, not_ne_iff]

alias sym2_nonempty ↔ _ finset.nonempty.sym2

attribute [protected] finset.nonempty.sym2

@[simp] lemma sym_univ [fintype α] (n : ℕ) : (univ : finset α).sym n = univ :=
eq_univ_iff_forall.2 $ λ s, mem_sym_iff.2 $ λ a _, mem_univ _

@[simp] lemma sym_mono (h : s ⊆ t) (n : ℕ): s.sym n ⊆ t.sym n :=
λ m hm, mem_sym_iff.2 $ λ a ha, h $ mem_sym_iff.1 hm _ ha

@[simp] lemma sym_inter (s t : finset α) (n : ℕ) : (s ∩ t).sym n = s.sym n ∩ t.sym n :=
by { ext m, simp only [mem_inter, mem_sym_iff, imp_and_distrib, forall_and_distrib] }

@[simp] lemma sym_union (s t : finset α) (n : ℕ) : s.sym n ∪ t.sym n ⊆ (s ∪ t).sym n :=
begin
  refine λ m hm, mem_sym_iff.2 (λ a ha, mem_union.2 _),
  rw [mem_union, mem_sym_iff, mem_sym_iff] at hm,
  cases hm,
  { exact or.inl (hm _ ha) },
  { exact or.inr (hm _ ha) }
end

end sym
end finset

namespace simple_graph
variables {a : α}

lemma neighbor_set_bot (a : α) : (⊥ : simple_graph α).neighbor_set a = ∅ :=
set.eq_empty_iff_forall_not_mem.2 $ λ x, id

instance simple_graph.bot.locally_finite : locally_finite (⊥ : simple_graph α) :=
λ a, ⟨∅, λ x, neighbor_set_bot x ▸ x.2⟩

-- instance [fintype α] [decidable_rel G.adj] [fintype G.edge_set] : fintype G.subgraph :=
-- fintype.of_surjective (λ s : finset (sym2 α) × finset α, begin

-- end)
-- begin

-- end

variables (G)

/-- Constructs a subgraph from its vertices and edges. -/
@[simps] def subgraph_of_edges (verts : set α) (edges : set (sym2 α))
  (hverts : edges ⊆ G.edge_set) (hedges : ∀ (e ∈ edges) (a ∈ e), a ∈ verts) :
  G.subgraph :=
{ verts := verts,
  adj := λ a b, ⟦(a, b)⟧ ∈ edges,
  adj_sub := λ a b h, hverts h,
  edge_vert := λ a b h, hedges _ h _ (sym2.mem_mk_left _ _),
  symm := λ a b h, by rwa sym2.eq_swap }

lemma subgraph_of_edges_edge_set (verts : set α) (edges : set (sym2 α)) {hverts hedges} :
  (G.subgraph_of_edges verts edges hverts hedges).edge_set = edges :=
by { ext ⟨a, b⟩, exact subgraph.mem_edge_set }

lemma subgraph_of_edges_injective_left {v₁ v₂ e₁ e₂ hv₁ hv₂ he₁ he₂}
  (h : G.subgraph_of_edges v₁ e₁ hv₁ he₁ = G.subgraph_of_edges v₂ e₂ hv₂ he₂) :
  v₁ = v₂ :=
congr_arg subgraph.verts h

lemma subgraph_of_edges_injective_right {v₁ v₂ e₁ e₂ hv₁ hv₂ he₁ he₂}
  (h : G.subgraph_of_edges v₁ e₁ hv₁ he₁ = G.subgraph_of_edges v₂ e₂ hv₂ he₂) :
  e₁ = e₂ :=
by convert congr_arg subgraph.edge_set h; rw subgraph_of_edges_edge_set

instance [decidable_eq α] [fintype α] [decidable_rel G.adj] [fintype G.edge_set] :
  fintype G.subgraph :=
{ elems := begin
    refine ((univ : finset (finset α)).sigma $ λ s, _).map ⟨λ s, _, _⟩,
    { exact λ s, {t : finset (sym2 α) // ↑t ⊆ G.edge_set ∧ ∀ (e ∈ t) (a ∈ e), a ∈ s} },
    { exact G.subgraph_of_edges s.1 s.2.1 s.2.2.1 s.2.2.2 },
    { rintro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ h,
      exact sigma.subtype_ext (coe_injective $ G.subgraph_of_edges_injective_left h)
        (coe_injective $ G.subgraph_of_edges_injective_right h) },
    {
      have := G.edge_finset.powerset,
      sorry
    }
  end,
  complete := _ }

end simple_graph
