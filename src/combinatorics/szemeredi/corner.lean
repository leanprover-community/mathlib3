/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import .triangle_removal
import combinatorics.additive.salem_spencer

/-!
# The corners theorem and Roth's theorem

This file proves the corners theorem and Roth's theorem.
-/

open_locale classical
open finset function

variables {N : ℕ}

/-- A corner in `s` is three points of the form `(x, y), (x + h, y), (x, y + h)` with `0 < h`. Here,
we record `x`, `y`, `h`. -/
def is_corner (s : finset (ℕ × ℕ)) : ℕ → ℕ → ℕ → Prop :=
λ x y h, (x, y) ∈ s ∧ (x + h, y) ∈ s ∧ (x, y + h) ∈ s

/-- A corner in `s` is three points of the form `(x, y), (x + h, y), (x, y + h)` with `h < 0`. Here,
we record `x`, `y`, `h`. Note that we use a slightly different formulation because of natural
subtraction.-/
def is_anticorner (s : finset (ℕ × ℕ)) : ℕ → ℕ → ℕ → Prop :=
λ x y h, (x, y) ∈ s ∧ (h ≤ x ∧ (x - h, y) ∈ s) ∧ (h ≤ y ∧ (x, y - h) ∈ s)

namespace corners

/-- The type of vertices of the corners graph. -/
inductive vertices (N : ℕ)
| horiz : fin N → vertices
| vert : fin N → vertices
| diag : fin (2 * N) → vertices

open vertices

instance (N : ℕ) : inhabited (vertices (N + 1)) := ⟨vert default⟩

instance : fintype (vertices N) :=
fintype.of_equiv (fin N ⊕ fin N ⊕ fin (2 * N))
{ to_fun := sum.elim horiz (sum.elim vert diag),
  inv_fun := λ i, vertices.rec_on i sum.inl (sum.inr ∘ sum.inl) (sum.inr ∘ sum.inr),
  left_inv := λ i, by { rcases i with (_ | _ | _); refl },
  right_inv := λ i, by { rcases i with (_ | _ | _); refl } }

@[simp] lemma card_vertices : fintype.card (vertices N) = 4 * N :=
by { simp only [fintype.of_equiv_card, fintype.card_fin, fintype.card_sum], ring }

/-- The edges of the corners graph. -/
inductive edges (s : finset (ℕ × ℕ)) : vertices N → vertices N → Prop
| hv {h v : fin N} : ((h : ℕ), (v : ℕ)) ∈ s → edges (horiz h) (vert v)
| vh {h v : fin N} : ((h : ℕ), (v : ℕ)) ∈ s → edges (vert v) (horiz h)
| hd {h : fin N} {k : fin (2 * N)} :
    (h : ℕ) ≤ k → ((h : ℕ), (k : ℕ) - h) ∈ s → edges (horiz h) (diag k)
| dh {h : fin N} {k : fin (2 * N)} :
    (h : ℕ) ≤ k → ((h : ℕ), (k : ℕ) - h) ∈ s → edges (diag k) (horiz h)
| vd {v : fin N} {k : fin (2 * N)} :
    (v : ℕ) ≤ k → ((k : ℕ) - v, (v : ℕ)) ∈ s → edges (vert v) (diag k)
| dv {v : fin N} {k : fin (2 * N)} :
    (v : ℕ) ≤ k → ((k : ℕ) - v, (v : ℕ)) ∈ s → edges (diag k) (vert v)

variables {s : finset (ℕ × ℕ)}

section edges
open edges

lemma edges_symm : ∀ (x y : vertices N), edges s x y → edges s y x
| _ _ (hv h) := vh h
| _ _ (vh h) := hv h
| _ _ (hd h₁ h₂) := dh h₁ h₂
| _ _ (dh h₁ h₂) := hd h₁ h₂
| _ _ (vd h₁ h₂) := dv h₁ h₂
| _ _ (dv h₁ h₂) := vd h₁ h₂

lemma edges_irrefl : ∀ (x : vertices N), ¬ edges s x x.

/-- Picturing a `N × N` grid, this is the graph whose vertices are vertical, horizontal and diagonal
(one way) lines and whose edges are the pairs of lines that meet within `s`. -/
def graph (N : ℕ) (s : finset (ℕ × ℕ)) : simple_graph (vertices N) :=
{ adj := edges s, symm := edges_symm, loopless := edges_irrefl }

@[simp] lemma edges_horiz_vert {h v : fin N} :
  (graph _ s).adj (horiz h) (vert v) ↔ ((h : ℕ), (v : ℕ)) ∈ s :=
⟨by { rintro ⟨⟩, assumption }, edges.hv⟩

@[simp] lemma edges_horiz_diag {h : fin N} {k} :
  (graph _ s).adj (horiz h) (diag k) ↔ (h : ℕ) ≤ k ∧ ((h : ℕ), (k : ℕ) - h) ∈ s :=
⟨by { rintro ⟨⟩, tauto }, λ i, edges.hd i.1 i.2⟩

@[simp] lemma edges_vert_diag {v : fin N} {k} :
  (graph _ s).adj (vert v) (diag k) ↔ (v : ℕ) ≤ k ∧ ((k : ℕ) - v, (v : ℕ)) ∈ s :=
⟨by { rintro ⟨⟩, tauto }, λ i, edges.vd i.1 i.2⟩

/-- Throwaway tactic. -/
meta def sets_simp : tactic unit :=
`[ext] >> `[simp only [finset.mem_insert, finset.mem_singleton]] >> `[try {tauto}]

lemma graph_triple {s : finset (ℕ × ℕ)} {N : ℕ} :
  ∀ x y z, (graph N s).adj x y → (graph N s).adj x z → (graph N s).adj y z →
    ∃ h v {k : fin (2 * N)}, {horiz h, vert v, diag k} = ({x, y, z} : finset (vertices N)) ∧
      (graph _ s).adj (horiz h) (vert v) ∧ (graph _ s).adj (horiz h) (diag k) ∧
        (graph _ s).adj (vert v) (diag k)
| _ _ _ h₁@(hv _) h₂@(hd _ _) h₃ := ⟨_, _, _, rfl, h₁, h₂, h₃⟩
| _ _ _ (vh h₁) (vd h₂ i₂) (hd h₃ i₃) := ⟨_, _, _, by sets_simp, hv h₁, hd h₃ i₃, vd h₂ i₂⟩
| _ _ _ (hd h₁ i₁) (hv h₂) (dv h₃ i₃) := ⟨_, _, _, by sets_simp, hv h₂, hd h₁ i₁, vd h₃ i₃⟩
| _ _ _ (dh h₁ i₁) (dv h₂ i₂) (hv h₃) := ⟨_, _, _, by sets_simp, hv h₃, hd h₁ i₁, vd h₂ i₂⟩
| _ _ _ (vd h₁ i₁) (vh h₂) (dh h₃ i₃) := ⟨_, _, _, by sets_simp, hv h₂, hd h₃ i₃, vd h₁ i₁⟩
| _ _ _ (dv h₁ i₁) (dh h₂ i₂) (vh h₃) := ⟨_, _, _, by sets_simp, hv h₃, hd h₂ i₂, vd h₁ i₁⟩

end edges

/-- Maps an horizontal, a vertical and a diagonal line to their three points of intersection. -/
noncomputable def triangle_map : fin N × fin N × fin (2 * N) → finset (vertices N) :=
λ hvk, {horiz hvk.1, vert hvk.2.1, diag hvk.2.2}

/-- State whether an horizontal, a vertical and a diagonal line meet within `s`. -/
@[derive decidable_pred]
def explicit_triangles (s : finset (ℕ × ℕ)) (N : ℕ) : fin N × fin N × fin (2 * N) → Prop :=
λ (i : fin N × fin N × fin (2 * N)),
  (↑i.1, ↑i.2.1) ∈ s ∧ ((i.1 : ℕ) ≤ i.2.2 ∧ (↑i.1, ↑i.2.2 - ↑i.1) ∈ s) ∧
    ((i.2.1 : ℕ) ≤ i.2.2 ∧ (↑i.2.2 - ↑i.2.1, ↑i.2.1) ∈ s)

lemma triangle_map_mem (x : fin N × fin N × fin (2 * N)) (hx : explicit_triangles s N x) :
  triangle_map x ∈ (graph N s).triangle_finset :=
by simpa [simple_graph.mem_triangle_finset'', explicit_triangles, triangle_map] using hx

lemma triangle_map_injective : injective (triangle_map : _ → finset (vertices N)) :=
begin
  rintro ⟨h₁, v₁, k₁⟩ ⟨h₂, v₂, k₂⟩,
  simpa only [triangle_map, finset.subset.antisymm_iff, subset_iff, mem_insert, mem_singleton,
    forall_eq_or_imp, forall_eq, prod.mk.inj_iff, or_false, false_or] using and.left,
end

lemma triangle_map_surj {t} (ht : t ∈ (graph N s).triangle_finset) :
  ∃ a, explicit_triangles s N a ∧ triangle_map a = t :=
begin
  rw simple_graph.mem_triangle_finset''' at ht,
  obtain ⟨x, y, z, xy, xz, yz, rfl⟩ := ht,
  obtain ⟨h, v, k, i₀, i₁, i₂, i₃⟩ := graph_triple _ _ _ xy xz yz,
  exact ⟨⟨h, v, k⟩, ⟨by simpa using i₁, by simpa using i₂, by simpa using i₃⟩, i₀⟩,
end

lemma card_triangles_graph {s : finset (ℕ × ℕ)} {N : ℕ} :
  (graph N s).triangle_finset.card = (univ.filter (explicit_triangles s N)).card :=
begin
  refine (card_congr (λ a _, triangle_map a) (λ t ht, _) (λ x y _ _, _) (λ t ht, _)).symm,
  { apply triangle_map_mem _ (mem_filter.1 ht).2 },
  { apply triangle_map_injective },
  obtain ⟨_, ht', rfl⟩ := triangle_map_surj ht,
  exact ⟨w, by simpa using ht', rfl⟩,
end

lemma triangle_gives_corner_or_anticorner {h v : fin N} {k : fin (2 * N)} (hv : (↑h, ↑v) ∈ s)
  (hk₁ : (h : ℕ) ≤ k) (hk₁' : ((h : ℕ), (k : ℕ) - h) ∈ s)
  (vk₁ : (v : ℕ) ≤ k) (vk₁' : ((k : ℕ) - v, (v : ℕ)) ∈ s) :
  ((h : ℕ) + v ≤ k ∧ is_corner s h v (k - (h + v))) ∨
    ((k : ℕ) ≤ h + v ∧ is_anticorner s h v (h + v - k)) :=
begin
  cases le_total ((h : ℕ) + v) (k : ℕ) with hvk hvk,
  { refine or.inl ⟨hvk, hv, _, _⟩,
    { rwa [←nat.add_sub_assoc hvk, nat.add_sub_add_left] },
    { rwa [←nat.add_sub_assoc hvk, add_comm (v : ℕ), nat.add_sub_add_right] } },
  { have hvkh : (h : ℕ) + v - k ≤ h,
    { rwa [tsub_le_iff_right, add_le_add_iff_left], },
    have hvkv : (h : ℕ) + v - k ≤ v,
    { rwa [tsub_le_iff_right, add_comm, add_le_add_iff_left] },
    refine or.inr ⟨hvk, hv, ⟨hvkh, _⟩, ⟨hvkv, _⟩⟩,
    { convert vk₁' using 2,
      rw [tsub_eq_iff_eq_add_of_le hvkh, ←nat.sub_add_comm vk₁, nat.add_sub_of_le hvk,
        add_tsub_cancel_right] },
    { convert hk₁' using 2,
      rw [eq_tsub_iff_add_eq_of_le hk₁, add_comm, ←nat.add_sub_assoc hvkv, nat.sub_sub_self hvk] } }
end

lemma triangle_trivial_of_no_corners (cs : ∀ (x y h : ℕ), is_corner s x y h → h = 0)
  (as : ∀ (x y h : ℕ), is_anticorner s x y h → h = 0)
  {h v : fin N} {k : fin (2 * N)} (hv : (↑h, ↑v) ∈ s)
  (hk₁ : (h : ℕ) ≤ k) (hk₁' : ((h : ℕ), (k : ℕ) - h) ∈ s)
  (vk₁ : (v : ℕ) ≤ k) (vk₁' : ((k : ℕ) - v, (v : ℕ)) ∈ s) :
  (k : ℕ) = h + v :=
begin
  rcases triangle_gives_corner_or_anticorner hv hk₁ hk₁' vk₁ vk₁' with (⟨i₁, i₂⟩ | ⟨i₁, i₂⟩),
  { apply le_antisymm (nat.le_of_sub_eq_zero (cs _ _ _ i₂)) i₁ },
  { apply le_antisymm i₁ (nat.le_of_sub_eq_zero (as _ _ _ i₂)) },
end

lemma trivial_triangles_graph {s : finset (ℕ × ℕ)} {n : ℕ}
  (cs : ∀ (x y h : ℕ), is_corner s x y h → h = 0)
  (as : ∀ (x y h : ℕ), is_anticorner s x y h → h = 0) :
  (graph n s).triangle_finset.card ≤ n^2 :=
begin
  have : ((range n).product (range n)).card = n^2,
  { simp [sq] },
  rw [←this, card_triangles_graph],
  refine card_le_card_of_inj_on (λ i, ⟨i.1, i.2.1⟩) _ _,
  { rintro ⟨h, v, k⟩ -,
    simp only [mem_range, mem_product],
    exact ⟨h.prop, v.prop⟩ },
  simp only [true_and, prod.forall, mem_filter, mem_univ, prod.mk.inj_iff, explicit_triangles],
  rintro h ⟨v, k₁⟩ ⟨hv, ⟨hk₁', hk₁⟩, vk₁', vk₁⟩ h₂ ⟨v₂, k₂⟩ ⟨-, ⟨hk₂', hk₂⟩, vk₂', vk₂⟩ ⟨heq, veq⟩,
  dsimp at *,
  rw subtype.coe_injective.eq_iff at heq veq,
  substs heq veq,
  simp only [true_and, prod.mk.inj_iff, eq_self_iff_true, subtype.ext_iff],
  rw triangle_trivial_of_no_corners cs as hv hk₁' hk₁ vk₁' vk₁,
  rw triangle_trivial_of_no_corners cs as hv hk₂' hk₂ vk₂' vk₂,
end

/-- The trivial triangles -/
def trivial_triangles (N : ℕ) (s : finset (ℕ × ℕ)) : finset (fin N × fin N × fin (2 * N)) :=
univ.filter (λ xyz, (↑xyz.1, ↑xyz.2.1) ∈ s ∧ (xyz.1 : ℕ) + xyz.2.1 = xyz.2.2)

lemma trivial_triangles_mem :
  ∀ x ∈ trivial_triangles N s, explicit_triangles s N x :=
λ ⟨h, v, k⟩ t,
begin
  simp only [trivial_triangles, true_and, mem_filter, mem_univ] at t,
  exact ⟨t.1, by simp [←t.2, t.1]⟩,
end

lemma card_trivial_triangles (hA : s ⊆ (range N).product (range N)) :
  (trivial_triangles N s).card = s.card :=
begin
  refine card_congr (λ xyz _, (xyz.1, xyz.2.1)) _ _ _,
  { rintro ⟨x, y, z⟩ t,
    apply (mem_filter.1 t).2.1 },
  { rintro ⟨x₁, y₁, z₁⟩ ⟨x₂, y₂, z₂⟩ t₁ t₂ hxy,
    simp only [prod.mk.inj_iff] at hxy,
    simp only [prod.mk.inj_iff, subtype.ext_iff, ←and.assoc, hxy, true_and, eq_self_iff_true],
    rw ←(mem_filter.1 t₁).2.2,
    rw ←(mem_filter.1 t₂).2.2,
    simp [hxy.1, hxy.2] },
  rintro ⟨x, y⟩ hxy,
  have := hA hxy,
  simp only [mem_range, mem_product] at this,
  refine ⟨⟨⟨_, this.1⟩, ⟨_, this.2⟩, ⟨x + y, _⟩⟩, mem_filter.2 ⟨mem_univ _, hxy, rfl⟩, rfl⟩,
  rw two_mul,
  apply add_lt_add this.1 this.2,
end

lemma triangle_free_far {ε : ℝ} (hA : s ⊆ (range N).product (range N)) (hA' : ε * N^2 ≤ s.card) :
  (graph N s).triangle_free_far (ε/16) :=
begin
  refine simple_graph.triangle_free_far_of_disjoint_triangles
    ((trivial_triangles N s).map ⟨_, triangle_map_injective⟩) _ _ _,
  { simp only [subset_iff, and_imp, exists_prop, forall_exists_index, embedding.coe_fn_mk,
      mem_map],
    rintro _ x hx rfl,
    apply triangle_map_mem _ (trivial_triangles_mem _ hx), },
  { simp only [set.pairwise, mem_map, mem_coe, forall_exists_index, prod.forall, prod.forall',
      embedding.coe_fn_mk, trivial_triangles, true_and, and_imp, mem_filter, mem_univ],
    rintro _ ⟨h₁, _⟩ ⟨⟨v₁, _⟩, ⟨_, k₁⟩⟩ t₁ i₁ rfl _ ⟨h₂, _⟩ ⟨⟨v₂, _⟩, ⟨_, k₂⟩⟩ t₂ i₂ rfl q,
    dsimp at i₁ i₂ t₁ t₂,
    substs i₁ i₂,
    rw triangle_map_injective.ne_iff at q,
    dsimp [triangle_map],
    simp only [prod.mk.inj_iff, subtype.mk_eq_mk, ne.def] at q,
    rw finset.card_le_one,
    simp only [and_imp, mem_insert, mem_inter, mem_singleton, true_and, forall_eq_or_imp, and_true,
      false_or, forall_eq, implies_true_iff, eq_self_iff_true, subtype.mk_eq_mk, or_false,
      forall_and_distrib, and_assoc, @imp.swap (_ + _ = _)],
    refine ⟨_, _, _, _, _, _⟩;
    { intros i₁ i₂,
      apply q,
      simpa [i₁] using i₂ } },
  rw [card_map, card_trivial_triangles hA, card_vertices],
  norm_num,
  linarith,
end

end corners

open corners

lemma weak_corners_theorem {ε : ℝ} (hε : 0 < ε) :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ s ⊆ (range n).product (range n), ε * n^2 ≤ s.card →
      ∃ x y h, 0 < h ∧ (is_corner s x y h ∨ is_anticorner s x y h) :=
begin
  refine ⟨⌊1/(simple_graph.triangle_removal_bound (ε / 16) * 64)⌋₊ + 1, λ n hn s hA hA', _⟩,
  rw nat.add_one_le_iff at hn,
  have n_pos : 0 < n := (nat.zero_le _).trans_lt hn,
  have : ε ≤ 1,
  { have := hA'.trans (nat.cast_le.2 (card_le_of_subset hA)),
    simp only [sq, card_range, nat.cast_mul, card_product] at this,
    rwa mul_le_iff_le_one_left at this,
    exact mul_pos (nat.cast_pos.2 n_pos) (nat.cast_pos.2 n_pos) },
  have tf : (graph n s).triangle_free_far (ε/16) := triangle_free_far hA hA',
  by_contra h,
  simp only [not_and', or_imp_distrib, forall_and_distrib, not_exists, not_lt, le_zero_iff] at h,
  have h₁ := simple_graph.triangle_removal_2 (show 0 < ε/16, by linarith) (by linarith) tf,
  rw card_vertices at h₁,
  have i := h₁.trans (nat.cast_le.2 (trivial_triangles_graph h.1 h.2)),
  rw [nat.cast_mul, mul_pow, nat.cast_pow, ←mul_assoc] at i,
  norm_num at i,
  have : simple_graph.triangle_removal_bound (ε / 16) * 64 * n ≤ 1,
  { apply le_of_mul_le_mul_right _ (sq_pos_of_ne_zero (n : ℝ) (nat.cast_ne_zero.2 n_pos.ne')),
    rwa [one_mul, mul_assoc, ←pow_succ] },
  have po : 0 < simple_graph.triangle_removal_bound (ε / 16) * 64 :=
    mul_pos (simple_graph.triangle_removal_bound_pos (by linarith) (by linarith)) (by norm_num),
  apply not_lt_of_le this,
  rwa [nat.floor_lt (one_div_nonneg.2 po.le), div_lt_iff' po] at hn,
end

lemma alt_set (c : ℕ × ℕ) (s : finset (ℕ × ℕ)) :
  (s.filter (λ (x : ℕ × ℕ), x.1 ≤ c.1 ∧ x.2 ≤ c.2 ∧ (c.1 - x.1, c.2 - x.2) ∈ s)).card =
    ((s.product s).filter (λ (x : (ℕ × ℕ) × ℕ × ℕ), (x.1.1 + x.2.1, x.1.2 + x.2.2) = c)).card :=
begin
  rcases c with ⟨c₁, c₂⟩,
  refine (card_congr (λ (a : _ × _) ha, a.1) _ _ _).symm,
  { rintro ⟨⟨a₁, a₂⟩, b₁, b₂⟩ i,
    dsimp,
    simp only [mem_filter, mem_product, prod.mk.inj_iff] at i,
    simp only [mem_filter],
    rw [←i.2.1, ←i.2.2],
    simpa using i.1 },
  { dsimp,
    simp only [prod.forall, mem_filter, mem_product, prod.mk.inj_iff],
    rintro a₁ a₂ ⟨a₃, a₄⟩ ⟨⟨a₅, a₆⟩, a₇, a₈⟩ ⟨-, rfl, rfl⟩ ⟨_, h₁⟩ ⟨⟩,
    simpa [eq_comm] using h₁ },
  simp only [and_imp, exists_prop, prod.forall, mem_filter, exists_and_distrib_right,
    prod.mk.inj_iff, exists_eq_right_right, exists_eq_right, prod.exists, mem_product],
  intros x y xy hx hy t,
  refine ⟨_, _, ⟨xy, t⟩, _, _⟩,
  { rw [←nat.add_sub_assoc hx, nat.add_sub_cancel_left] },
  { rw [←nat.add_sub_assoc hy, nat.add_sub_cancel_left] },
end

lemma correlate {n : ℕ} (hn : 0 < n) (s : finset (ℕ × ℕ)) (hA : s ⊆ (range n).product (range n)) :
  ∃ c ∈ (range (2 * n)).product (range (2 * n)),
    (s.card : ℝ)^2 / ((2 * n)^2) ≤
      (s.filter (λ (xy : ℕ × ℕ), xy.1 ≤ c.1 ∧ xy.2 ≤ c.2 ∧ (c.1 - xy.1, c.2 - xy.2) ∈ s)).card :=
begin
  simp_rw [alt_set _ s],
  let f : (ℕ × ℕ) × ℕ × ℕ → ℕ × ℕ := λ ab, (ab.1.1 + ab.2.1, ab.1.2 + ab.2.2),
  have : ∀ a ∈ s.product s, f a ∈ (range (2 * n)).product (range (2 * n)),
  { rintro ⟨⟨a₁, a₂⟩, a₃, a₄⟩ h,
    simp only [mem_product] at h,
    have i := and.intro (hA h.1) (hA h.2),
    simp only [mem_range, mem_product] at i,
    simp only [mem_product, mem_range, two_mul],
    exact ⟨add_lt_add i.1.1 i.2.1, add_lt_add i.1.2 i.2.2⟩ },
  refine exists_le_card_fiber_of_mul_le_card_of_maps_to' this _ _,
  { simp [hn.ne'] },
  { simp only [card_product, card_range, nsmul_eq_mul, nat.cast_pow, nat.cast_two,
      nat.cast_mul, ←sq],
    rw [mul_div_assoc', mul_div_cancel_left],
    simp [hn.ne'] }
end

lemma corners_theorem {ε : ℝ} (hε : 0 < ε) :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ s ⊆ (range n).product (range n), ε * n^2 ≤ s.card →
      ∃ x y h, 0 < h ∧ is_corner s x y h :=
begin
  let ε' : ℝ := (ε/2)^2,
  have hε' : 0 < ε' := pow_pos (by linarith) _,
  obtain ⟨n₀, hn₀⟩ := weak_corners_theorem hε',
  refine ⟨n₀ + 1, λ n hn s hA hAcard, _⟩,
  obtain ⟨⟨c₁, c₂⟩, -, hA'card⟩ := correlate (nat.succ_pos'.trans_le hn) s hA,
  let A' : finset (ℕ × ℕ) := s.filter (λ xy, xy.1 ≤ c₁ ∧ xy.2 ≤ c₂ ∧ (c₁ - xy.1, c₂ - xy.2) ∈ s),
  have hA' : A' ⊆ s := filter_subset _ _,
  have : (s.card : ℝ)^2 / ((2 * n)^2) ≤ A'.card := hA'card,
  by_contra h,
  simp only [not_and', or_imp_distrib, forall_and_distrib, not_exists, not_lt, le_zero_iff] at h,
  have nc : ¬(∃ (x y h : ℕ), 0 < h ∧ (is_corner A' x y h ∨ is_anticorner A' x y h)),
  { simp only [not_exists, not_and', not_lt, or_imp_distrib, le_zero_iff, forall_and_distrib],
    refine ⟨λ x y k i, h x y k ⟨hA' i.1, hA' i.2.1, hA' i.2.2⟩, _⟩,
    { rintro x y k ⟨xy, ⟨kx, xky⟩, ky, xyk⟩,
      simp only [mem_filter] at xy xky xyk,
      rw tsub_tsub_assoc xy.2.2.1 ky at xyk,
      rw tsub_tsub_assoc xy.2.1 kx at xky,
      apply h (c₁ - x) (c₂ - y) k ⟨xy.2.2.2, xky.2.2.2, xyk.2.2.2⟩ } },
  refine nc (hn₀ _ ((nat.le_succ _).trans hn) A' (hA'.trans hA) (le_trans _ this)),
  rw [←mul_pow, ←div_pow],
  refine pow_le_pow_of_le_left (mul_nonneg (by linarith) (nat.cast_nonneg _)) _ _,
  rw le_div_iff,
  { exact (le_of_eq (by ring)).trans hAcard },
  exact mul_pos zero_lt_two (nat.cast_pos.2 (nat.succ_pos'.trans_le hn)),
end

lemma roth (δ : ℝ) (hδ : 0 < δ) :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ s ⊆ range n, δ * n ≤ s.card → ∃ a d, 0 < d ∧ a ∈ s ∧ a + d ∈ s ∧ a + 2 * d ∈ s :=
begin
  let δ' : ℝ := δ/4,
  have hδ' : 0 < δ' := div_pos hδ (by norm_num),
  obtain ⟨n₀, hn₀⟩ := corners_theorem hδ',
  refine ⟨n₀, λ n hn s hA hAcard, _⟩,
  let B : finset (ℕ × ℕ) :=
    ((range (2 * n)).product (range (2 * n))).filter (λ xy, xy.1 ≤ xy.2 ∧ xy.2 - xy.1 ∈ s),
  have : n * card s ≤ card B,
  { rw [←card_range n, ←card_product],
    refine card_le_card_of_inj_on (λ ia, (ia.1, ia.1 + ia.2)) _ _,
    { rintro ⟨i, a⟩ t,
      simp only [mem_range, mem_product] at t,
      simp only [true_and, mem_filter, add_tsub_cancel_left, mem_range, le_add_iff_nonneg_right,
        zero_le', mem_product, t.2, and_true, two_mul],
      exact ⟨t.1.trans_le (nat.le_add_right _ _), add_lt_add t.1 (mem_range.1 (hA t.2))⟩ },
    simp only [and_imp, prod.forall, mem_range, prod.mk.inj_iff, mem_product],
    rintro i a₁ hi ha₁ _ a₂ - ha₂ rfl,
    simp },
  have : δ' * ↑(2 * n) ^ 2 ≤ ↑(B.card),
  { refine le_trans _ (nat.cast_le.2 this),
    rw [nat.cast_mul, nat.cast_two, mul_pow, ←mul_assoc, nat.cast_mul],
    norm_num,
    rw [sq, ←mul_assoc, mul_comm _ (s.card : ℝ)],
    apply mul_le_mul_of_nonneg_right hAcard (nat.cast_nonneg _) },
  obtain ⟨x, y, k, hk, xy, xky, xyk⟩ :=
    hn₀ _ (hn.trans (nat.le_mul_of_pos_left zero_lt_two)) B (filter_subset _ _) this,
  refine ⟨y - (x + k), k, hk, (mem_filter.1 xky).2.2, _, _⟩,
  { rw [←nat.sub_add_comm (mem_filter.1 xky).2.1, nat.add_sub_add_right],
    apply (mem_filter.1 xy).2.2 },
  { rw [←nat.sub_add_comm (mem_filter.1 xky).2.1, two_mul, ←add_assoc, nat.add_sub_add_right],
    apply (mem_filter.1 xyk).2.2 },
end

lemma roth' (δ : ℝ) (hδ : 0 < δ) :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ s ⊆ range n, δ * n ≤ s.card → ¬ add_salem_spencer (s : set ℕ) :=
begin
  obtain ⟨n₀, hn₀⟩ := roth δ hδ,
  refine ⟨n₀, λ n hn s hA hAcard hA', _⟩,
  obtain ⟨a, d, hd, x, y, z⟩ := hn₀ n hn s hA hAcard,
  exact mul_ne_zero two_ne_zero hd.ne' (self_eq_add_right.1 $ hA' x z y $ by ring),
end

open asymptotics filter

lemma roth_asymptotic : is_o (λ N, (roth_number_nat N : ℝ)) (λ N, (N : ℝ)) at_top :=
begin
  rw is_o_iff,
  intros δ hδ,
  rw eventually_at_top,
  obtain ⟨n₀, hn₀⟩ := roth' δ hδ,
  refine ⟨n₀, λ n hn, _⟩,
  simp only [real.norm_coe_nat, ←not_lt],
  obtain ⟨s, hA₁, hA₂, hA₃⟩ := add_roth_number_spec (range n),
  refine λ h, (hn₀ n hn _ hA₁ _) hA₃,
  rw hA₂,
  exact h.le,
end
