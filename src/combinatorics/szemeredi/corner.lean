/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import .triangle_removal
import combinatorics.additive.salem_spencer
import combinatorics.pigeonhole
import combinatorics.simple_graph.triangle.tripartite

/-!
# The corners theorem and Roth's theorem

This file proves the corners theorem and Roth's theorem.

## References

* [Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
* [Wikipedia, *Corners theorem*](https://en.wikipedia.org/wiki/Corners_theorem)
-/

section linear_ordered_semifield
variables {α : Type*} [linear_ordered_semifield α] {a b c : α}

lemma div_le_comm₀ (hb : 0 < b) (hc : 0 < c) : a / b ≤ c ↔ a / c ≤ b :=
by rw [div_le_iff hb, div_le_iff' hc]

end linear_ordered_semifield

attribute [simp] fin.coe_eq_coe

open finset function simple_graph simple_graph.tripartite_from_triangles sum sum3

variables {n : ℕ} {ε : ℝ}

/-- A corner in `s` is three points of the form `(x, y), (x + h, y), (x, y + h)`. A corner is
nontrivial if `h ≠ 0`. A corner with `h ≤ 0` is called an anticorner. Here, we record `x`, `y`, `d`.
-/
def is_corner (s : finset (ℤ × ℤ)) : ℤ → ℤ → ℤ → Prop :=
λ x y d, (x, y) ∈ s ∧ (x + d, y) ∈ s ∧ (x, y + d) ∈ s

lemma is_corner.mono {s t : finset (ℤ × ℤ)} (hst : s ⊆ t) {x y d : ℤ} (h : is_corner s x y d) :
  is_corner t x y d :=
⟨hst h.1, hst h.2.1, hst h.2.2⟩

namespace corners
variables {s : finset (fin n × fin n)} {x : fin n × fin n × fin (n + n)}

/-- The triangle indices for the proof of the corners theorem construction. -/
private def triangle_indices (s : finset (fin n × fin n)) : finset (fin n × fin n × fin (n + n)) :=
s.map ⟨λ ab, (ab.1, ab.2, ⟨ab.1.val + ab.2.val, add_lt_add ab.1.2 ab.2.2⟩),
  by { rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ ⟨⟩, refl }⟩

@[simp] lemma mem_triangle_indices :
  x ∈ triangle_indices s ↔ (x.1, x.2.1) ∈ s ∧ x.2.2 = ⟨_, add_lt_add x.1.2 x.2.1.2⟩ :=
begin
  simp only [triangle_indices, prod.ext_iff, fin.val_eq_coe, mem_map, embedding.coe_fn_mk,
    exists_prop, prod.exists, eq_comm],
  refine ⟨_, λ h, ⟨_, _, h.1, rfl, rfl, h.2⟩⟩,
  rintro ⟨_, _, h₁, rfl, rfl, h₂⟩,
  exact ⟨h₁, h₂⟩,
end

lemma mk_mem_triangle_indices {a b : fin n} {c : fin (n + n)} :
  (a, b, c) ∈ triangle_indices s ↔ (a, b) ∈ s ∧ c = ⟨_, add_lt_add a.2 b.2⟩ :=
mem_triangle_indices

@[simp] lemma card_triangle_indices : (triangle_indices s).card = s.card := card_map _

instance : explicit_disjoint (triangle_indices s) :=
begin
  constructor;
  { simp only [mk_mem_triangle_indices, prod.mk.inj_iff, exists_prop, forall_exists_index, and_imp],
    rintro a b _ a' - rfl - h',
    simp [*] at * }
end

lemma no_accidental (h : ∀ (x y : ℕ) d, is_corner (s.image $ prod.map coe coe) x y d → d = 0) :
  no_accidental (triangle_indices s) :=
⟨λ a a' b b' c c' ha hb hc, begin
  simp only [fin.val_eq_coe, mem_triangle_indices] at ha hb hc,
  refine or.inl (eq.symm $ fin.ext $ nat.cast_injective $ sub_eq_zero.1 $ h a b _ ⟨_, _, _⟩),
  { exact mem_image_of_mem _ hc.1 },
  { simpa only [coe_coe, add_sub_cancel'_right] using mem_image_of_mem _ ha.1 },
  rw [ha.2, fin.mk_eq_mk] at hb,
  convert mem_image_of_mem _ hb.1,
  simpa [prod.ext_iff, ←add_sub_assoc, sub_eq_iff_eq_add, add_comm] using congr_arg coe hb.2,
end⟩

lemma far_from_triangle_free_graph (hε : ε * n ^ 2 ≤ s.card) :
  (graph $ triangle_indices s).far_from_triangle_free (ε / 16) :=
begin
  refine far_from_triangle_free _ _,
  simp_rw [card_triangle_indices, fintype.card_fin, mul_comm_div, nat.cast_pow, nat.cast_add],
  ring_nf,
  simpa only [mul_comm] using hε,
end

lemma weak_corners_theorem {ε : ℝ} (hε : 0 < ε) :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ s : finset (fin n × fin n), ε * n^2 ≤ s.card →
      ∃ (x y : ℕ) (d ≠ 0), is_corner (s.image $ prod.map coe coe) x y d :=
begin
  refine ⟨⌊(triangle_removal_bound (ε / 16) * 64)⁻¹⌋₊ + 1, λ n hn s hA, _⟩,
  rw nat.add_one_le_iff at hn,
  have n_pos : 0 < n := (nat.zero_le _).trans_lt hn,
  have hε₁ : ε ≤ 1,
  { have := hA.trans (nat.cast_le.2 s.card_le_univ),
    simp only [sq, nat.cast_mul, fintype.card_prod, fintype.card_fin] at this,
    rwa mul_le_iff_le_one_left at this,
    exact mul_pos (nat.cast_pos.2 n_pos) (nat.cast_pos.2 n_pos) },
  by_contra' h,
  simp_rw not_imp_not at h,
  haveI := no_accidental h,
  rw [nat.floor_lt' n_pos.ne', inv_pos_lt_iff_one_lt_mul'] at hn,
  refine hn.not_le (le_of_mul_le_mul_right _ $ pow_pos (nat.cast_pos.2 n_pos) 2),
  have h₁ := (far_from_triangle_free_graph hA).le_card_clique_finset,
  rw [card_triangles, card_triangle_indices] at h₁,
  convert h₁.trans (nat.cast_le.2 $ card_le_univ _) using 1; simp; ring,
  { have : ε / 16 ≤ 1 := by linarith,
    positivity }
end

end corners

open corners

lemma alt_set (c : ℕ × ℕ) (s : finset (ℕ × ℕ)) :
  (s.filter $ λ x : ℕ × ℕ, x.1 ≤ c.1 ∧ x.2 ≤ c.2 ∧ (c.1 - x.1, c.2 - x.2) ∈ s).card =
    ((s ×ˢ s).filter $ λ x : (ℕ × ℕ) × ℕ × ℕ, (x.1.1 + x.2.1, x.1.2 + x.2.2) = c).card :=
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
  refine (λ x y xy hx hy t, ⟨_, _, ⟨xy, t⟩, _, _⟩); rw [←nat.add_sub_assoc, nat.add_sub_cancel_left];
    assumption,
end

lemma correlate {n : ℕ} (hn : 0 < n) (s : finset (ℕ × ℕ)) (hA : s ⊆ range n ×ˢ range n) :
  ∃ c ∈ range (n + n) ×ˢ range (n + n),
    (s.card : ℝ)^2 / (n + n)^2 ≤
      (s.filter (λ (xy : ℕ × ℕ), xy.1 ≤ c.1 ∧ xy.2 ≤ c.2 ∧ (c.1 - xy.1, c.2 - xy.2) ∈ s)).card :=
begin
  simp_rw [alt_set _ s],
  let f : (ℕ × ℕ) × ℕ × ℕ → ℕ × ℕ := λ ab, (ab.1.1 + ab.2.1, ab.1.2 + ab.2.2),
  have : ∀ a ∈ s ×ˢ s, f a ∈ range (n + n) ×ˢ range (n + n),
  { simp only [subset_iff, mem_range, mem_product, two_mul] at ⊢ hA,
    exact λ a ha, ⟨add_lt_add (hA ha.1).1 (hA ha.2).1, add_lt_add (hA ha.1).2 (hA ha.2).2⟩ },
  refine exists_le_card_fiber_of_nsmul_le_card_of_maps_to this _ _,
  { simp [hn.ne'] },
  simp only [card_product, card_range, nsmul_eq_mul, nat.cast_pow, nat.cast_add, ←sq],
  rw [mul_div_assoc', mul_div_cancel_left],
  simp [hn.ne'],
end

lemma corners_theorem (hε : 0 < ε) :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ s ⊆ range n ×ˢ range n, ε * n^2 ≤ s.card →
    ∃ x y d : ℕ, d ≠ 0 ∧ is_corner (s.image $ prod.map coe coe) x y d :=
begin
  obtain ⟨n₀, hn₀⟩ := weak_corners_theorem (by positivity : 0 < (ε / 2) ^ 2),
  refine ⟨n₀ + 1, λ n hn s hA hAcard, _⟩,
  obtain ⟨⟨c₁, c₂⟩, -, hA'card⟩ := correlate (nat.succ_pos'.trans_le hn) s hA,
  let A' : finset (fin n × fin n) :=
    univ.filter (λ xy, (↑xy.1, ↑xy.2) ∈ s ∧ ↑xy.1 ≤ c₁ ∧ ↑xy.2 ≤ c₂ ∧ (c₁ - xy.1, c₂ - xy.2) ∈ s),
  have hA' : A'.image (prod.map coe coe : fin n × fin n → ℤ × ℤ) ⊆ s.image (prod.map coe coe) :=
    image_subset_iff.2 (λ x hx, mem_image.2 ⟨x.map coe coe, (mem_filter.1 hx).2.1, rfl⟩),
  have : (ε / 2) ^ 2 * ↑n ^ 2 ≤ A'.card,
  { refine le_trans _ (hA'card.trans _),
    { rw [←mul_pow, ←div_pow],
      refine pow_le_pow_of_le_left (by positivity) _ _,
      cases n,
      { simp },
      rwa [le_div_iff, mul_comm_div, mul_assoc, mul_comm_div, ←two_mul,
        mul_div_cancel_left _ (two_ne_zero' ℝ), ←sq],
      positivity },
    norm_cast,
    refine (card_mono _).trans card_image_le,
    { exact prod.map coe coe },
    simp only [le_iff_subset, subset_iff, mem_filter, mem_image, mem_univ, true_and,
      _root_.prod_map, exists_prop, prod.exists, and_imp, prod.forall],
    rintro a b hab hac hbc hcab,
    obtain ⟨ha, hb⟩ := mem_product.1 (hA hab),
    exact ⟨⟨a, mem_range.1 ha⟩, ⟨b, mem_range.1 hb⟩, ⟨hab, hac, hbc, hcab⟩, rfl⟩ },
  obtain ⟨x, y, d, hd, hxyd⟩ := hn₀ _ (nat.le_of_succ_le hn) A' this,
  obtain ⟨d, rfl | rfl⟩ := d.eq_coe_or_neg,
  { exact ⟨_, _, _, nat.cast_ne_zero.1 hd, hxyd.mono hA'⟩ },
  simp only [is_corner, mem_image, mem_filter, mem_univ, true_and, _root_.prod_map, coe_coe,
    prod.mk.inj_iff, exists_prop, prod.exists] at hxyd,
  norm_cast at hxyd,
  obtain ⟨⟨a₁, a₂, ⟨-, hac₁, hac₂, hac⟩, rfl, rfl⟩, ⟨b₁, b₂, ⟨-, hbc₁, hbc₂, hbc⟩, hba₁, hba₂⟩,
    e₁, e₂, ⟨-, hec₁, hec₂, hec⟩, hea₁, hea₂⟩ := hxyd,
  simp only [nat.cast_inj, fin.coe_eq_coe] at hba₂ hea₁,
  obtain ⟨rfl, rfl⟩ := ⟨hba₂, hea₁⟩,
  refine ⟨c₁ - e₁, c₂ - b₂, _, nat.cast_ne_zero.1 $ neg_ne_zero.1 hd, mem_image.2 ⟨_, hac, _⟩,
    mem_image.2 ⟨_, hbc, _⟩, mem_image.2 ⟨_, hec, _⟩⟩; simp [*, sub_add, ←sub_eq_add_neg],
end

lemma roth (δ : ℝ) (hδ : 0 < δ) :
  ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
    ∀ s ⊆ range n, δ * n ≤ s.card → ∃ a d, 0 < d ∧ a ∈ s ∧ a + d ∈ s ∧ a + 2 * d ∈ s :=
begin
  obtain ⟨n₀, hn₀⟩ := corners_theorem (by positivity : 0 < δ/4),
  refine ⟨n₀, λ n hn s hA hAcard, _⟩,
  let B : finset (ℕ × ℕ) :=
    (range (n + n) ×ˢ range (n + n)).filter (λ xy, xy.1 ≤ xy.2 ∧ xy.2 - xy.1 ∈ s),
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
  have : δ/4 * ↑(n + n) ^ 2 ≤ ↑(B.card),
  { refine le_trans _ (nat.cast_le.2 this),
    rw [nat.cast_add, ←two_mul, mul_pow, ←mul_assoc, nat.cast_mul],
    norm_num,
    rw [sq, ←mul_assoc, mul_comm _ (s.card : ℝ)],
    exact mul_le_mul_of_nonneg_right hAcard (nat.cast_nonneg _) },
  obtain ⟨x, y, k, hk, xy, xky, xyk⟩ := hn₀ _ (hn.trans le_add_self) B (filter_subset _ _) this,
  have : injective (prod.map coe coe : ℕ × ℕ → ℤ × ℤ) :=
    nat.cast_injective.prod_map nat.cast_injective,
  replace xy : (x, y) ∈ B := this.mem_finset_image.1 xy,
  replace xky : (x + k, y) ∈ B := this.mem_finset_image.1 xky,
  replace xyk : (x, y + k) ∈ B := this.mem_finset_image.1 xyk,
  refine ⟨y - (x + k), k, pos_iff_ne_zero.2 hk, (mem_filter.1 xky).2.2, _, _⟩,
  { rw [←nat.sub_add_comm (mem_filter.1 xky).2.1, nat.add_sub_add_right],
    exact (mem_filter.1 xy).2.2 },
  { rw [←nat.sub_add_comm (mem_filter.1 xky).2.1, two_mul, ←add_assoc, nat.add_sub_add_right],
    exact (mem_filter.1 xyk).2.2 }
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

lemma roth_asymptotic : is_o at_top (λ N, (roth_number_nat N : ℝ)) (λ N, (N : ℝ)) :=
begin
  simp_rw [is_o_iff, eventually_at_top, ←not_lt],
  refine λ δ hδ, (roth' δ hδ).imp (λ n₀, forall₂_imp $ λ n hn h hδn, _),
  obtain ⟨s, hs₁, hs₂, hs₃⟩ := roth_number_nat_spec n,
  rw [←hs₂, real.norm_coe_nat, real.norm_coe_nat] at hδn,
  exact h s hs₁ hδn.le hs₃,
end
