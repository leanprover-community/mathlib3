/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .triangle
import tactic.norm_fin

/-!
# The corners theorem

This file defines combinatorial corners and proves the two dimensional corners theorem.
-/

open finset function
open_locale big_operators

variables {α ι ι' : Type*} [add_comm_monoid α] [decidable_eq ι] [fintype ι] [decidable_eq ι']
  [fintype ι'] {ε : ℝ}

lemma exists_ne_ne_fin {n : ℕ} (hn : 3 ≤ n) (a b : fin n) : ∃ c, a ≠ c ∧ b ≠ c :=
begin
  obtain ⟨c, hc⟩ : ({a,b}ᶜ : finset (fin n)).nonempty,
  { rw [←card_pos, card_compl, fintype.card_fin],
    apply nat.sub_pos_of_lt ((card_insert_le _ _).trans_lt _),
    rw card_singleton,
    linarith },
  exact ⟨c, by simpa [not_or_distrib, @eq_comm _ c] using hc⟩,
end

lemma fin3_cases (i j : fin 3) : i = j ∨ i = j + 1 ∨ i = j + 2 :=
by { fin_cases i; fin_cases j; finish }

/-! ### Simplex domain -/

section simplex_domain

/-- The `ι`-th combinatorial simplex domain of size `n + 1`. -/
def simplex_domain (ι : Type*) [fintype ι] (n : ℕ) : Type* := {f : ι → ℕ // ∑ i, f i = n}

namespace simplex_domain
variables {n : ℕ} {s : set (simplex_domain ι n)} {x : simplex_domain ι n} {f : ι → ℕ} {i : ι}

/-- The `i`-th coordinate of `x : simplex_domain ι n` as an element of `f (n + 1)`. -/
protected def apply (x : simplex_domain ι n) (i : ι) : fin (n + 1) :=
⟨x.val i, begin
  simp_rw [nat.lt_succ_iff, ←x.2],
  exact single_le_sum (λ i _, nat.zero_le _) (mem_univ _),
end⟩

@[simp] lemma coe_apply : (x.apply i : ℕ) = x.val i := rfl

@[ext] lemma ext {x y : simplex_domain ι n} (h : ∀ i, x.apply i = y.apply i) : x = y :=
begin
  ext i,
  exact (fin.ext_iff _ _).1 (h i),
end

/-- Projects a point in a simplex domain onto a smaller simplex domain in one direction. -/
def proj (x : simplex_domain ι' n) (f : ι ↪ ι') (i : ι) : simplex_domain ι n :=
begin
  refine ⟨finset.piecewise {i} (n - ∑ j in univ.erase i, x.val (f j)) (x.val ∘ f),
    (sum_piecewise _ _ _ _).trans _⟩,
  rw [univ_inter, sum_singleton, sdiff_singleton_eq_erase, pi.sub_apply, sum_apply],
  simp only [nat.cast_id, pi.coe_nat],
  refine tsub_add_cancel_of_le ((sum_le_sum_of_subset $ erase_subset _ _).trans _),
  simp_rw [←finset.sum_map, ←x.2],
  exact sum_le_sum_of_subset (subset_univ _),
end

lemma proj_apply_self {x : simplex_domain ι' n} {f : ι ↪ ι'} {i : ι} :
  (proj x f i).1 i = n - ∑ (c : ι) in univ.erase i, x.1 (f.1 c) :=
begin
  dsimp [proj],
  simp,
end

lemma proj_apply_ne {x : simplex_domain ι' n} {f : ι ↪ ι'} {i k : ι} (h : k ≠ i) :
  (proj x f i).1 k = x.1 (f k) :=
begin
  dsimp [proj],
  rw piecewise_singleton,
  rw update_noteq h,
end

-- /-- A corner in `s : set (simplex_domain ι n)` is a point whose projections all are within `s` -/
-- def corners (s : set (simplex_domain ι n)) : set (ι → ℕ) :=
-- {f | if h : ∑ i, f i ≤ n
--   then (∀ i, simplex_domain.proj f i ((sum_mono_set f $ erase_subset _ _).trans h) ∈ s)
--   else false }

/-- A corner in `s : set (simplex_domain ι n)` is a point `x : simplex_domain (option ι) n` whose
projections all are within `s` -/
def corners (s : set (simplex_domain ι n)) : set (simplex_domain (option ι) n) :=
{x | ∀ i, x.proj embedding.some i ∈ s}

/-- The set of elements of `simplex_domain ι n` whose `i`-th coordinate is `a`. -/
def line (n : ℕ) (i : ι) (a : ℕ) : set (simplex_domain ι n) := {x | x.val i = a}

/-- The set of elements of `simplex_domain ι n` whose coordinates are the same as `a` except the `i`-th and `j`-th ones. -/
def line' (n : ℕ) (i j : ι) (a : ι → ℕ) : set (simplex_domain ι n) :=
{x | ∀ k, k ≠ i → k ≠ j → x.val k = a k}

/-- The set of elements of `simplex_domain ι n` whose coordinates are the same as `a` on `s : set \io `except the `i`-th and `j`-th ones. -/
def line'' (n : ℕ) (s : set ι) (a : ι → ℕ) : set (simplex_domain ι n) :=
{x | ∀ ⦃i⦄, i ∈ s → x.val i = a i}

instance (n : ℕ) (i : ι) (a : ℕ) (x : simplex_domain ι n) : decidable (x ∈ line n i a) :=
by { unfold line, apply_instance }

/-- Projects any point onto the simplex domain in one direction. -/
def mem_line_self (x : simplex_domain ι n) (i : ι) : x ∈ line n i (x.val i) := rfl

/-- The lines of `simplex_domain ι n` a point of `simplex_domain ι' n` belongs to. -/
def lines (x : simplex_domain ι' n) (f : ι → ι') : finset (ι × fin (n + 1)) :=
univ.map ⟨λ i, (i, x.apply (f i)), λ a b hab, (prod.mk.inj hab).1⟩

lemma mem_lines {x : simplex_domain ι' n} {ia : ι × fin (n + 1)} {f : ι → ι'} :
  ia ∈ x.lines f ↔ ∃ i, ia = (i, x.apply (f i)) :=
begin
  unfold lines,
  simp_rw @eq_comm _ ia,
  simp,
end

lemma mem_lines_self (x : simplex_domain ι' n) (i : ι) (f : ι → ι') :
  (i, x.apply (f i)) ∈ x.lines f :=
mem_lines.2 ⟨_, rfl⟩

lemma card_lines {x : simplex_domain ι' n} {f : ι → ι'} : (x.lines f).card = fintype.card ι :=
card_map _

/-- The graph appearing in the simplex corners theorem. -/
def corners_graph (s : set (simplex_domain ι n)) : simple_graph (ι × fin (n + 1)) :=
{ adj := λ a b, a ≠ b ∧ ∃ x, x ∈ s ∧ x ∈ line n a.1 a.2 ∧ x ∈ line n b.1 b.2,
  symm := begin
      rintro a b ⟨h, x, hx, hax, hbx⟩,
      exact ⟨h.symm, x, hx, hbx, hax⟩,
    end,
  loopless := λ a h, h.1 rfl }

instance [decidable_pred (∈ s)] : decidable_rel (corners_graph s).adj :=
begin
  rw corners_graph,
  sorry
end

/-- The trivial `n`-clique in the corners graph. -/
def trivial_n_clique (x : simplex_domain ι n) : finset (ι × fin (n + 1)) :=
(univ.filter $ λ i, x ∈ line n i (x.val i)).image $ λ i, (i, x.apply i)

lemma card_trivial_n_clique (x : simplex_domain ι n) : x.trivial_n_clique.card = fintype.card ι :=
begin
  rw [trivial_n_clique, card_image_of_injective, filter_true_of_mem, card_univ],
  { exact λ i _, x.mem_line_self i },
  { exact λ a b h, (prod.mk.inj h).1 }
end

lemma mem_trivial_n_clique {i : ι} {a : fin (n + 1)} :
  (i, a) ∈ x.trivial_n_clique ↔ x.apply i = a :=
begin
  simp_rw [trivial_n_clique, mem_image, exists_prop, mem_filter, prod.mk.inj_iff],
  split,
  { rintro ⟨i, ⟨_, hx⟩, rfl, ha⟩,
    exact ha },
  { rintro h,
    exact ⟨i, ⟨mem_univ i, x.mem_line_self i⟩, rfl, h⟩ }
end

lemma trivial_n_clique_is_n_clique (hx : x ∈ s) :
  (corners_graph s).is_n_clique (fintype.card ι) x.trivial_n_clique :=
begin
  refine ⟨x.card_trivial_n_clique, _⟩,
  rintro ⟨i, a⟩ ha ⟨j, b⟩ hb hab,
  refine ⟨hab, x, hx, _⟩,
  rw [mem_coe, mem_trivial_n_clique] at ha hb,
  rw [←ha, ←hb],
  exact ⟨x.mem_line_self i, x.mem_line_self j⟩,
end

lemma trivial_n_clique_injective : injective (@trivial_n_clique ι _ _ n) :=
λ a b h, ext $ λ i, by rw [←mem_trivial_n_clique, h, mem_trivial_n_clique]

end simplex_domain

open simplex_domain

/-! ### Simplex corners theorem -/

section simplex_corner

variables {n : ℕ} {s : finset (simplex_domain (fin 3) n)} {x : simplex_domain (fin 3) n}
  {f : fin 3 → ℕ} {i j k : fin 3} {a b : ℕ}

lemma simplex_domain.line_inter_line (h : i ≠ j) :
  line n i a ∩ line n j b = ∅ :=
begin
  sorry
end

--  s.pairwise_disjoint (@trivial_n_clique ι _ _ n)
-- lemma trivial_n_clique_pairwise_disjoint :
--   (s.image trivial_n_clique : set (finset (fin 3 × fin (n + 1)))).pairwise_disjoint :=
-- begin
--   rintro x hx y hy h,
--   rw [mem_coe, mem_image] at hx hy,
--   obtain ⟨x, hx, rfl⟩ := hx,
--   obtain ⟨y, hy, rfl⟩ := hy,
--   rw trivial_n_clique_injective.ne_iff at h,
--   rw finset.disjoint_left,
--   rintro ⟨i, a⟩ hax hay,
--   rw mem_trivial_n_clique at hax hay,
--   sorry -- wrong
-- end

lemma mem_corners_iff_lines_is_n_clique {s : set (simplex_domain (fin 3) n)}
  {x : simplex_domain (option (fin 3)) n} :
  x ∈ corners s ↔ (corners_graph s).is_n_clique 3 (x.lines some) :=
begin
  split,
  { refine λ hx, ⟨card_map _, λ a ha b hb hab, ⟨hab, _⟩⟩,
    rw [mem_coe, mem_lines] at ha hb,
    obtain ⟨i, rfl⟩ := ha,
    obtain ⟨j, rfl⟩ := hb,
    obtain ⟨k, hik, hjk⟩ := exists_ne_ne_fin le_rfl i j,
    exact ⟨x.proj embedding.some k, hx k, proj_apply_ne hik, proj_apply_ne hjk⟩ },
  { rintro ⟨_, h⟩ i,
    obtain ⟨_, y, hy, hy₁, hy₂⟩ := h _ (x.mem_lines_self (i + 1) _) _ (x.mem_lines_self (i + 2) _) _,
    suffices : x.proj embedding.some i = y,
    { rwa this },
    ext j,
    rw [coe_apply, coe_apply],
    obtain rfl | rfl | rfl := fin3_cases j i,
    { rw proj_apply_self,
      sorry },
    { rw proj_apply_ne,
      exact eq.symm hy₁,
      norm_num },
    { rw proj_apply_ne,
      exact eq.symm hy₂,
      sorry },
    norm_num }
end

lemma card_le_card_triangle_finset_corners_graph :
  s.card ≤ (corners_graph (s : set (simplex_domain (fin 3) n))).triangle_finset.card :=
begin
  rw ←card_image_of_injective s trivial_n_clique_injective,
  refine card_le_of_subset (λ v hv, _),
  rw mem_image at hv,
  obtain ⟨x, hx, rfl⟩ := hv,
  rw simple_graph.mem_triangle_finset',
  exact trivial_n_clique_is_n_clique (mem_coe.2 hx),
end

lemma corners_graph_triangle_free_far (hs : ε * (3 * (n + 1) : ℕ) ^ 2 ≤ s.card) :
  (corners_graph (s : set (simplex_domain (fin 3) n))).triangle_free_far ε :=
begin
  refine simple_graph.triangle_free_far_of_disjoint_triangles (s.image trivial_n_clique) _ _ _,
  { rintro x hx,
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hx,
    rw simple_graph.mem_triangle_finset',
    exact trivial_n_clique_is_n_clique (mem_coe.2 hy) },
  { rintro a ha b hb hab,
    rw [mem_coe, mem_image] at ha hb,
    obtain ⟨a, ha, rfl⟩ := ha,
    obtain ⟨b, hb, rfl⟩ := hb,
    have h : a ≠ b := ne_of_apply_ne _ hab,
    sorry
  },
  { rw [fintype.card_prod, fintype.card_fin, fintype.card_fin],
    exact hs.trans (nat.cast_le.2 (card_image_of_injective s trivial_n_clique_injective).ge) }
end

lemma corners_theorem {ε : ℝ} (hε : 0 < ε) :
  ∃ n : ℕ, ∀ A : finset (simplex_domain (fin 3) n), ε * n^2 ≤ A.card →
    ∃ x : simplex_domain (option (fin 3)) n, 0 < x.val none ∧ corners ↑A x :=
begin
  sorry
end

lemma strengthened_corners_theorem {ε : ℝ} (hε : 0 < ε) :
  ∃ n : ℕ, ∀ n', n ≤ n' → ∀ A : finset (simplex_domain (fin 3) n'), ε * n'^2 ≤ A.card →
    ∃ x : simplex_domain (option (fin 3)) n', 0 < x.val none ∧ corners ↑A x :=
begin
  sorry
end

end simplex_corner

/-! ### Usual corners -/

/-- Combinatorial corners. -/
def higher_corners (A : set (ι → α)) : set ((ι → α) × α) :=
{x | x.1 ∈ A ∧ ∀ i, x.1 + set.indicator {i} (λ _, x.2) ∈ A}

/-- Two-dimensional combinatorial corner. -/
def is_corner (A : set (α × α)) : α → α → α → Prop :=
λ x y h, (x, y) ∈ A ∧ (x + h, y) ∈ A ∧ (x, y + h) ∈ A

end simplex_domain
