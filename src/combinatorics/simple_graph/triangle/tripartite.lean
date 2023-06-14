/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.triangle.basic

/-!
# Construct a tripartite graph from its triangles

This file contains the construction of a simple graph on `α ⊕ β ⊕ γ` from a list of triangles
`(a, b, c)` (with `a` in the first summand, `b` in the second, `c` in the third).

We call
* `t : finset (α × β × γ)` the set of *triangle indices* (its elements are not triangles within the
  graph but instead index them).
* *explicit* a triangle of the constructed graph coming from a triangle index.
* *accidental* a triangle of the constructed graph not coming from a triangle.

The two important properties of this construction are:
* `simple_graph.tripartite_from_triangles.explicit_disjoint`: Whether the explicit triangles are
  edge-disjoint.
* `simple_graph.tripartite_from_triangles.no_accidental`: Whether all triangles are explicit.

This construction shows up unrelatingly twice in the theory of Roth numbers:
* The lower bound of the Ruzsa-Szemerédi problem: From a Salem-Spencer set `s` on a commutative ring
  `α` (in which `2` is invertible), we build a locally linear graph on `α ⊕ α ⊕ α`. The triangle
  indices are `(x, x + a, x + 2 * a)` for `x` any element and `a ∈ s`. The explicit triangles are
  edge-disjoint and there is no accidental triangle.
* The proof of the corners theorem from the triangle removal lemma. For a subset `s` of the `n × n`
  grid, we construct a tripartite graph whose vertices are the horizontal, vertical and diagonal
  lines in the grid. The explicit triangles are `(h, v, d)` where `h`, `v`, `d` are horizontal, vertical, diagonal lines that intersect in an element of `s`. The explicit triangles are
  edge-disjoint. However, there are accidental triangles (and this is what the argument wants to
  prove).
-/

open finset function sum3

variables {α β γ : Type*} {t : finset (α × β × γ)} {a a' : α} {b b' : β} {c c' : γ} {x : α × β × γ}

namespace simple_graph
namespace tripartite_from_triangles

/-- The underlying relation of the tripartite-from-triangles graph. Two vertices are related iff
there exists a triangle index containing them both. -/
@[mk_iff] inductive rel (t : finset (α × β × γ)) : α ⊕ β ⊕ γ → α ⊕ β ⊕ γ → Prop
| in₀₁ ⦃a b c⦄ : (a, b, c) ∈ t → rel (in₀ a) (in₁ b)
| in₁₀ ⦃a b c⦄ : (a, b, c) ∈ t → rel (in₁ b) (in₀ a)
| in₀₂ ⦃a b c⦄ : (a, b, c) ∈ t → rel (in₀ a) (in₂ c)
| in₂₀ ⦃a b c⦄ : (a, b, c) ∈ t → rel (in₂ c) (in₀ a)
| in₁₂ ⦃a b c⦄ : (a, b, c) ∈ t → rel (in₁ b) (in₂ c)
| in₂₁ ⦃a b c⦄ : (a, b, c) ∈ t → rel (in₂ c) (in₁ b)

open rel

lemma rel_irrefl : ∀ x, ¬ rel t x x.
lemma rel_symm : symmetric (rel t) := λ x y h, by cases h; constructor; assumption

/-- The tripartite-from-triangles graph. Two vertices are related iff there exists a triangle index
containing them both. -/
def graph (t : finset (α × β × γ)) : simple_graph (α ⊕ β ⊕ γ) := ⟨rel t, rel_symm, rel_irrefl⟩

namespace graph

@[simp] lemma not_in₀₀ : ¬ (graph t).adj (in₀ a) (in₀ a') .
@[simp] lemma not_in₁₁ : ¬ (graph t).adj (in₁ b) (in₁ b') .
@[simp] lemma not_in₂₂ : ¬ (graph t).adj (in₂ c) (in₂ c') .

@[simp] lemma in₀₁_iff : (graph t).adj (in₀ a) (in₁ b) ↔ ∃ c, (a, b, c) ∈ t :=
⟨by { rintro ⟨⟩, exact ⟨_, ‹_›⟩ }, λ ⟨_, h⟩, in₀₁ h⟩
@[simp] lemma in₁₀_iff : (graph t).adj (in₁ b) (in₀ a) ↔ ∃ c, (a, b, c) ∈ t :=
⟨by { rintro ⟨⟩, exact ⟨_, ‹_›⟩ }, λ ⟨_, h⟩, in₁₀ h⟩
@[simp] lemma in₀₂_iff : (graph t).adj (in₀ a) (in₂ c) ↔ ∃ b, (a, b, c) ∈ t :=
⟨by { rintro ⟨⟩, exact ⟨_, ‹_›⟩ }, λ ⟨_, h⟩, in₀₂ h⟩
@[simp] lemma in₂₀_iff : (graph t).adj (in₂ c) (in₀ a) ↔ ∃ b, (a, b, c) ∈ t :=
⟨by { rintro ⟨⟩, exact ⟨_, ‹_›⟩ }, λ ⟨_, h⟩, in₂₀ h⟩
@[simp] lemma in₁₂_iff : (graph t).adj (in₁ b) (in₂ c) ↔ ∃ a, (a, b, c) ∈ t :=
⟨by { rintro ⟨⟩, exact ⟨_, ‹_›⟩ }, λ ⟨_, h⟩, in₁₂ h⟩
@[simp] lemma in₂₁_iff : (graph t).adj (in₂ c) (in₁ b) ↔ ∃ a, (a, b, c) ∈ t :=
⟨by { rintro ⟨⟩, exact ⟨_, ‹_›⟩ }, λ ⟨_, h⟩, in₂₁ h⟩

lemma in₀₁_iff' :
  (graph t).adj (in₀ a) (in₁ b) ↔ ∃ (x : α × β × γ) (hx : x ∈ t), x.1 = a ∧ x.2.1 = b :=
⟨by { rintro ⟨⟩, exact ⟨_, ‹_›, rfl, rfl⟩ },
  by { rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩, constructor, assumption }⟩
lemma in₁₀_iff' :
  (graph t).adj (in₁ b) (in₀ a) ↔ ∃ (x : α × β × γ) (hx : x ∈ t), x.2.1 = b ∧ x.1 = a :=
⟨by { rintro ⟨⟩, exact ⟨_, ‹_›, rfl, rfl⟩ },
  by { rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩, constructor, assumption }⟩
lemma in₀₂_iff' :
  (graph t).adj (in₀ a) (in₂ c) ↔ ∃ (x : α × β × γ) (hx : x ∈ t), x.1 = a ∧ x.2.2 = c :=
⟨by { rintro ⟨⟩, exact ⟨_, ‹_›, rfl, rfl⟩ },
  by { rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩, constructor, assumption }⟩
lemma in₂₀_iff' :
  (graph t).adj (in₂ c) (in₀ a) ↔ ∃ (x : α × β × γ) (hx : x ∈ t), x.2.2 = c ∧ x.1 = a :=
⟨by { rintro ⟨⟩, exact ⟨_, ‹_›, rfl, rfl⟩ },
  by { rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩, constructor, assumption }⟩
lemma in₁₂_iff' :
  (graph t).adj (in₁ b) (in₂ c) ↔ ∃ (x : α × β × γ) (hx : x ∈ t), x.2.1 = b ∧ x.2.2 = c :=
⟨by { rintro ⟨⟩, exact ⟨_, ‹_›, rfl, rfl⟩ },
  by { rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩, constructor, assumption }⟩
lemma in₂₁_iff' :
  (graph t).adj (in₂ c) (in₁ b) ↔ ∃ (x : α × β × γ) (hx : x ∈ t), x.2.2 = c ∧ x.2.1 = b :=
⟨by { rintro ⟨⟩, exact ⟨_, ‹_›, rfl, rfl⟩ },
  by { rintro ⟨⟨a, b, c⟩, h, rfl, rfl⟩, constructor, assumption }⟩

end graph

open graph

/-- Predicate on the triangle indices for the explicit triangles to be edge-disjoint. -/
class explicit_disjoint (t : finset (α × β × γ)) : Prop :=
(inj₀ : ∀ ⦃a b c a'⦄, (a, b, c) ∈ t → (a', b, c) ∈ t → a = a')
(inj₁ : ∀ ⦃a b c b'⦄, (a, b, c) ∈ t → (a, b', c) ∈ t → b = b')
(inj₂ : ∀ ⦃a b c c'⦄, (a, b, c) ∈ t → (a, b, c') ∈ t → c = c')

/-- Predicate on the triangle indices for there to be no accidental triangle.

Note that we cheat a bit, since the exact translation of this informal description would have
`(a', b', c') ∈ s` as a conclusion rather than `a = a' ∨ b = b' ∨ c = c'`. Those conditions are
equivalent when the explicit triangles are edge-disjoint (which is the case we care about). -/
class no_accidental (t : finset (α × β × γ)) : Prop :=
(wow : ∀ ⦃a a' b b' c c'⦄, (a', b, c) ∈ t → (a, b', c) ∈ t → (a, b, c') ∈ t →
  a = a' ∨ b = b' ∨ c = c')

section decidable_eq
variables [decidable_eq α] [decidable_eq β] [decidable_eq γ]

instance : decidable_rel (graph t).adj
| (in₀ a) (in₀ a') := decidable.is_false not_in₀₀
| (in₀ a) (in₁ b') := decidable_of_iff' _ in₀₁_iff'
| (in₀ a) (in₂ c') := decidable_of_iff' _ in₀₂_iff'
| (in₁ b) (in₀ a') := decidable_of_iff' _ in₁₀_iff'
| (in₁ b) (in₁ b') := decidable.is_false not_in₁₁
| (in₁ b) (in₂ b') := decidable_of_iff' _ in₁₂_iff'
| (in₂ c) (in₀ a') := decidable_of_iff' _ in₂₀_iff'
| (in₂ c) (in₁ b') := decidable_of_iff' _ in₂₁_iff'
| (in₂ c) (in₂ b') := decidable.is_false not_in₂₂

/-- This lemma reorders the elements of a triangle in the tripartite graph. It turns a triangle
`{x, y, z}` into a triangle `{a, b, c}` where `a : α `, `b : β`, `c : γ`. -/
 lemma graph_triple ⦃x y z⦄ :
  (graph t).adj x y → (graph t).adj x z → (graph t).adj y z → ∃ a b c,
    ({in₀ a, in₁ b, in₂ c} : finset (α ⊕ β ⊕ γ)) = {x, y, z} ∧ (graph t).adj (in₀ a) (in₁ b) ∧
      (graph t).adj (in₀ a) (in₂ c) ∧ (graph t).adj (in₁ b) (in₂ c) :=
by rintro (_ | _ | _) (_ | _ | _) (_ | _ | _); refine ⟨_, _, _, by ext; simp only
  [finset.mem_insert, finset.mem_singleton]; try { tauto }, _, _, _⟩; constructor; assumption

/-- The map that turns a triangle index into an explicit triangle. -/
def to_triangle (x : α × β × γ) : finset (α ⊕ β ⊕ γ) := {in₀ x.1, in₁ x.2.1, in₂ x.2.2}

lemma to_triangle_injective : injective (to_triangle : α × β × γ → finset (α ⊕ β ⊕ γ)) :=
begin
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩,
  simpa only [to_triangle, finset.subset.antisymm_iff, finset.subset_iff, mem_insert, mem_singleton,
    forall_eq_or_imp, forall_eq, prod.mk.inj_iff, or_false, false_or, in₀, in₁, in₂, sum.inl.inj_eq,
    sum.inr.inj_eq] using and.left,
end

lemma to_triangle_is_3_clique (hx : x ∈ t) : (graph t).is_n_clique 3 (to_triangle x) :=
begin
  rcases x with ⟨a, b, c⟩,
  simp only [to_triangle, is_3_clique_triple_iff, in₀₁_iff, in₀₂_iff, in₁₂_iff],
  exact ⟨⟨_, hx⟩, ⟨_, hx⟩, _, hx⟩,
end

lemma exists_mem_to_triangle {x y : α ⊕ β ⊕ γ} (hxy : (graph t).adj x y) :
  ∃ z ∈ t, x ∈ to_triangle z ∧ y ∈ to_triangle z :=
by cases hxy; exact ⟨_, ‹_›, by simp [to_triangle]⟩

lemma is_3_clique_iff [no_accidental t] {s : finset (α ⊕ β ⊕ γ)} :
  (graph t).is_n_clique 3 s ↔ ∃ x, x ∈ t ∧ to_triangle x = s :=
begin
  refine ⟨λ h, _, _⟩,
  { rw is_3_clique_iff at h,
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := h,
    obtain ⟨a, b, c, habc, hab, hac, hbc⟩ := graph_triple hxy hxz hyz,
    refine ⟨(a, b, c), _, habc⟩,
    obtain ⟨c', hc'⟩ := in₀₁_iff.1 hab,
    obtain ⟨b', hb'⟩ := in₀₂_iff.1 hac,
    obtain ⟨a', ha'⟩ := in₁₂_iff.1 hbc,
    obtain (rfl | rfl | rfl) := no_accidental.wow ha' hb' hc'; assumption },
  { rintro ⟨x, hx, rfl⟩,
    exact to_triangle_is_3_clique hx }
end

lemma to_triangle_surj_on [no_accidental t] :
  (t : set (α × β × γ)).surj_on to_triangle ((graph t).clique_set 3) :=
λ s, is_3_clique_iff.1

variables (t)

lemma image_to_triangle_disjoint [explicit_disjoint t] :
  (t.image to_triangle : set (finset (α ⊕ β ⊕ γ))).pairwise $
    λ x y, (x ∩ y : set (α ⊕ β ⊕ γ)).subsingleton :=
begin
  intro,
  simp only [finset.coe_image, set.mem_image, finset.mem_coe, prod.exists, ne.def,
    forall_exists_index, and_imp],
  rintro a b c habc rfl e x y z hxyz rfl h',
  have := ne_of_apply_ne _ h',
  simp only [ne.def, prod.mk.inj_iff, not_and] at this,
  simp only [to_triangle, in₀, in₁, in₂, set.mem_inter_iff, mem_insert, mem_singleton, mem_coe,
    and_imp, sum.forall, or_false, forall_eq, false_or, eq_self_iff_true, implies_true_iff,
    true_and, and_true, set.subsingleton],
  suffices : ¬ (a = x ∧ b = y) ∧ ¬ (a = x ∧ c = z) ∧ ¬ (b = y ∧ c = z),
  { tauto },
  refine ⟨_, _, _⟩,
  { rintro ⟨rfl, rfl⟩,
    exact this rfl rfl (explicit_disjoint.inj₂ habc hxyz) },
  { rintro ⟨rfl, rfl⟩,
    exact this rfl (explicit_disjoint.inj₁ habc hxyz) rfl },
  { rintro ⟨rfl, rfl⟩,
    exact this (explicit_disjoint.inj₀ habc hxyz) rfl rfl }
end

lemma clique_set_eq_image [no_accidental t] : (graph t).clique_set 3 = to_triangle '' t :=
by ext; exact is_3_clique_iff

section fintype
variables [fintype α] [fintype β] [fintype γ]

lemma clique_finset_eq_image [no_accidental t] : (graph t).clique_finset 3 = t.image to_triangle :=
coe_injective $ by { push_cast, exact clique_set_eq_image _ }

lemma clique_finset_eq_map [no_accidental t] :
  (graph t).clique_finset 3 = t.map ⟨_, to_triangle_injective⟩ :=
by simp [clique_finset_eq_image, map_eq_image]

@[simp] lemma card_triangles [no_accidental t] : ((graph t).clique_finset 3).card = t.card :=
by rw [clique_finset_eq_map, card_map]

end fintype
end decidable_eq

variables (t)

lemma locally_linear [explicit_disjoint t] [no_accidental t] : (graph t).locally_linear :=
begin
  classical,
  refine ⟨_, λ x y hxy, _⟩,
  { unfold edge_disjoint_triangles,
    convert image_to_triangle_disjoint t,
    rw [clique_set_eq_image, coe_image] },
  { obtain ⟨z, hz, hxy⟩ := exists_mem_to_triangle hxy,
    exact ⟨_, to_triangle_is_3_clique hz, hxy⟩ }
end

end tripartite_from_triangles
end simple_graph
