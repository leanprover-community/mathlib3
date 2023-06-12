/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import combinatorics.simple_graph.triangle.basic

/-!
# Construct a tripartite graph from its triangles


-/

open finset function sum3

variables {α β γ : Type*} {t : finset (α × β × γ)} {a a' : α} {b b' : β} {c c' : γ} {x : α × β × γ}

namespace simple_graph
namespace tripartite_from_triangles

@[mk_iff]
inductive rel (t : finset (α × β × γ)) : α ⊕ β ⊕ γ → α ⊕ β ⊕ γ → Prop
| in₀₁ ⦃a b c⦄ : (a, b, c) ∈ t → rel (in₀ a) (in₁ b)
| in₁₀ ⦃a b c⦄ : (a, b, c) ∈ t → rel (in₁ b) (in₀ a)
| in₀₂ ⦃a b c⦄ : (a, b, c) ∈ t → rel (in₀ a) (in₂ c)
| in₂₀ ⦃a b c⦄ : (a, b, c) ∈ t → rel (in₂ c) (in₀ a)
| in₁₂ ⦃a b c⦄ : (a, b, c) ∈ t → rel (in₁ b) (in₂ c)
| in₂₁ ⦃a b c⦄ : (a, b, c) ∈ t → rel (in₂ c) (in₁ b)

open rel

lemma rel_irrefl : ∀ x, ¬ rel t x x.
lemma rel_symm : symmetric (rel t) := λ x y h, by cases h; constructor; assumption

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

end graph

open graph

variables [decidable_eq α] [decidable_eq β] [decidable_eq γ]

instance [fintype α] [fintype β] [fintype γ] : decidable_rel (graph t).adj
| (in₀ a) (in₀ a') := decidable.is_false not_in₀₀
| (in₀ a) (in₁ b') := decidable_of_iff' _ in₀₁_iff
| (in₀ a) (in₂ c') := decidable_of_iff' _ in₀₂_iff
| (in₁ b) (in₀ a') := decidable_of_iff' _ in₁₀_iff
| (in₁ b) (in₁ b') := decidable.is_false not_in₁₁
| (in₁ b) (in₂ b') := decidable_of_iff' _ in₁₂_iff
| (in₂ c) (in₀ a') := decidable_of_iff' _ in₂₀_iff
| (in₂ c) (in₁ b') := decidable_of_iff' _ in₂₁_iff
| (in₂ c) (in₂ b') := decidable.is_false not_in₂₂

/-- Throwaway tactic. -/
private meta def sets_simp : tactic unit :=
`[ext] >> `[simp only [finset.mem_insert, finset.mem_singleton]] >> `[try {tauto}]

 lemma graph_triple :
  ∀ x y z, (graph t).adj x y → (graph t).adj x z → (graph t).adj y z →
    ∃ a b c, ({in₀ a, in₁ b, in₂ c} : finset (α ⊕ β ⊕ γ)) = {x, y, z} ∧
      (graph t).adj (in₀ a) (in₁ b) ∧ (graph t).adj (in₀ a) (in₂ c) ∧ (graph t).adj (in₁ b) (in₂ c)
| _ _ _ (in₀₁ h₁) (in₀₂ h₃) (in₁₂ h₂) := ⟨_, _, _, by sets_simp, in₀₁ h₁, in₀₂ h₃, in₁₂ h₂⟩
| _ _ _ (in₁₀ h₁) (in₁₂ h₃) (in₀₂ h₂) := ⟨_, _, _, by sets_simp, in₀₁ h₁, in₀₂ h₂, in₁₂ h₃⟩
| _ _ _ (in₁₂ h₁) (in₁₀ h₃) (in₂₀ h₂) := ⟨_, _, _, by sets_simp, in₀₁ h₃, in₀₂ h₂, in₁₂ h₁⟩
| _ _ _ (in₂₁ h₁) (in₂₀ h₃) (in₁₀ h₂) := ⟨_, _, _, by sets_simp, in₀₁ h₂, in₀₂ h₃, in₁₂ h₁⟩
| _ _ _ (in₂₀ h₁) (in₂₁ h₃) (in₀₁ h₂) := ⟨_, _, _, by sets_simp, in₀₁ h₂, in₀₂ h₁, in₁₂ h₃⟩
| _ _ _ (in₀₂ h₁) (in₀₁ h₃) (in₂₁ h₂) := ⟨_, _, _, by sets_simp, in₀₁ h₃, in₀₂ h₁, in₁₂ h₂⟩

/-- -/
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

class triangles_disjoint (t : finset (α × β × γ)) : Prop :=
(inj₀ : ∀ ⦃a a' b c⦄, (a, b, c) ∈ t → (a', b, c) ∈ t → a = a')
(inj₁ : ∀ ⦃a b b' c⦄, (a, b, c) ∈ t → (a, b', c) ∈ t → b = b')
(inj₂ : ∀ ⦃a b c c'⦄, (a, b, c) ∈ t → (a, b, c') ∈ t → c = c')

class no_accidental_triangle (t : finset (α × β × γ)) : Prop :=
(wow : ∀ a a' b b' c c', (a', b, c) ∈ t → (a, b', c) ∈ t → (a, b, c') ∈ t →
  a = a' ∨ b = b' ∨ c = c')

lemma is_3_clique_iff [no_accidental_triangle t] {s : finset (α ⊕ β ⊕ γ)} :
  (graph t).is_n_clique 3 s ↔ ∃ x, x ∈ t ∧ to_triangle x = s :=
begin
  refine ⟨λ h, _, _⟩,
  { rw is_3_clique_iff at h,
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := h,
    obtain ⟨a, b, c, habc, hab, hac, hbc⟩ := graph_triple _ _ _ hxy hxz hyz,
    refine ⟨(a, b, c), _, habc⟩,
    obtain ⟨c', hc'⟩ := in₀₁_iff.1 hab,
    obtain ⟨b', hb'⟩ := in₀₂_iff.1 hac,
    obtain ⟨a', ha'⟩ := in₁₂_iff.1 hbc,
    obtain (rfl | rfl | rfl) := no_accidental_triangle.wow _ _ _ _ _ _ ha' hb' hc'; assumption },
  { rintro ⟨x, hx, rfl⟩,
    exact to_triangle_is_3_clique hx }
end

lemma to_triangle_surj_on [no_accidental_triangle t] :
  (t : set (α × β × γ)).surj_on to_triangle ((graph t).clique_set 3) :=
λ s, is_3_clique_iff.1

variables (t)

lemma image_to_triangle_disjoint [triangles_disjoint t] :
  (t.image to_triangle : set (finset (α ⊕ β ⊕ γ))).pairwise (λ x y, (x ∩ y).card ≤ 1) :=
begin
  intro,
  simp only [finset.coe_image, set.mem_image, finset.mem_coe, prod.exists, ne.def,
    forall_exists_index, and_imp],
  rintro a b c habc rfl e x y z hxyz rfl h',
  have := ne_of_apply_ne _ h',
  simp only [ne.def, prod.mk.inj_iff, not_and] at this,
  rw finset.card_le_one,
  simp only [to_triangle],
  simp only [in₀, in₁, in₂, mem_inter, mem_insert, mem_singleton, and_imp, sum.forall, or_false,
    forall_eq, false_or, eq_self_iff_true, implies_true_iff, true_and, and_true],
  suffices : ¬ (a = x ∧ b = y) ∧ ¬ (a = x ∧ c = z) ∧ ¬ (b = y ∧ c = z),
  { tauto },
  refine ⟨_, _, _⟩,
  { rintro ⟨rfl, rfl⟩,
    exact this rfl rfl (triangles_disjoint.inj₂ habc hxyz) },
  { rintro ⟨rfl, rfl⟩,
    exact this rfl (triangles_disjoint.inj₁ habc hxyz) rfl },
  { rintro ⟨rfl, rfl⟩,
    exact this (triangles_disjoint.inj₀ habc hxyz) rfl rfl }
end

lemma clique_set_eq_image [no_accidental_triangle t] : (graph t).clique_set 3 = to_triangle '' t :=
by ext; exact is_3_clique_iff

lemma clique_finset_eq_image [no_accidental_triangle t] [fintype α] [fintype β] [fintype γ] :
  (graph t).clique_finset 3 = t.image to_triangle :=
coe_injective $ by { push_cast, exact clique_set_eq_image _ }

lemma clique_finset_eq_map [no_accidental_triangle t] [fintype α] [fintype β] [fintype γ] :
  (graph t).clique_finset 3 = t.map ⟨_, to_triangle_injective⟩ :=
by simp [clique_finset_eq_image, map_eq_image]

@[simp] lemma card_triangles [no_accidental_triangle t] [fintype α] [fintype β] [fintype γ] :
  ((graph t).clique_finset 3).card = t.card :=
by rw [clique_finset_eq_map, card_map]

lemma edge_disjoint_triangles [triangles_disjoint t] [no_accidental_triangle t] :
  (graph t).edge_disjoint_triangles :=
begin
  unfold edge_disjoint_triangles,
  convert image_to_triangle_disjoint t,
  rw [clique_set_eq_image, coe_image],
end

end tripartite_from_triangles
end simple_graph
