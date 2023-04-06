/-
Copyright (c) 2021 Grayson Burton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Grayson Burton, Yaël Dillies, Violeta Hernández Palacios
-/
import .grade
import order.zorn

/-!
# Flags of polytopes

In this file we prove that isomorphisms preserve flags, and as such, automorphisms of orders induce
a group action on flags. We also define flag-adjacency and (strong) flag-connectedness.

Flags turn out to be crucial in proving a critical theorem: every graded partial order has elements
of each possible grade. As such, various important theorems that don't directly reference flags are
also proven in this file.

## Main definitions

* `graded.idx`: returns some element of a given grade.

## Main results

* `graded.exists_grade_eq`: there's an element of any possible grade in a graded order.
* `graded.flag_card_eq`: all flags of a graded order have the same cardinality.
* `graded.scon_iff_sfcon`: strong connectedness and strong flag-connectedness are equivalent.

There's a few more of both I'm missing.
-/

universe u
variables {𝕆 α β : Type*}

instance [fintype α] [preorder α] [decidable_pred (@is_max_chain α (<))] : fintype (flag α) :=
sorry

-- first get `fintype (flags α × fin (grade ⊤ + 1))`,
-- then the obvious injection `α → flags α × fin (grade ⊤ + 1)`
-- noncomputable
def fintype.of_flag [partial_order α] [bounded_order α] [fintype (flag α)] : fintype α := sorry

/-- One can build a chain by concatenating two others. -/
lemma chain_of_chains [preorder α] {x y z : α} (c : set (set.Icc x y)) (d : set (set.Ioc y z)) :
  is_chain (<) c → is_chain (<) d → is_chain (<) (subtype.val '' c ∪ subtype.val '' d) :=
begin
  intros hc hd a ha b hb hne,
  obtain ⟨a', hac, ha⟩ | ⟨a', had, ha⟩ := ha,
  all_goals { obtain ⟨b', hbc, hb⟩ | ⟨b', hbd, hb⟩ := hb },
  all_goals { rw [←ha, ←hb] },
  { exact or.imp id id (hc hac hbc (subtype.ne_of_val_ne $ by rwa [ha, hb])) },
  { exact or.inl (lt_of_le_of_lt a'.prop.right b'.prop.left) },
  { exact or.inr (lt_of_le_of_lt b'.prop.right a'.prop.left) },
  { exact or.imp id id (hd had hbd (subtype.ne_of_val_ne $ by rwa [ha, hb])) },
end

namespace graded
section partial_order
variables [partial_order α] [bounded_order α] [grade_min_order ℕ α] (j : fin (grade ℕ (⊤ : α) + 1))

/-- A graded partial order has an element of grade `j` when `j ≤ grade 𝕆 ⊤`. -/
theorem exists_grade_eq : ∃ a : α, grade ℕ a = j :=
begin
  obtain ⟨s : flag α⟩ := flag.nonempty,
  classical,
  obtain ⟨a, ha⟩ := @ex_of_grade_lin s _ _ _ j (nat.lt_succ_iff.1 j.2),
  exact ⟨a, ha⟩,
end

/-- The element of a certain grade in a graded partial order. -/
noncomputable def idx : α := classical.some (exists_grade_eq j)

/-- Like `idx`, but allows specifying the type explicitly. -/
noncomputable abbreviation idx' (α : Type*) [partial_order α] [bounded_order α]
  [grade_min_order ℕ α] (j : fin (grade ℕ ⊤ + 1)) : α :=
idx j

/-- The defining property of `idx`. -/
@[simp] theorem grade_idx : grade ℕ (idx j) = j := classical.some_spec (exists_grade_eq j)

end partial_order

section order_iso
variables [partial_order α] [bounded_order α] [grade_min_order ℕ α] [partial_order β]
  [bounded_order β] [grade_min_order ℕ β]

-- Todo(Vi): Generalize! This doesn't actually require `order_top`.
private lemma grade_le_of_order_iso {e : α ≃o β} {n : ℕ} :
  ∀ x, grade ℕ x = n → grade ℕ x ≤ grade ℕ (e x) :=
begin
  apply nat.strong_induction_on n,
  intros n H x,
  induction n with n,
  { intro hg,
    rw hg,
    exact zero_le _ },
  intro hgx,
  suffices : ∃ y, grade ℕ y = n ∧ y < x,
  { rcases this with ⟨y, hgy, h⟩,
    rw [hgx, ←hgy],
    exact nat.succ_le_of_lt
      ((H n (lt_add_one n) y hgy).trans_lt (grade_strict_mono $ e.strict_mono h)) },
  cases flag.exists_mem x with s hx,
  let x' : s := ⟨x, hx⟩,
  have hn : n < grade ℕ (⊤ : s) + 1,
  { refine nat.lt_succ_of_le (n.le_succ.trans _),
    rw ←hgx,
    exact grade_le_grade_top x },
  refine ⟨↑(graded.idx ⟨n, hn⟩), grade_idx ⟨n, hn⟩, (_ : _ < x')⟩,
  classical,
  refine grade_lt_grade_iff.1 _,
  exact ℕ,
  apply_instance,
  apply_instance,
  rw [grade_idx, ←flag.grade_coe x', subtype.coe_mk, hgx],
  exact lt_add_one n,
end

/-- Order isomorphisms preserve grades. In other words, grade functions are unique when they
exist. -/
-- Todo(Vi): Generalize! This doesn't actually require `order_top`.
theorem grade_eq_of_order_iso (e : α ≃o β) (x : α) : grade ℕ x = grade ℕ (e x) :=
begin
  rw eq_iff_le_not_lt,
  refine ⟨grade_le_of_order_iso _ rfl, _⟩,
  rw (by rw (order_iso.symm_apply_apply _ _) : grade ℕ x = grade ℕ (e.symm (e x))),
  exact not_lt_of_le (grade_le_of_order_iso _ rfl)
end

/-- Order isomorphisms preserve top grades. -/
lemma grade_top_eq_of_order_iso (e : α ≃o β) : grade ℕ (⊤ : α) = grade ℕ (⊤ : β) :=
by { rw ←e.map_top, exact grade_eq_of_order_iso e ⊤ }

end order_iso

section linear_order
variables [linear_order α] [bounded_order α] [grade_min_order ℕ α] (j : fin (grade ℕ (⊤ : α) + 1))

/-- `idx j` is the unique element of grade `j` in the linear order. -/
theorem grade_eq_iff_idx (a : α) : grade ℕ a = j ↔ a = graded.idx j :=
begin
  have idx := grade_idx j,
  refine ⟨λ ha, _, λ h, by rwa h⟩,
  obtain ⟨_, _, h⟩ := ex_unique_of_grade (nat.lt_succ_iff.1 j.2),
  rw [h _ ha, h _ idx],
end

/-- `grade_fin` is an order isomorphism for linearly ordered `α` with a top element. -/
noncomputable def order_iso_fin : α ≃o fin (grade ℕ ⊤ + 1) :=
rel_iso.of_surjective order_embedding.grade_fin $ λ x,
  ⟨graded.idx x, by simp [order_embedding.grade_fin]⟩

@[reducible]
noncomputable def grade_order.to_fintype : fintype α :=
fintype.of_bijective (order_iso_fin).inv_fun order_iso_fin.symm.bijective

/-- The cardinality of a linear order is its top grade plus one. -/
@[simp]
theorem fincard_eq_gt [fintype α] : fintype.card α = grade ℕ (⊤ : α) + 1 :=
begin
  cases hfc : fintype.card α, { rw fintype.card_eq_zero_iff at hfc, exact hfc.elim' ⊤ },
  rw [fintype.card_of_bijective order_iso_fin.bijective,
      fintype.card_fin (grade ℕ (⊤ : α) + 1)] at hfc,
  rw ←hfc
end

end linear_order

section partial_order
variables [partial_order α] [bounded_order α] [grade_min_order ℕ α] [fintype α]

/-- The cardinality of any flag is the grade of the top element. In other words, in a graded order,
all flags have the same cardinality. -/
theorem flag_card_eq_top_grade_succ (Φ : flag α) [fintype Φ] :
  fintype.card Φ = grade ℕ (⊤ : α) + 1 :=
sorry -- fincard_eq_gt

/-- Any two flags have the same cardinality. -/
theorem flag_card_eq (Φ Ψ : flag α) [fintype Φ] [fintype Ψ] : fintype.card Φ = fintype.card Ψ :=
by repeat { rw flag_card_eq_top_grade_succ }

end partial_order

def Icc_foo [preorder α] [Π Φ : flag α, fintype Φ] (x y : α) :
  Π Φ : flag (set.Icc x y), fintype Φ :=
begin
  intro Φ,
  --apply fintype.of_injective ,
  sorry
end

def foo [preorder α] [order_bot α] [Π Φ : flag α, fintype Φ]
  (hf : ∀ (Φ Ψ : flag α), fintype.card Φ = fintype.card Ψ) :
  grade_order ℕ α :=
sorry

end graded

namespace flag
section

/-- Two flags are adjacent when there's exactly one element in one but not in the other. This isn't
quite the usual definition, and we've made it more general than necessary for reasons of
convenience, but we prove it to be equivalent to the usual one in the case of graded orders (see
`adjacent_iff_ex_j_adjacent`). -/
def adjacent [preorder α] (Φ Ψ : flag α) : Prop := ∃! a, a ∈ (Φ \ Ψ : set α)

instance [preorder α] : is_irrefl (flag α) adjacent := ⟨λ _ ⟨_, ⟨hl, hr⟩, _⟩, hr hl⟩

variables [partial_order α] [bounded_order α] [grade_min_order ℕ α]

/-- If the indices of two flags are equal, all elements of one are in the other. -/
private lemma eq_of_eq_idx {Φ Ψ : flag α} :
  (∀ j, (graded.idx' Φ j).val = (graded.idx' Ψ j).val) → ∀ a, a ∈ Φ → a ∈ Ψ :=
begin
  intros h a ha,
  let a' : Φ := ⟨a, ha⟩,
  sorry
  -- let ga := grade_fin a',
  -- change a with a'.val,
  -- have heq := h (grade _ a'),
  -- have hga : (graded.idx' Φ ga) = a' := begin
  --   symmetry,
  --   apply (graded.grade_eq_iff_idx ga a').1,
  --   refl,
  -- end,
  -- rw hga at heq,
  -- rw heq,
  -- exact (graded.idx' Ψ ga).prop,
end

/-- Two flags are equal iff their elements of all grades are equal. -/
lemma eq_iff_eq_idx (Φ Ψ : flag α) : Φ = Ψ ↔ ∀ j, (graded.idx' Φ j).val = (graded.idx' Ψ j).val :=
sorry
-- ⟨λ h _, by rw h, λ h, subtype.ext_val
--   (set.ext (λ _, ⟨eq_of_eq_idx h _, eq_of_eq_idx (λ j, (h j).symm) _⟩))⟩

/-- Two flags are j-adjacent iff they share all but their j-th element. Note that a flag is never
adjacent to itself. -/
def j_adjacent (j : fin (grade ℕ ⊤ + 1)) (Φ Ψ : flag α) : Prop :=
∀ i, (graded.idx' Φ i).val = (graded.idx' Ψ i).val ↔ i ≠ j

instance (j : fin (grade ℕ ⊤ + 1)) : is_irrefl (flag α) (j_adjacent j) :=
⟨λ _ h, (h j).1 rfl rfl⟩

/-- j-adjacency is symmetric. -/
theorem j_adjacent.symm {j : fin (grade ℕ ⊤ + 1)} {Φ Ψ : flag α} :
  j_adjacent j Φ Ψ → j_adjacent j Ψ Φ :=
by { intros h i, rw ←(h i), exact eq_comm }

/-- Two flags in a graded order are adjacent iff they're j-adjacent for some j. -/
theorem adjacent_iff_ex_j_adjacent {Φ Ψ : flag α} : adjacent Φ Ψ ↔ ∃ j, j_adjacent j Φ Ψ :=
begin
  refine ⟨λ hΦΨ, _, λ h, _⟩,
  { cases hΦΨ with a ha,
    have : a ∈ Φ := sorry,
    let a' : Φ := ⟨a, this⟩,
    -- let j := grade_fin a',
    -- refine ⟨grade_fin a', λ j, ⟨λ hj hja, _, _⟩⟩
    -- { symmetry' at hja,
    --   rw subtype.ext_iff_val at hja,
    --   have : grade a' = j := sorry,
    --   rw graded.grade_eq_iff_idx at this,
    --   --rw ←this at hj,
    --   sorry },
    sorry },
  sorry,
end

/-- Adjacency is symmetric in a graded order. -/
theorem adjacent.symm {Φ Ψ : flag α} : adjacent Φ Ψ → adjacent Ψ Φ :=
by repeat { rw adjacent_iff_ex_j_adjacent }; exact λ ⟨j, hj⟩, ⟨j, hj.symm⟩

end
end flag
