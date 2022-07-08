/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

import analysis.normed_space.basic

/-!
# Hamming spaces

The Hamming metric counts the number of places two members of a (finite) Pi type
differ. The Hamming norm is the same as the Hamming metric over additive groups, and
counts the number of places a member of a (finite) Pi type differs from zero.

This is a useful notion in various applications, but in particular it is relevant
in coding theory, in which it is fundamental for defining the minimum distance of a
code.

In this file we define `hamm_dist` and `hamm_norm`, the Hamming distance and Hamming norm. We also
define `hamm β`, the type synonym of a Pi type with `hamm_dist` and `hamm_norm` attached, and
provide instances and API for this type synonym.
-/
section hamm_dist_wt

open finset function

variables {α ι : Type*} {β : ι → Type*} [fintype ι] [Π i, decidable_eq (β i)]
variables {γ : ι → Type*} [Π i, decidable_eq (γ i)]

/-- The Hamming distance function to the naturals. -/
def hamm_dist (x y : Π i, β i) : ℕ := (univ.filter (λ i, x i ≠ y i)).card

/-- Corresponds to `dist_self`. -/
@[simp] lemma hamm_dist_self (x : Π i, β i) : hamm_dist x x = 0 :=
by { rw [hamm_dist, card_eq_zero, filter_eq_empty_iff], exact λ _ _ H, H rfl }

/-- Corresponds to `dist_nonneg`. -/
lemma hamm_dist_nonneg {x y : Π i, β i} : 0 ≤ hamm_dist x y := zero_le _

/-- Corresponds to `dist_comm`. -/
lemma hamm_dist_comm (x y : Π i, β i) : hamm_dist x y = hamm_dist y x :=
by simp_rw [hamm_dist, ne_comm]

/-- Corresponds to `dist_triangle`. -/
lemma hamm_dist_triangle (x y z : Π i, β i) :
  hamm_dist x z ≤ hamm_dist x y + hamm_dist y z :=
begin
  classical, simp_rw hamm_dist, refine le_trans (card_mono _) (card_union_le _ _), rw ← filter_or,
  refine monotone_filter_right _ _, intros i h, by_contra' H, exact h (eq.trans H.1 H.2)
end

/-- Corresponds to `dist_triangle_left`. -/
lemma hamm_dist_triangle_left (x y z : Π i, β i) : hamm_dist x y ≤ hamm_dist z x + hamm_dist z y :=
by { rw hamm_dist_comm z, exact hamm_dist_triangle _ _ _ }

/-- Corresponds to `dist_triangle_right`. -/
lemma hamm_dist_triangle_right (x y z : Π i, β i) : hamm_dist x y ≤ hamm_dist x z + hamm_dist y z :=
by { rw hamm_dist_comm y, exact hamm_dist_triangle _ _ _ }

/-- Corresponds to `swap_dist`. -/
theorem swap_hamm_dist : swap (@hamm_dist _ β _ _) = hamm_dist :=
by { funext x y, exact hamm_dist_comm _ _ }

/-- Corresponds to `eq_of_hamm_dist_eq_zero`. -/
lemma eq_of_hamm_dist_eq_zero {x y : Π i, β i} : hamm_dist x y = 0 → x = y :=
by simp_rw [  hamm_dist, card_eq_zero, filter_eq_empty_iff, not_not,
              funext_iff,  mem_univ, forall_true_left, imp_self]

/-- Corresponds to `dist_eq_zero`. -/
@[simp] lemma hamm_dist_eq_zero {x y : Π i, β i} : hamm_dist x y = 0 ↔ x = y :=
⟨eq_of_hamm_dist_eq_zero, (λ H, by {rw H, exact hamm_dist_self _})⟩

/-- Corresponds to `eq_of_zero_eq_dist`. -/
@[simp] lemma hamm_zero_eq_dist {x y : Π i, β i} : 0 = hamm_dist x y ↔ x = y :=
by rw [eq_comm, hamm_dist_eq_zero]

/-- Corresponds to `dist_ne_zero`. -/
lemma hamm_dist_ne_zero {x y : Π i, β i} : hamm_dist x y ≠ 0 ↔ x ≠ y :=
not_iff_not.mpr hamm_dist_eq_zero

/-- Corresponds to `dist_ne_zero`. -/
lemma hamm_dist_pos {x y : Π i, β i} : 0 < hamm_dist x y ↔ x ≠ y :=
by rw [←hamm_dist_ne_zero, iff_not_comm, not_lt, nat.le_zero_iff]

@[simp] lemma hamm_dist_lt_one {x y : Π i, β i} : hamm_dist x y < 1 ↔ x = y :=
by {rw nat.lt_one_iff, exact hamm_dist_eq_zero}

lemma hamm_dist_le_card_fintype {x y : Π i, β i} : hamm_dist x y ≤ fintype.card ι := card_le_univ _

lemma hamm_dist_comp_le_hamm_dist (f : Π i, γ i → β i) {x y : Π i, γ i} :
  hamm_dist (λ i, f i (x i)) (λ i, f i (y i)) ≤ hamm_dist x y :=
card_mono (monotone_filter_right _ $ λ i H1 H2, H1 $ congr_arg (f i) H2)

lemma hamm_dist_comp (f : Π i, γ i → β i) {x y : Π i, γ i} (hf : Π i, injective (f i)) :
  hamm_dist (λ i, f i (x i)) (λ i, f i (y i)) = hamm_dist x y :=
begin
  refine le_antisymm (hamm_dist_comp_le_hamm_dist _) _,
  exact card_mono (monotone_filter_right _ $ λ i H1 H2, H1 $ hf i H2)
end

lemma hamm_dist_smul_le_hamm_dist [Π i, has_smul α (β i)] {k : α} {x y : Π i, β i} :
  hamm_dist (k • x) (k • y) ≤ hamm_dist x y :=
hamm_dist_comp_le_hamm_dist $ λ i, (•) k

/-- Corresponds to `dist_smul` with the discrete norm on `α`. -/
lemma hamm_dist_smul [Π i, has_smul α (β i)] {k : α} {x y : Π i, β i}
  (hk : Π i, is_smul_regular (β i) k) : hamm_dist (k • x) (k • y) = hamm_dist x y :=
hamm_dist_comp (λ i, (•) k) hk

section has_zero

variables [Π i, has_zero (β i)] [Π i, has_zero (γ i)]

/-- The Hamming weight function to the naturals. -/
def hamm_wt (x : Π i, β i) : ℕ := hamm_dist x 0

lemma hamm_wt_eq (x : Π i, β i) : hamm_wt x = card {i // x i ≠ 0} := rfl

lemma hamm_wt_eq_hamm_dist_zero (x : Π i, β i) : hamm_wt x = hamm_dist x 0 := rfl

lemma hamm_wt_nonneg {x : Π i, β i} : 0 ≤ hamm_wt x := hamm_dist_nonneg

lemma hamm_wt_le_card_fintype {x : Π i, β i} : hamm_wt x ≤ card ι := hamm_dist_le_card_fintype

lemma hamm_wt_comp_le_hamm_wt (f : Π i, γ i → β i) {x : Π i, γ i} (hf : Π i, f i 0 = 0) :
  hamm_wt (λ i, f i (x i)) ≤ hamm_wt x :=
begin
  refine eq.trans_le _ (hamm_dist_comp_le_hamm_dist f),
  simp_rw [hamm_wt, pi.zero_def, hf],
end

lemma hamm_wt_comp (f : Π i, γ i → β i) {x : Π i, γ i} (hf₁ : Π i, injective (f i))
  (hf₂ : Π i, f i 0 = 0) : hamm_wt (λ i, f i (x i)) = hamm_wt x :=
begin
  simp_rw hamm_wt_eq_hamm_dist_zero, convert hamm_dist_comp f hf₁,
  simp_rw [pi.zero_apply, hf₂], refl
end

lemma hamm_wt_smul_le_hamm_wt [has_zero α] [Π i, smul_with_zero α (β i)] {k : α}
  {x : Π i, β i} : hamm_wt (k • x) ≤ hamm_wt x :=
hamm_wt_comp_le_hamm_wt (λ i (c : β i), k • c) (λ i, by simp_rw smul_zero')

lemma hamm_wt_smul [has_zero α] [Π i, smul_with_zero α (β i)] {k : α}
  (hk : ∀ i, is_smul_regular (β i) k) (x : Π i, β i) : hamm_wt (k • x) = hamm_wt x :=
hamm_wt_comp (λ i (c : β i), k • c) hk (λ i, by simp_rw smul_zero')

@[simp] lemma hamm_wt_eq_zero {x : Π i, β i} : hamm_wt x = 0 ↔ x = 0 := hamm_dist_eq_zero

@[simp] lemma hamm_wt_zero : hamm_wt (0 : Π i, β i) = 0 := hamm_dist_self _

lemma hamm_wt_ne_zero {x : Π i, β i} : hamm_wt x ≠ 0 ↔ x ≠ 0 := hamm_dist_ne_zero

lemma hamm_wt_pos_iff {x : Π i, β i} : 0 < hamm_wt x ↔ x ≠ 0 := hamm_dist_pos

@[simp] lemma hamm_wt_lt_one {x : Π i, β i} : hamm_wt x < 1 ↔ x = 0 := hamm_dist_lt_one

lemma hamm_wt_zero_iff_forall_zero {x : Π i, β i} : hamm_wt x = 0 ↔ ∀ i, x i = 0 :=
hamm_dist_eq_zero_iff_forall_eq_zero

lemma hamm_wt_ne_zero_iff_exists_ne_zero {x : Π i, β i} : hamm_wt x ≠ 0 ↔ ∃ i, x i ≠ 0 :=
hamm_dist_ne_zero_iff_exists_ne_zero

end has_zero

lemma hamm_dist_eq_hamm_wt_sub [Π i, add_group (β i)] (x y : Π i, β i) :
  hamm_dist x y = hamm_wt (x - y) :=
by simp_rw [hamm_wt_eq, hamm_dist, pi.sub_apply, sub_ne_zero]

end hamm_dist_wt

/-! ### The `hamm` type synonym -/

/--
Type synonym for a Pi type which we equip with the Hamming metric, adding relevant
instances as needed.
-/
def hamm {ι : Type*} (β : ι → Type*) : Type* := Π i, β i

namespace hamm

section

variables {α ι : Type*} {β : ι → Type*}

instance [Π i, inhabited (β i)] : inhabited (hamm β) := ⟨λ i, default⟩
instance [decidable_eq ι] [fintype ι] [Π i, fintype (β i)] : fintype (hamm β) := pi.fintype
instance [inhabited ι] [inst : ∀ i, nonempty (β i)] [nontrivial (β default)] : nontrivial (hamm β)
:= pi.nontrivial
instance [fintype ι] [Π i, decidable_eq (β i)] : decidable_eq (hamm β) :=
fintype.decidable_pi_fintype
instance [Π i, has_zero (β i)] : has_zero (hamm β) := pi.has_zero
instance [Π i, has_one (β i)] : has_one (hamm β) := pi.has_one
instance [Π i, has_neg (β i)] : has_neg (hamm β) := pi.has_neg
instance [Π i, has_add (β i)] : has_add (hamm β) := pi.has_add
instance [Π i, has_sub (β i)] : has_sub (hamm β) := pi.has_sub
instance [Π i, has_mul (β i)] : has_mul (hamm β) := pi.has_mul
instance [Π i, has_smul α (β i)] : has_smul α (hamm β) := pi.has_smul
instance [has_zero α] [Π i, has_zero (β i)] [Π i, smul_with_zero α (β i)] :
  smul_with_zero α (hamm β) := pi.smul_with_zero _
instance [Π i, add_monoid (β i)] : add_monoid (hamm β) := pi.add_monoid
instance [Π i, add_comm_monoid (β i)] : add_comm_monoid (hamm β) := pi.add_comm_monoid
instance [Π i, add_comm_group (β i)] : add_comm_group (hamm β) := pi.add_comm_group
instance (α) [semiring α] (β : ι → Type*) [Π i, add_comm_monoid (β i)]
  [Π i, module α (β i)] : module α (hamm β) := pi.module _ _ _

/-- `to_hamm` is the identity function to the `hamm` of a type.  -/
@[pattern] def to_hamm : (Π i, β i) ≃ hamm β := equiv.refl _

/-- `of_hamm` is the identity function from the `hamm` of a type.  -/
@[pattern] def of_hamm : hamm β ≃ Π i, β i := equiv.refl _

@[simp] lemma to_hamm_symm_eq                 : (@to_hamm _ β).symm = of_hamm := rfl
@[simp] lemma of_hamm_symm_eq                 : (@of_hamm _ β).symm = to_hamm := rfl
@[simp] lemma to_hamm_of_hamm (x : hamm β)    : to_hamm (of_hamm x) = x := rfl
@[simp] lemma of_hamm_to_hamm (x : Π i, β i)  : of_hamm (to_hamm x) = x := rfl
@[simp] lemma to_hamm_inj {x y : Π i, β i}    : to_hamm x = to_hamm y ↔ x = y := iff.rfl
@[simp] lemma of_hamm_inj {x y : hamm β}      : of_hamm x = of_hamm y ↔ x = y := iff.rfl

@[simp] lemma to_hamm_zero [Π i, has_zero (β i)] : to_hamm (0 : Π i, β i) = 0 := rfl
@[simp] lemma of_hamm_zero [Π i, has_zero (β i)] : of_hamm (0 : hamm β) = 0 := rfl
@[simp] lemma to_hamm_one [Π i, has_one (β i)] : to_hamm (1 : Π i, β i) = 1 := rfl
@[simp] lemma of_hamm_one [Π i, has_one (β i)] : of_hamm (1 : hamm β) = 1 := rfl
@[simp] lemma to_hamm_neg [Π i, has_neg (β i)] {x : Π i, β i} : to_hamm (-x) = - to_hamm x := rfl
@[simp] lemma of_hamm_neg [Π i, has_neg (β i)] {x : hamm β} : of_hamm (-x)  = - of_hamm x := rfl
@[simp] lemma to_hamm_add [Π i, has_add (β i)] {x y : Π i, β i} :
  to_hamm (x + y) = to_hamm x + to_hamm y := rfl
@[simp] lemma of_hamm_add [Π i, has_add (β i)] {x y : hamm β} :
  of_hamm (x + y) = of_hamm x + of_hamm y := rfl
@[simp] lemma to_hamm_sub [Π i, has_sub (β i)] {x y : Π i, β i} :
  to_hamm (x - y) = to_hamm x - to_hamm y := rfl
@[simp] lemma of_hamm_sub [Π i, has_sub (β i)] {x y : hamm β} :
  of_hamm (x - y) = of_hamm x - of_hamm y := rfl
@[simp] lemma to_hamm_mul [Π i, has_mul (β i)] {x y : Π i, β i} :
  to_hamm (x * y) = to_hamm x * to_hamm y := rfl
@[simp] lemma of_hamm_mul [Π i, has_mul (β i)] {x y : hamm β} :
  of_hamm (x * y) = of_hamm x * of_hamm y := rfl
@[simp] lemma to_hamm_smul [Π i, has_smul α (β i)] {r : α} {x : Π i, β i} :
  to_hamm (r • x) = r • to_hamm x := rfl
@[simp] lemma of_hamm_smul [Π i, has_smul α (β i)] {r : α} {x : hamm β} :
  of_hamm (r • x) = r • of_hamm x := rfl

end

section

variables {α ι : Type*} {β : ι → Type*} [fintype ι] [Π i, decidable_eq (β i)]

instance : has_dist (hamm β) := ⟨λ x y, hamm_dist (of_hamm x) (of_hamm y)⟩

@[simp, push_cast] lemma dist_eq_hamm_dist (x y : hamm β) :
  dist x y = hamm_dist (of_hamm x) (of_hamm y) := rfl

instance : pseudo_metric_space (hamm β) :=
{ dist_self           :=  by {push_cast, exact_mod_cast hamm_dist_self},
  dist_comm           :=  by {push_cast, exact_mod_cast hamm_dist_comm},
  dist_triangle       :=  by {push_cast, exact_mod_cast hamm_dist_triangle},
  to_uniform_space    :=  ⊥,
  uniformity_dist     :=  uniformity_dist_of_mem_uniformity _ _ $ λ s,
                          by {push_cast, split,
                          { refine λ hs, ⟨1, zero_lt_one, λ _ _ hab, _⟩,
                            rw_mod_cast [hamm_dist_lt_one] at hab,
                            rw [of_hamm_inj, ← mem_id_rel] at hab, exact hs hab },
                          { rintros ⟨_, hε, hs⟩ ⟨_, _⟩ hab, rw mem_id_rel at hab, rw hab,
                            refine hs (lt_of_eq_of_lt _ hε), exact_mod_cast hamm_dist_self _ }},
  to_bornology        :=  ⟨⊥, bot_le⟩,
  cobounded_sets      :=  by  {ext, push_cast,
                              refine iff_of_true  (filter.mem_sets.mpr filter.mem_bot)
                                                  ⟨fintype.card ι, λ _ _ _ _, _⟩,
                              exact_mod_cast hamm_dist_le_card_fintype},
  ..hamm.has_dist }

instance : metric_space (hamm β) :=
{ eq_of_dist_eq_zero  := by {push_cast, exact_mod_cast eq_of_hamm_dist_eq_zero},
  ..hamm.pseudo_metric_space }

instance [Π i, has_zero (β i)] : has_norm (hamm β) := ⟨λ x, hamm_wt (of_hamm x)⟩

@[simp, push_cast] lemma norm_eq_hamm_wt [Π i, has_zero (β i)] (x : hamm β) :
  ∥x∥ = hamm_wt (of_hamm x) := rfl

instance [Π i, add_comm_group (β i)] : semi_normed_group (hamm β) :=
{ dist_eq := by {push_cast, exact_mod_cast hamm_dist_eq_hamm_wt_sub}, ..pi.add_comm_group }

instance [Π i, add_comm_group (β i)] : normed_group (hamm β) := { ..hamm.semi_normed_group }

end

end hamm
