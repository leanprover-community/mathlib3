/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/

import analysis.normed.group.basic

/-!
# Hamming spaces

The Hamming metric counts the number of places two members of a (finite) Pi type
differ. The Hamming norm is the same as the Hamming metric over additive groups, and
counts the number of places a member of a (finite) Pi type differs from zero.

This is a useful notion in various applications, but in particular it is relevant
in coding theory, in which it is fundamental for defining the minimum distance of a
code.

## Main definitions
* `hamming_dist x y`: the Hamming distance between `x` and `y`, the number of entries which differ.
* `hamming_norm x`: the Hamming norm of `x`, the number of non-zero entries.
* `hamming β`: a type synonym for `Π i, β i` with `dist` and `norm` provided by the above.
* `hamming.to_hamming`, `hamming.of_hamming`: functions for casting between `hamming β` and
`Π i, β i`.
* `hamming.normed_add_comm_group`: the Hamming norm forms a normed group on `hamming β`.
-/
section hamming_dist_norm

open finset function

variables {α ι : Type*} {β : ι → Type*} [fintype ι] [Π i, decidable_eq (β i)]
variables {γ : ι → Type*} [Π i, decidable_eq (γ i)]

/-- The Hamming distance function to the naturals. -/
def hamming_dist (x y : Π i, β i) : ℕ := (univ.filter (λ i, x i ≠ y i)).card

/-- Corresponds to `dist_self`. -/
@[simp] lemma hamming_dist_self (x : Π i, β i) : hamming_dist x x = 0 :=
by { rw [hamming_dist, card_eq_zero, filter_eq_empty_iff], exact λ _ _ H, H rfl }

/-- Corresponds to `dist_nonneg`. -/
lemma hamming_dist_nonneg {x y : Π i, β i} : 0 ≤ hamming_dist x y := zero_le _

/-- Corresponds to `dist_comm`. -/
lemma hamming_dist_comm (x y : Π i, β i) : hamming_dist x y = hamming_dist y x :=
by simp_rw [hamming_dist, ne_comm]

/-- Corresponds to `dist_triangle`. -/
lemma hamming_dist_triangle (x y z : Π i, β i) :
  hamming_dist x z ≤ hamming_dist x y + hamming_dist y z :=
begin
  classical, simp_rw hamming_dist, refine le_trans (card_mono _) (card_union_le _ _),
  rw ← filter_or, refine monotone_filter_right _ _, intros i h,
  by_contra' H, exact h (eq.trans H.1 H.2)
end

/-- Corresponds to `dist_triangle_left`. -/
lemma hamming_dist_triangle_left (x y z : Π i, β i) :
  hamming_dist x y ≤ hamming_dist z x + hamming_dist z y :=
by { rw hamming_dist_comm z, exact hamming_dist_triangle _ _ _ }

/-- Corresponds to `dist_triangle_right`. -/
lemma hamming_dist_triangle_right (x y z : Π i, β i) :
  hamming_dist x y ≤ hamming_dist x z + hamming_dist y z :=
by { rw hamming_dist_comm y, exact hamming_dist_triangle _ _ _ }

/-- Corresponds to `swap_dist`. -/
theorem swap_hamming_dist : swap (@hamming_dist _ β _ _) = hamming_dist :=
by { funext x y, exact hamming_dist_comm _ _ }

/-- Corresponds to `eq_of_dist_eq_zero`. -/
lemma eq_of_hamming_dist_eq_zero {x y : Π i, β i} : hamming_dist x y = 0 → x = y :=
by simp_rw [hamming_dist, card_eq_zero, filter_eq_empty_iff, not_not,
            funext_iff,  mem_univ, forall_true_left, imp_self]

/-- Corresponds to `dist_eq_zero`. -/
@[simp] lemma hamming_dist_eq_zero {x y : Π i, β i} : hamming_dist x y = 0 ↔ x = y :=
⟨eq_of_hamming_dist_eq_zero, (λ H, by {rw H, exact hamming_dist_self _})⟩

/-- Corresponds to `zero_eq_dist`. -/
@[simp] lemma hamming_zero_eq_dist {x y : Π i, β i} : 0 = hamming_dist x y ↔ x = y :=
by rw [eq_comm, hamming_dist_eq_zero]

/-- Corresponds to `dist_ne_zero`. -/
lemma hamming_dist_ne_zero {x y : Π i, β i} : hamming_dist x y ≠ 0 ↔ x ≠ y :=
hamming_dist_eq_zero.not

/-- Corresponds to `dist_pos`. -/
@[simp] lemma hamming_dist_pos {x y : Π i, β i} : 0 < hamming_dist x y ↔ x ≠ y :=
by rw [←hamming_dist_ne_zero, iff_not_comm, not_lt, le_zero_iff]

@[simp] lemma hamming_dist_lt_one {x y : Π i, β i} : hamming_dist x y < 1 ↔ x = y :=
by rw [nat.lt_one_iff, hamming_dist_eq_zero]

lemma hamming_dist_le_card_fintype {x y : Π i, β i} :
  hamming_dist x y ≤ fintype.card ι := card_le_univ _

lemma hamming_dist_comp_le_hamming_dist (f : Π i, γ i → β i) {x y : Π i, γ i} :
  hamming_dist (λ i, f i (x i)) (λ i, f i (y i)) ≤ hamming_dist x y :=
card_mono (monotone_filter_right _ $ λ i H1 H2, H1 $ congr_arg (f i) H2)

lemma hamming_dist_comp (f : Π i, γ i → β i) {x y : Π i, γ i} (hf : Π i, injective (f i)) :
  hamming_dist (λ i, f i (x i)) (λ i, f i (y i)) = hamming_dist x y :=
begin
  refine le_antisymm (hamming_dist_comp_le_hamming_dist _) _,
  exact card_mono (monotone_filter_right _ $ λ i H1 H2, H1 $ hf i H2)
end

lemma hamming_dist_smul_le_hamming_dist [Π i, has_smul α (β i)] {k : α} {x y : Π i, β i} :
  hamming_dist (k • x) (k • y) ≤ hamming_dist x y :=
hamming_dist_comp_le_hamming_dist $ λ i, (•) k

/-- Corresponds to `dist_smul` with the discrete norm on `α`. -/
lemma hamming_dist_smul [Π i, has_smul α (β i)] {k : α} {x y : Π i, β i}
  (hk : Π i, is_smul_regular (β i) k) : hamming_dist (k • x) (k • y) = hamming_dist x y :=
hamming_dist_comp (λ i, (•) k) hk

section has_zero

variables [Π i, has_zero (β i)] [Π i, has_zero (γ i)]

/-- The Hamming weight function to the naturals. -/
def hamming_norm (x : Π i, β i) : ℕ := (univ.filter (λ i, x i ≠ 0)).card

/-- Corresponds to `dist_zero_right`. -/
@[simp] lemma hamming_dist_zero_right (x : Π i, β i) : hamming_dist x 0 = hamming_norm x := rfl

/-- Corresponds to `dist_zero_left`. -/
@[simp] lemma hamming_dist_zero_left : hamming_dist (0 : Π i, β i) = hamming_norm :=
funext $ λ x, by rw [hamming_dist_comm, hamming_dist_zero_right]

/-- Corresponds to `norm_nonneg`. -/
@[simp] lemma hamming_norm_nonneg {x : Π i, β i} : 0 ≤ hamming_norm x := zero_le _

/-- Corresponds to `norm_zero`. -/
@[simp] lemma hamming_norm_zero : hamming_norm (0 : Π i, β i) = 0 := hamming_dist_self _

/-- Corresponds to `norm_eq_zero`. -/
@[simp] lemma hamming_norm_eq_zero {x : Π i, β i} : hamming_norm x = 0 ↔ x = 0 :=
hamming_dist_eq_zero

/-- Corresponds to `norm_ne_zero_iff`. -/
lemma hamming_norm_ne_zero_iff {x : Π i, β i} : hamming_norm x ≠ 0 ↔ x ≠ 0 :=
hamming_norm_eq_zero.not

/-- Corresponds to `norm_pos_iff`. -/
@[simp] lemma hamming_norm_pos_iff {x : Π i, β i} : 0 < hamming_norm x ↔ x ≠ 0 := hamming_dist_pos

@[simp] lemma hamming_norm_lt_one {x : Π i, β i} : hamming_norm x < 1 ↔ x = 0 := hamming_dist_lt_one

lemma hamming_norm_le_card_fintype {x : Π i, β i} : hamming_norm x ≤ fintype.card ι :=
hamming_dist_le_card_fintype

lemma hamming_norm_comp_le_hamming_norm (f : Π i, γ i → β i) {x : Π i, γ i} (hf : Π i, f i 0 = 0) :
  hamming_norm (λ i, f i (x i)) ≤ hamming_norm x :=
by {convert hamming_dist_comp_le_hamming_dist f, simp_rw hf, refl}

lemma hamming_norm_comp (f : Π i, γ i → β i) {x : Π i, γ i} (hf₁ : Π i, injective (f i))
  (hf₂ : Π i, f i 0 = 0) : hamming_norm (λ i, f i (x i)) = hamming_norm x :=
by {convert hamming_dist_comp f hf₁, simp_rw hf₂, refl}

lemma hamming_norm_smul_le_hamming_norm [has_zero α] [Π i, smul_with_zero α (β i)] {k : α}
  {x : Π i, β i} : hamming_norm (k • x) ≤ hamming_norm x :=
hamming_norm_comp_le_hamming_norm (λ i (c : β i), k • c) (λ i, by simp_rw smul_zero)

lemma hamming_norm_smul [has_zero α] [Π i, smul_with_zero α (β i)] {k : α}
  (hk : ∀ i, is_smul_regular (β i) k) (x : Π i, β i) : hamming_norm (k • x) = hamming_norm x :=
hamming_norm_comp (λ i (c : β i), k • c) hk (λ i, by simp_rw smul_zero)

end has_zero

/-- Corresponds to `dist_eq_norm`. -/
lemma hamming_dist_eq_hamming_norm [Π i, add_group (β i)] (x y : Π i, β i) :
  hamming_dist x y = hamming_norm (x - y) :=
by simp_rw [hamming_norm, hamming_dist, pi.sub_apply, sub_ne_zero]

end hamming_dist_norm

/-! ### The `hamming` type synonym -/

/-- Type synonym for a Pi type which inherits the usual algebraic instances, but is equipped with
the Hamming metric and norm, instead of `pi.normed_add_comm_group` which uses the sup norm. -/
def hamming {ι : Type*} (β : ι → Type*) : Type* := Π i, β i

namespace hamming

variables {α ι : Type*} {β : ι → Type*}

/-! Instances inherited from normal Pi types. -/

instance [Π i, inhabited (β i)] : inhabited (hamming β) := ⟨λ i, default⟩
instance [decidable_eq ι] [fintype ι] [Π i, fintype (β i)] : fintype (hamming β) := pi.fintype
instance [inhabited ι] [∀ i, nonempty (β i)] [nontrivial (β default)] :
  nontrivial (hamming β) := pi.nontrivial
instance [fintype ι] [Π i, decidable_eq (β i)] : decidable_eq (hamming β) :=
fintype.decidable_pi_fintype

instance [Π i, has_zero (β i)]    : has_zero (hamming β) := pi.has_zero
instance [Π i, has_neg (β i)]     : has_neg (hamming β) := pi.has_neg
instance [Π i, has_add (β i)]     : has_add (hamming β) := pi.has_add
instance [Π i, has_sub (β i)]     : has_sub (hamming β) := pi.has_sub
instance [Π i, has_smul α (β i)]  : has_smul α (hamming β) := pi.has_smul

instance [has_zero α] [Π i, has_zero (β i)] [Π i, smul_with_zero α (β i)] :
  smul_with_zero α (hamming β) := pi.smul_with_zero _
instance [Π i, add_monoid (β i)] : add_monoid (hamming β) := pi.add_monoid
instance [Π i, add_comm_monoid (β i)] : add_comm_monoid (hamming β) := pi.add_comm_monoid
instance [Π i, add_comm_group (β i)] : add_comm_group (hamming β) := pi.add_comm_group
instance (α) [semiring α] (β : ι → Type*) [Π i, add_comm_monoid (β i)]
  [Π i, module α (β i)] : module α (hamming β) := pi.module _ _ _

/-! API to/from the type synonym. -/

/-- `to_hamming` is the identity function to the `hamming` of a type.  -/
@[pattern] def to_hamming : (Π i, β i) ≃ hamming β := equiv.refl _

/-- `of_hamming` is the identity function from the `hamming` of a type.  -/
@[pattern] def of_hamming : hamming β ≃ Π i, β i := equiv.refl _

@[simp] lemma to_hamming_symm_eq : (@to_hamming _ β).symm = of_hamming := rfl
@[simp] lemma of_hamming_symm_eq : (@of_hamming _ β).symm = to_hamming := rfl
@[simp] lemma to_hamming_of_hamming (x : hamming β) : to_hamming (of_hamming x) = x := rfl
@[simp] lemma of_hamming_to_hamming (x : Π i, β i) : of_hamming (to_hamming x) = x := rfl
@[simp] lemma to_hamming_inj {x y : Π i, β i} : to_hamming x = to_hamming y ↔ x = y := iff.rfl
@[simp] lemma of_hamming_inj {x y : hamming β} : of_hamming x = of_hamming y ↔ x = y := iff.rfl

@[simp] lemma to_hamming_zero [Π i, has_zero (β i)] : to_hamming (0 : Π i, β i) = 0 := rfl
@[simp] lemma of_hamming_zero [Π i, has_zero (β i)] : of_hamming (0 : hamming β) = 0 := rfl
@[simp] lemma to_hamming_neg [Π i, has_neg (β i)] {x : Π i, β i} :
  to_hamming (-x) = - to_hamming x := rfl
@[simp] lemma of_hamming_neg [Π i, has_neg (β i)] {x : hamming β} :
  of_hamming (-x)  = - of_hamming x := rfl
@[simp] lemma to_hamming_add [Π i, has_add (β i)] {x y : Π i, β i} :
  to_hamming (x + y) = to_hamming x + to_hamming y := rfl
@[simp] lemma of_hamming_add [Π i, has_add (β i)] {x y : hamming β} :
  of_hamming (x + y) = of_hamming x + of_hamming y := rfl
@[simp] lemma to_hamming_sub [Π i, has_sub (β i)] {x y : Π i, β i} :
  to_hamming (x - y) = to_hamming x - to_hamming y := rfl
@[simp] lemma of_hamming_sub [Π i, has_sub (β i)] {x y : hamming β} :
  of_hamming (x - y) = of_hamming x - of_hamming y := rfl
@[simp] lemma to_hamming_smul [Π i, has_smul α (β i)] {r : α} {x : Π i, β i} :
  to_hamming (r • x) = r • to_hamming x := rfl
@[simp] lemma of_hamming_smul [Π i, has_smul α (β i)] {r : α} {x : hamming β} :
  of_hamming (r • x) = r • of_hamming x := rfl

section

/-! Instances equipping `hamming` with `hamming_norm` and `hamming_dist`. -/

variables [fintype ι] [Π i, decidable_eq (β i)]

instance : has_dist (hamming β) := ⟨λ x y, hamming_dist (of_hamming x) (of_hamming y)⟩

@[simp, push_cast] lemma dist_eq_hamming_dist (x y : hamming β) :
  dist x y = hamming_dist (of_hamming x) (of_hamming y) := rfl

instance : pseudo_metric_space (hamming β) :=
{ dist_self        := by { push_cast, exact_mod_cast hamming_dist_self },
  dist_comm        := by { push_cast, exact_mod_cast hamming_dist_comm },
  dist_triangle    := by { push_cast, exact_mod_cast hamming_dist_triangle },
  to_uniform_space := ⊥,
  uniformity_dist  := uniformity_dist_of_mem_uniformity _ _ $ λ s, begin
    push_cast,
    split,
    { refine λ hs, ⟨1, zero_lt_one, λ _ _ hab, _⟩,
      rw_mod_cast [hamming_dist_lt_one] at hab,
      rw [of_hamming_inj, ← mem_id_rel] at hab,
      exact hs hab },
    { rintros ⟨_, hε, hs⟩ ⟨_, _⟩ hab,
      rw mem_id_rel at hab,
      rw hab,
      refine hs (lt_of_eq_of_lt _ hε),
      exact_mod_cast hamming_dist_self _ }
  end,
  to_bornology     := ⟨⊥, bot_le⟩,
  cobounded_sets   := begin
    ext,
    push_cast,
    refine iff_of_true (filter.mem_sets.mpr filter.mem_bot) ⟨fintype.card ι, λ _ _ _ _, _⟩,
    exact_mod_cast hamming_dist_le_card_fintype
  end,
  ..hamming.has_dist }

@[simp, push_cast] lemma nndist_eq_hamming_dist (x y : hamming β) :
  nndist x y = hamming_dist (of_hamming x) (of_hamming y) := rfl

instance : metric_space (hamming β) :=
{ eq_of_dist_eq_zero  :=
  by { push_cast, exact_mod_cast @eq_of_hamming_dist_eq_zero _ _ _ _ },
  ..hamming.pseudo_metric_space }

instance [Π i, has_zero (β i)] : has_norm (hamming β) := ⟨λ x, hamming_norm (of_hamming x)⟩

@[simp, push_cast] lemma norm_eq_hamming_norm [Π i, has_zero (β i)] (x : hamming β) :
  ‖x‖ = hamming_norm (of_hamming x) := rfl

instance [Π i, add_comm_group (β i)] : seminormed_add_comm_group (hamming β) :=
{ dist_eq := by { push_cast, exact_mod_cast hamming_dist_eq_hamming_norm }, ..pi.add_comm_group }

@[simp, push_cast] lemma nnnorm_eq_hamming_norm [Π i, add_comm_group (β i)] (x : hamming β) :
  ‖x‖₊ = hamming_norm (of_hamming x) := rfl

instance [Π i, add_comm_group (β i)] : normed_add_comm_group (hamming β) :=
{ ..hamming.seminormed_add_comm_group }

end

end hamming
