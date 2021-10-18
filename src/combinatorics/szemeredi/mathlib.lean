/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import analysis.special_functions.exp_log
import combinatorics.simple_graph.basic
import data.set.equitable

/-! # Things that belong to mathlib -/

open_locale big_operators nat
open finset fintype function

variables {α β : Type*}

namespace sym2

attribute [elab_as_eliminator]
lemma ind {f : sym2 α → Prop} : (∀ x y, f ⟦(x,y)⟧) → ∀ (i : sym2 α), f i :=
begin
  intro hf,
  apply quotient.ind,
  rintro ⟨x, y⟩,
  apply hf
end

attribute [elab_as_eliminator]
lemma induction_on {f : sym2 α → Prop} (i : sym2 α) (hf : ∀ x y, f ⟦(x,y)⟧) : f i :=
sym2.ind hf i

lemma sum_sym2 [decidable_eq α] {β : Type*} [division_ring β] [char_zero β] (f : sym2 α → β)
  (s : finset (α × α)) {hs₁ : ∀ i j, (i,j) ∈ s → i ≠ j} (hs₂ : ∀ i j, (i,j) ∈ s → (j,i) ∈ s) :
  ∑ (i : sym2 _) in s.image quotient.mk, f i = (∑ i in s, f ⟦i⟧)/2 :=
begin
  rw sum_div,
  apply sum_image',
  rintro ⟨x, y⟩ h,
  suffices : s.filter (λ c', ⟦c'⟧ = ⟦(x,y)⟧) = {(x,y), (y,x)},
  { rw [this, sum_pair, sym2.eq_swap, add_halves'],
    rintro ⟨⟩,
    apply hs₁ _ _ h rfl, },
  ext ⟨i, j⟩,
  simp only [mem_filter, mem_insert, prod.mk.inj_iff, sym2.eq_iff, mem_singleton],
  tauto {closer := `[subst_vars; solve_by_elim]},
end

end sym2

lemma lt_of_not_le [linear_order α] {a b : α} (h : ¬ a ≤ b) : b < a := lt_of_not_ge' h

section group_power
variables {R : Type*}

lemma pow_right_comm [ordered_semiring R] {a : R} {b c : ℕ} : (a^b)^c = (a^c)^b :=
by rw [←pow_mul, mul_comm, pow_mul]

variables [linear_ordered_ring R] {a : R} {n : ℕ}

lemma odd.pow_nonneg (hn : odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
⟨λ h, le_of_not_lt (λ ha, h.not_lt $ pow_odd_neg ha hn), λ ha, pow_nonneg ha n⟩

lemma odd.pow_nonpos (hn : odd n) : a ^ n ≤ 0 ↔ a ≤ 0 :=
⟨λ h, le_of_not_lt (λ ha, h.not_lt $ pow_odd_pos ha hn), λ ha, pow_odd_nonpos ha hn⟩

lemma odd.pow_pos (hn : odd n) : 0 < a ^ n ↔ 0 < a :=
⟨λ h, lt_of_not_le (λ ha, h.not_le $ pow_odd_nonpos ha hn), λ ha, pow_pos ha n⟩

lemma odd.pow_neg (hn : odd n) : a ^ n < 0 ↔ a < 0 :=
⟨λ h, lt_of_not_le (λ ha, h.not_le $ pow_odd_nonneg ha hn), λ ha, pow_odd_neg ha hn⟩

end group_power

lemma one_div_le_one_of_one_le [linear_ordered_field α] {a : α} (ha : 1 ≤ a) : 1 / a ≤ 1 :=
(div_le_one $ zero_lt_one.trans_le ha).2 ha

lemma finset.pairwise_disjoint_range_singleton [decidable_eq α] :
  (set.range (singleton : α → finset α)).pairwise_disjoint :=
begin
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h,
  rw [disjoint_singleton, not_mem_singleton],
  exact ne_of_apply_ne _ h.symm,
end

lemma set.pairwise_disjoint.elim_finset [decidable_eq α] {s : set (finset α)}
  (hs : s.pairwise_disjoint) {x y : finset α} (hx : x ∈ s) (hy : y ∈ s) (z : α) (hzx : z ∈ x)
  (hzy : z ∈ y) : x = y :=
hs.elim hx hy (finset.not_disjoint_iff.2 ⟨z, hzx, hzy⟩)

lemma set.pairwise_disjoint_empty [semilattice_inf_bot α] : (∅ : set α).pairwise_disjoint :=
set.pairwise_on_empty _

lemma set.pairwise_disjoint.image_set [semilattice_inf_bot α] {s : set α}
  (hs : s.pairwise_disjoint) {f : α → α} (hf : ∀ a, f a ≤ a) :
  (f '' s).pairwise_disjoint :=
begin
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ h,
  exact (hs a ha b hb $ ne_of_apply_ne _ h).mono (hf a) (hf b),
end

lemma set.pairwise_disjoint.image_finset [decidable_eq α] [semilattice_inf_bot α]
  {s : finset α} (hs : (s : set α).pairwise_disjoint) {f : α → α} (hf : ∀ a, f a ≤ a) :
  set.pairwise_disjoint (s.image f :set α) :=
begin
  rw coe_image,
  exact hs.image_set hf,
end

lemma set.pairwise_disjoint_singleton [semilattice_inf_bot α] (a : α) :
  ({a} : set α ).pairwise_disjoint :=
set.pairwise_on_singleton a _

lemma set.pairwise_disjoint_insert [semilattice_inf_bot α] {s : set α} {a : α} :
  (insert a s).pairwise_disjoint ↔ s.pairwise_disjoint ∧ ∀ b ∈ s, a ≠ b → disjoint a b :=
set.pairwise_on_insert_of_symmetric symmetric_disjoint

lemma set.pairwise_disjoint.insert [semilattice_inf_bot α] {s : set α} (hs : s.pairwise_disjoint)
  {a : α} (hx : ∀ b ∈ s, a ≠ b → disjoint a b) :
  (insert a s).pairwise_disjoint :=
set.pairwise_disjoint_insert.2 ⟨hs, hx⟩

-- lemma set.pairwise_disjoint.bUnion [semilattice_inf_bot α] {s : set β} {f : β → set α}
--   (hs : (f '' s).pairwise_disjoint) (hf : ∀ a ∈ s, (f a).pairwise_disjoint) :
--   (⋃ a ∈ s, f a).pairwise_disjoint :=
-- begin
--   rintro a ha b hb hab,
--   simp_rw set.mem_Union at ha hb,
--   obtain ⟨c, hc, ha⟩ := ha,
--   obtain ⟨d, hd, hb⟩ := hb,
--   obtain hcd | hcd := eq_or_ne (f c) (f d),
--   { exact hf d hd a (hcd.subst ha) b hb hab },
--   {
--     have := hs _ (set.mem_image_of_mem _ hc) _ (set.mem_image_of_mem _ hd) hcd,
--     sorry
--   }
-- end


lemma set.pairwise_disjoint_insert_finset [semilattice_inf_bot α] {s : finset α} {a : α} :
  (insert a s : set α).pairwise_disjoint ↔ (s : set α).pairwise_disjoint ∧
    ∀ b ∈ s, a ≠ b → disjoint a b :=
set.pairwise_on_insert_of_symmetric symmetric_disjoint

lemma set.pairwise_disjoint.insert_finset [semilattice_inf_bot α] {s : finset α}
  (hs : (s : set α).pairwise_disjoint) {a : α} (hx : ∀ b ∈ s, a ≠ b → disjoint a b) :
  (insert a s : set α).pairwise_disjoint :=
set.pairwise_disjoint_insert.2 ⟨hs, hx⟩

-- lemma set.pairwise_disjoint_coe_iff [decidable_eq α] {s : set (finset α)} :
--   s.pairwise_disjoint ↔ ((coe : finset α → set α) '' s).pairwise_disjoint :=
-- sorry
-- #exit
namespace real

lemma le_exp_iff_log_le {a b : ℝ} (ha : 0 < a) : log a ≤ b ↔ a ≤ exp b :=
by rw [←exp_le_exp, exp_log ha]

end real

lemma sum_mul_sq_le_sq_mul_sq (s : finset α) (f g : α → ℝ) :
  (∑ i in s, f i * g i)^2 ≤ (∑ i in s, (f i)^2) * (∑ i in s, (g i)^2) :=
begin
  have : 0 ≤ ∑ i in s, (g i)^2 := sum_nonneg (λ i hi, sq_nonneg _),
  cases this.eq_or_lt with h h,
  { rw [eq_comm, sum_eq_zero_iff_of_nonneg] at h,
    { simp only [nat.succ_pos', pow_eq_zero_iff] at h,
      rw [finset.sum_congr rfl (show ∀ i ∈ s, f i * g i = 0, from λ i hi, by simp [h i hi]),
          finset.sum_congr rfl (show ∀ i ∈ s, g i ^ 2 = 0, from λ i hi, by simp [h i hi])],
      simp },
    { intros i hi,
      apply sq_nonneg } },
  let lambda := (∑ i in s, f i * g i) / (∑ i in s, (g i)^2),
  have : 0 ≤ ∑ i in s, (f i - lambda * g i)^2,
  { apply sum_nonneg,
    intros i hi,
    apply sq_nonneg },
  simp_rw [sub_sq, sum_add_distrib, sum_sub_distrib, mul_pow, mul_assoc, ←mul_sum,
    mul_left_comm _ lambda, ←mul_sum, div_pow, div_mul_eq_mul_div, ←sq, ←div_mul_eq_mul_div,
    div_mul_eq_mul_div_comm, sq (∑ i in s, g i ^ 2), div_self_mul_self', ←div_eq_mul_inv, two_mul,
    ←sub_sub, sub_add_cancel, sub_nonneg] at this,
  rw div_le_iff h at this,
  assumption
end

lemma chebyshev' (s : finset α) (f : α → ℝ) :
  (∑ (i : α) in s, f i) ^ 2 ≤ (∑ (i : α) in s, f i ^ 2) * s.card :=
by simpa using sum_mul_sq_le_sq_mul_sq s f (λ _, 1)

lemma chebyshev (s : finset α) (f : α → ℝ) :
  ((∑ i in s, f i) / s.card)^2 ≤ (∑ i in s, (f i)^2) / s.card :=
begin
  rcases s.eq_empty_or_nonempty with rfl | hs,
  { simp },
  rw div_pow,
  have hs' : 0 < (s.card : ℝ),
  { rwa [nat.cast_pos, card_pos] },
  rw [div_le_div_iff (sq_pos_of_ne_zero _ hs'.ne') hs', sq (s.card : ℝ), ←mul_assoc],
  apply mul_le_mul_of_nonneg_right (chebyshev' _ _) hs'.le,
end

namespace nat

lemma lt_div_mul_add {a b : ℕ} (hb : 0 < b) : a < a/b*b + b :=
begin
  rw [←nat.succ_mul, ←nat.div_lt_iff_lt_mul _ _ hb],
  exact nat.lt_succ_self _,
end

lemma succ_sub_self : ∀ {n : ℕ}, n.succ - n = 1
| 0       := rfl
| (n + 1) := by rw [succ_sub_succ, succ_sub_self]

end nat

open finset

/-! ## pairs_finset and pairs_density -/

namespace relation
variables (r : α → α → Prop) [decidable_rel r]

/-- Finset of edges between two finsets of vertices -/
def pairs_finset (U V : finset α) : finset (α × α) :=
(U.product V).filter (λ e, r e.1 e.2)

lemma mem_pairs_finset (U V : finset α) (x : α × α) :
  x ∈ pairs_finset r U V ↔ x.1 ∈ U ∧ x.2 ∈ V ∧ r x.1 x.2 :=
by simp only [pairs_finset, and_assoc, mem_filter, finset.mem_product]

lemma mem_pairs_finset' (U V : finset α) (x y : α) :
  (x, y) ∈ pairs_finset r U V ↔ x ∈ U ∧ y ∈ V ∧ r x y :=
mem_pairs_finset _ _ _ _

@[simp] lemma pairs_finset_empty_left (V : finset α) :
  pairs_finset r ∅ V = ∅ :=
by rw [pairs_finset, finset.empty_product, filter_empty]

lemma pairs_finset_mono {A B A' B' : finset α} (hA : A' ⊆ A) (hB : B' ⊆ B) :
  pairs_finset r A' B' ⊆ pairs_finset r A B :=
begin
  intro x,
  rw [mem_pairs_finset, mem_pairs_finset],
  exact λ h, ⟨hA h.1, hB h.2.1, h.2.2⟩,
end

lemma card_pairs_finset_compl (U V : finset α) :
  (pairs_finset r U V).card + (pairs_finset (λ x y, ¬r x y) U V).card = U.card * V.card :=
begin
  classical,
  rw [←finset.card_product, pairs_finset, pairs_finset, ←finset.card_union_eq,
    finset.filter_union_filter_neg_eq],
  rw finset.disjoint_filter,
  exact λ x _, not_not.2,
end

section decidable_eq
variable [decidable_eq α]

lemma pairs_finset_disjoint_left {U U' : finset α} (hU : disjoint U U') (V : finset α) :
  disjoint (pairs_finset r U V) (pairs_finset r U' V) :=
begin
  rw [disjoint_iff_inter_eq_empty, ←subset_empty] at ⊢ hU,
  rintro x hx,
  rw [mem_inter, mem_pairs_finset, mem_pairs_finset] at hx,
  exact hU (mem_inter.2 ⟨hx.1.1, hx.2.1⟩),
end

lemma pairs_finset_disjoint_right (U : finset α) {V V' : finset α} (hV : disjoint V V') :
  disjoint (pairs_finset r U V) (pairs_finset r U V') :=
begin
  rw [disjoint_iff_inter_eq_empty, ←subset_empty] at ⊢ hV,
  rintro x hx,
  rw [mem_inter, mem_pairs_finset, mem_pairs_finset] at hx,
  exact hV (mem_inter.2 ⟨hx.1.2.1, hx.2.2.1⟩),
end

lemma pairs_finset_bUnion_left (A : finset (finset α)) (V : finset α) (f : finset α → finset α) :
  pairs_finset r (A.bUnion f) V = A.bUnion (λ a, pairs_finset r (f a) V) :=
by { ext x, simp only [mem_pairs_finset, mem_bUnion, exists_and_distrib_right] }

lemma pairs_finset_bUnion_right (U : finset α) (B : finset (finset α)) (f : finset α → finset α) :
  pairs_finset r U (B.bUnion f) = B.bUnion (λ b, pairs_finset r U (f b)) :=
begin
  ext x,
  simp only [mem_pairs_finset, mem_bUnion, exists_prop],
  simp only [←and_assoc, exists_and_distrib_right, @and.right_comm _ (x.fst ∈ U)],
  rw [and_comm (x.fst ∈ U), and.right_comm],
end

lemma pairs_finset_bUnion (A B : finset (finset α)) (f g : finset α → finset α) :
  pairs_finset r (A.bUnion f) (B.bUnion g) =
  (A.product B).bUnion (λ ab, pairs_finset r (f ab.1) (g ab.2)) :=
by simp_rw [product_bUnion, pairs_finset_bUnion_left, pairs_finset_bUnion_right]

end decidable_eq

/-- Number of edges between two finsets of vertices -/
def pairs_count (U V : finset α) : ℕ := (pairs_finset r U V).card

lemma pairs_count_le_mul (U V : finset α) : pairs_count r U V ≤ U.card * V.card :=
begin
  rw [pairs_count, pairs_finset, ←finset.card_product],
  exact finset.card_filter_le _ _,
end

/-- Edge density between two finsets of vertices -/
noncomputable def pairs_density (U V : finset α) : ℝ :=
pairs_count r U V / (U.card * V.card)

lemma pairs_density_nonneg (U V : finset α) : 0 ≤ pairs_density r U V :=
by { apply div_nonneg; exact_mod_cast nat.zero_le _ }

lemma pairs_density_le_one (U V : finset α) : pairs_density r U V ≤ 1 :=
begin
  refine div_le_one_of_le _ (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _)),
  norm_cast,
  exact pairs_count_le_mul r U V,
end

lemma pairs_density_compl {U V : finset α} (hU : U.nonempty) (hV : V.nonempty) :
  pairs_density r U V + pairs_density (λ x y, ¬r x y) U V = 1 :=
begin
  have h : ((U.card * V.card : ℕ) : ℝ) ≠ 0 := nat.cast_ne_zero.2 (mul_pos (finset.card_pos.2 hU)
    (finset.card_pos.2 hV)).ne.symm,
  rw [pairs_density, pairs_density, div_add_div_same, ←nat.cast_mul, div_eq_iff h, one_mul],
  exact_mod_cast card_pairs_finset_compl r U V,
end

@[simp] lemma pairs_density_empty_left (V : finset α) : pairs_density r ∅ V = 0 :=
by rw [pairs_density, finset.card_empty, nat.cast_zero, zero_mul, div_zero]

@[simp] lemma pairs_density_empty_right (U : finset α) : pairs_density r U ∅ = 0 :=
by rw [pairs_density, finset.card_empty, nat.cast_zero, mul_zero, div_zero]

section symmetric
variables {r} (hr : symmetric r)
include hr

lemma mem_pairs_finset_comm (U V : finset α) (x y : α) :
  (x, y) ∈ pairs_finset r U V ↔ (y, x) ∈ pairs_finset r V U :=
begin
  rw [mem_pairs_finset', mem_pairs_finset'],
  split; exact λ h, ⟨h.2.1, h.1, hr h.2.2⟩,
end

lemma pairs_count_comm (U V : finset α) : pairs_count r U V = pairs_count r V U :=
begin
  apply finset.card_congr (λ (i : α × α) hi, (i.2, i.1)) _ _ _,
  { rintro ⟨i, j⟩ h,
    rw mem_pairs_finset_comm hr,
    exact h },
  { rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ h₁ h₂ h,
    rcases h,
    refl },
  rintro ⟨i, j⟩ h,
  refine ⟨⟨j, i⟩, _, rfl⟩,
  rw mem_pairs_finset_comm hr,
  exact h,
end

lemma pairs_density_comm (U V : finset α) : pairs_density r U V = pairs_density r V U :=
by rw [pairs_density, mul_comm, pairs_count_comm hr, pairs_density]

end symmetric

end relation

/-! ## Specialization to `simple_graph` -/

namespace simple_graph
variables (G : simple_graph α) [decidable_rel G.adj]

open relation

def edge_count (U V : finset α) : ℝ := (pairs_finset G.adj U V).card

/- Remnants of what's now under `relation`. The only point for keeping it is to sometimes avoid
writing `G.adj` and `G.sym` sometimes. -/
/-- Edge density between two finsets of vertices -/
noncomputable def edge_density : finset α → finset α → ℝ := pairs_density G.adj

lemma edge_density_eq_edge_count_div_card (U V : finset α) :
  G.edge_density U V = G.edge_count U V/(U.card * V.card) :=
rfl

lemma edge_density_comm (U V : finset α) : G.edge_density U V = G.edge_density V U :=
pairs_density_comm G.symm U V

lemma edge_density_nonneg (U V : finset α) : 0 ≤ G.edge_density U V := pairs_density_nonneg _ U V

lemma edge_density_le_one (U V : finset α) : G.edge_density U V ≤ 1 := pairs_density_le_one _ U V

noncomputable def sym2_edge_density : sym2 (finset α) → ℝ :=
sym2.lift ⟨G.edge_density, G.edge_density_comm⟩

@[simp]
lemma sym2_edge_density_mk {U V : finset α} : G.sym2_edge_density ⟦(U, V)⟧ = G.edge_density U V :=
rfl

end simple_graph

/-! ## is_uniform for simple_graph -/

namespace simple_graph
variables (G : simple_graph α) (ε : ℝ) [decidable_rel G.adj]

/-- A pair of finsets of vertices is ε-uniform iff their edge density is close to the density of any
big enough pair of subsets. Intuitively, the edges between them are random-like. -/
def is_uniform (U V : finset α) : Prop :=
∀ U', U' ⊆ U → ∀ V', V' ⊆ V → (U.card : ℝ) * ε ≤ U'.card → (V.card : ℝ) * ε ≤ V'.card →
abs (edge_density G U' V' - edge_density G U V) < ε

/-- If the pair `(U, V)` is `ε`-uniform and `ε ≤ ε'`, then it is `ε'`-uniform. -/
lemma is_uniform_mono {ε ε' : ℝ} {U V : finset α} (h : ε ≤ ε') (hε : is_uniform G ε U V) :
  is_uniform G ε' U V :=
begin
  intros U' hU' V' hV' hU hV,
  refine (hε _ hU' _ hV' (le_trans _ hU) (le_trans _ hV)).trans_le h;
  exact mul_le_mul_of_nonneg_left h (nat.cast_nonneg _),
end

lemma is_uniform.symm {G : simple_graph α} [decidable_rel G.adj] {ε : ℝ} {U V : finset α}
  (h : G.is_uniform ε U V) :
  G.is_uniform ε V U :=
begin
  intros V' hV' U' hU' hV hU,
  rw [edge_density_comm _ V', edge_density_comm _ V],
  apply h _ hU' _ hV' hU hV,
end

lemma is_uniform_symmetric : symmetric (is_uniform G ε) := λ U V h, h.symm

lemma is_uniform_comm {U V : finset α} : is_uniform G ε U V ↔ is_uniform G ε V U :=
⟨λ h, h.symm, λ h, h.symm⟩

lemma is_uniform_singleton {ε : ℝ} {x y : α} (hε : 0 < ε) : G.is_uniform ε {x} {y} :=
begin
  rintro U' hU' V' hV' hU hV,
  rw [card_singleton, nat.cast_one, one_mul] at hU hV,
  obtain rfl | rfl := finset.subset_singleton_iff.1 hU',
  { rw [finset.card_empty] at hU,
    exact (hε.not_le hU).elim },
  obtain rfl | rfl := finset.subset_singleton_iff.1 hV',
  { rw [finset.card_empty] at hV,
    exact (hε.not_le hV).elim },
  rwa [sub_self, abs_zero],
end

def sym2_is_uniform (UV : sym2 (finset α)) : Prop := sym2.from_rel (G.is_uniform_symmetric ε) UV

@[simp]
lemma sym2_is_uniform_mk {ε : ℝ} {U V : finset α} :
  G.sym2_is_uniform ε ⟦(U, V)⟧ ↔ G.is_uniform ε U V :=
iff.rfl

end simple_graph

/-! ## finpartition -/

/-- A finite partition of `a : α` is a pairwise disjoint finite set of elements whose supremum is
`a`. -/
@[ext] structure finpartition {α : Type*} [distrib_lattice_bot α] (a : α) :=
(parts : finset α)
(disjoint : (parts : set α).pairwise_disjoint)
(sup_parts : parts.sup id = a)
(not_bot_mem : ⊥ ∉ parts)

namespace finpartition
section distrib_lattice_bot
variables (α) [distrib_lattice_bot α]

@[simps] protected def empty : finpartition (⊥ : α) :=
{ parts := ∅,
  disjoint := coe_empty.symm.subst set.pairwise_disjoint_empty,
  sup_parts := finset.sup_empty,
  not_bot_mem := not_mem_empty ⊥ }

variables {α} {a : α}

@[simps] def _root_.indiscrete_finpartition (ha : a ≠ ⊥) : finpartition a :=
{ parts := {a},
  disjoint := (coe_singleton a).symm.subst (set.pairwise_disjoint_singleton _),
  sup_parts := finset.sup_singleton,
  not_bot_mem := λ h, ha (mem_singleton.1 h).symm }

instance : inhabited (finpartition (⊥ : α)) :=
⟨finpartition.empty α ⟩

variables (P : finpartition a)

protected lemma le {b : α} (hb : b ∈ P.parts) : b ≤ a :=
(le_sup hb).trans P.sup_parts.le

lemma ne_bot_of_mem_parts {b : α} (hb : b ∈ P.parts) : b ≠ ⊥ :=
λ h, P.not_bot_mem $ h.subst hb

lemma eq_empty (P : finpartition (⊥ : α)) : P = finpartition.empty α :=
begin
  ext a,
  exact iff_of_false (λ h, P.ne_bot_of_mem_parts h $ le_bot_iff.1 $ P.le h) (not_mem_empty a),
end

instance : unique (finpartition (⊥ : α)) :=
{ uniq := eq_empty
  ..finpartition.inhabited }

/-- The size of a finpartition is its number of parts. -/
protected def size : ℕ := P.parts.card

lemma size_eq_card_parts : P.size = P.parts.card := rfl

variables {P}

lemma empty_parts_iff : P.parts = ∅ ↔ a = ⊥ :=
begin
  simp_rw ←P.sup_parts,
  refine ⟨λ h, _, λ h, eq_empty_iff_forall_not_mem.2 (λ b hb, P.not_bot_mem _)⟩,
  { rw h,
    exact finset.sup_empty },
  { rwa ←le_bot_iff.1 ((le_sup hb).trans h.le) }
end

/-- Given a finpartition `P` of `a` and finpartitions of each part of `P`, this yields the
finpartition of `a` obtained by juxtaposing all the subpartitions. -/
@[simps] def bind [decidable_eq α] (P : finpartition a) (Q : Π i ∈ P.parts, finpartition i) :
  finpartition a :=
{ parts := P.parts.attach.bUnion (λ i, (Q i.1 i.2).parts),
  disjoint := λ a ha b hb h, begin
    rw [finset.mem_coe, finset.mem_bUnion] at ha hb,
    obtain ⟨⟨A, hA⟩, -, ha⟩ := ha,
    obtain ⟨⟨B, hB⟩, -, hb⟩ := hb,
    obtain rfl | hAB := eq_or_ne A B,
    { exact (Q A hA).disjoint _ ha _ hb h },
    { exact (P.disjoint _ hA _ hB hAB).mono ((Q A hA).le ha) ((Q B hB).le hb) }
  end,
  sup_parts := begin
    simp_rw [sup_bUnion, ←P.sup_parts],
    rw [eq_comm, ←finset.sup_attach],
    exact sup_congr rfl (λ b hb, (Q b.1 b.2).sup_parts.symm),
  end,
  not_bot_mem := λ h, begin
    rw finset.mem_bUnion at h,
    obtain ⟨⟨A, hA⟩, -, h⟩ := h,
    exact (Q A hA).not_bot_mem h,
  end }

lemma mem_bind_parts [decidable_eq α] {P : finpartition a} {Q : Π i ∈ P.parts, finpartition i}
  {a : α} :
  a ∈ (P.bind Q).parts ↔ ∃ A hA, a ∈ (Q A hA).parts :=
begin
  rw [bind, mem_bUnion],
  split,
  { rintro ⟨⟨A, hA⟩, -, h⟩,
    exact ⟨A, hA, h⟩ },
  { rintro ⟨A, hA, h⟩,
    exact ⟨⟨A, hA⟩, mem_attach _ ⟨A, hA⟩, h⟩ }
end

end distrib_lattice_bot

section generalized_boolean_algebra
variables [generalized_boolean_algebra α] [decidable_eq α] {a : α} (P : finpartition a)

/-- Restricts a finpartition to avoid a given subset. -/
def avoid (b : α) : finpartition (a \ b) :=
{ parts := (P.parts.image (\ b)).erase ⊥,
  disjoint := (P.disjoint.image_finset $ λ a, sdiff_le).subset (erase_subset _ _),
  sup_parts :=
    begin
      rw [sup_erase_bot, sup_image, comp.left_id, finset.sup_sdiff_right],
      congr,
      exact P.sup_parts,
    end,
  not_bot_mem := not_mem_erase _ _ }

end generalized_boolean_algebra
end finpartition

/-! ### Finite partitions of finsets -/

namespace finpartition
variables [decidable_eq α] (s : finset α)

/-- The discrete equipartition of a fintype is the partition in singletons. -/
@[simps] def _root_.discrete_finpartition : finpartition s :=
{ parts := s.map ⟨singleton, singleton_injective⟩,
  disjoint :=
    begin
      rw finset.coe_map,
      exact finset.pairwise_disjoint_range_singleton.subset (set.image_subset_range _ _),
    end,
  sup_parts := by rw [sup_map, comp.left_id, embedding.coe_fn_mk, finset.sup_singleton'],
  not_bot_mem := by simp }

variables {s} (P : finpartition s)

lemma nonempty_of_mem_parts {a : finset α} (ha : a ∈ P.parts) : a.nonempty :=
nonempty_iff_ne_empty.2 $ P.ne_bot_of_mem_parts ha

lemma nonempty_parts_iff : P.parts.nonempty ↔ s.nonempty :=
by rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, not_iff_not, empty_parts_iff, bot_eq_empty]

lemma exists_mem {a : α} (ha : a ∈ s) : ∃ t ∈ P.parts, a ∈ t :=
begin
  simp_rw ←P.sup_parts at ha,
  exact mem_sup.1 ha,
end

lemma bUnion_parts_eq : P.parts.bUnion id = s := by rw [←sup_eq_bUnion, P.sup_parts]

lemma sum_card_parts : ∑ i in P.parts, i.card = s.card :=
begin
  rw ←card_bUnion P.disjoint,
  exact congr_arg finset.card P.bUnion_parts_eq,
end

lemma bind_size (Q : Π i ∈ P.parts, finpartition i) :
  (P.bind Q).size = ∑ A in P.parts.attach, (Q _ A.2).size :=
begin
  apply card_bUnion,
  rintro ⟨A, hA⟩ - ⟨B, hB⟩ - hAB c,
  rw [inf_eq_inter, mem_inter],
  rintro ⟨hcA, hcB⟩,
  apply hAB,
  rw subtype.mk_eq_mk,
  obtain ⟨x, hx⟩ := nonempty_of_mem_parts _ hcA,
  exact P.disjoint.elim_finset hA hB x (finpartition.le _ hcA hx) (finpartition.le _ hcB hx),
end

lemma parts_nonempty [nonempty α] [fintype α] (P : finpartition (univ : finset α)) :
  P.parts.nonempty :=
P.nonempty_parts_iff.2 univ_nonempty

end finpartition

/-! # pairs_count with finpartition -/

namespace relation
variables [decidable_eq α] {r : α → α → Prop} [decidable_rel r]

lemma pairs_count_finpartition_left {U : finset α} (P : finpartition U) (V : finset α) :
  pairs_count r U V = ∑ a in P.parts, pairs_count r a V :=
begin
  unfold pairs_count,
  simp_rw [←P.bUnion_parts_eq, pairs_finset_bUnion_left, id],
  rw card_bUnion,
  exact λ x hx y hy h, pairs_finset_disjoint_left r (P.disjoint x hx y hy h) _,
end

lemma pairs_count_finpartition_right (U : finset α) {V : finset α} (P : finpartition V) :
  pairs_count r U V = ∑ b in P.parts, pairs_count r U b :=
begin
  unfold pairs_count,
  simp_rw [←P.bUnion_parts_eq, pairs_finset_bUnion_right, id],
  rw card_bUnion,
  exact λ x hx y hy h, pairs_finset_disjoint_right r _ (P.disjoint x hx y hy h),
end

lemma pairs_count_finpartition {U V : finset α} (P : finpartition U) (Q : finpartition V) :
  pairs_count r U V = ∑ ab in P.parts.product Q.parts, pairs_count r ab.1 ab.2 :=
by simp_rw [pairs_count_finpartition_left P, pairs_count_finpartition_right _ Q, sum_product]

end relation


/-! ## is_equipartition -/

namespace finpartition
variables [decidable_eq α] {s : finset α} (P : finpartition s)

/-- An equipartition is a partition whose parts are all the same size, up to a difference of `1`. -/
def is_equipartition : Prop := (P.parts : set (finset α)).equitable_on card

lemma is_equipartition_iff_card_parts_eq_average : P.is_equipartition ↔
  ∀ a : finset α, a ∈ P.parts → a.card = s.card/P.size ∨ a.card = s.card/P.size + 1 :=
begin
  simp_rw [is_equipartition, finset.equitable_on_iff, ←card_bUnion P.disjoint, ←P.bUnion_parts_eq],
  refl,
end

end finpartition

lemma finpartition.is_equipartition_iff_card_parts_eq_average' [decidable_eq α] [fintype α]
  {P : finpartition (univ : finset α)} :
  P.is_equipartition ↔
    ∀ a : finset α, a ∈ P.parts → a.card = card α/P.size ∨ a.card = card α/P.size + 1 :=
by rw [P.is_equipartition_iff_card_parts_eq_average, card_univ]

lemma finpartition.is_equipartition.average_le_card_part [decidable_eq α] [fintype α]
  {P : finpartition (univ : finset α)} (hP : P.is_equipartition) {a : finset α} (ha : a ∈ P.parts) :
  card α/P.size ≤ a.card :=
(finpartition.is_equipartition_iff_card_parts_eq_average'.1 hP a ha).elim ge_of_eq (λ h,
  (nat.le_succ _).trans h.ge)

/-! ### Discrete and indiscrete finpartition -/

namespace discrete_finpartition
variables [decidable_eq α] (s : finset α) (G : simple_graph α)

lemma is_equipartition : (discrete_finpartition s).is_equipartition :=
set.equitable_on_iff_exists_eq_eq_add_one.2 ⟨1, by simp⟩

protected lemma size : (discrete_finpartition s).size = s.card := finset.card_map _

end discrete_finpartition
