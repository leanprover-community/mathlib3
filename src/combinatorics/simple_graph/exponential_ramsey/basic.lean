import combinatorics.simple_graph.ramsey
import combinatorics.simple_graph.graph_probability
import combinatorics.simple_graph.density
import data.seq.seq

open finset real
namespace simple_graph
open_locale big_operators

variables {V K : Type*}

def col_density [decidable_eq V] [decidable_eq K] (χ : top_edge_labelling V K) (k : K)
  (X Y : finset V) : ℝ :=
edge_density (χ.label_graph k) X Y

@[reducible] def red_density [decidable_eq V] (χ : top_edge_labelling V (fin 2)) (X Y : finset V) :
  ℝ := col_density χ 0 X Y
@[reducible] def blue_density [decidable_eq V] (χ : top_edge_labelling V (fin 2)) (X Y : finset V) :
  ℝ := col_density χ 1 X Y

def col_neighbor_finset [fintype V] [decidable_eq V] [decidable_eq K] (χ : top_edge_labelling V K)
  (k : K) (x : V) : finset V :=
neighbor_finset (χ.label_graph k) x

@[reducible] def red_neighbors [fintype V] [decidable_eq V] (χ : top_edge_labelling V (fin 2))
  (x : V) : finset V := col_neighbor_finset χ 0 x
@[reducible] def blue_neighbors [fintype V] [decidable_eq V] (χ : top_edge_labelling V (fin 2))
  (x : V) : finset V := col_neighbor_finset χ 1 x

variables [fintype V] [decidable_eq V]

lemma mem_col_neighbor_finset [decidable_eq K] {χ : top_edge_labelling V K} {x y : V} {k : K} :
  y ∈ col_neighbor_finset χ k x ↔ ∃ (H : x ≠ y), χ.get x y = k :=
by rw [col_neighbor_finset, mem_neighbor_finset, top_edge_labelling.label_graph_adj]

lemma mem_col_neighbor_finset' [decidable_eq K] {χ : top_edge_labelling V K} {x y : V} {k : K} :
  y ∈ col_neighbor_finset χ k x ↔ ∃ (H : y ≠ x), χ.get y x = k :=
by rw [col_neighbor_finset, mem_neighbor_finset, adj_comm, top_edge_labelling.label_graph_adj]

-- (3)
noncomputable def pair_weight (χ : top_edge_labelling V (fin 2)) (X Y : finset V) (x y : V) : ℝ :=
Y.card⁻¹ *
  ((red_neighbors χ x ∩ red_neighbors χ y ∩ Y).card -
    red_density χ X Y * (red_neighbors χ x ∩ Y).card)

-- (4)
noncomputable def weight (χ : top_edge_labelling V (fin 2)) (X Y : finset V) (x : V) : ℝ :=
∑ y in X.erase x, pair_weight χ X Y x y

-- (5)
noncomputable def q_function (k : ℕ) (p₀ : ℝ) (h : ℕ) : ℝ :=
p₀ + ((1 + k^(- 1/4 : ℝ)) ^ h - 1) / k

lemma q_function_zero {k : ℕ} {p₀ : ℝ} : q_function k p₀ 0 = p₀ :=
by rw [q_function, pow_zero, sub_self, zero_div, add_zero]

-- The bound on h here is about k / ε, which is not good enough in general so I'm not gonna bother
-- exposing it, later I show h ≤ 2 log k / ε works for suff large k, which is what's actually needed
lemma q_function_above_one {k : ℕ} {p₀ : ℝ} (hk : k ≠ 0) (hp₀ : 0 ≤ p₀) :
  ∃ h, 1 ≤ h ∧ 1 ≤ q_function k p₀ h :=
begin
  simp only [q_function],
  set ε : ℝ := k^(- 1/4 : ℝ),
  have hε : 0 < ε := real.rpow_pos_of_pos (by positivity) _,
  have hε' : -2 ≤ ε := hε.le.trans' (by norm_num),
  let h := ⌈(k : ℝ) / ε⌉₊,
  refine ⟨h, _, le_add_of_nonneg_of_le hp₀ _⟩,
  { rw nat.one_le_ceil_iff,
    positivity },
  rw one_le_div,
  swap,
  { positivity },
  refine (sub_le_sub_right (one_add_mul_le_pow hε' h) _).trans' _,
  rw [add_sub_cancel', ←div_le_iff hε],
  exact nat.le_ceil _,
end

-- (5)
noncomputable def height (k : ℕ) (p₀ p : ℝ) : ℕ :=
if h : k ≠ 0 ∧ 0 ≤ p₀ then nat.find (q_function_above_one h.1 h.2) else 1

lemma one_le_height {k : ℕ} {p₀ p : ℝ} : 1 ≤ height k p₀ p :=
begin
  rw height,
  split_ifs with h,
  { exact (nat.find_spec (q_function_above_one h.1 h.2)).1 },
  exact le_rfl
end

-- (6)
noncomputable def alpha_function (k : ℕ) (h : ℕ) : ℝ :=
k^(- 1/4 : ℝ) * (1 + k^(- 1/4 : ℝ)) ^ (h - 1) / k

-- (6)
lemma alpha_function_eq_q_diff {k : ℕ} {p₀ : ℝ} {h : ℕ} :
  alpha_function k (h + 1) = q_function k p₀ (h + 1) - q_function k p₀ h :=
begin
  rw [alpha_function, q_function, q_function, add_sub_add_left_eq_sub, div_sub_div_same,
    sub_sub_sub_cancel_right, pow_succ, ←sub_one_mul, add_sub_cancel', nat.add_sub_cancel]
end

section

variables {χ : top_edge_labelling V K}

namespace top_edge_labelling

def monochromatic_between (χ : top_edge_labelling V K)
  (X Y : finset V) (k : K) : Prop :=
∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ Y → x ≠ y → χ.get x y = k

@[simp] lemma monochromatic_between_empty_left {Y : finset V} {k : K} :
  χ.monochromatic_between ∅ Y k :=
by simp [monochromatic_between]

@[simp] lemma monochromatic_between_empty_right {X : finset V} {k : K} :
  χ.monochromatic_between X ∅ k :=
by simp [monochromatic_between]

lemma monochromatic_between_singleton_left {x : V} {Y : finset V} {k : K} :
  χ.monochromatic_between {x} Y k ↔ ∀ ⦃y⦄, y ∈ Y → x ≠ y → χ.get x y = k :=
by simp [monochromatic_between]

lemma monochromatic_between_singleton_right {y : V} {X : finset V} {k : K} :
  χ.monochromatic_between X {y} k ↔ ∀ ⦃x⦄, x ∈ X → x ≠ y → χ.get x y = k :=
by simp [monochromatic_between]

lemma monochromatic_between_union_left {X Y Z : finset V} {k : K} :
  χ.monochromatic_between (X ∪ Y) Z k ↔
    χ.monochromatic_between X Z k ∧ χ.monochromatic_between Y Z k :=
by simp only [monochromatic_between, mem_union, or_imp_distrib, forall_and_distrib]

lemma monochromatic_between_union_right {X Y Z : finset V} {k : K} :
  χ.monochromatic_between X (Y ∪ Z) k ↔
    χ.monochromatic_between X Y k ∧ χ.monochromatic_between X Z k :=
by simp only [monochromatic_between, mem_union, or_imp_distrib, forall_and_distrib]

lemma monochromatic_between_self {X : finset V} {k : K} :
  χ.monochromatic_between X X k ↔ χ.monochromatic_of X k :=
by simp only [monochromatic_between, monochromatic_of, mem_coe]

lemma _root_.disjoint.monochromatic_between {X Y : finset V} {k : K} (h : disjoint X Y) :
  χ.monochromatic_between X Y k ↔
    ∀ ⦃x⦄, x ∈ X → ∀ ⦃y⦄, y ∈ Y → χ.get x y (h.forall_ne_finset ‹_› ‹_›) = k :=
forall₄_congr $ λ x hx y hy, by simp [h.forall_ne_finset hx hy]

lemma monochromatic_between.subset_left {X Y Z : finset V} {k : K}
  (hYZ : χ.monochromatic_between Y Z k) (hXY : X ⊆ Y) :
  χ.monochromatic_between X Z k :=
λ x hx y hy h, hYZ (hXY hx) hy _

lemma monochromatic_between.subset_right {X Y Z : finset V} {k : K}
  (hXZ : χ.monochromatic_between X Z k) (hXY : Y ⊆ Z) :
  χ.monochromatic_between X Y k :=
λ x hx y hy h, hXZ hx (hXY hy) _

lemma monochromatic_between.symm {X Y : finset V} {k : K}
  (hXY : χ.monochromatic_between X Y k) :
  χ.monochromatic_between Y X k :=
λ y hy x hx h, by { rw get_swap _ _ h.symm, exact hXY hx hy _ }

lemma monochromatic_between.comm {X Y : finset V} {k : K} :
  χ.monochromatic_between Y X k ↔ χ.monochromatic_between X Y k :=
⟨monochromatic_between.symm, monochromatic_between.symm⟩
-- λ y hy x hx h, by { rw get_swap _ _ h.symm, exact hXY hx hy _ }

end top_edge_labelling

end

structure book_config (χ : top_edge_labelling V (fin 2)) :=
  (X Y A B : finset V)
  (hXY : disjoint X Y)
  (hXA : disjoint X A)
  (hXB : disjoint X B)
  (hYA : disjoint Y A)
  (hYB : disjoint Y B)
  (hAB : disjoint A B)
  (red_A : χ.monochromatic_of A 0)
  (red_XYA : χ.monochromatic_between (X ∪ Y) A 0)
  (blue_B : χ.monochromatic_of B 1)
  (blue_XB : χ.monochromatic_between X B 1)

open book_config

variable {χ : top_edge_labelling V (fin 2)}

def book_config.p (C : book_config χ) : ℝ := red_density χ C.X C.Y

def start (X : finset V) : book_config χ :=
begin
  refine ⟨X, Xᶜ, ∅, ∅, disjoint_compl_right, _, _, _, _, _, _, _, _, _⟩,
  all_goals { simp }
end

def red_step (C : book_config χ) (x : V) (hx : x ∈ C.X) : book_config χ :=
{ X := red_neighbors χ x ∩ C.X,
  Y := red_neighbors χ x ∩ C.Y,
  A := insert x C.A,
  B := C.B,
  hXY := disjoint_of_subset_left (inter_subset_right _ _)
          (disjoint_of_subset_right (inter_subset_right _ _) C.hXY),
  hXA :=
  begin
    rw [disjoint_insert_right, mem_inter, not_and_distrib],
    refine ⟨or.inl (not_mem_neighbor_finset_self _ _), _⟩,
    exact disjoint_of_subset_left (inter_subset_right _ _) C.hXA,
  end,
  hXB := disjoint_of_subset_left (inter_subset_right _ _) C.hXB,
  hYA :=
  begin
    rw [disjoint_insert_right, mem_inter, not_and_distrib],
    refine ⟨or.inl (not_mem_neighbor_finset_self _ _), _⟩,
    exact disjoint_of_subset_left (inter_subset_right _ _) C.hYA,
  end,
  hYB := disjoint_of_subset_left (inter_subset_right _ _) C.hYB,
  hAB :=
  begin
    simp only [disjoint_insert_left, C.hAB, and_true],
    exact finset.disjoint_left.1 C.hXB hx,
  end,
  red_A :=
  begin
    have : x ∉ (C.A : set V) := finset.disjoint_left.1 C.hXA hx,
    rw [coe_insert, top_edge_labelling.monochromatic_of_insert this, and_iff_right C.red_A],
    intros a ha,
    exact C.red_XYA (mem_union_left _ hx) ha _,
  end,
  red_XYA :=
  begin
    rw [←inter_distrib_left, insert_eq, top_edge_labelling.monochromatic_between_union_right,
      top_edge_labelling.monochromatic_between_singleton_right],
    split,
    { simp only [mem_inter, and_imp, red_neighbors, mem_col_neighbor_finset'],
      -- intros y hy,

    },
  end,
  blues := sorry,
  -- red_XA :=
  -- begin
  --   rw [insert_eq, top_edge_labelling.monochromatic_between_union_right],
  --   -- simp only [mem_inter, mem_insert],
  --   -- rintro x' a ⟨hx', hx''⟩ (rfl | ha),
  --   -- { simp only [red_neighbors, col_neighbor_finset, mem_neighbor_finset,
  --   --     top_edge_labelling.label_graph_adj] at hx',
  --   --   obtain ⟨_, hx'⟩ := hx',
  --   --   rw top_edge_labelling.get_swap,
  --   --   exact hx' },
  --   -- exact C.red_XA _ _ hx'' ha,
  -- end,
  -- red_YA :=
  -- begin
  --   simp only [mem_inter, mem_insert],
  --   rintro y' a ⟨hy', hy''⟩ (rfl | ha),
  --   { simp only [red_neighbors, col_neighbor_finset, mem_neighbor_finset,
  --       top_edge_labelling.label_graph_adj] at hy',
  --     obtain ⟨_, hy'⟩ := hy',
  --     rw top_edge_labelling.get_swap,
  --     exact hy' },
  --   exact C.red_YA _ _ hy'' ha,
  -- end,
  -- blue_B := C.blue_B,
  -- blue_XB :=
  -- begin
  --   simp only [mem_inter],
  --   intros x' b hx' hb,
  --   exact C.blue_XB x' b hx'.2 hb,
  -- end
}

#exit

def big_blue_step (C : book_config χ) (S T : finset V) (hS : S ⊆ C.X) (hT : T ⊆ C.X)
  (hSS : χ.monochromatic_of S 1) (hST : disjoint S T)
  (hST' : ∀ s t (hs : s ∈ S) (ht : t ∈ T), χ.get s t (hST.forall_ne_finset hs ht) = 1) :
  book_config χ :=
{ X := T,
  Y := C.Y,
  A := C.A,
  B := C.B ∪ S,
  hXY := disjoint_of_subset_left hT C.hXY,
  hXA := disjoint_of_subset_left hT C.hXA,
  hXB := disjoint_union_right.2 ⟨disjoint_of_subset_left hT C.hXB, hST.symm⟩,
  hYA := C.hYA,
  hYB := disjoint_union_right.2 ⟨C.hYB, disjoint_of_subset_right hS C.hXY.symm⟩,
  hAB := disjoint_union_right.2 ⟨C.hAB, disjoint_of_subset_right hS C.hXA.symm⟩,
  red_A := C.red_A,
  red_XA := sorry,
  red_YA := sorry,

}

end simple_graph
