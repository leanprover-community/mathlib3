import combinatorics.simple_graph.ramsey
import combinatorics.simple_graph.graph_probability
import combinatorics.simple_graph.density
import data.seq.seq

namespace simple_graph
open_locale big_operators

variables {V : Type*} (χ : top_edge_labelling V (fin 2))

def col_density [decidable_eq V] (k : fin 2) (X Y : finset V) : ℝ :=
edge_density (χ.label_graph k) X Y

abbreviation red_density [decidable_eq V] (X Y : finset V) : ℝ := col_density χ 0 X Y
abbreviation blue_density [decidable_eq V] (X Y : finset V) : ℝ := col_density χ 1 X Y

def col_neighbor_finset [fintype V] [decidable_eq V] (k : fin 2) (x : V) : finset V :=
neighbor_finset (χ.label_graph k) x

abbreviation red_neighbors [fintype V] [decidable_eq V] (x : V) : finset V :=
col_neighbor_finset χ 0 x
abbreviation blue_neighbors [fintype V] [decidable_eq V] (x : V) : finset V :=
col_neighbor_finset χ 1 x

variables [fintype V] [decidable_eq V]

-- (3)
noncomputable def pair_weight (X Y : finset V) (x y : V) : ℝ :=
Y.card⁻¹ *
  ((red_neighbors χ x ∩ red_neighbors χ y ∩ Y).card -
    red_density χ X Y * (red_neighbors χ x ∩ Y).card)

-- (4)
noncomputable def weight (X Y : finset V) (x : V) : ℝ :=
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


structure configuration (χ : top_edge_labelling V (fin 2)) :=
(X Y A B : finset V)
(hXY : disjoint X Y)
(hXA : disjoint X A)
(hXB : disjoint X B)
(hYA : disjoint Y A)
(hYB : disjoint Y B)
(hAB : disjoint A B)
(red_A : χ.monochromatic_of A 0)
(red_XA : ∀ x a (hx : x ∈ X) (ha : a ∈ A), χ.get x a (hXA.forall_ne_finset hx ha) = 0)
(red_YA : ∀ y a (hy : y ∈ Y) (ha : a ∈ A), χ.get y a (hYA.forall_ne_finset hy ha) = 0)
(blue_B : χ.monochromatic_of B 1)
(blue_XB : ∀ x b (hx : x ∈ X) (hb : b ∈ B), χ.get x b (hXB.forall_ne_finset hx hb) = 1)

open configuration

def configuration.p (C : configuration χ) : ℝ := red_density χ C.X C.Y

def start (X : finset V) : configuration χ :=
begin
  refine ⟨X, Xᶜ, ∅, ∅, disjoint_compl_right, _, _, _, _, _, _, _, _, _, _⟩,
  all_goals { simp }
end

end simple_graph
