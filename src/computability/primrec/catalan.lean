import data.list.basic
import data.tree
import data.list.prod_sigma
import data.finset.basic
import data.finset.prod
import algebra.big_operators
import combinatorics.catalan

namespace unit_tree

@[simp] lemma height_eq_zero_iff {x : unit_tree} : x.height = 0 ↔ x = nil :=
by cases x; simp [height]

lemma height_le_nodes (x : unit_tree) : x.height ≤ x.nodes :=
begin
  induction x with l r ihl ihr, { simp, },
  simp only [height, nodes, add_le_add_iff_right, max_le_iff],
  exact ⟨le_add_right ihl, le_add_left ihr⟩,
end

/-- A list of trees with height less than or equal to `n`.
  This is the same as `height_le_finset`, but usable with
  `primrec` so that we don't have to worry about a `tencodable`
  instance for `finset` -/
def height_le_list : ℕ → list unit_tree
| 0 := [nil]
| (n + 1) := let ih := height_le_list n in
  nil :: ((ih ×ˢ ih).map $ λ x, x.1.node x.2)

@[simp] lemma mem_height_le_list {n : ℕ} {x : unit_tree} :
  x ∈ height_le_list n ↔ x.height ≤ n :=
begin
  induction n with n ih generalizing x,
  { simp [height_le_list], },
  cases x with l r, { simp [height_le_list], },
  simp [height_le_list, nat.succ_eq_add_one, ih],
end

@[simp] def pairwise_node (a : finset unit_tree) (b : finset unit_tree) : finset unit_tree :=
  (a ×ˢ b).map ⟨λ x, x.1.node x.2, λ ⟨x₁, x₂⟩ ⟨y₁, y₂⟩, by { simp, tauto, }⟩

def height_le_finset : ℕ → finset unit_tree
| 0 := {nil}
| (n + 1) := let ih := height_le_finset n in
  insert nil (pairwise_node ih ih)

@[simp] lemma mem_height_le_finset {n : ℕ} {x : unit_tree} :
  x ∈ height_le_finset n ↔ x.height ≤ n :=
begin
  induction n with n ih generalizing x,
  { simp [height_le_finset], },
  cases x with l r, { simp [height_le_finset], },
  simp [height_le_finset, nat.succ_eq_add_one, ih],
end

def nodes_eq_finset (n : ℕ) : finset unit_tree :=
(height_le_finset n).filter (λ x, x.nodes = n)

@[simp] lemma mem_nodes_le_finset {n : ℕ} {x : unit_tree} :
  x ∈ nodes_eq_finset n ↔ x.nodes = n :=
⟨by simp [nodes_eq_finset], λ h, by simpa [nodes_eq_finset, ← h] using x.height_le_nodes⟩

lemma nodes_eq_succ (n : ℕ) :
  nodes_eq_finset (n + 1) = (finset.nat.antidiagonal n).bUnion
    (λ ij, pairwise_node (nodes_eq_finset ij.1) (nodes_eq_finset ij.2)) :=
by { ext x, cases x with l r; simp [n.succ_ne_zero.symm], }

open_locale big_operators
open finset

lemma catalan_succ' (n : ℕ) :
  catalan (n + 1) = ∑ m in nat.antidiagonal n, catalan m.1 * catalan m.2 :=
begin
  rw catalan_succ, symmetry,
  apply sum_bij (λ (a : ℕ × ℕ) ha, fin.mk a.1 (nat.lt_succ_iff.mpr $ nat.antidiagonal.fst_le ha)),
  { simp, },
  { rintro ⟨i, j⟩,
    simp only [fin.coe_mk, mul_eq_mul_left_iff, nat.mem_antidiagonal],
    rintro rfl, rw add_comm i j,
    simp, },
  { intros a₁ a₂ ha₁ ha₂ H, rw nat.antidiagonal_congr ha₁ ha₂, simpa using H, },
  rintros ⟨b, b_lt⟩ _,
  refine ⟨⟨b, n-b⟩, _, _⟩,
  { rw nat.lt_succ_iff at b_lt, rw nat.mem_antidiagonal, zify, ring, },
  { simp, },
end

lemma nodes_eq_card_catalan (n : ℕ) :
  (nodes_eq_finset n).card = catalan n :=
begin
  induction n using nat.case_strong_induction_on with n ih,
  { simp, refl, },
  rw [nodes_eq_succ, finset.card_bUnion, catalan_succ'],
  { apply sum_congr rfl, rintros ⟨i, j⟩ H,
    simp [ih i (nat.antidiagonal.fst_le H), ih j (nat.antidiagonal.snd_le H)], },
  rintros ⟨x₁, x₂⟩ hx ⟨y₁, y₂⟩ hy hne a ha,
  refine hne _,
  rsuffices ⟨⟨l, r, ⟨rfl, rfl⟩, rfl⟩, ⟨l', r', ⟨rfl, rfl⟩, ⟨_⟩⟩⟩ :
    (∃ (l r : unit_tree), (l.nodes = x₁ ∧ r.nodes = x₂) ∧ l.node r = a) ∧
    (∃ (l r : unit_tree), (l.nodes = y₁ ∧ r.nodes = y₂) ∧ l.node r = a),
  { refl, },
  simpa using ha,
end

end unit_tree
