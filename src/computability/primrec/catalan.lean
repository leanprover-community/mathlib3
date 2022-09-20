import data.list.basic
import data.tree
import data.list.prod_sigma
import data.finset.basic
import data.finset.prod

namespace unit_tree

@[simp] def height : unit_tree → ℕ
| nil := 0
| (node x y) := max (height x) (height y) + 1

@[simp] lemma height_eq_zero_iff {x : unit_tree} : x.height = 0 ↔ x = nil :=
by cases x; simp [height]

lemma height_le_nodes (x : unit_tree) : x.height ≤ x.nodes :=
begin
  induction x with l r ihl ihr, { simp, },
  simp only [height, nodes, add_le_add_iff_right, max_le_iff],
  exact ⟨le_add_right ihl, le_add_left ihr⟩,
end

/-- A list of trees with height less than or equal to `n` -/
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

def height_le_finset : ℕ → finset unit_tree
| 0 := {nil}
| (n + 1) := let ih := height_le_finset n in
  insert nil ((ih ×ˢ ih).map ⟨λ x, x.1.node x.2, λ ⟨x₁, x₂⟩ ⟨y₁, y₂⟩, by { simp, tauto, }⟩)

@[simp] lemma mem_height_le_finset {n : ℕ} {x : unit_tree} :
  x ∈ height_le_finset n ↔ x.height ≤ n :=
begin
  induction n with n ih generalizing x,
  { simp [height_le_finset], },
  cases x with l r, { simp [height_le_finset], },
  simp [height_le_finset, nat.succ_eq_add_one, ih],
end

def nodes_le_finset (n : ℕ) : finset unit_tree :=
(height_le_finset n).filter (λ x, x.nodes = n)

lemma mem_nodes_le_finset {n : ℕ} {x : unit_tree} :
  x ∈ nodes_le_finset n ↔ x.nodes = n :=
⟨by simp [nodes_le_finset], λ h, by simpa [nodes_le_finset, ← h] using x.height_le_nodes⟩

end unit_tree
