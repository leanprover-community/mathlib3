import tactic
import data.sigma.order
.

variables {α : Type*} (f : ℕ → list α) (hf : ∀ n, f n ≠ [])

def indices : Type := Σ n : ℕ, fin (f n).length

local attribute [instance]
def indices.linear_order : linear_order (indices f) :=
sigma.lex.linear_order

local attribute [instance]
def indices.le_dec : decidable_rel ((≤) : indices f → indices f → Prop) :=
sigma.lex.decidable _ _

open list

def embed : ℕ → indices f
| 0 := ⟨0, 0, length_pos_of_ne_nil (hf _)⟩
| (k+1) :=
  let ⟨row, col, col_lt⟩ := embed k in
  if h : col+1 < (f row).length then ⟨row, col+1, h⟩
  else ⟨row+1, 0, length_pos_of_ne_nil (hf _)⟩

-- ouch
lemma embed_row_le_succ (n : ℕ) : (embed f hf (n + 1)).1 ≤ (embed f hf n).1 + 1 :=
begin
  induction n with n ih,
  { dsimp [embed],
    split_ifs; simp [embed] },
  { dsimp [embed],
    rcases embed f hf n with ⟨row, col, col_lt⟩,
    dsimp [embed],
    intro h,
    split_ifs; dsimp [embed]; split_ifs; simp [embed] }
end

lemma embed_surj (i : indices f) : ∃ k, i = embed f hf k :=
begin
  rcases i with ⟨row, col, col_lt⟩,
  induction row with row ih_row generalizing col,
  { induction col with col ih_col,
    { use 0, refl },
    { cases ih_col ((nat.lt_succ_self _).trans col_lt) with w hw,
      use w+1,
      dsimp [embed],
      rw ← hw,
      simp [embed, col_lt] } },
  { cases ih_row _ (buffer.lt_aux_2 (length_pos_of_ne_nil (hf _))) with prev h_prev,
    induction col with col ih_col,
    { use prev+1,
      dsimp [embed],
      rw ← h_prev,
      simp [embed, nat.sub_add_cancel (length_pos_of_ne_nil (hf row))], },
    { cases ih_col ((nat.lt_succ_self _).trans col_lt) with w hw,
      use w+1,
      dsimp [embed],
      rw ← hw,
      simp [embed, col_lt], } }
end

lemma embed_succ_lt (k : ℕ) : embed f hf k < embed f hf (k+1) :=
begin
  induction k with k ih,
  { dsimp [embed],
    split_ifs; dec_trivial },
  { rcases hek : embed f hf k with ⟨row, col, col_lt⟩,
    simp only [embed, hek],
    split_ifs;
    { dsimp [embed],
      split_ifs,
      { apply sigma.lex.right, simp, },
      { apply sigma.lex.left, simp } } }
end

lemma embed_mono {m n : ℕ} (hmn : m < n) : embed f hf m < embed f hf n :=
strict_mono_nat_of_lt_succ (embed_succ_lt _ _) hmn

def elt_of_index : indices f → α
| ⟨row, col, col_lt⟩ := (f row).nth_le _ col_lt

def flatten {α : Type*} (f : ℕ → list α) (hf : ∀ n, f n ≠ []) : ℕ → α :=
λ n, elt_of_index f (embed f hf n)

lemma flatten_surj {a : α} {i : ℕ} (hai : a ∈ f i) : ∃ k, a = flatten f hf k :=
begin
  rcases mem_iff_nth_le.mp hai with ⟨col, col_lt, hcol⟩,
  cases embed_surj f hf ⟨i, col, col_lt⟩ with w hw,
  use w,
  simp only [flatten, ← hw, elt_of_index, hcol]
end

variables {β : Type*} [linear_order β] {v : α → β}
  (hv1 : ∀ n, ∀ i j ∈ f n, v i = v j)
  (hv2 : ∀ n, ∀ i ∈ f n, ∀ j ∈ f (n+1), v i < v j)
include hv1 hv2


lemma flatten_le (n : ℕ) : v (flatten f hf n) ≤ v (flatten f hf (n+1)) :=
begin
  dsimp [flatten],
  have hlt : embed f hf n < embed f hf (n+1) := embed_succ_lt f hf _,
  have hrowle := embed_row_le_succ f hf n,
  rcases heq1 : embed f hf n with ⟨row1, col1, col_lt1⟩,
  rcases heq2 : embed f hf (n+1) with ⟨row2, col2, col_lt2⟩,
  dsimp [elt_of_index],
  rw [heq1, heq2] at hlt hrowle,
  dsimp at hrowle,
  by_cases hrow : row1 = row2,
  { cases hrow,
    apply le_of_eq,
    apply hv1; apply nth_le_mem },
  { apply le_of_lt,
    apply hv2 _ _ (nth_le_mem _ _ _),
    convert nth_le_mem _ _ _,
    have hrlt : row1 < row2 := by simpa [hrow] using sigma.lex_iff.mp hlt,
    linarith }
end
