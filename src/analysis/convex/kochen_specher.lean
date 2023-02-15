import data.real.sqrt
import data.zmod.defs
import algebra.big_operators.fin
import data.fin.vec_notation
import algebra.big_operators.basic
import tactic.polyrith
import tactic.fin_cases
import tactic.derive_fintype
-- import tactic.LibrarySearch

open_locale big_operators

-- blue, 3
def A₀ : zmod 3 → ℝ × ℝ := ![(2, 0), (0, 0), (0, 0)]
def A (i : zmod 3) : zmod 3 → ℝ × ℝ := λ j, A₀ (i + j)

-- green, 2 * 3
def B₀ (b : units ℤ) : zmod 3 → ℝ × ℝ := ![(2, 0), (2 * b, 0), (0, 0)]
def B (b : units ℤ) (i : zmod 3) : zmod 3 → ℝ × ℝ := λ j, B₀ b (i + j)

-- pink, 2 * 6
def D₀ (b : units ℤ) : zmod 3 → ℝ × ℝ := ![(2, 0), (0, b), (0, 0)]
def D (b : units ℤ) (p : equiv.perm (zmod 3)) : zmod 3 → ℝ × ℝ := λ i, D₀ b (p i)

-- first yellow, 2 * 3
def F₀ (b : units ℤ) : zmod 3 → ℝ × ℝ := ![(2, 0), (0, b), (0, b)]
def F (b : units ℤ) (i : zmod 3) : zmod 3 → ℝ × ℝ := λ j, F₀ b (i + j)

-- second yellow, 6
def G₀ : zmod 3 → ℝ × ℝ := ![(2, 0), (0, 1), (0, -1)]
def G (p : equiv.perm (zmod 3)) : zmod 3 → ℝ × ℝ := λ i, G₀ (p i)

-- @[derive fintype]
inductive point_index : Type
| a : zmod 3 → point_index
| b : units ℤ → zmod 3 → point_index
| d : units ℤ → equiv.perm (zmod 3) → point_index
| f : units ℤ → zmod 3 → point_index
| g : equiv.perm (zmod 3) → point_index

def point : point_index → zmod 3 → ℝ × ℝ
| (point_index.a i) := A i
| (point_index.b b i) := B b i
| (point_index.d b p) := D b p
| (point_index.f b i) := F b i
| (point_index.g p) := G p

def mkSurd (s : ℝ) : ℝ × ℝ → ℝ := λ p, p.1 + p.2 * s

def Perp (x y : zmod 3 → ℝ) : Prop := ∑ i, x i * y i = 0

@[simp] lemma Perp_iff (x y : zmod 3 → ℝ) : Perp x y ↔ x 0 * y 0 + (x 1 * y 1 + x 2 * y 2) = 0 :=
begin
  change ∑ i : fin 3, x i * y i = 0 ↔ _,
  simp [fin.sum_univ_succ]
end

@[simp] lemma matrix.comp_vec_cons {α β : Type*} {n : ℕ} (h : α) (v : fin n → α) (f : α → β) :
  f ∘ matrix.vec_cons h v = matrix.vec_cons (f h) (f ∘ v) :=
sorry

@[simp] lemma matrix.comp_vec_empty {α β : Type*} (f : α → β) :
  f ∘ matrix.vec_empty = matrix.vec_empty :=
sorry

example
  {spin : (zmod 3 → ℝ) → ℕ}
  (H : ∀ X : zmod 3 → zmod 3 → ℝ,
    (∀ i, X i ≠ 0) →
    (∀ i, Perp (X i) (X (i + 1))) →
    (∃ i, spin (X i) = 0 ∧ spin (X (i + 1)) = 1 ∧ spin (X (i + 2)) = 1)) :
  false :=
begin
  -- let x : ℝ := real.sqrt 2,
  let p : zmod 3 → point_index := ![point_index.a 0, point_index.b 1 0, point_index.g 1],
  have : ∀ i, Perp (mkSurd (real.sqrt 2) ∘ (point (p i))) (mkSurd (real.sqrt 2) ∘ point (p (i + 1))),
  { intro i; fin_cases i,
    simp [A, B, G, A₀, B₀, G₀, p, point, mkSurd, Perp_iff],


  },
  -- have : ∀ i : zmod 3, Perp (p i) ()
  obtain ⟨i, hi₀, hi₁, hi₂⟩ := H (function.comp (function.comp (mkSurd (real.sqrt 2))) (point ∘ p)) _ _,
  fin_cases i,
  simp [A, B, G, A₀, B₀, G₀, p, point, mkSurd] at *,
  -- rw A at hi₀,

end
  -- simp_rw [Function.comp_apply] at hi₁
  -- have : spin (mkSurd 3 ∘ ![(1,0), (1,0), (1,0)]) = 0
  -- convert hi₁
  -- apply congr_arg
  -- rw [foo']

  -- have := hi₁.symm.trans <| congr_arg spin <| congr_arg (mkSurd 3) (@foo' 2 _ _ _)
  -- -- rw [foo] at hi
