import data.matrix.notation
import linear_algebra.determinant
import group_theory.perm.fin
import tactic.norm_swap

variables {α β : Type} [semiring α] [ring β]

namespace matrix

open_locale matrix

example {a a' b b' c c' d d' : α} :
  ![![a, b], ![c, d]] + ![![a', b'], ![c', d']] = ![![a + a', b + b'], ![c + c', d + d']] :=
by simp

example {a a' b b' c c' d d' : β} :
  ![![a, b], ![c, d]] - ![![a', b'], ![c', d']] = ![![a - a', b - b'], ![c - c', d - d']] :=
by simp

example {a a' b b' c c' d d' : α} :
  ![![a, b], ![c, d]] ⬝ ![![a', b'], ![c', d']] =
    ![![a * a' + b * c', a * b' + b * d'], ![c * a' + d * c', c * b' + d * d']] :=
by simp

example {a b c d x y : α} :
  mul_vec ![![a, b], ![c, d]] ![x, y] = ![a * x + b * y, c * x + d * y] :=
by simp

example {a b c d : α} : minor ![![a, b], ![c, d]] ![1, 0] ![0] = ![![c], ![a]] :=
by { ext, simp }

example {a b c : α} : ![a, b, c] 0 = a := by simp
example {a b c : α} : ![a, b, c] 1 = b := by simp
example {a b c : α} : ![a, b, c] 2 = c := by simp

example {a b c d : α} : ![a, b, c, d] 0 = a := by simp
example {a b c d : α} : ![a, b, c, d] 1 = b := by simp
example {a b c d : α} : ![a, b, c, d] 2 = c := by simp
example {a b c d : α} : ![a, b, c, d] 3 = d := by simp
example {a b c d : α} : ![a, b, c, d] 42 = c := by simp

example {a b c d e : α} : ![a, b, c, d, e] 0 = a := by simp
example {a b c d e : α} : ![a, b, c, d, e] 1 = b := by simp
example {a b c d e : α} : ![a, b, c, d, e] 2 = c := by simp
example {a b c d e : α} : ![a, b, c, d, e] 3 = d := by simp
example {a b c d e : α} : ![a, b, c, d, e] 4 = e := by simp
example {a b c d e : α} : ![a, b, c, d, e] 5 = a := by simp
example {a b c d e : α} : ![a, b, c, d, e] 6 = b := by simp
example {a b c d e : α} : ![a, b, c, d, e] 7 = c := by simp
example {a b c d e : α} : ![a, b, c, d, e] 8 = d := by simp
example {a b c d e : α} : ![a, b, c, d, e] 9 = e := by simp
example {a b c d e : α} : ![a, b, c, d, e] 123 = d := by simp
example {a b c d e : α} : ![a, b, c, d, e] 123456789 = e := by simp

example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 5 = f := by simp
example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 7 = h := by simp
example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 37 = f := by simp
example {a b c d e f g h : α} : ![a, b, c, d, e, f, g, h] 99 = d := by simp

example {α : Type*} [comm_ring α] {a b c d : α} :
  matrix.det ![![a, b], ![c, d]] = a * d - b * c :=
begin
  simp [matrix.det_succ_row_zero, fin.sum_univ_succ],
  /-
  Try this: simp only [matrix.det_succ_row_zero, fin.sum_univ_succ, det_fin_zero,
      finset.sum_singleton, fin.sum_univ_zero, minor_apply, cons_val_zero, cons_val_succ,
      fin.succ_above_zero, fin.coe_succ, fin.coe_zero],
  -/
  ring
end

example {α : Type*} [comm_ring α] (A : matrix (fin 3) (fin 3) α) {a b c d e f g h i : α} :
        matrix.det ![![a, b, c], ![d, e, f], ![g, h, i]] =
          a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g :=
begin
  simp [matrix.det_succ_row_zero, fin.sum_univ_succ],
  /-
  Try this: simp only [matrix.det_succ_row_zero, fin.sum_univ_succ, det_fin_zero,
      finset.sum_singleton, fin.sum_univ_zero, minor_apply, cons_val_zero, cons_val_succ,
      fin.succ_above_zero, fin.succ_succ_above_zero, fin.succ_succ_above_succ,
      fin.coe_zero, fin.coe_succ, pow_zero, pow_add],
   -/
  ring
end

end matrix
