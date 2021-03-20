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
  -- TODO: can we make this require less steering?
  simp [matrix.det_apply', finset.univ_perm_fin_succ, ←finset.univ_product_univ, finset.sum_product,
        fin.sum_univ_succ, fin.prod_univ_succ],
  ring
end

example {α : Type*} [comm_ring α] (A : matrix (fin 3) (fin 3) α) {a b c d e f g h i : α} :
        matrix.det ![![a, b, c], ![d, e, f], ![g, h, i]] =
          a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g :=
begin
  -- We utilize the `norm_swap` plugin for `norm_num` to reduce swap terms
  norm_num [matrix.det_apply', finset.univ_perm_fin_succ, ←finset.univ_product_univ,
            finset.sum_product, fin.sum_univ_succ, fin.prod_univ_succ],
  ring
end

end matrix
