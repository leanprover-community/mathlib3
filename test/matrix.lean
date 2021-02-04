import data.matrix.notation

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

end matrix
