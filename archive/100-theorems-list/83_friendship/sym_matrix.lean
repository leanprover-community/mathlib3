import data.matrix.basic
import linear_algebra.matrix
import data.polynomial
import linear_algebra.determinant
import linear_algebra.basic

-- open_locale classical
noncomputable theory

universes u v
variables {m : Type u} {R : Type v} [fintype m]

def sym_matrix (M : matrix m m R) : Prop :=
  M = M.transpose

lemma sym_matrix_apply {M : matrix m m R} (h : sym_matrix M) (i j : m):
  M i j = M j i :=
by { unfold sym_matrix at h, conv_rhs {rw h}, refl, }

variables [ring R] --

def matrix_J : matrix m m R :=
  λ (i j : m), (1 : R)

@[simp] lemma matrix_J_apply {i j : m} : matrix_J i j = (1 : R) := rfl

lemma trace_J (m:Type*) [fintype m] :
matrix.trace m R R matrix_J = fintype.card m :=
begin
  rw matrix.trace,
  rw matrix_J,
  change (finset.univ.sum ∘ ⇑(matrix.diag m R R)) (λ (i j : m), 1) =
    ↑(fintype.card m),
  rw function.comp_apply,
  rw fintype.card,
  simp,
end
