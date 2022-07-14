import data.fin.vec_notation
import tactic.fin_cases
import data.matrix.basic

namespace matrix
variables {m n : ℕ} {α : Type*}

section
-- Note that here we are disabling the "safety" of reflected, to allow us to reuse `nat.mk_numeral`.
-- The usual way to provide the required `reflected` instance would be via rewriting to prove that
-- the expression we use here is equivalent.
local attribute [semireducible] reflected
meta instance reflect : Π n, has_reflect (fin n)
| 0 := fin_zero_elim
| (n + 1) := nat.mk_numeral `(fin n.succ)
              `(by apply_instance : has_zero (fin n.succ))
              `(by apply_instance : has_one (fin n.succ))
              `(by apply_instance : has_add (fin n.succ)) ∘ subtype.val
end

def fin_vec.eta_expand : Π {m}, (fin m → α) → fin m → α
| 0 v := ![]
| (n + 1) v := matrix.vec_cons (v 0) (fin_vec.eta_expand (vec_tail v))

lemma fin_vec.eta_expand_eq : Π {m} (v : fin m → α), fin_vec.eta_expand v = v
| 0 := λ v, subsingleton.elim _ _
| (n + 1) := begin
  simp_rw [fin_vec.eta_expand,fin_vec.eta_expand_eq],
  exact fin.cons_self_tail,
end

def eta_expand {m n} (A : matrix (fin m) (fin n) α) : matrix (fin m) (fin n) α :=
matrix.of (fin_vec.eta_expand (λ i, fin_vec.eta_expand (λ j, A i j)))

def eta_expand_eq {m n} (A : matrix (fin m) (fin n) α) :
  eta_expand A = A :=
by simp_rw [eta_expand, fin_vec.eta_expand_eq, matrix.of, equiv.refl_apply]

/-- make a nice version of `eta_expand` -/
meta def mk_nice_eta_expand (m n : ℕ) : tactic expr :=
do
  u ← tactic.mk_meta_univ,
  α ← tactic.mk_local' `α binder_info.implicit (expr.sort u.succ),
  let mat_typ := (expr.const `matrix [level.zero, level.zero, u] `(fin %%`(m)) `(fin %%`(n)) α),
  A ← tactic.mk_local' `A binder_info.default
    (expr.const `matrix [level.zero, level.zero, u] `(fin %%`(m)) `(fin %%`(n)) α),
  let entries := λ (i : fin m) (j : fin n), A `(i) `(j),
  let entry_vals := pi_fin.to_pexpr (λ i, pi_fin.to_pexpr (λ j, to_pexpr $ entries i j)),
  let A_eta := (``(@matrix.of (fin %%`(m)) (fin %%`(n)) _).app entry_vals),
  tactic.lambdas [α, A] mat_typ


/-- Prove a statement of the form `∀ A : matrix m n α, A = !![A 0 0, ...]`.
Returns the type of this statement and its proof. -/
meta def prove_eta (m n : ℕ) : tactic (expr × expr) :=
do
  u ← tactic.mk_meta_univ,
  α ← tactic.mk_local' `α binder_info.implicit (expr.sort u.succ),
  A ← tactic.mk_local' `A binder_info.default
    (expr.const `matrix [level.zero, level.zero, u] `(fin %%`(m)) `(fin %%`(n)) α),
  let entries := λ (i : fin m) (j : fin n), A `(i) `(j),
  let entry_vals := pi_fin.to_pexpr (λ i, pi_fin.to_pexpr (λ j, to_pexpr $ entries i j)),
  let A_eta := (``(@matrix.of (fin %%`(m)) (fin %%`(n)) _).app entry_vals),
  A_eq ← tactic.to_expr ``(%%A = %%A_eta),
  t ← tactic.pis [α, A] A_eq,
  ((), pr) ← tactic.solve_aux t `[intros α A, exact (matrix.eta_expand_eq A).symm],
  pure (t, pr)

meta def derive_eta_proof : tactic unit :=
do
  target@`(%%A' = %%A_eta) ← tactic.target,
  (expr.const `matrix ls, [`(fin %%m), `(fin %%n), α]) ← expr.get_app_fn_args <$> tactic.infer_type A',
  some (m, n) ← pure (prod.mk <$> m.to_nat <*> n.to_nat) |
    fail!"Dimensions {m} {n} are not numerals",
  (t,pr) ← prove_eta m n,

  tactic.unify target (t.instantiate_pis [α, A']),
  tactic.exact (pr α A')

theorem fin_eta (A : matrix (fin m) (fin n) α) {«![A 0 0, ...]» : matrix (fin m) (fin n) α}
  (h : A = «![A 0 0, ...]» . derive_eta_proof) : A = «![A 0 0, ...]» := h

def B : matrix (fin 20) (fin 20) ℕ := 0

example : B = B :=
begin
  have := matrix.fin_eta B,
  rw this,
end

end matrix
