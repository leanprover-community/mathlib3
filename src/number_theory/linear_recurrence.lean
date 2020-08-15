import data.polynomial.ring_division
import linear_algebra.dimension
import algebra.polynomial.big_operators

open finset

open_locale big_operators

noncomputable theory

structure linear_recurrence (α : Type*) [field α] := (order : ℕ) (coeffs : fin order → α)

variables {α : Type*} [field α]

namespace linear_recurrence

variables (E : linear_recurrence α)

def is_solution (u : ℕ → α) :=
  ∀ n, u (n + E.order) = (∑ i, E.coeffs i * u (n + i))

def mk_sol (init : fin E.order → α) : ℕ → α
| n := if h : n < E.order then init ⟨n, h⟩ else
  ∑ k : fin E.order, have n - E.order + k.1 < n, by have := k.2; omega,
    E.coeffs k * mk_sol (n - E.order + k)

def is_sol_mk_sol (init : fin E.order → α) :
  E.is_solution (E.mk_sol init) :=
  λ n, by rw mk_sol; simp

def mk_sol_eq_init (init : fin E.order → α) :
  ∀ n : fin E.order, E.mk_sol init n = init n :=
  λ n, by rw mk_sol; simp [fin.coe_eq_val, n.2]

lemma eq_mk_of_is_sol_of_eq_init {u : ℕ → α} {init : fin E.order → α}
  (h : E.is_solution u) (heq : ∀ n : fin E.order, u n = init n) :
  ∀ n, u n = E.mk_sol init n
| n := if h' : n < E.order
  then by rw mk_sol; simp only [h', dif_pos]; exact_mod_cast heq ⟨n, h'⟩
  else begin
    rw mk_sol,
    rw ← nat.sub_add_cancel (le_of_not_lt h'),
    rw h (n-E.order),
    simp [h'],
    congr',
    ext k,
    exact have wf : n - E.order + k.1 < n, by have := k.2; omega,
      by rw eq_mk_of_is_sol_of_eq_init
  end

def sol_space : subspace α (ℕ → α) :=
{ carrier := {u | E.is_solution u},
  zero_mem' := λ n, by simp,
  add_mem' := λ u v hu hv n, by simp [mul_add, sum_add_distrib, hu n, hv n],
  smul_mem' := λ a u hu n, by simp [hu n, mul_sum]; congr'; ext; ac_refl }

lemma is_sol_iff_mem_sol_space (u : ℕ → α) :
  E.is_solution u ↔ u ∈ E.sol_space := by refl

def sol_space_linear_equiv_init_space :
  E.sol_space ≃ₗ[α] (fin E.order → α) :=
{ to_fun := λ u x, (u : ℕ → α) x,
  map_add' := λ u v, by ext; simp; norm_cast,
  map_smul' := λ a u, by ext; simp,
  inv_fun := λ u, ⟨E.mk_sol u, E.is_sol_mk_sol u⟩,
  left_inv := λ u, by ext n; symmetry; apply E.eq_mk_of_is_sol_of_eq_init u.2; intros k; refl,
  right_inv := λ u, function.funext_iff.mpr (λ n, E.mk_sol_eq_init u n) }

lemma sol_space_dim :
  vector_space.dim α E.sol_space = E.order :=
@dim_fin_fun α _ E.order ▸ E.sol_space_linear_equiv_init_space.dim_eq

def char_poly : polynomial α :=
  polynomial.monomial E.order 1 - (∑ i : fin E.order, polynomial.monomial i (E.coeffs i))

#check polynomial.eval₂_finset_sum

lemma geom_sol_iff_root_char_poly (q : α) :
  E.is_solution (λ n, q^n) ↔ E.char_poly.is_root q :=
begin
  rw [char_poly, polynomial.is_root.def, polynomial.eval],
  simp only [polynomial.eval₂_finset_sum, one_mul,
              ring_hom.id_apply, polynomial.eval₂_monomial, polynomial.eval₂_sub],
  split,
  { intro h,
    specialize h 0,
    simp only [zero_add] at h,
    rwa ← sub_eq_zero_iff_eq at h },
  { intros h n,
    rw sub_eq_zero_iff_eq at h,
    simp only [pow_add],
    rw [h, mul_sum],
    congr,
    ext,
    ring }
end

theorem target (h : ∑ x in E.char_poly.roots, E.char_poly.root_multiplicity x = E.order) (u : ℕ → α) :
  E.is_solution u ↔
    ∃ (a : α → polynomial α)
      (h : ∀ x, (a x).degree < E.char_poly.root_multiplicity x),
    u = λ n, ∑ x in E.char_poly.roots, (a x).eval n * x^n := sorry

end linear_recurrence
