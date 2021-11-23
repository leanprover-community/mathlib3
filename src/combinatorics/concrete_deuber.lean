import combinatorics.deuber
import data.matrix.basic

open_locale big_operators

variables {R M : Type*} [comm_semiring R] {m n : ℕ} (p : P R)

def eval (x : fin m → R) (v : fin m → R) : R := matrix.dot_product v x

def inc.matrix (f : inc R m n) : matrix (fin m) (fin n) R :=
λ i j, (f.mat j).elim 0 $ λ p, if p.snd = i then p.fst else 0

lemma map_vec_eq_vec_mul (f : inc R m n) (v : fin m → R) :
  f.map_vec v = f.matrix.vec_mul v :=
begin
  funext j,
  rcases h : f.mat j with _ | ⟨r, i⟩,
  { simp_rw [inc.map_vec_none h, matrix.vec_mul, matrix.dot_product, inc.matrix, h, option.elim,
      mul_zero, finset.sum_const_zero] },
  { simp_rw [inc.map_vec_some h, matrix.vec_mul, matrix.dot_product],
    rw [finset.sum_eq_single_of_mem i (finset.mem_univ _), inc.matrix],
    { simp_rw [h, option.elim, if_pos rfl] },
    { intros i' junk ne, rw inc.matrix, simp_rw [h, option.elim, if_neg ne.symm, mul_zero] } }
end

def mpc_set (x : fin m → R) : set R := eval x '' ⋃ i, row p i

theorem concrete_deuber (κ) [fintype κ] : ∃ n, ∀ (co : R → κ) (y : fin n → R),
  ∃ (x : fin m → R), mpc_set p x ⊆ mpc_set (p^(fintype.card κ * m + 2)) y ∧
    ∃ k, ∀ r ∈ mpc_set p x, co r = k :=
begin
  obtain ⟨n, hn⟩ := deuber m p κ,
  use n,
  intros co y,
  specialize hn (co ∘ eval y),
  obtain ⟨f, fsmall, k, hk⟩ := hn,
  refine ⟨f.matrix.mul_vec y, _, k, _⟩,
  { intros r hr,
    simp only [mpc_set, set.mem_Union, set.mem_image] at hr,
    obtain ⟨v, ⟨i, vi⟩, h⟩ := hr,
    simp only [mpc_set, set.mem_Union, set.mem_image],
    refine ⟨f.map_vec v, ⟨f.emb i, inc.map_row fsmall vi⟩, _⟩,
    simp only [eval, map_vec_eq_vec_mul, matrix.dot_product_mul_vec, ←h] },
  { simp only [mpc_set, set.mem_Union, set.mem_image],
    rintros _ ⟨v, ⟨i, vi⟩, rfl⟩,
    specialize hk i v vi,
    rw ←hk,
    congr' 1,
    simp only [eval, map_vec_eq_vec_mul, matrix.dot_product_mul_vec] }
end
