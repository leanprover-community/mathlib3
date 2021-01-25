import m4r.koszul_of_free ring_theory.localization algebra.homology.homology
  category_theory.abelian.basic algebra.category.Module.abelian
universe u
open_locale classical
section
variables  {R : Type u} [comm_ring R] {M : Type u} [add_comm_group M] [module R M]

structure reg_seq (N : submodule R M) {n : ℕ} (seq : fin n → R) :=
(span_smul_ne : ideal.span (set.range seq) • N ≠ N)
(cond : ∀ (i : fin n) (x : N),
  (seq i) • (x : M) ∈ ideal.span (set.image seq ({j | j < i})) • N
    → (x : M) ∈ ideal.span (set.image seq ({j | j < i})) • N)

noncomputable def depth (I : ideal R) (N : submodule R M) : enat :=
dite (∃ (n : ℕ), (∃ (s : fin n → R) (h : reg_seq N s), set.range s ⊆ I) ∧
  (∀ (m : ℕ), (∃ (s : fin m → R) (h : reg_seq N s), set.range s ⊆ I) → m ≤ n))
 (λ h, ((classical.some h : ℕ) : enat)) (λ h, ⊤)

end
section

variables {R : Type u} [comm_ring R] [is_noetherian_ring R] {M : Type u}
  [add_comm_group M] [module R M]

theorem exists_depth (I : ideal R) (N : submodule R M) (hfg : N.fg) :
  ∃ (n : ℕ), (∃ (s : fin n → R) (h : reg_seq N s), set.range s ⊆ I) ∧
  (∀ m : ℕ, (∃ (s : fin m → R) (h : reg_seq N s), set.range s ⊆ I) → m ≤ n) :=
sorry

noncomputable def finite_depth (I : ideal R) (N : submodule R M) (hfg : N.fg) :=
classical.some (exists_depth I N hfg)

theorem finite_depth_eq_depth (I : ideal R) (N : submodule R M) (hfg : N.fg) :
  depth I N = finite_depth I N hfg :=
dif_pos (exists_depth I N hfg)

theorem seventeen_point_one [local_ring R] (s : fin 2 → R)
  (hx : set.range s ⊆ local_ring.maximal_ideal R) :
  nonempty (reg_seq (⊤ : submodule R (fin 2 → R)) s) ↔
    ((cochain_complex.cohomology _ 1).obj (free_Koszul R 1 s) = Module.of R punit) :=
sorry

theorem seventeen_point_two [local_ring R] {n : ℕ} (s : fin n → R)
  (h : reg_seq (⊤ : submodule R (fin n → R)) s)
  (hx : set.range s ⊆ local_ring.maximal_ideal R)
  (σ : equiv.perm (fin n)) :
  reg_seq (⊤ : submodule R (fin n → R)) (s ∘ σ) :=
sorry

end
