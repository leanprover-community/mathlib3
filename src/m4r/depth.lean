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

lemma fin.set_lt_zero_eq_empty {n : ℕ} :
  {j : fin n.succ | j < 0} = ∅ :=
set.ext (λ y, ⟨λ h', nat.not_lt_zero _ (fin.coe_fin_lt.2 h'), λ h', false.elim h'⟩)

@[simp] lemma cond_zero {N : submodule R M} {n : ℕ} (seq : fin n.succ → R) (x : N) :
  (seq 0) • (x : M) ∈ ideal.span (set.image seq ({j | j < 0})) • N ↔ seq 0 • x = 0 :=
by rw [fin.set_lt_zero_eq_empty, set.image_empty, ideal.span, submodule.span_empty,
      submodule.bot_smul, submodule.mem_bot, ←submodule.coe_smul, submodule.coe_eq_zero]

lemma singleton_reg_seq (x : R) (h : ideal.span ({x} : set R) ≠ ⊤) :
  nonempty (reg_seq (⊤ : submodule R R) (λ i : fin 1, x)) ↔ x ∈ non_zero_divisors R :=
begin
  split,
  { rintro ⟨H⟩ y hy,
    rw [mul_comm, ←algebra.id.smul_eq_mul] at hy,
    have H' : (λ i : fin 1, x) 0 • (⟨y, submodule.mem_top⟩ : (⊤ : submodule R R)) = 0,
    from (submodule.mk_eq_zero _ submodule.mem_top).2 hy,
    have := H.2 0 ⟨y, submodule.mem_top⟩ ((cond_zero (λ i : fin 1, x) _).2 H'),
    rwa [fin.set_lt_zero_eq_empty, set.image_empty, ideal.span, submodule.span_empty,
        submodule.bot_smul, submodule.mem_bot] at this },
  { intro H,
    exact ⟨{ span_smul_ne := by convert h;
      rw [set.range_unique, algebra.id.smul_eq_mul, ideal.mul_top],
             cond :=
      begin
        intros i y hy,
        simp only [subsingleton.elim i 0] at *,
        rw [fin.set_lt_zero_eq_empty, set.image_empty, ideal.span, submodule.span_empty,
          submodule.bot_smul, submodule.mem_bot] at *,
        rw [algebra.id.smul_eq_mul, mul_comm] at hy,
        exact H y hy,
      end }⟩}
end

#exit
lemma Koszul_reg_one (x : R) (hx : ¬(is_unit x)) :
  nonempty (reg_seq (⊤ : submodule R R) (λ i : fin 1, x)) ↔
theorem seventeen_point_one [local_ring R] (s : fin 2 → R)
  (hx : set.range s ⊆ local_ring.maximal_ideal R) :
  nonempty (reg_seq (⊤ : submodule R (fin 2 → R)) s) ↔
    ((cochain_complex.cohomology _ 1).obj (free_Koszul R 1 s) = Module.of R punit) :=
begin
  split,
  { sorry },
  { sorry },
end

theorem seventeen_point_two [local_ring R] {n : ℕ} (s : fin n → R)
  (h : reg_seq (⊤ : submodule R (fin n → R)) s)
  (hx : set.range s ⊆ local_ring.maximal_ideal R)
  (σ : equiv.perm (fin n)) :
  reg_seq (⊤ : submodule R (fin n → R)) (s ∘ σ) :=
sorry

end
