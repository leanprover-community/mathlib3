import m4r.inductive_koszul ring_theory.localization m4r.projective_resolution
universe u
open_locale classical
section
variables  {R : Type u} [comm_ring R] {M : Type u} [add_comm_group M] [module R M]

class reg_seq (N : submodule R M) {n : ℕ} (seq : fin n → R) : Prop :=
(span_smul_ne : ideal.span (set.range seq) • N ≠ N)
(cond : ∀ (i : fin n) (x : N),
  (seq i) • (x : M) ∈ ideal.span (set.image seq ({j | j < i})) • N
    → (x : M) ∈ ideal.span (set.image seq ({j | j < i})) • N)

noncomputable def enat_depth (I : ideal R) (N : submodule R M) : enat :=
enat.find (λ n, ∀ m, n < m → (∀ f : fin m → R, set.range f ⊆ I → ¬(reg_seq N f)))

end
section

variables {R : Type u} [comm_ring R] [is_noetherian_ring R] {M : Type u}
  [add_comm_group M] [module R M]

theorem exists_depth_of_fg (I : ideal R) (N : submodule R M) (hfg : N.fg) :
  ∃ n : ℕ, enat_depth I N = n := sorry

noncomputable def depth (I : ideal R) (N : submodule R M) (hfg : N.fg) :=
classical.some (exists_depth_of_fg I N hfg)

theorem enat_depth_eq_depth (I : ideal R) (N : submodule R M) (hfg : N.fg) :
  enat_depth I N = depth I N hfg :=
classical.some_spec (exists_depth_of_fg I N hfg)

lemma fin.set_lt_zero_eq_empty {n : ℕ} :
  {j : fin n.succ | j < 0} = ∅ :=
set.ext (λ y, ⟨λ h', nat.not_lt_zero _ (fin.coe_fin_lt.2 h'), λ h', false.elim h'⟩)

@[simp] lemma cond_zero {N : submodule R M} {n : ℕ} (seq : fin n.succ → R) (x : N) :
  (seq 0) • (x : M) ∈ ideal.span (set.image seq ({j | j < 0})) • N ↔ seq 0 • x = 0 :=
by rw [fin.set_lt_zero_eq_empty, set.image_empty, ideal.span, submodule.span_empty,
      submodule.bot_smul, submodule.mem_bot, ←submodule.coe_smul, submodule.coe_eq_zero]

lemma singleton_reg_seq (x : R) (h : ideal.span ({x} : set R) ≠ ⊤) :
  (reg_seq (⊤ : submodule R R) (λ i : fin 1, x)) ↔ x ∈ non_zero_divisors R :=
begin
  split,
  { rintro ⟨H⟩ y hy,
    rw [mul_comm, ←algebra.id.smul_eq_mul] at hy,
    have H' : (λ i : fin 1, x) 0 • (⟨y, submodule.mem_top⟩ : (⊤ : submodule R R)) = 0,
    from (submodule.mk_eq_zero _ submodule.mem_top).2 hy,
    sorry,
    /-  have := H.2 0 ⟨y, submodule.mem_top⟩ ((cond_zero (λ i : fin 1, x) _).2 H'),
        rwa [fin.set_lt_zero_eq_empty, set.image_empty, ideal.span, submodule.span_empty,
        submodule.bot_smul, submodule.mem_bot] at this -/
        },
  { intro H,
    exact {
      span_smul_ne := by convert h;
      rw [set.range_unique, algebra.id.smul_eq_mul, ideal.mul_top],
             cond :=
      begin
        intros i y hy,
        simp only [subsingleton.elim i 0] at *,
        rw [fin.set_lt_zero_eq_empty, set.image_empty, ideal.span, submodule.span_empty,
          submodule.bot_smul, submodule.mem_bot] at *,
        rw [algebra.id.smul_eq_mul, mul_comm] at hy,
        exact H y hy,
      end
      }}
end

def subsingleton_of_ker_le_range (F : cochain_complex ℤ (Module.{u} R)) (i : ℤ)
  (H : (F.d i (i + 1)).ker ≤ (F.d (i - 1) i).range) :
  subsingleton (cochain_complex.cohomology R F i) :=
⟨begin
  intros a b,
  refine quotient.induction_on' a (λ x, _),
  refine quotient.induction_on' b (λ y, _),
  erw [←sub_eq_zero, ←submodule.quotient.mk_sub],
  rw [submodule.quotient.mk_eq_zero, submodule.mem_comap],
  exact H (subtype.prop (x - y)),
end⟩

#exit
theorem seventeen_point_one [local_ring R] (s : fin 2 → R)
  (hs : set.range s ⊆ local_ring.maximal_ideal R) :
  nonempty (reg_seq (⊤ : submodule R (fin 2 → R)) s) ↔
    (subsingleton (cochain_complex.cohomology R (inductive_Koszul R 1 s) 1)) :=
begin
  split,
  { rintro ⟨H⟩,
    refine subsingleton_of_ker_le_range _ _ _,
    intros x hx,
    obtain ⟨X, Y⟩ := inductive_Koszul_prod R 0 s x,
    have H : s 0 * X + s 1 * Y = 0 :=
    begin
      rw linear_map.mem_ker at hx,
      erw cochain_complex.mk'_d' at hx,
      unfold total_d at hx,
      unfold total_d_fst at hx,
      unfold total_d_snd at hx,
      unfold direct_sum.to_module at hx,
      erw dfinsupp.sum_add_hom_apply at hx,
      erw dfinsupp.sum_add at hx,
      simp only [linear_map.comp_apply] at hx,
      have := direct_sum.ext_iff.1 hx,
      dsimp at hx,
      erw dfinsupp.sum_apply at hx,
      --simp only [linear_map.comp_apply] at hx,
      erw ←dfinsupp.sum_add_hom_apply at hx,
      change direct_sum.to_module R _ _ _
        + direct_sum.to_module R _ _ _ = 0 at hx,
      rw dfinsupp.sum_single at hx,
      rw linear_equiv.map_add at hx,
      --simp only [inductive_Koszul] at hx,
      --change @total_d R _ (smul_complex R (s 1)) (smul_complex R (s 0)) 1 x = 0 at hx,
      --have : total_d R _ _ x = 0 := hx,
      --change total_d _ _ _ _ = _ at hx,


    end,

    sorry,
     },
  { sorry },
end

theorem seventeen_point_two [local_ring R] {n : ℕ} (s : fin n → R)
  (h : reg_seq (⊤ : submodule R (fin n → R)) s)
  (hx : set.range s ⊆ local_ring.maximal_ideal R)
  (σ : equiv.perm (fin n)) :
  reg_seq (⊤ : submodule R (fin n → R)) (s ∘ σ) :=
sorry

end
