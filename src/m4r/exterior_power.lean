import m4r.tpow_to_talg linear_algebra.exterior_algebra

universe u
variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M] [module R M]

open exterior_algebra

lemma wedge_eq_ι_multi {n : ℕ} (v : fin n → M) :
  wedge R M v = ι_multi R n v :=
begin
  rw ι_multi_apply,
  show exterior_algebra.quot R M (list.prod _) = _,
  unfold exterior_algebra.ι,
  simp only [alg_hom.to_linear_map_apply, linear_map.comp_apply, alg_hom.map_prod', list.map_map],
  congr,
  rw list.of_fn_eq_map,
  refl,
end

def exists_same (n : ℕ) : set (fin n → M) :=
{ v | ∃ (i j : fin n) (h : v i = v j), i ≠ j }

def epow_ker (n : ℕ) : submodule R (tpow R M n) :=
submodule.span R (tpow.mk' R M n '' exists_same M n)

@[reducible] def epow' (n : ℕ) := (epow_ker R M n).quotient

def epow'.mk (n : ℕ) : multilinear_map R (λ i : fin n, M) (epow' R M n) :=
(epow_ker R M n).mkq.comp_multilinear_map (tpow.mk' R M n)

variables {N : Type u} [add_comm_group N] [module R N] {n : ℕ}

def quot_prod_equiv {p : submodule R M} {q : submodule R N} :
  (p.quotient × q.quotient) ≃ₗ[R] (p.prod q).quotient :=
linear_equiv.of_linear (linear_map.coprod (p.liftq
  ((p.prod q).mkq.comp $ linear_map.inl R M N) $
    λ x hx, by rw [linear_map.ker_comp, submodule.ker_mkq]; exact ⟨hx, q.zero_mem⟩)
    (q.liftq ((p.prod q).mkq.comp $ linear_map.inr R M N) $
    λ x hx, by rw [linear_map.ker_comp, submodule.ker_mkq]; exact ⟨p.zero_mem, hx⟩))
  ((p.prod q).liftq (linear_map.prod_map p.mkq q.mkq) $
  λ x hx, by erw linear_map.ker_prod; simp only [linear_map.ker_comp, submodule.ker_mkq];
    exact ⟨hx.1, hx.2⟩)
  (begin
    ext,
    refine quotient.induction_on' x (λ y, _),
    show (p.prod q).mkq _ + (p.prod q).mkq _ = (p.prod q).mkq y,
    erw ←linear_map.map_add,
    congr,
    show (y.1 + 0, 0 + y.2) = y, by simp only [add_zero, zero_add, prod.mk.eta],
  end)
  (begin
    ext ⟨x, y⟩,
     all_goals { refine quotient.induction_on' x (λ z, _),
      refine quotient.induction_on' y (λ w, _)},
      show p.mkq (z + 0) = p.mkq z, by rw add_zero,
      show q.mkq (0 + w) = q.mkq w, by rw zero_add,
  end)

-- can't find in mathlib rn
def submodule.pi {ι : Type*} (M : ι → Type*) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π₀ i, submodule R (M i)) :
  submodule R (direct_sum ι M) :=
{ carrier := { f | ∀ i, f i ∈ p i},
  zero_mem' := λ i, (p i).zero_mem,
  add_mem' := λ x y hx hy i, by {rw dfinsupp.add_apply,
    exact (p i).add_mem (hx i) (hy i)},
  smul_mem' := λ c x hx i, by {rw dfinsupp.smul_apply,
    exact (p i).smul_mem c (hx i)} }

variables {ι : Type*} [decidable_eq ι] (F : ι → Type*) [Π i, add_comm_group (F i)]
  [Π i, module R (F i)] (p : Π₀ i, submodule R (F i))

def quot_pi_equiv {ι : Type*} [decidable_eq ι] (M : ι → Type*) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π₀ i, submodule R (M i)) :
  direct_sum ι (λ i, (p i).quotient) ≃ₗ[R] (submodule.pi R M p).quotient :=
linear_equiv.of_linear (direct_sum.to_module R ι _ (λ i, (p i).liftq
  ((submodule.pi R M p).mkq.comp (direct_sum.lof R ι M i)) $
  by {rw linear_map.ker_comp,
    rw submodule.ker_mkq,
    intros x hx j,
    rcases classical.em (j = i) with ⟨rfl, hj⟩,
      rw direct_sum.lof_apply, exact hx,
    convert (p j).zero_mem,
    exact dfinsupp.single_eq_of_ne (ne.symm h)}))
  ((submodule.pi R M p).liftq (direct_sum.to_module R ι _
    (λ i, (direct_sum.lof R ι _ i).comp (p i).mkq)) sorry) sorry sorry

lemma quot_pi_equiv_apply {ι : Type*} [decidable_eq ι] (M : ι → Type*) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π₀ i, submodule R (M i)) (i : ι) (x : M i) :
  quot_pi_equiv R M p (direct_sum.lof R ι _ i ((p i).mkq x)) =
    (submodule.pi R M p).mkq (direct_sum.lof R ι _ i x) :=
begin
  erw linear_equiv.of_linear_apply,
  rw direct_sum.to_module_lof,
  erw (p i).liftq_apply,
end

lemma quot_pi_equiv_symm_apply {ι : Type*} [decidable_eq ι] (M : ι → Type*) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π₀ i, submodule R (M i)) (i : ι) (x : M i) :
  (quot_pi_equiv R M p).symm ((submodule.pi R M p).mkq (direct_sum.lof R ι _ i x)) =
    (direct_sum.lof R ι _ i ((p i).mkq x)) :=
begin
  erw linear_equiv.of_linear_symm_apply,
  simp only [direct_sum.to_module_lof, submodule.liftq_apply,
    submodule.mkq_apply, linear_map.comp_apply],
end

def epow'_lift (f : alternating_map R M N (fin n)) :
  epow' R M n →ₗ[R] N :=
(epow_ker R M n).liftq (tpow.lift R n N f) $ submodule.span_le.2
begin
  rintro x ⟨v, ⟨i, j, hv, hij⟩, rfl⟩,
  erw linear_map.mem_ker,
  rw tpow.lift_mk_apply,
  exact f.map_eq_zero_of_eq v hv hij,
end

lemma epow'_lift_mk (f : alternating_map R M N (fin n)) {v : fin n → M} :
  epow'_lift R M f (epow'.mk R M n v) = f v :=
tpow.lift_mk_apply n f.to_multilinear_map v

@[reducible] def ealg := direct_sum ℕ (epow' R M)

#exit
def epow_map (n : ℕ) : tpow R M n →ₗ[R] exterior_algebra R M :=
(((exterior_algebra.quot R M).comp (talg_equiv R M).to_alg_hom)).to_linear_map.comp
  $ (direct_sum.lof R ℕ (tpow R M) n : tpow R M n →ₗ[R] talg R M)

@[reducible] def epow (n : ℕ) := (epow_map R M n).ker.quotient

def epow.mk (n : ℕ) : multilinear_map R (λ i : fin n, M) (epow R M n) :=
linear_map.comp_multilinear_map (submodule.mkq (epow_map R M n).ker) (tpow.mk' R M n)

variables (R M N n)

def epow.incl (n : ℕ) : epow R M n →ₗ[R] exterior_algebra R M :=
submodule.liftq (epow_map R M n).ker (epow_map R M n) (le_refl _)
