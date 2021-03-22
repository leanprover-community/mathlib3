import m4r.tpow_to_talg linear_algebra.exterior_algebra m4r.sq_zero

universes u v
variables (R : Type u) [comm_ring R] (M : Type u) [add_comm_group M] [module R M]

open exterior_algebra
open_locale classical

def exists_same (n : ℕ) : set (fin n → M) :=
{ v | ∃ (i j : fin n) (h : v i = v j), i ≠ j }

def epow_ker (n : ℕ) : submodule R (tpow R M n) :=
submodule.span R (tpow.mk' R M n '' exists_same M n)

@[reducible] def epow (n : ℕ) := (epow_ker R M n).quotient

def epow.mk (n : ℕ) : alternating_map R M (epow R M n) (fin n) :=
{ map_eq_zero_of_eq' := λ v i j h hij, (submodule.quotient.mk_eq_zero _).2 $
  submodule.subset_span $ set.mem_image_of_mem _ ⟨i, j, h, hij⟩,
  ..(epow_ker R M n).mkq.comp_multilinear_map (tpow.mk' R M n) }

variables {M} {N : Type u} [add_comm_group N] [module R N] {n : ℕ}
  {p : submodule R M} {q : submodule R N}

def quot_prod_to_quot :
  (p.quotient × q.quotient) →ₗ[R] (p.prod q).quotient :=
linear_map.coprod (p.liftq
  ((p.prod q).mkq.comp $ linear_map.inl R M N) $
    λ x hx, by rw [linear_map.ker_comp, submodule.ker_mkq]; exact ⟨hx, q.zero_mem⟩)
    (q.liftq ((p.prod q).mkq.comp $ linear_map.inr R M N) $
    λ x hx, by rw [linear_map.ker_comp, submodule.ker_mkq]; exact ⟨p.zero_mem, hx⟩)

def quot_to_quot_prod :
  (p.prod q).quotient →ₗ[R] (p.quotient × q.quotient) :=
(p.prod q).liftq (linear_map.prod_map p.mkq q.mkq) $
  λ x hx, by erw linear_map.ker_prod; simp only [linear_map.ker_comp, submodule.ker_mkq];
    exact ⟨hx.1, hx.2⟩

lemma quot_prod_to_quot_left_inv (x : (p.prod q).quotient) :
  quot_prod_to_quot R (quot_to_quot_prod R x) = x :=
begin
  refine quotient.induction_on' x (λ y, _),
  show (p.prod q).mkq _ + (p.prod q).mkq _ = (p.prod q).mkq y,
  erw ←linear_map.map_add,
  congr,
  show (y.1 + 0, 0 + y.2) = y, by simp only [add_zero, zero_add, prod.mk.eta],
end

lemma quot_prod_to_quot_right_inv (x : p.quotient × q.quotient) :
  quot_to_quot_prod R (quot_prod_to_quot R x) = x :=
begin
  rcases x with ⟨x, y⟩,
  ext,
  all_goals { refine quotient.induction_on' x (λ z, _),
  refine quotient.induction_on' y (λ w, _)},
  { show p.mkq (z + 0) = p.mkq z, by rw add_zero },
  { show q.mkq (0 + w) = q.mkq w, by rw zero_add },
end

def quot_prod_equiv {p : submodule R M} {q : submodule R N} :
  (p.quotient × q.quotient) ≃ₗ[R] (p.prod q).quotient :=
linear_equiv.of_linear (quot_prod_to_quot R)
  (quot_to_quot_prod R) (linear_map.ext $ quot_prod_to_quot_left_inv R)
  (linear_map.ext $ quot_prod_to_quot_right_inv R)

def submodule.pi {ι : Type v} (M : ι → Type u) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π i, submodule R (M i)) :
  submodule R (direct_sum ι M) :=
{ carrier := { f | ∀ i, f i ∈ p i},
  zero_mem' := λ i, (p i).zero_mem,
  add_mem' := λ x y hx hy i, by rw dfinsupp.add_apply;
    exact (p i).add_mem (hx i) (hy i),
  smul_mem' := λ c x hx i, by rw dfinsupp.smul_apply;
    exact (p i).smul_mem c (hx i) }

lemma lof_mem_pi {ι : Type v} [decidable_eq ι] {M : ι → Type u} [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] {p : Π i, submodule R (M i)} {i : ι} {x : M i} :
  direct_sum.lof R ι M i x ∈ submodule.pi R M p ↔ x ∈ p i :=
begin
  split,
  { intro h,
    rw ←direct_sum.lof_apply R i x,
    exact h i },
  { intros hx j,
    rcases classical.em (i = j) with ⟨rfl, hij⟩,
    { rw direct_sum.lof_apply,
      exact hx },
    { erw dfinsupp.single_eq_of_ne h,
      exact (p j).zero_mem }},
end
open_locale classical

lemma mem_direct_sum {ι : Type v} [decidable_eq ι] {M : ι → Type u} [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (S : submodule R (direct_sum ι M)) (x : direct_sum ι M)
  (H : ∀ i, direct_sum.lof R ι M i (x i) ∈ S) :
  x ∈ S :=
begin
  rw ←@dfinsupp.sum_single _ _ _ _ _ x,
  refine submodule.sum_mem _ _,
  intros i hi,
  exact H i,
end

lemma pi_eq_span {ι : Type v} [decidable_eq ι] {M : ι → Type u} [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] {p : Π i, submodule R (M i)} :
  submodule.pi R M p = submodule.span R (set.Union (λ i, (p i).map (direct_sum.lof R ι M i))) :=
begin
  refine le_antisymm _ _,
  { rw submodule.span_Union,
    simp only [submodule.span_eq],
    rw le_supr_iff,
    intros b hb x hx,
    apply mem_direct_sum _ _,
    intros i,
    refine hb i _,
    apply_instance,
    exact submodule.mem_map_of_mem (hx i) },
  { rw submodule.span_le,
    intros x hx i,
    rw set.mem_Union at hx,
    rcases hx with ⟨j, y, hy, rfl⟩,
    rcases classical.em (i = j) with (rfl | hij),
    { rw direct_sum.lof_apply,
      exact hy },
    { erw dfinsupp.single_eq_of_ne (ne.symm hij),
      exact submodule.zero_mem _ }},
end

def direct_sum.map_range {ι : Type v} [decidable_eq ι] {M : ι → Type u} [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] {N : ι → Type u} [Π i, add_comm_group (N i)] [Π i, module R (N i)]
  (f : Π i, M i →ₗ[R] N i) : direct_sum ι M →ₗ[R] direct_sum ι N :=
{ to_fun := dfinsupp.map_range (λ i, f i) (λ i, linear_map.map_zero _),
  map_add' := λ x y, by ext; simp only [linear_map.map_add,
    dfinsupp.map_range_apply, direct_sum.add_apply],
  map_smul' := λ r x, by ext; simp only [dfinsupp.smul_apply,
    dfinsupp.map_range_apply, linear_map.map_smul] }

@[simp] lemma direct_sum.map_range_apply {ι : Type v} [decidable_eq ι]
  (M : ι → Type u) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (N : ι → Type u) [Π i, add_comm_group (N i)] [Π i, module R (N i)]
  (f : Π i, M i →ₗ[R] N i) (g : direct_sum ι M) (i : ι) :
  direct_sum.map_range R f g i = f i (g i) :=
dfinsupp.map_range_apply (λ i, f i) (λ i, linear_map.map_zero _) _ _

lemma quot_pi_to_quot_aux {ι : Type v} [decidable_eq ι]
  (M : ι → Type u) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π i, submodule R (M i)) (i : ι) :
  p i ≤ ((submodule.pi R M p).mkq.comp (direct_sum.lof R ι M i)).ker :=
begin
  rw [linear_map.ker_comp, submodule.ker_mkq],
  intros x hx j,
  rcases classical.em (j = i) with ⟨rfl, hj⟩,
  { rw direct_sum.lof_apply,
    exact hx },
  { convert (p j).zero_mem,
    exact dfinsupp.single_eq_of_ne (ne.symm h) }
end

def quot_pi_to_quot {ι : Type v} [decidable_eq ι] (M : ι → Type u) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π i, submodule R (M i)) :
  direct_sum ι (λ i, (p i).quotient) →ₗ[R] (submodule.pi R M p).quotient :=
(direct_sum.to_module R ι (submodule.pi R M p).quotient
  (λ i, (p i).liftq
  ((submodule.pi R M p).mkq.comp (direct_sum.lof R ι M i)) $
  quot_pi_to_quot_aux R M p i))

lemma quot_to_quot_pi_aux {ι : Type v} [decidable_eq ι]
  (M : ι → Type u) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π i, submodule R (M i)) :
  submodule.pi R M p ≤ (direct_sum.map_range R (λ (i : ι), (p i).mkq)).ker :=
λ x hx,
begin
  rw linear_map.mem_ker,
  ext,
  rw direct_sum.map_range_apply,
  refine linear_map.mem_ker.1 (by rw submodule.ker_mkq; exact hx i)
end

def quot_to_quot_pi {ι : Type v} [decidable_eq ι] (M : ι → Type u) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π i, submodule R (M i)) :
  (submodule.pi R M p).quotient →ₗ[R] direct_sum ι (λ i, (p i).quotient) :=
(submodule.pi R M p).liftq (direct_sum.map_range R $ λ i, (p i).mkq) $
quot_to_quot_pi_aux R M p

lemma quot_pi_to_quot_right_inv {ι : Type v} [decidable_eq ι]
  (M : ι → Type u) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π i, submodule R (M i)) (x : direct_sum ι (λ i, (p i).quotient)) :
  quot_to_quot_pi R M p (quot_pi_to_quot R M p x) = x :=
begin
  refine direct_sum.linduction_on R x _ _ _,
  { rw [linear_map.map_zero, linear_map.map_zero] },
  { intros i x,
    refine quotient.induction_on' x (λ y, _),
    ext j,
    rcases classical.em (i = j) with ⟨rfl, hij⟩,
    erw [dfinsupp.single_eq_same, dfinsupp.lsingle_apply, direct_sum.to_module_lof],
    show (direct_sum.map_range R (λ i, (p i).mkq) (direct_sum.lof R ι M i y)) i = submodule.quotient.mk y,
    rw [direct_sum.map_range_apply, direct_sum.lof_apply],
    refl,
    unfold quot_to_quot_pi quot_pi_to_quot,
    erw [dfinsupp.single_eq_of_ne h, direct_sum.to_module_lof],
    show (direct_sum.map_range R (λ i, (p i).mkq) (direct_sum.lof R ι M i y)) j = 0,
    rw direct_sum.map_range_apply,
    erw [submodule.quotient.mk_eq_zero, dfinsupp.single_eq_of_ne h],
    exact (p j).zero_mem },
  { intros z w hz hw,
    erw linear_map.map_add,
    rw linear_map.map_add,
    erw [hz, hw] },
end

lemma quot_pi_to_quot_left_inv {ι : Type v} [decidable_eq ι]
  (M : ι → Type u) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π i, submodule R (M i)) (x : (submodule.pi R M p).quotient) :
  quot_pi_to_quot R M p (quot_to_quot_pi R M p x) = x :=
begin
  refine quotient.induction_on' x (λ y, _),
  refine direct_sum.linduction_on R y _ _ _,
  { convert linear_map.map_zero _ },
  { intros i z,
    erw linear_map.comp_apply,
    exact direct_sum.to_module_lof R i z },
  { intros z w hz hw,
    erw linear_map.map_add,
    rw linear_map.map_add,
    erw [hz, hw],
    refl },
end

def quot_pi_equiv {ι : Type v} [decidable_eq ι] (M : ι → Type u) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π i, submodule R (M i)) :
  direct_sum ι (λ i, (p i).quotient) ≃ₗ[R] (submodule.pi R M p).quotient :=
linear_equiv.of_linear (quot_pi_to_quot R M p) (quot_to_quot_pi R M p)
(linear_map.ext $ quot_pi_to_quot_left_inv R M p)
(linear_map.ext $ quot_pi_to_quot_right_inv R M p)

lemma quot_pi_equiv_apply {ι : Type v} [decidable_eq ι]
  (M : ι → Type u) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π i, submodule R (M i)) (i : ι) (x : M i) :
  quot_pi_equiv R M p (direct_sum.lof R ι _ i ((p i).mkq x)) =
    (submodule.pi R M p).mkq (direct_sum.lof R ι _ i x) :=
begin
  erw [linear_equiv.of_linear_apply, direct_sum.to_module_lof, (p i).liftq_apply],
end

lemma quot_pi_equiv_symm_apply {ι : Type v} [decidable_eq ι]
  (M : ι → Type u) [Π i, add_comm_group (M i)]
  [Π i, module R (M i)] (p : Π i, submodule R (M i)) (i : ι) (x : M i) :
  (quot_pi_equiv R M p).symm ((submodule.pi R M p).mkq (direct_sum.lof R ι _ i x)) =
    (direct_sum.lof R ι _ i ((p i).mkq x)) :=
begin
  erw linear_equiv.of_linear_symm_apply,
  simp only [submodule.liftq_apply, submodule.mkq_apply],
  ext j,
  rcases classical.em (i = j) with ⟨rfl, hij⟩,
  { erw dfinsupp.single_eq_same,
    show direct_sum.map_range R (λ (i : ι), (p i).mkq)
      (direct_sum.lof R ι (λ (i : ι), M i) i x) i = _,
    rw direct_sum.map_range_apply,
    erw dfinsupp.single_eq_same,
    refl },
  { erw dfinsupp.single_eq_of_ne h,
    show direct_sum.map_range R (λ (i : ι), (p i).mkq)
      (direct_sum.lof R ι (λ (i : ι), M i) i x) j = _,
    erw [direct_sum.map_range_apply, dfinsupp.single_eq_of_ne h],
    rw linear_map.map_zero },
end

def epow_lift (f : alternating_map R M N (fin n)) :
  epow R M n →ₗ[R] N :=
(epow_ker R M n).liftq (tpow.lift R n N f) $ submodule.span_le.2
begin
  rintro x ⟨v, ⟨i, j, hv, hij⟩, rfl⟩,
  erw linear_map.mem_ker,
  rw tpow.lift_mk_apply,
  exact f.map_eq_zero_of_eq v hv hij,
end

@[simp] lemma epow_lift_mk (f : alternating_map R M N (fin n)) {v : fin n → M} :
  epow_lift R f (epow.mk R M n v) = f v :=
tpow.lift_mk_apply n f.to_multilinear_map v

variables (M)

def ealg_ker : submodule R (talg R M) :=
@submodule.pi R _ ℕ (tpow R M) _ _ (epow_ker R M)

lemma ealg_ker_eq : ealg_ker R M =
  submodule.span R (set.Union (λ n, talg_mk R M '' exists_same M n)) :=
begin
  unfold ealg_ker,
  rw pi_eq_span,
  unfold epow_ker,
  rw submodule.span_Union,
  ext,
  simp only [submodule.span_image, submodule.map_coe, submodule.span_eq],
  rw submodule.supr_eq_span,
  split,
  { intro h,
    refine submodule.span_le.2 _ h,
    intros i hi,
    rw set.mem_Union at *,
    rcases hi with ⟨j, ⟨z, hzm, hz⟩⟩,
    rw ←hz,
    suffices : (submodule.span R (⇑(tpow.mk' R M j) '' exists_same M j)).map
      (direct_sum.lof R ℕ (tpow R M) j) ≤
        (submodule.span R (⋃ (n : ℕ), talg_mk R M '' exists_same M n)),
    from this (submodule.mem_map_of_mem hzm),
    rw submodule.map_span,
    refine submodule.span_mono _,
    rw set.image_image,
    exact set.subset_Union _ j },
  { intro h,
    refine submodule.span_mono _ h,
    intros y hy,
    rw set.mem_Union at hy,
    rcases hy with ⟨j, z, hzm, hz⟩,
    rw set.mem_Union,
    use j,
    rw submodule.map_span,
    refine submodule.subset_span _,
    rw [set.image_image, ←hz],
    exact set.mem_image_of_mem _ hzm },
end

lemma antisymm_of_square_eq_zero {ι : Type v} [add_comm_monoid ι] {S : Type u} [ring S]
  (f : ι →+ S) (h : ∀ x : ι, f x * f x = 0) (x y : ι) :
  f x * f y = -(f y * f x) :=
begin
  refine add_eq_zero_iff_eq_neg.1 _,
  suffices : (f x + f y) * (f x + f y) = 0, by
      simpa [h, mul_add, add_mul],
  rw ←f.map_add,
  exact h _,
end

lemma of_fn_prod_add {ι : Type v} [add_comm_monoid ι] {S : Type u} [ring S]
  (f : ι →+ S) {n : ℕ} (v : fin n → ι) {x y : ι} :
  (list.of_fn (f ∘ fin.cons x v)).prod + (list.of_fn (f ∘ fin.cons y v)).prod =
    (list.of_fn (f ∘ fin.cons (x + y) v)).prod :=
begin
  simp only [fin.comp_cons, list.of_fn_succ, list.prod_cons],
  convert (add_mul _ _ _).symm,
  { ext z,
    simp only [fin.cons_succ] },
  { simp only [fin.cons_zero, f.map_add] },
  { ext z,
    simp only [fin.cons_succ] },
end

lemma neg_one_pow_commutes {S : Type u} [ring S] {n : ℕ} (x : S) :
  (-1 : S) ^ n * x = x * (-1 : S) ^ n :=
begin
    cases neg_one_pow_eq_or n,
    rw [h, mul_one, one_mul],
    rw h,
    simp only [neg_mul_eq_neg_mul_symm, mul_one, one_mul, mul_neg_eq_neg_mul_symm],
end

lemma swap_prod {ι : Type v} [add_comm_monoid ι] {S : Type u} [ring S]
  (f : ι →+ S) (h : ∀ x : ι, f x * f x = 0) {n : ℕ} (v : fin n.succ → ι) {x : ι} :
  (list.of_fn (f ∘ fin.cons x v)).prod =
    (-1 : S) ^ (n.succ) * (list.of_fn (f ∘ fin.snoc v x)).prod :=
begin
  revert v,
  induction n with n hn,
  { intros,
    simp only [neg_mul_eq_neg_mul_symm, mul_one, one_mul, fin.cons_zero, list.of_fn_zero,
      function.comp_app, pow_one, fin.cons_succ, list.of_fn_succ, list.prod_cons, list.prod_nil],
    exact antisymm_of_square_eq_zero f h _ _ },
  { intros,
    conv_rhs {rw list.of_fn_succ},
    rw list.prod_cons,
    have huh : (λ (i : fin n.succ.succ), (f ∘ fin.snoc v x) i.succ) =
      f ∘ (fin.snoc (fin.tail v) x) :=
    begin
      ext i,
      simp only [function.comp_app],
      congr' 1,
      rcases classical.em (i = fin.last n.succ) with ⟨rfl, hi⟩,
      { erw [fin.snoc_last, fin.snoc_last] },
      { have : i = fin.cast_succ ⟨i, by
          contrapose h_1; rw not_not; exact fin.eq_last_of_not_lt h_1⟩ := fin.ext (rfl),
        rw [this, fin.snoc_cast_succ, ←fin.cast_succ_fin_succ, fin.snoc_cast_succ],
        refl },
    end,
    simp only [function.comp_app],
    rw [huh, pow_succ, mul_assoc, ←mul_assoc ((-1 : S) ^ n.succ), neg_one_pow_commutes,
       mul_assoc, ←hn (fin.tail v), list.of_fn_succ, list.prod_cons,
       function.comp_app, fin.cons_zero],
    show _ = (-1) * (f (v 0) * _),
    rw [list.of_fn_succ, list.prod_cons, function.comp_app, fin.cons_succ],
    conv_rhs {rw list.of_fn_succ},
    rw [list.prod_cons, function.comp_app, fin.cons_zero, ←mul_assoc,
        antisymm_of_square_eq_zero f h, ←neg_one_mul, mul_assoc, mul_assoc],
    congr,
    ext,
    simp only [function.comp_app, fin.cons_succ],
    refl },
end

lemma list.swap_prod {ι : Type v} [add_comm_monoid ι] {S : Type u} [ring S]
  (f : ι →+ S) (h : ∀ x : ι, f x * f x = 0) (v : list ι) (hv : v ≠ []) {x : ι} :
   (f x :: list.map f v).prod = (-1 : S) ^ v.length * (list.map f v ++ [f x]).prod :=
begin
  induction v with y t ht,
  { exact false.elim (hv rfl) },
  { intros,
    rcases classical.em (t = []) with ⟨rfl, ht0⟩,
    { simp only [neg_mul_eq_neg_mul_symm, mul_one, one_mul, list.length, pow_one,
        list.prod_cons, list.prod_nil, list.singleton_append, list.map],
      exact antisymm_of_square_eq_zero f h _ _ },
    { intros,
      conv_rhs {rw list.map_cons},
      rw [list.prod_cons, list.cons_append, list.prod_cons, list.length_cons, pow_succ,
          mul_assoc, ←mul_assoc ((-1 : S) ^ t.length), neg_one_pow_commutes, mul_assoc,
          ←ht h_1, list.prod_cons, list.map_cons, list.prod_cons, ←mul_assoc,
          antisymm_of_square_eq_zero f h],
      simp only [neg_mul_eq_neg_mul_symm, one_mul, neg_inj, mul_assoc] }},
end

instance : subsingleton (equiv.perm (fin 0)) :=
⟨λ x y, by {ext i, exact fin.elim0 i}⟩

lemma swap_zero_eq {n : ℕ} (σ : equiv.perm (fin n.succ)) :
  (equiv.swap 0 (σ 0) * σ) 0 = 0 :=
begin
  simp only [equiv.swap_apply_right, function.comp_app, equiv.perm.coe_mul],
end

lemma perm_succ_subtype_cond {n : ℕ} {σ : equiv.perm (fin n.succ)}
  (h : σ 0 = 0) (x : fin n.succ) :
  x ∈ set.range (@fin.succ n) ↔ σ x ∈ set.range (@fin.succ n) :=
⟨λ ⟨y, hy⟩, ⟨fin.pred (σ x) $ λ h0, by rw [←hy, ←h] at h0;
  exact fin.succ_ne_zero _ (σ.injective h0), fin.succ_pred _ _⟩,
λ ⟨y, hy⟩, ⟨x.pred $ λ h0, by rw [h0, h] at hy;
  exact fin.succ_ne_zero _ hy, fin.succ_pred _ _⟩⟩

lemma perm_ne_zero_of_succ {n : ℕ} (σ : equiv.perm (fin n.succ)) (h : σ 0 = 0) (x : fin n) :
  σ x.succ ≠ 0 :=
λ h0, by rw ←h at h0; exact fin.succ_ne_zero _ (σ.injective h0)

def perm_succ_subtype {n : ℕ} (σ : equiv.perm (fin n.succ)) (h : σ 0 = 0) :
  equiv.perm (set.range (fin.succ)) :=
equiv.perm.subtype_perm σ $ perm_succ_subtype_cond h

lemma perm_succ_subtype_prop {n : ℕ} (σ : equiv.perm (fin n.succ)) (h : σ 0 = 0) (x)
  (hx : σ x ≠ x) : x ∈ set.range (@fin.succ n) :=
begin
  use x.pred (λ h0, hx $ by rw h0; exact h),
  exact fin.succ_pred _ _,
end

open_locale classical

noncomputable def perm_succ_res {n : ℕ} (σ : equiv.perm (fin n.succ)) (h : σ 0 = 0) :
  equiv.perm (fin n) :=
equiv.perm_congr (equiv.of_injective _ (fin.succ_injective n)).symm
(perm_succ_subtype σ h)

lemma of_succ_injective_apply {n : ℕ} (x : fin n) :
  ((equiv.of_injective _ (fin.succ_injective n)) x : fin n.succ) = x.succ :=
rfl

lemma of_succ_injective_symm_apply {n : ℕ} (x : fin n) :
  (equiv.of_injective _ (fin.succ_injective n)).symm ⟨x.succ, set.mem_range_self _⟩ = x :=
begin
  symmetry,
  rw equiv.eq_symm_apply,
  refl,
end

lemma of_succ_injective_symm_succ {n : ℕ} (x : set.range (@fin.succ n)) :
  ((equiv.of_injective _ (fin.succ_injective n)).symm x).succ = x :=
begin
  rcases x.2 with ⟨y, hy⟩,
  rw subtype.val_eq_coe at hy,
  rw ←hy,
  congr,
  symmetry,
  rw equiv.eq_symm_apply,
  ext,
  rw ←hy,
  refl,
end


lemma perm_res_sign {n : ℕ} (σ : equiv.perm (fin n.succ)) (h : σ 0 = 0) :
  equiv.perm.sign (perm_succ_res σ h) = equiv.perm.sign σ :=
begin
  rw equiv.perm.sign_eq_sign_of_equiv (perm_succ_res σ h) (perm_succ_subtype σ h)
    (equiv.of_injective _ (fin.succ_injective n)),
  convert equiv.perm.sign_subtype_perm σ (perm_succ_subtype_cond h)
    (perm_succ_subtype_prop σ h),
  intro x,
  unfold perm_succ_subtype perm_succ_res,
  simp only [equiv.of_injective_apply, equiv.symm_symm, equiv.perm_congr_apply],
  exact equiv.apply_symm_apply (equiv.of_injective _ (fin.succ_injective n)) _,
end

lemma subtype_perm_apply {α : Type u} (f : equiv.perm α) {p : α → Prop}
  (h : ∀ (x : α), p x ↔ p (f x)) (x : subtype p) :
  f.subtype_perm h x = ⟨f (x : α), (h x).1 x.2⟩ :=
rfl

lemma swap_mul_swap_of_ne {ι : Type v} [decidable_eq ι] (i j k l : ι)
  (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
  (equiv.swap i j) * (equiv.swap k l) = (equiv.swap k l) * (equiv.swap i j) :=
begin
  rw equiv.swap_mul_eq_mul_swap (equiv.swap k l),
  congr,
  rw [equiv.swap_inv, equiv.swap_apply_of_ne_of_ne hik hil],
  rw [equiv.swap_inv, equiv.swap_apply_of_ne_of_ne hjk hjl],
end

lemma tail_comp_perm_succ_res_apply {ι : Type v} {n : ℕ}
  (σ : equiv.perm (fin n.succ)) (h : σ 0 = 0)
  (v : fin n.succ → ι) {m : fin n} : fin.tail v (perm_succ_res σ h m) = v (σ m.succ) :=
begin
  unfold fin.tail,
  erw of_succ_injective_symm_succ,
  refl,
end

lemma tail_comp_perm_succ_res {ι : Type v} {n : ℕ} (σ : equiv.perm (fin n.succ)) (h : σ 0 = 0)
  (v : fin n.succ → ι) {m : fin n} : fin.tail v ∘ perm_succ_res σ h = v ∘ σ ∘ fin.succ :=
begin
  ext,
  exact tail_comp_perm_succ_res_apply _ h _,
end

lemma take_drop_prod {S : Type u} [ring S] (l : list S) (n : ℕ) :
  l.prod = (l.take n).prod * (l.drop n).prod :=
begin
  revert n,
  induction l with x t ht,
  { intro n,
    simp only [list.take_nil, mul_one, list.drop_nil, list.split_at_eq_take_drop, list.prod_nil] },
  { intro n,
    induction n with n hn,
    simp only [one_mul, list.take_zero, list.split_at_eq_take_drop, list.prod_nil, list.drop],
    rw [list.prod_cons, @ht n, ←mul_assoc],
    congr' 1,
    rw ←list.prod_cons,
    congr },
end

lemma take_of_eq_succ {ι : Type v} {m n : ℕ} (v : fin n → ι) (h : 0 < n) :
  (list.of_fn v).take m.succ =
    v (⟨0, h⟩) :: (list.of_fn (fin.tail $ v ∘ fin.cast (nat.succ_pred_eq_of_pos h))).take m :=
begin
  rw ←list.take_cons,
  congr,
  convert list.of_fn_succ _,
  { exact (nat.succ_pred_eq_of_pos h).symm },
  { rw fin.heq_fun_iff (nat.succ_pred_eq_of_pos h).symm,
    intro i,
    cases i,
    refl },
  { refl },
end

lemma fin.nat_succ_eq_succ {n : ℕ} (m : fin n) :
  (m.succ : ℕ) = nat.succ m :=
begin
  simp only [fin.coe_succ]
end

lemma drop_eq_cons {ι : Type v} (v : list ι) {n : ℕ} (h : n < v.length) :
  v.drop n = v.nth_le n h :: v.drop n.succ :=
begin
  revert n h,
  induction v with x t ht,
  { intros,
    simp only [list.drop_nil],
    exact nat.not_lt_zero _ h },
  { intros,
    rcases classical.em (n = 0) with ⟨rfl, h0⟩,
    { refl },
    { have := @ht (nat.pred n),
      have H : list.drop n (x :: t) = list.drop n.pred t := by
        rw ←nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero h_1); refl,
      rw H,
      have ffs : n.pred < t.length := by
        rw ←nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero h_1) at h; exact nat.lt_of_succ_lt_succ h,
      rw this ffs,
      simp only [list.drop],
      split,
      show (x :: t).nth_le n.pred.succ (nat.succ_lt_succ ffs) = _,
      congr,
      { rw nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero h_1) },
      { rw nat.succ_pred_eq_of_pos (nat.pos_of_ne_zero h_1) }}},
end

lemma drop_of_fn_eq_cons {ι : Type v} {n : ℕ} (v : fin n → ι) (m : fin n) :
  (list.of_fn v).drop m = v m :: (list.of_fn v).drop m.succ :=
begin
  have := drop_eq_cons (list.of_fn v) (show (m : ℕ) < (list.of_fn v).length, by
    rw list.length_of_fn; exact m.2),
  rw [this, list.nth_le_of_fn'],
  congr,
  ext,
  refl,
  rw fin.nat_succ_eq_succ,
end

variables {R M}

lemma submodule.sum_mem' {ι : Type v} {t : multiset ι} {f : ι → M} :
  (∀c∈t, f c ∈ p) → (multiset.map f t).sum ∈ p :=
λ H, p.to_add_submonoid.multiset_sum_mem (multiset.map f t) $ λ x hx, by
  rcases multiset.mem_map.1 hx with ⟨y, hmy, rfl⟩; exact H y hmy

lemma submodule.sum_smul_mem' {ι : Type v} {t : multiset ι} {f : ι → M} (r : ι → R)
    (hyp : ∀ c ∈ t, f c ∈ p) : (multiset.map (λ i, r i • f i) t).sum ∈ p :=
submodule.sum_mem' (λ i hi, submodule.smul_mem  _ _ (hyp i hi))

lemma talg_mk_mul_mem (x : talg R M) {n : ℕ} {i : fin n → M} (h : i ∈ exists_same M n) :
  talg_mk R M i * x ∈ ealg_ker R M :=
begin
  rcases h with ⟨a, b, hi, hab⟩,
  refine direct_sum.linduction_on R x _ _ _,
  { rw mul_zero, exact submodule.zero_mem _ },
  { intros j y,
    rcases exists_sum_of_tpow R M y with ⟨s, rfl⟩,
    rw [map_sum, multiset.mul_sum, multiset.map_map],
    refine submodule.sum_mem' _,
    intros c hc,
    rw [function.comp_app, linear_map.map_smul, algebra.mul_smul_comm],
    refine submodule.smul_mem _ _ _,
    erw mul_apply,
    intro k,
    rcases classical.em (k = n + j) with ⟨rfl, hk⟩,
    { erw direct_sum.lof_apply,
    refine submodule.subset_span (set.mem_image_of_mem _ _),
    use [fin.cast_add j a, fin.cast_add j b],
    split,
      { convert hi,
        { convert fin.append_apply_fst _ _ _ _ _,
          { ext,
            refl },
          { exact a.2 }},
        { convert fin.append_apply_fst _ _ _ _ _,
          { ext,
            refl },
          { exact b.2 }}},
      { contrapose! hab,
        ext,
        rw fin.ext_iff at hab,
        exact hab }},
    { erw dfinsupp.single_eq_of_ne (ne.symm h),
      exact submodule.zero_mem _ }},
  { intros X Y HX HY,
    rw mul_add,
    exact submodule.add_mem _ HX HY },
end

lemma mul_talg_mk_mem (x : talg R M) {n : ℕ} {i : fin n → M} (h : i ∈ exists_same M n) :
  x * talg_mk R M i ∈ ealg_ker R M :=
begin
  rcases h with ⟨a, b, hi, hab⟩,
  refine direct_sum.linduction_on R x _ _ _,
  { rw zero_mul, exact submodule.zero_mem _ },
  { intros j y,
    rcases exists_sum_of_tpow R M y with ⟨s, rfl⟩,
    rw [map_sum, multiset.sum_mul, multiset.map_map],
    refine submodule.sum_mem' _,
    intros c hc,
    rw [function.comp_app, linear_map.map_smul, algebra.smul_mul_assoc],
    refine submodule.smul_mem _ _ _,
    erw mul_apply,
    intro k,
    rcases classical.em (k = j + n) with ⟨rfl, hk⟩,
    erw direct_sum.lof_apply,
    refine submodule.subset_span (set.mem_image_of_mem _ _),
    use [fin.nat_add j a, fin.nat_add j b],
    split,
    { convert hi,
      { rw fin.append_apply_snd,
        simp only [nat.add_sub_cancel_left, fin.coe_nat_add, fin.eta],
        { simp only [add_lt_iff_neg_left, not_lt, zero_le, fin.coe_nat_add] }},
      { rw fin.append_apply_snd,
        simp only [nat.add_sub_cancel_left, fin.coe_nat_add, fin.eta],
        { simp only [add_lt_iff_neg_left, not_lt, zero_le, fin.coe_nat_add] }}},
    { contrapose! hab,
      ext,
      rw fin.ext_iff at hab,
      exact nat.add_left_cancel hab },
    erw dfinsupp.single_eq_of_ne (ne.symm h),
    exact submodule.zero_mem _ },
  { intros X Y HX HY,
    rw add_mul,
    exact submodule.add_mem _ HX HY },
end

lemma mul_right_mem (x : talg R M) : (ealg_ker R M).map (mul R M x) ≤ ealg_ker R M :=
begin
  rw [ealg_ker_eq, submodule.map_span, submodule.span_le],
  rintros y ⟨Y, hYm, hY⟩,
  rw set.mem_Union at hYm,
  rcases hYm with ⟨i, z, hzm, hz⟩,
  rw [←hY, ←hz, ←ealg_ker_eq],
  exact mul_talg_mk_mem _ hzm,
end

lemma mul_right_mem_apply {x y : talg R M} (hy : y ∈ ealg_ker R M) : x * y ∈ ealg_ker R M :=
mul_right_mem x ⟨y, hy, rfl⟩

lemma mul_left_mem (x : talg R M) : (ealg_ker R M).map ((mul R M).flip x) ≤ ealg_ker R M :=
begin
  rw [ealg_ker_eq, submodule.map_span, submodule.span_le],
  rintros y ⟨Y, hYm, hY⟩,
  rw set.mem_Union at hYm,
  rcases hYm with ⟨i, z, hzm, hz⟩,
  rw [←hY, ←hz, ←ealg_ker_eq],
  exact talg_mk_mul_mem _ hzm,
end

lemma mul_left_mem_apply {x y : talg R M} (hy : y ∈ ealg_ker R M) : y * x ∈ ealg_ker R M :=
mul_left_mem x ⟨y, hy, rfl⟩

variables (R M)

def ealg_mul_aux (x : talg R M) : talg R M →ₗ[R] (ealg_ker R M).quotient :=
(ealg_ker R M).mkq.comp $ mul R M x

variables {R M}

lemma ealg_mul_aux_cond (x : talg R M) : ealg_ker R M ≤ (ealg_mul_aux R M x).ker :=
begin
  intros y hy,
  erw linear_map.ker_comp,
  rw submodule.ker_mkq,
  exact mul_right_mem_apply hy,
end

variables (R M)
@[reducible] def ealg := (ealg_ker R M).quotient

def ealg_mul : ealg R M →ₗ[R] ealg R M →ₗ[R] ealg R M :=
(ealg_ker R M).liftq
({ to_fun := λ x, (ealg_ker R M).liftq (ealg_mul_aux R M x) $
     ealg_mul_aux_cond x,
  map_add' := λ x y,
    begin
      ext z,
      refine quotient.induction_on' z _,
      intro w,
      unfold ealg_mul_aux,
      simp only [linear_map.add_apply, linear_map.map_add, linear_map.comp_add],
      refl,
    end,
  map_smul' := λ r x,
    begin
      ext z,
      refine quotient.induction_on' z _,
      intro w,
      unfold ealg_mul_aux,
      simp only [linear_map.smul_apply, linear_map.map_smul, linear_map.comp_add],
      refl,
    end }) $
  begin
    intros x hx,
    rw linear_map.mem_ker,
    ext y,
    rw linear_map.zero_apply,
    refine quotient.induction_on' y _,
    intro z,
    simp only [submodule.quotient.mk'_eq_mk, submodule.liftq_apply, linear_map.coe_mk],
    unfold ealg_mul_aux,
    rw linear_map.comp_apply,
    erw submodule.quotient.mk_eq_zero,
    exact mul_left_mem_apply hx,
  end

instance ealg.has_mul : has_mul (ealg R M) :=
⟨λ x, ealg_mul R M x⟩

lemma ealg.mul_def {x y : ealg R M} : ealg_mul R M x y = x * y := rfl

def ealg_mk {n : ℕ} (f : fin n → M) : ealg R M :=
(ealg_ker R M).mkq $ talg_mk R M f

lemma ealg_mk_def {n : ℕ} (f : fin n → M) :
  ealg_mk R M f = (ealg_ker R M).mkq (direct_sum.lof R ℕ (tpow R M) n (tpow.mk' _ _ n f)) :=
rfl

instance : has_one (ealg R M) :=
⟨(ealg_ker R M).mkq 1⟩

lemma ealg_mul_apply {m n : ℕ} (f : fin m → M) (g : fin n → M) :
  ealg_mk R M f * ealg_mk R M g = ealg_mk R M (fin.append rfl f g) :=
begin
  rw ←ealg.mul_def,
  erw [submodule.liftq_apply, linear_map.comp_apply],
  -- Amelia -- congr was taking forever here (making CI fail on your branch);
  -- I did some `show_term` stuff to find out what it was actually doing
  refine congr (congr_arg coe_fn (eq.refl (ealg_ker R M).mkq)) _,
  rw [mul_def, mul_apply]
end

@[simp] lemma zero_eq_ealg_mk : ealg_mk R M (λ i : fin 1, 0) = 0 :=
begin
  unfold ealg_mk,
  rw [zero_eq_mk, linear_map.map_zero],
end

@[simp] lemma one_eq_ealg_mk : ealg_mk R M (default (fin 0 → M)) = 1 :=
rfl

lemma ealg.mul_zero (x : ealg R M) : x * 0 = 0 :=
linear_map.map_zero _

lemma ealg.zero_mul (x : ealg R M) : 0 * x = 0 :=
linear_map.map_zero₂ _ _

lemma ealg.mul_add (x y z : ealg R M) : x * (y + z) = x * y + x * z :=
linear_map.map_add _ _ _

lemma ealg.add_mul (x y z : ealg R M) : (x + y) * z = x * z + y * z :=
linear_map.map_add₂ _ _ _ _

lemma ealg.mul_sum (s : multiset (ealg R M)) (x : ealg R M) :
  x * s.sum = (s.map (ealg_mul _ _ x)).sum :=
map_sum' _ _ _

lemma ealg.smul_assoc (r : R) (x y : ealg R M) :
  (r • x) * y = r • (x * y) :=
linear_map.map_smul₂ _ _ _ _

lemma ealg.mul_assoc (x y z : ealg R M) :
  x * y * z = x * (y * z) :=
begin
  refine quotient.induction_on' x _,
  refine quotient.induction_on' y _,
  refine quotient.induction_on' z _,
  intros a b c,
  rw [←ealg.mul_def, ←ealg.mul_def],
  erw [submodule.liftq_apply (ealg_ker R M) (ealg_ker R M).mkq,
    submodule.liftq_apply (ealg_ker R M) (ealg_ker R M).mkq],
  rw [mul_def, mul_def, talg.mul_assoc],
  refl,
  { rw submodule.ker_mkq,
    exact le_refl _ },
  { rw submodule.ker_mkq,
    exact le_refl _ },
end

lemma ealg.mul_one (x : ealg R M) : x * 1 = x :=
begin
  refine quotient.induction_on' x _,
  intro y,
  rw [←one_eq_ealg_mk, ←ealg.mul_def],
  erw submodule.liftq_apply,
  unfold ealg_mul_aux,
  rw [one_eq_mk, linear_map.comp_apply, mul_def, talg.mul_one],
  refl,
end

lemma ealg.one_mul (x : ealg R M) : 1 * x = x :=
begin
  refine quotient.induction_on' x _,
  intro y,
  rw [←one_eq_ealg_mk, ←ealg.mul_def],
  erw submodule.liftq_apply,
  unfold ealg_mul_aux,
  rw [one_eq_mk, linear_map.comp_apply, mul_def, talg.one_mul],
  refl,
end

instance ealg.monoid : monoid (ealg R M) :=
{ mul_assoc := ealg.mul_assoc _ _,
  one := 1,
  one_mul := ealg.one_mul _ _,
  mul_one := ealg.mul_one _ _, ..ealg.has_mul _ _ }

instance : ring (ealg R M) :=
{ left_distrib := by exact ealg.mul_add R M,
  right_distrib := by exact ealg.add_mul R M,
  ..submodule.quotient.add_comm_group _, ..ealg.monoid _ _ }

def talg.to_ealg_ring_hom : talg R M →+* ealg R M :=
{ to_fun := (ealg_ker R M).mkq,
  map_one' := rfl,
  map_mul' := λ x y, by rw ←ealg.mul_def; erw submodule.liftq_apply; refl,
  map_zero' := rfl,
  map_add' := linear_map.map_add _ }

def ealg.of_scalar : R →+* (ealg R M) :=
{ map_one' := rfl,
  map_mul' := λ x y,
    begin
      rw ←ealg.mul_def,
      erw submodule.liftq_apply,
      unfold ealg_mul_aux,
      show quotient.mk' _ = quotient.mk' _,
      congr,
      exact (talg.of_scalar R M).map_mul x y
    end,
  map_zero' := by convert linear_map.map_zero _,
  map_add' := λ x y, by convert linear_map.map_add _ x y,
  ..(ealg_ker R M).mkq.comp (direct_sum.lof R ℕ (tpow R M) 0) }

lemma ealg.of_scalar_apply {x : R} :
  ealg.of_scalar R M x = (ealg_ker R M).mkq (talg.of_scalar R M x) := rfl

lemma ealg.smul_one (r : R) : r • (1 : ealg R M) = ealg.of_scalar R M r :=
begin
  rw [ealg.of_scalar_apply, ←talg.smul_one, linear_map.map_smul],
  refl,
end

lemma ealg_commutes (r : R) (x : ealg R M) :
  ealg.of_scalar R M r * x = x * ealg.of_scalar R M r :=
begin
  rw ealg.of_scalar_apply,
  refine quotient.induction_on' x _,
  intro y,
  erw [←(talg.to_ealg_ring_hom R M).map_mul, algebra.commutes r y],
  rw ring_hom.map_mul,
  refl,
end

instance : algebra R (ealg R M) :=
{ smul := (•),
  to_fun := ealg.of_scalar R M,
  map_one' := ring_hom.map_one _,
  map_mul' := ring_hom.map_mul _,
  map_zero' := ring_hom.map_zero _,
  map_add' := ring_hom.map_add _,
  commutes' := ealg_commutes R M,
  smul_def' := λ r x,
    begin
      simp only,
      rw [←ealg.smul_one R M r, ←ealg.mul_def, linear_map.map_smul₂, ealg.mul_def, one_mul],
    end }

def talg.to_ealg : talg R M →ₐ[R] ealg R M :=
{ commutes' := λ r, rfl, ..talg.to_ealg_ring_hom R M }

@[simp] lemma talg.to_ealg_apply (x) :
  talg.to_ealg R M x = quotient.mk' x := rfl

lemma multiset.sum_eq_zero {ι : Type v} [add_comm_monoid ι] (s : multiset ι) :
  (∀ (x : ι), x ∈ s → x = 0) → s.sum = 0 :=
begin
  refine multiset.induction_on s _ _,
  { intro,
    rw multiset.sum_zero },
  { intros a s hs,
    rw multiset.sum_cons,
    intro h,
    rw [hs (λ x hx, h x (multiset.mem_cons_of_mem hx)),
      h a (multiset.mem_cons_self a s), zero_add] },
end

lemma pred_sum {C : M → Prop} (H0 : C 0)
  (Hadd : ∀ x y, C x → C y → C (x + y))
  {s : multiset M} (h : ∀ x ∈ s, C x) :
  C s.sum :=
begin
  revert h,
  refine multiset.induction_on s _ _,
  { intros,
    rw multiset.sum_zero,
    exact H0 },
  { intros a t ht hat,
    rw multiset.sum_cons,
    refine Hadd _ _ _ _,
    { exact hat a (multiset.mem_cons_self a t)},
    { exact ht (λ x hx, hat x $ multiset.mem_cons_of_mem hx) }},
end

lemma talg.induction_on {C : talg R M → Prop}
  (H0 : C 0) (H : ∀ {n} (i : fin n → M), C (talg_mk R M i))
  (Hadd : ∀ x y, C x → C y → C (x + y))
  (Hsmul : ∀ (r : R) x, C x → C (r • x)) (x : talg R M) :
  C x :=
begin
  refine direct_sum.linduction_on R x H0 _ Hadd,
  intros i x,
  rcases exists_sum_of_tpow R M x with ⟨s, rfl⟩,
  rw map_sum,
  refine pred_sum _ H0 Hadd _,
  intros y hy,
  rw multiset.mem_map at hy,
  rcases hy with ⟨z, hzm, hz⟩,
  rw linear_map.map_smul at hz,
  rw ←hz,
  refine Hsmul _ _ _,
  exact H _,
end

lemma talg.lift_comp_ι {A : Type u} [ring A] [algebra R A]
  (f : M →ₗ[R] A) : (talg.lift R M f).to_linear_map.comp (ι R M) = f :=
by ext; exact talg.lift_ι_apply _ _ _

lemma wtf {α β γ δ: Type u} (f : α → β) (g : β → γ) (h : γ → δ) :
  (h ∘ g) ∘ f = h ∘ (g ∘ f) :=
rfl

lemma ealg.lift_cond {A : Type u} [ring A] [algebra R A]
  (f : M →ₗ[R] A) (h : ∀ m, f m * f m = 0) :
  ealg_ker R M ≤ (talg.lift R M f).to_linear_map.ker :=
begin
  rw [ealg_ker_eq, submodule.span_le],
  intros x hx,
  rw set.mem_Union at hx,
  rcases hx with ⟨i, y, ⟨j, k, hf, hjk⟩, hy⟩,
  erw linear_map.mem_ker,
  rw [←hy, talg_mk_prod, alg_prod_apply],
  erw alg_hom.map_prod',
  rw [list.of_fn_eq_map, list.map_map, ←list.of_fn_eq_map],
  have : talg.lift R M f ∘ ι R M = (talg.lift R M f).to_linear_map.comp (ι R M) :=
    by ext; refl,
  show (list.of_fn (((talg.lift R M f) ∘ ι R M) ∘ y)).prod = 0,
  rw [this, talg.lift_comp_ι],
  exact prod_eq_zero_map f.to_add_monoid_hom h _ _ _ hjk hf,
end

def ealg.lift {A : Type u} [ring A] [algebra R A]
  (f : M →ₗ[R] A) (h : ∀ m, f m * f m = 0) :
  ealg R M →ₐ[R] A :=
{ to_fun := (ealg_ker R M).liftq (talg.lift R M f).to_linear_map $
    ealg.lift_cond R M f h,
  map_one' := by erw [←one_eq_ealg_mk, submodule.liftq_apply, one_eq_mk, alg_hom.map_one],
  map_mul' := λ x y,
    begin
      refine quotient.induction_on' x _,
      refine quotient.induction_on' y _,
      intros z w,
      erw [submodule.liftq_apply, alg_hom.map_mul],
      refl,
    end,
  map_zero' := linear_map.map_zero _,
  map_add' := linear_map.map_add _,
  commutes' := λ r, by erw [submodule.liftq_apply, (talg.lift R M f).commutes] }

@[simp] lemma ealg.lift_ι_apply {A : Type u} [ring A] [algebra R A]
  (f : M →ₗ[R] A) (h : ∀ m, f m * f m = 0) (x : M) :
  ealg.lift R M f h ((ealg_ker R M).mkq (ι R M x)) = f x :=
talg.lift_ι_apply R M f

def to_ext_alg : ealg R M →ₐ[R] exterior_algebra R M :=
ealg.lift R M (exterior_algebra.ι R) exterior_algebra.ι_square_zero

lemma ealg_ι_square_zero (m : M) :
  (ealg_ker R M).mkq (ι R M m) * (ealg_ker R M).mkq (ι R M m) = 0 :=
begin
  rw ι_eq_mk,
  erw ←ealg_mk_def,
  rw ealg_mul_apply,
  erw submodule.quotient.mk_eq_zero,
  rw ealg_ker_eq,
  refine submodule.subset_span _,
  rw set.mem_Union,
  use 2,
  refine set.mem_image_of_mem _ _,
  use [0, 1],
  split,
  rw fin.append_apply_fst,
  rw fin.append_apply_snd,
  all_goals {norm_num},
end

def to_ealg : exterior_algebra R M →ₐ[R] ealg R M :=
exterior_algebra.lift R ⟨(ealg_ker R M).mkq.comp (ι R M), ealg_ι_square_zero R M⟩

local attribute [semireducible] ring_quot ring_quot.mk_alg_hom
  ring_quot.mk_ring_hom tensor_algebra.mk tensor_algebra.mk_aux exterior_algebra.ι

lemma tensor_algebra.mk_apply {n : ℕ} (v : fin n → M) :
  tensor_algebra.mk R M v = ((list.fin_range n).map (λ i, tensor_algebra.ι R (v i))).prod :=
rfl

lemma ealg_left_inverse (x : exterior_algebra R M) :
  to_ext_alg R M (to_ealg R M x) = x :=
begin
  refine quot.induction_on x _,
  intro y,
  show _ = ring_quot.mk_alg_hom R (exterior_algebra.rel R M) y,
  unfold to_ealg exterior_algebra.lift ring_quot.lift_alg_hom,
  simp only [equiv.coe_fn_mk, subtype.coe_mk, alg_hom.coe_mk],
  refine tensor_algebra.induction_on _ _ _ _ y,
  { intros n i,
    show to_ext_alg R M (tensor_algebra.lift R _ (list.prod _)) = _,
    rw [alg_hom.map_prod', alg_hom.map_prod', list.map_map, list.map_map],
    unfold to_ext_alg,
    rw [tensor_algebra.mk_apply, alg_hom.map_prod' R (ring_quot.mk_alg_hom R
      (exterior_algebra.rel R M)) (list.map (λ (i_1 : fin n), (tensor_algebra.ι R) (i i_1))
      (list.fin_range n)), list.map_map],
    congr' 2,
    ext j,
    simp only [function.comp_app, submodule.mkq_apply,
      linear_map.comp_apply, tensor_algebra.lift_ι_apply],
    erw [(ealg_ker R M).liftq_apply, submodule.liftq_apply, talg.lift_ι_apply],
    { refl },
    { exact ealg.lift_cond R M _ (ι_square_zero) },
    { exact ealg.lift_cond R M _ (ι_square_zero) }},
  { intros x y hx hy,
    simp only [hx, hy, alg_hom.map_add] },
  { intros x c hx,
    simp only [hx, alg_hom.map_smul] },
  { intros x y hx hy,
    simp only [hx, hy, alg_hom.map_mul] },
end

lemma ealg_right_inverse (x : ealg R M) :
  to_ealg R M (to_ext_alg R M x) = x :=
begin
  refine quotient.induction_on' x _,
  intro y,
  refine talg.induction_on R M _ _ _ _ y,
  { simp only [submodule.quotient.mk'_eq_mk, alg_hom.map_zero, submodule.quotient.mk_zero] },
  { intros n i,
    unfold to_ext_alg,
    rw [talg_mk_prod, alg_prod_apply, ←talg.to_ealg_apply],
    simp only [alg_hom.map_prod', list.map_map, list.of_fn_eq_map],
    congr' 2,
    ext j,
    simp only [function.comp_app],
    erw [ealg.lift_ι_apply, exterior_algebra.lift_ι_apply],
    refl },
  { intros X Y HX HY,
    show to_ealg R M (to_ext_alg R M (quotient.mk' X + quotient.mk' Y)) = _,
    simp only [HX, HY, alg_hom.map_add],
    refl },
  { intros r X hX,
    show to_ealg R M (to_ext_alg R M (r • quotient.mk' X)) = _,
    simp only [hX, alg_hom.map_smul],
    refl, }
end

def ealg_equiv : ealg R M ≃ₐ[R] exterior_algebra R M :=
alg_equiv.of_alg_hom (ealg.lift R M (exterior_algebra.ι R) exterior_algebra.ι_square_zero)
  (to_ealg R M) (alg_hom.ext $ ealg_left_inverse R M) (alg_hom.ext $ ealg_right_inverse R M)
