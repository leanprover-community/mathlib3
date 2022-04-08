import algebra.big_operators.norm_num
import data.nat.fib
import data.nat.succ_pred
import linear_algebra.basis
import ring_theory.adjoin_root
import ring_theory.power_basis

open_locale big_operators

-- TODO: generalize this so we don't assume a multiplication on `S`
-- or even no structure on `S` at all
structure times_table (ι R S : Type*)
  [semiring R] [add_comm_monoid S] [module R S] [has_mul S] :=
(basis : basis ι R S)
(table : ι → ι → ι → R)
(mul_def : ∀ i j k, basis.repr (basis i * basis j) k = table i j k)

mk_simp_attribute times_table_simps "The simpset `times_table_simps` is used by the tactic
`times_table` to reduce an expression of the form `(t : times_table).basis.repr x k` to a numeral."

section semiring
variables {ι R S : Type*} [comm_semiring R] [non_unital_non_assoc_semiring S] [module R S]
variables [smul_comm_class R S S] [is_scalar_tower R S S]

lemma times_table.coeff_mul_coeff [fintype ι] (t : times_table ι R S) (x y : ι → R) :
  t.basis.equiv_fun.symm x * t.basis.equiv_fun.symm y =
    t.basis.equiv_fun.symm (λ k, ∑ i j : ι, x i * y j * t.table i j k) :=
begin
  calc t.basis.equiv_fun.symm x * t.basis.equiv_fun.symm y
      = ∑ (i j : ι), x j • t.basis j * y i • t.basis i :
    by simp only [basis.equiv_fun_symm_apply, finset.sum_mul, finset.mul_sum]
  ... = ∑ (i j : ι), x i • t.basis i * y j • t.basis j :
    finset.sum_comm
  ... = ∑ (i j : ι), (x i * y j) • ∑ (k : ι), t.basis.repr (t.basis i * t.basis j) k • t.basis k :
    _
  ... = ∑ (i j k : ι), (x i * y j * t.basis.repr (t.basis i * t.basis j) k) • t.basis k :
    by simp only [finset.smul_sum, mul_smul]
  ... = ∑ (i k j : ι), (x i * y j * t.basis.repr (t.basis i * t.basis j) k) • t.basis k :
    finset.sum_congr rfl (λ _ _, finset.sum_comm)
  ... = ∑ (k j i : ι), (x j * y i * t.basis.repr (t.basis j * t.basis i) k) • t.basis k :
    finset.sum_comm
  ... = t.basis.equiv_fun.symm (λ k, ∑ i j : ι, x i * y j * t.table i j k) :
    by simp only [basis.equiv_fun_symm_apply, finset.sum_smul, t.mul_def],
  refine finset.sum_congr rfl (λ i _, finset.sum_congr rfl (λ j _, _)),
  simp only [finset.smul_sum, mul_smul, t.basis.sum_repr],
  simp only [← @smul_eq_mul S],
  rw [smul_comm (y j) (t.basis i) (t.basis j)],
  simp only [smul_assoc],
end

lemma times_table.unfold_mul [fintype ι] (t : times_table ι R S) (x y : S) (k : ι) :
  t.basis.repr (x * y) k =
    ∑ i j : ι, t.basis.repr x i * t.basis.repr y j * t.table i j k :=
begin
  simp only [← basis.equiv_fun_apply],
  rw [← t.basis.equiv_fun.symm_apply_apply x, ← t.basis.equiv_fun.symm_apply_apply y,
    t.coeff_mul_coeff, linear_equiv.symm_apply_apply, linear_equiv.symm_apply_apply,
    linear_equiv.apply_symm_apply]
end

@[simp] lemma linear_equiv.map_bit0 {R M N : Type*} [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]
  (f : M ≃ₗ[R] N) (x : M) : f (bit0 x) = bit0 (f x) :=
by { unfold bit0, simp only [_root_.map_add, finsupp.coe_add, pi.add_apply] }
@[simp] lemma linear_equiv.map_bit1 {R M N : Type*} [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N] [has_one M]
  (f : M ≃ₗ[R] N) (x : M) : f (bit1 x) = bit0 (f x) + f 1 :=
by { unfold bit1 bit0, simp only [_root_.map_add, finsupp.coe_add, pi.add_apply] }

noncomputable def times_table.reindex {ι' : Type*} (t : times_table ι R S) (e : ι ≃ ι') :
  times_table ι' R S :=
{ basis := t.basis.reindex e,
  table := λ i j k, t.table (e.symm i) (e.symm j) (e.symm k),
  mul_def := λ i j k, by simpa only [basis.reindex_apply, basis.reindex_repr]
    using t.mul_def (e.symm i) (e.symm j) (e.symm k) }

end semiring

/-
section ring
variables {ι R S : Type*} [comm_ring R] [comm_ring S] [algebra R S]

namespace power_basis

variables (pb : power_basis R S)

protected noncomputable def times_table : times_table (fin pb.dim) R S :=
{ basis := pb.basis,
  table := λ i j k, pb.basis.repr (pb.basis i * pb.basis j) k,
  mul_def := λ _ _ _, rfl }

@[simp] lemma times_table_apply_of_lt (i j k : fin pb.dim) (hlt : (i + j : ℕ) < pb.dim) :
  pb.times_table.table i j k = if i + j = k then 1 else 0 :=
begin
  simp only [power_basis.times_table, ← pow_add, power_basis.coe_basis],
  rw ← fin.coe_mk hlt,
  convert congr_fun (congr_arg coe_fn (pb.basis.repr_self ⟨i + j, hlt⟩)) _,
  { rw pb.coe_basis },
  ext,
  rw [fin.coe_add, nat.mod_eq_of_lt hlt, fin.coe_mk]
end

end power_basis

namespace adjoin_root

variables [nontrivial R] {f : polynomial R} (hf : f.monic)

protected noncomputable def times_table : times_table (fin f.nat_degree) R (adjoin_root f) :=
(power_basis' hf).times_table

@[simp] lemma times_table_apply (i j k : fin f.nat_degree) :
  (adjoin_root.times_table hf).table i j k =
    if (i + j : ℕ) < f.nat_degree then _ else _:=
begin
  simp only [adjoin_root.times_table, power_basis.times_table, power_basis.coe_basis,
      power_basis'_gen, ← pow_add],
end

end adjoin_root

end ring
-/

open polynomial

-- Define a new structure
-- Might just as well have been a synonym for `adjoin_root (X^2 - 3 : (adjoin_root (X^2 - 2))[X]),
-- but this shows off the general design.
@[ext]
structure sqrt_2_sqrt_3 :=
(a b c d : ℚ)

namespace sqrt_2_sqrt_3

instance : add_comm_group sqrt_2_sqrt_3 :=
{ zero := ⟨0, 0, 0, 0⟩,
  add := λ x y, ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩,
  add_comm := λ x y, by { ext : 1; apply add_comm },
  add_zero := λ x, by { ext : 1; apply add_zero },
  zero_add := λ x, by { ext : 1; apply zero_add },
  add_assoc := λ x y z, by { ext : 1; apply add_assoc },
  neg := λ x, ⟨-x.a, -x.b, -x.c, -x.d⟩,
  add_left_neg := λ x, by { ext : 1; apply add_left_neg },
  sub := λ x y, ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩ }

.

instance : module ℚ sqrt_2_sqrt_3 :=
{ smul := λ c x, ⟨c * x.a, c * x.b, c * x.c, c * x.d⟩,
  add_smul := λ c d x, by { ext : 1; apply add_mul },
  smul_add := λ c x y, by { ext : 1; apply mul_add },
  mul_smul := λ c d x, by { ext : 1; apply mul_assoc },
  one_smul := λ x, by { ext : 1; apply one_mul },
  smul_zero := λ c, by { ext : 1; apply mul_zero },
  zero_smul := λ x, by { ext : 1; apply zero_mul } }

noncomputable def basis : basis (fin 4) ℚ sqrt_2_sqrt_3 :=
basis.of_equiv_fun $
{ to_fun := λ x, ![x.a, x.b, x.c, x.d],
  inv_fun := λ x, ⟨x 0, x 1, x 2, x 3⟩,
  left_inv := λ ⟨a, b, c, d⟩, rfl,
  right_inv := λ x, by { ext i : 1, fin_cases i; simp },
  map_add' := λ ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩, by { ext i : 1, fin_cases i; refl },
  map_smul' := λ r ⟨a, b, c, d⟩, by { ext i : 1, fin_cases i; refl } }

def table : fin 4 → fin 4 → fin 4 → ℚ :=
![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]],
  ![![0, 1, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 2, 0]],
  ![![0, 0, 1, 0], ![0, 0, 0, 1], ![3, 0, 0, 0], ![0, 3, 0, 0]],
  ![![0, 0, 0, 1], ![0, 0, 2, 0], ![0, 3, 0, 0], ![6, 0, 0, 0]]]

noncomputable def mul : sqrt_2_sqrt_3 →ₗ[ℚ] sqrt_2_sqrt_3 →ₗ[ℚ] sqrt_2_sqrt_3 :=
sqrt_2_sqrt_3.basis.constr ℚ $ λ i,
sqrt_2_sqrt_3.basis.constr ℚ $ λ j,
sqrt_2_sqrt_3.basis.equiv_fun.symm (table i j)

noncomputable instance : field sqrt_2_sqrt_3 :=
{ mul := λ x y, mul x y,
  one := ⟨1, 0, 0, 0⟩,
  .. sqrt_2_sqrt_3.add_comm_group }

noncomputable instance : algebra ℚ sqrt_2_sqrt_3 :=
{ to_fun := λ c, ⟨c, 0, 0, 0⟩,
  .. sqrt_2_sqrt_3.module }

@[simp] lemma sqrt_2_sqrt_3.basis_repr (x : sqrt_2_sqrt_3) :
  ⇑(sqrt_2_sqrt_3.basis.repr x) = ![x.a, x.b, x.c, x.d] :=
rfl

noncomputable def sqrt_2_sqrt_3.times_table : times_table (fin 4) ℚ sqrt_2_sqrt_3 :=
{ basis := sqrt_2_sqrt_3.basis,
  table := sqrt_2_sqrt_3.table,
  mul_def := sorry }

@[simp, times_table_simps] -- TODO: get rid of `@[simp]`
lemma sqrt_2_sqrt_3.times_table_apply (i j k : fin 4) :
  sqrt_2_sqrt_3.times_table.table i j k =
  ![![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]],
    ![![0, 1, 0, 0], ![2, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 2, 0]],
    ![![0, 0, 1, 0], ![0, 0, 0, 1], ![3, 0, 0, 0], ![0, 3, 0, 0]],
    ![![0, 0, 0, 1], ![0, 0, 2, 0], ![0, 3, 0, 0], ![6, 0, 0, 0]]] i j k :=
rfl

@[times_table_simps] lemma repr_one (i : fin 4) :
  sqrt_2_sqrt_3.times_table.basis.repr 1 i = ![1, 0, 0, 0] i := rfl


@[simp, times_table_simps] lemma repr_mk (a b c d : ℚ) (i : fin 4) :
  sqrt_2_sqrt_3.times_table.basis.repr ⟨a, b, c, d⟩ i = ![a, b, c, d] i := rfl

def sqrt_2 : sqrt_2_sqrt_3 := ⟨0, 1, 0, 0⟩
@[times_table_simps] lemma repr_sqrt_2 (i : fin 4) :
  sqrt_2_sqrt_3.times_table.basis.repr sqrt_2 i = ![0, 1, 0, 0] i := rfl

def sqrt_3 : sqrt_2_sqrt_3 := ⟨0, 0, 1, 0⟩
@[times_table_simps] lemma repr_sqrt_3 (i : fin 4) :
  sqrt_2_sqrt_3.times_table.basis.repr sqrt_3 i = ![0, 0, 1, 0] i := rfl

@[simp]
lemma finsupp.bit0_apply {α M : Type*} [add_monoid M] (f : α →₀ M) (i : α) : (bit0 f) i = bit0 (f i) := rfl

end sqrt_2_sqrt_3

namespace tactic.times_table

open tactic

section add_comm_monoid

variables {R S ι : Type*} [comm_semiring R] [add_comm_monoid S] [module R S]
variables [has_mul S]

protected lemma eval_repr_zero (t : times_table ι R S) (k : ι) :
  t.basis.repr 0 k = 0 :=
by rw [_root_.map_zero, finsupp.zero_apply]

protected lemma eval_repr_bit0 (t : times_table ι R S) (k : ι) {e₁ : S} {e₁' e' : R}
  (e₁_eq : t.basis.repr e₁ k = e₁') (e_eq : e₁' + e₁' = e') :
  t.basis.repr (bit0 e₁) k = e' :=
by rw [bit0, _root_.map_add, finsupp.add_apply, e₁_eq, e_eq]

protected lemma eval_repr_bit1 [has_one S] (t : times_table ι R S) (k : ι) {e₁ : S} {e₁' e' o : R}
  (e₁_eq : t.basis.repr e₁ k = e₁') (one_eq : t.basis.repr 1 k = o) (e_eq : e₁' + e₁' + o = e') :
  t.basis.repr (bit1 e₁) k = e' :=
by simp only [bit1, bit0, _root_.map_add, finsupp.add_apply, e₁_eq, one_eq, e_eq]

protected lemma eval_repr_add (t : times_table ι R S) (k : ι) {e₁ e₂ : S} {e₁' e₂' e' : R}
  (e₁_eq : t.basis.repr e₁ k = e₁') (e₂_eq : t.basis.repr e₂ k = e₂') (e_eq : e₁' + e₂' = e') :
  t.basis.repr (e₁ + e₂) k = e' :=
by rw [_root_.map_add, finsupp.add_apply, e₁_eq, e₂_eq, e_eq]


end add_comm_monoid

section non_assoc_non_unital_semiring

variables {R S ι : Type*} [comm_semiring R] [non_unital_non_assoc_semiring S] [module R S]
variables [smul_comm_class R S S] [is_scalar_tower R S S]

protected lemma eval_repr_mul [fintype ι] (t : times_table ι R S) (k : ι) (e₁ e₂ : S) (e' : R)
  (eq : ∑ i j : ι, t.basis.repr e₁ i * t.basis.repr e₂ j * t.table i j k = e') :
  t.basis.repr (e₁ * e₂) k = e' :=
by rw [times_table.unfold_mul t, eq]

end non_assoc_non_unital_semiring

section semiring

variables {R S ι : Type*} [comm_semiring R] [semiring S] [algebra R S]

protected lemma eval_pow_zero (t : times_table ι R S) (k : ι) (e₁ : S) {e' : R}
  (e_eq : t.basis.repr 1 k = e') :
  t.basis.repr (e₁ ^ 0) k = e' :=
by rw [pow_zero, e_eq]

protected lemma eval_pow_one (t : times_table ι R S) (k : ι) {e₁ : S} {e' : R}
  (e_eq : t.basis.repr e₁ k = e') :
  t.basis.repr (e₁ ^ 1) k = e' :=
by rw [pow_one, e_eq]

protected lemma eval_pow_bit0 (t : times_table ι R S) (k : ι) (n : ℕ) {e₁ : S} {e' : R}
  (e_eq : t.basis.repr (e₁ ^ n * e₁ ^ n) k = e') :
  t.basis.repr (e₁ ^ (bit0 n)) k = e' :=
by rw [pow_bit0, e_eq]

protected lemma eval_pow_bit1 (t : times_table ι R S) (k : ι) (n : ℕ) {e₁ : S} {e' : R}
  (e_eq : t.basis.repr (e₁ ^ n * e₁ ^ n * e₁) k = e') :
  t.basis.repr (e₁ ^ (bit1 n)) k = e' :=
by rw [pow_bit1, e_eq]

end semiring

section ring

variables {R S ι : Type*} [comm_ring R] [ring S] [algebra R S]

protected lemma eval_repr_sub (t : times_table ι R S) (k : ι) {e₁ e₂ : S} {e₁' e₂' e' : R}
  (e₁_eq : t.basis.repr e₁ k = e₁') (e₂_eq : t.basis.repr e₂ k = e₂') (e_eq : e₁' - e₂' = e') :
  t.basis.repr (e₁ - e₂) k = e' :=
by rw [_root_.map_sub, finsupp.sub_apply, e₁_eq, e₂_eq, e_eq]

end ring

section comm_ring

variables {R S ι : Type*} [comm_ring R] [comm_ring S] [algebra R S]
end comm_ring

/-- Simplify expressions of the form `(t : times_table).basis.repr x k` using lemmas tagged
`@[times_table_simps]`. -/
meta def simp_times_table : expr → tactic (expr × expr)
| e := do
  simps ← mk_simp_set tt [`times_table_simps] [],
  (e', pf, _) ← simplify simps.1 [] e <|>
    fail!"Failed to simplify {e}, are you missing a `@[times_table_simps]` lemma?",
  pure (e', pf)

/-- Evaluate `((t : times_table _ _ _).basis.repr e) k` using `norm_num`. -/
protected meta def eval (ι R S t k : expr) : expr → tactic (expr × expr)
| `(0) := trace_error "zero" $ do
  e ← expr.of_nat R 0,
  pf ← i_to_expr ``(tactic.times_table.eval_repr_zero %%t %%k),
  pure (e, pf)
| `(bit0 %%e₁) := trace_error "bit0" $ do
  (e₁', e₁_eq) ← eval e₁,
  (e', e_eq) ← i_to_expr ``(%%e₁' + %%e₁') >>= or_refl_conv norm_num.derive,
  eq ← i_to_expr ``(tactic.times_table.eval_repr_bit0 %%t %%k %%e₁_eq %%e_eq),
  pure (e', eq)
| `(bit1 %%e₁) := trace_error "bit1" $ do
  (e₁', e₁_eq) ← eval e₁,
  (one', one_eq) ← expr.of_nat S 1 >>= eval,
  (e', e_eq) ← i_to_expr ``(%%e₁' + %%e₁' + %%one') >>= or_refl_conv norm_num.derive,
  eq ← i_to_expr ``(tactic.times_table.eval_repr_bit1 %%t %%k %%e₁_eq %%one_eq %%e_eq),
  pure (e', eq)
| `(%%e₁ + %%e₂) := trace_error "add" $ do
  (e₁', e₁_eq) ← eval e₁,
  (e₂', e₂_eq) ← eval e₂,
  (e', e_eq) ← i_to_expr ``(%%e₁' + %%e₂') >>= or_refl_conv norm_num.derive,
  eq ← i_to_expr ``(tactic.times_table.eval_repr_add %%t %%k %%e₁_eq %%e₂_eq %%e_eq),
  pure (e', eq)
| `(%%e₁ - %%e₂) := trace_error "sub" $ do
  (e₁', e₁_eq) ← eval e₁,
  (e₂', e₂_eq) ← eval e₂,
  (e', e_eq) ← i_to_expr ``(%%e₁' - %%e₂') >>= or_refl_conv norm_num.derive,
  eq ← i_to_expr ``(tactic.times_table.eval_repr_sub %%t %%k %%e₁_eq %%e₂_eq %%e_eq),
  pure (e', eq)
| `(%%e₁ * %%e₂) := trace_error "mul" $ do
    -- TODO: optimize multiplication with numerals?
    -- Rewrite `repr (e₁ * e₂) k = ∑ i j, table i j k * repr e₁ i * repr e₂ j`,
    -- then use `norm_num.derive` to expand the sum.
    -- TODO: expand the sum here so we don't switch so much between tactics.
    e ← i_to_expr ``(∑ (i j : %%ι), (%%t).basis.repr %%e₁ i * (%%t).basis.repr %%e₂ j * (%%t).table i j %%k),
    trace "multiplication becomes " >> trace e,
    (e', e_eq) ← or_refl_conv norm_num.derive e,
    trace "derives to " >> infer_type e_eq >>= trace,
    eq ← trace_error "eval_repr_mul" $ mk_app `tactic.times_table.eval_repr_mul [t, k, e₁, e₂, e', e_eq],
    trace "proved " >> infer_type eq >>= trace,
    pure (e', eq)
| `(%%e₁ ^ %%n) := trace_error "pow" $ do
  match norm_num.match_numeral n with
  | norm_num.match_numeral_result.zero := do
    one ← expr.of_nat S 1,
    (one', one_eq) ← eval one,
    eq ← i_to_expr ``(tactic.times_table.eval_pow_zero %%t %%k %%e₁ %%one_eq),
    pure (one', eq)
  | norm_num.match_numeral_result.one := do
    (e', e₁_eq) ← eval e₁,
    eq ← i_to_expr ``(tactic.times_table.eval_pow_one %%t %%k %%e₁_eq),
    pure (e', eq)
  | norm_num.match_numeral_result.bit0 b := do
    e₁' ← i_to_expr ``((%%e₁ ^ %%b) * (%%e₁ ^ %%b)),
    (e', e_eq) ← eval e₁',
    eq ← i_to_expr ``(tactic.times_table.eval_pow_bit0 %%t %%k %%b %%e_eq),
    pure (e', eq)
  | norm_num.match_numeral_result.bit1 b := do
    e₁' ← i_to_expr ``((%%e₁ ^ %%b) * (%%e₁ ^ %%b) * %%e₁),
    (e', e_eq) ← eval e₁',
    eq ← i_to_expr ``(tactic.times_table.eval_pow_bit1 %%t %%k %%b %%e_eq),
    pure (e', eq)

  | _ := failed
  end
| e := do
  trace "fallback: simping",
  full_e ← i_to_expr ``(basis.repr (times_table.basis %%t) %%e %%k),
  (e', pr) ← simp_times_table full_e,
  trace "managed to simp to ", infer_type pr >>= trace,
  pure (e', pr)

/-- `norm_num` extension for expressions of the form `basis.repr (times_table.basis _) _` -/
@[norm_num]
protected meta def norm : expr → tactic (expr × expr)
| ek@(expr.app (expr.app coe_fn' (expr.app `(coe_fn (basis.repr (times_table.basis %%t))) e)) k) := do
  -- TODO: check that `coe_fn'` is indeed `⇑`
  ι ← infer_type k,
  S ← infer_type e,
  R ← infer_type ek,
  (e', pf) ← tactic.trace_error "Internal error in `tactic.times_table.eval`:" $ tactic.times_table.eval ι R S t k e,
  pf_ty ← infer_type pf,
  match pf_ty with
  | `(%%lhs = %%rhs) := do
    is_def_eq ek lhs <|> (trace "lhs does not match:" >> trace ek >> trace " ≠ " >> trace lhs),
    is_def_eq e' rhs <|> (trace "rhs does not match:" >> trace e' >> trace " ≠ " >> trace rhs)
  | _ := trace "Proof type is not an equality: " >> trace pf_ty
  end,
  pure (e', pf)
| _ := failure

meta def conv_subexpressions (step : expr → tactic (expr × expr)) (e : expr) : tactic (expr × expr) :=
do e ← instantiate_mvars e,
   (_, e', pr) ←
    ext_simplify_core () {} simp_lemmas.mk (λ _, trace "no discharger" >> failed) (λ _ _ _ _ _, failed)
      (λ _ _ _ _ e,
        do trace e, (new_e, pr) ← step e,
           guard (¬ new_e =ₐ e) <|> (trace "rewriting was idempotent: " >> trace e >> trace " → " >> trace new_e >> failure),
           return ((), new_e, some pr, tt))
      `eq e,
    trace "rewrite: " >> trace e >> trace " → " >> trace e',
    return (e', pr)

/-- TODO: integrate into `norm_num` -/
meta def _root_.tactic.interactive.times_table_eval
  (hs : interactive.parse tactic.simp_arg_list)
  (locat : interactive.parse interactive.types.location) : tactic unit := do
  /-
  -- Write the term as a product (TODO: efficient handling of exponentiation?)
  /- repeat { ring_nf SOP }, -/ simp only [pow_succ, pow_zero, mul_one],
  -- Use the times table for multiplications.
  simp only [_root_.map_add, finsupp.coe_add, pi.add_apply,
    _root_.map_sub, finsupp.coe_sub, pi.sub_apply,
    pi.mul_apply, times_table.unfold_mul],
  -- Determine what the values in the table refer to.
  simp only [linear_equiv.map_bit0, linear_equiv.map_bit1, finsupp.bit0_apply, finsupp.add_apply,
    sqrt_2_sqrt_3.times_table, sqrt_2_sqrt_3.table, repr_one, repr_sqrt_2, repr_sqrt_3],
  norm_num,
  -/
  `[simp only [pow_succ, pow_zero, mul_one]],
    -- Use the times table for multiplications.
  `[simp only [_root_.map_add, finsupp.coe_add, pi.add_apply, _root_.map_sub, finsupp.coe_sub,
    pi.sub_apply, pi.mul_apply, times_table.unfold_mul]],
  `[simp only [linear_equiv.map_bit0, linear_equiv.map_bit1, finsupp.bit0_apply, finsupp.add_apply]],
  -- Determine what the values in the table refer to.
  tactic.interactive.simp none none tt hs [] locat,
  `[norm_num]

end tactic.times_table

namespace sqrt_2_sqrt_3

set_option profiler true

example (x y : sqrt_2_sqrt_3) : x * y = y * x :=
begin
  cases x, cases y,
  apply sqrt_2_sqrt_3.times_table.basis.ext_elem (λ k, _),
  do { (new_t, pr) ← tactic.target >>= (tactic.times_table.conv_subexpressions tactic.times_table.norm),
        tactic.replace_target new_t pr },
  /-
  norm_num,
  -/
  /-
  fin_cases k; ring
  -/
end

example (x y z : sqrt_2_sqrt_3) : x * y * z = x * (y * z) :=
begin
  cases x, cases y, cases z,
  apply sqrt_2_sqrt_3.times_table.basis.ext_elem (λ k, _),
  norm_num,

  fin_cases k; norm_num; ring
end

-- Bottom-up: should compute efficiently.
example : (sqrt_2 + sqrt_3)^3 - 9 * (sqrt_2 + sqrt_3) = 2 * sqrt_2 :=
begin
  -- Work coefficient-wise.
  apply sqrt_2_sqrt_3.times_table.basis.ext_elem (λ k, _),
  /-
  do { (new_t, pr) ← tactic.target >>= (tactic.times_table.conv_subexpressions tactic.times_table.norm),
        tactic.replace_target new_t pr },
  -/
  norm_num,
  -- Finish the proof coefficientwise.
  fin_cases k; norm_num,
end

/-
-- Top-down: easier to do with `simp`, but produces huge terms
example : (sqrt_2 + sqrt_3)^3 - 9 * (sqrt_2 + sqrt_3) = 2 * sqrt_2 :=
begin
  -- Work coefficient-wise.
  apply sqrt_2_sqrt_3.times_table.basis.ext_elem (λ k, _),
  times_table_eval [sqrt_2_sqrt_3.times_table, sqrt_2_sqrt_3.table, repr_one, repr_sqrt_2, repr_sqrt_3],
  -- Finish the proof coefficientwise.
  fin_cases k; norm_num,
end
-/

end sqrt_2_sqrt_3
