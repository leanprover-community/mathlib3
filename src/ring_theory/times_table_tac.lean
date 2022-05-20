import algebra.big_operators.norm_num
import data.nat.fib
import data.nat.succ_pred
import linear_algebra.basis
import ring_theory.adjoin_root
import ring_theory.power_basis
import tactic.norm_fin

open_locale big_operators

local attribute [-instance] rat.semiring rat.comm_semiring rat.comm_ring

-- TODO: generalize this so we don't assume a multiplication on `S`
-- or even no structure on `S` at all
structure times_table (ι R S : Type*) [fintype ι]
  [semiring R] [add_comm_monoid S] [module R S] [has_mul S] :=
(basis : basis ι R S)
(table : ι → ι → ι → R)
(unfold_mul : ∀ x y k, basis.repr (x * y) k = ∑ i j : ι, basis.repr x i * basis.repr y j * table i j k)
-- (mul_def : ∀ i j k, basis.repr (basis i * basis j) k = table i j k)

mk_simp_attribute times_table_simps "The simpset `times_table_simps` is used by the tactic
`times_table` to reduce an expression of the form `(t : times_table).basis.repr x k` to a numeral."

section semiring
variables {ι R S : Type*} [fintype ι] [comm_semiring R] [non_unital_non_assoc_semiring S] [module R S]

noncomputable def times_table.reindex {ι' : Type*} [fintype ι'] (t : times_table ι R S) (e : ι ≃ ι') :
  times_table ι' R S :=
{ basis := t.basis.reindex e,
  table := λ i j k, t.table (e.symm i) (e.symm j) (e.symm k),
  unfold_mul := λ x y k, sorry }

@[simp] lemma times_table.mul_def (t : times_table ι R S) (i j k : ι)  :
  t.basis.repr (t.basis i * t.basis j) k = t.table i j k :=
by { simp only [t.unfold_mul, basis.repr_self],
     rw [fintype.sum_eq_single i, fintype.sum_eq_single j, finsupp.single_eq_same,
         finsupp.single_eq_same, one_mul, one_mul];
       { intros x hx, simp [finsupp.single_eq_of_ne hx.symm] } }

variables [smul_comm_class R S S] [is_scalar_tower R S S]

-- TODO: should be much easier now that `unfold_mul` is the primitive
lemma times_table.coeff_mul_coeff (t : times_table ι R S) (x y : ι → R) :
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

/-
lemma times_table.unfold_mul [fintype ι] (t : times_table ι R S) (x y : S) (k : ι) :
  t.basis.repr (x * y) k =
    ∑ i j : ι, t.basis.repr x i * t.basis.repr y j * t.table i j k :=
begin
  simp only [← basis.equiv_fun_apply],
  rw [← t.basis.equiv_fun.symm_apply_apply x, ← t.basis.equiv_fun.symm_apply_apply y,
    t.coeff_mul_coeff, linear_equiv.symm_apply_apply, linear_equiv.symm_apply_apply,
    linear_equiv.apply_symm_apply]
end
-/

@[simp] lemma linear_equiv.map_bit0 {R M N : Type*} [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]
  (f : M ≃ₗ[R] N) (x : M) : f (bit0 x) = bit0 (f x) :=
by { unfold bit0, simp only [_root_.map_add, finsupp.coe_add, pi.add_apply] }
@[simp] lemma linear_equiv.map_bit1 {R M N : Type*} [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N] [has_one M]
  (f : M ≃ₗ[R] N) (x : M) : f (bit1 x) = bit0 (f x) + f 1 :=
by { unfold bit1 bit0, simp only [_root_.map_add, finsupp.coe_add, pi.add_apply] }

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

/-
noncomputable instance : algebra ℚ sqrt_2_sqrt_3 :=
{ to_fun := λ c, ⟨c, 0, 0, 0⟩,
  .. sqrt_2_sqrt_3.module }
-/

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

variables {R S ι : Type*} [fintype ι] [comm_semiring R] [add_comm_monoid S] [module R S]
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
-- variables [smul_comm_class R S S] [is_scalar_tower R S S]

/- ∑ (i j : fin 4),
    ⇑(⇑(sqrt_2_sqrt_3.times_table.basis.repr) {a := x_a, b := x_b, c := x_c, d := x_d}) i *
        ⇑(⇑(sqrt_2_sqrt_3.times_table.basis.repr) {a := y_a, b := y_b, c := y_c, d := y_d}) j *
      sqrt_2_sqrt_3.times_table.table i j k
-/
protected lemma eval_repr_mul [fintype ι] (t : times_table ι R S) (k : ι) (e₁ e₂ : S) (e' : R)
  (eq : ∑ i j : ι, t.basis.repr e₁ i * t.basis.repr e₂ j * t.table i j k = e') :
  t.basis.repr (e₁ * e₂) k = e' :=
by rw [times_table.unfold_mul t, eq]

protected lemma eval_repr_repr_table {r₁ r₂ : ι → R} {t : ι → ι → ι → R} {i j k : ι}
  {e₁' e₂' t' e' : R} (e₁_eq : r₁ i = e₁') (e₂_eq : r₂ j = e₂')
  (t_eq : t i j k = t') (eq : e₁' * e₂' * t' = e') :
  r₁ i * r₂ j * t i j k = e' :=
by rw [e₁_eq, e₂_eq, t_eq, eq]

end non_assoc_non_unital_semiring

section semiring

variables {R S ι : Type*} [fintype ι] [comm_semiring R] [semiring S] [module R S]

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

variables {R S ι : Type*} [comm_ring R] [ring S] [module R S]

protected lemma eval_repr_sub (t : times_table ι R S) (k : ι) {e₁ e₂ : S} {e₁' e₂' e' : R}
  (e₁_eq : t.basis.repr e₁ k = e₁') (e₂_eq : t.basis.repr e₂ k = e₂') (e_eq : e₁' - e₂' = e') :
  t.basis.repr (e₁ - e₂) k = e' :=
by rw [_root_.map_sub, finsupp.sub_apply, e₁_eq, e₂_eq, e_eq]

end ring

section matrix

open matrix

section converter

meta structure context :=
(simps : simp_lemmas)

meta def converter := expr → state_t context tactic (expr × expr)

/-- `trace_error msg t` executes the tactic `t`. If `t` fails, traces `msg` and the failure message
of `t`. -/
meta def trace_error {α σ} (msg : string) (t : state_t σ tactic α) : state_t σ tactic α :=
{ run := λ s ts, match t.run s ts with
       | (result.success r s') := result.success r s'
       | (result.exception (some msg') p s') := (trace msg >> trace (msg' ()) >> result.exception
            (some msg') p) s'
       | (result.exception none p s') := result.exception none p s'
       end }

meta def lift {σ α} : tactic α → state_t σ tactic α := state_t.lift
meta def converter.lift {σ α β} : (α → tactic β) → α → state_t σ tactic β := λ t x, lift (t x)

meta def converter.refl : converter
| e := lift (refl_conv e)

meta def converter.or_refl : converter → converter
| c e := c e <|> converter.refl e

meta def converter.trans : converter → converter → converter
| c d e := do
  (e', pf_c) ← c.or_refl e,
  (e'', pf_d) ← d.or_refl e',
  pf ← lift $ mk_eq_trans pf_c pf_d,
  pure (e'', pf)

meta def get_context : state_t context tactic context :=
state_t.get

end converter

namespace tactic.norm_num

/-- Use `norm_num` to decide equality between two expressions.

If the decision procedure succeeds, the `bool` value indicates whether the expressions are equal,
and the `expr` is a proof of (dis)equality.
This procedure is partial: it will fail in cases where `norm_num` can't reduce either side
to a rational numeral.
-/
meta def decide_eq (l r : expr) : tactic (bool × expr) := do
  (l', l'_pf) ← or_refl_conv norm_num.derive l,
  (r', r'_pf) ← or_refl_conv norm_num.derive r,
  n₁ ← l'.to_rat, n₂ ← r'.to_rat,
  c ← infer_type l' >>= mk_instance_cache,
  if n₁ = n₂ then do
    pf ← i_to_expr ``(eq.trans %%l'_pf $ eq.symm %%r'_pf),
    pure (tt, pf)
  else do
    (_, p) ← norm_num.prove_ne c l' r' n₁ n₂,
    pure (ff, p)

lemma list.not_mem_cons {α : Type*} {x y : α} {ys : list α} (h₁ : x ≠ y) (h₂ : x ∉ ys) :
  x ∉ y :: ys :=
λ h, ((list.mem_cons_iff _ _ _).mp h).elim h₁ h₂

/-- Use a decision procedure for the equality of list elements to decide list membership.

If the decision procedure succeeds, the `bool` value indicates whether the expressions are equal,
and the `expr` is a proof of (dis)equality.
This procedure is partial iff its parameter `decide_eq` is partial.
-/
meta def list.decide_mem (decide_eq : expr → expr → tactic (bool × expr)) :
  expr → list expr → tactic (bool × expr)
| x [] := do
  pf ← i_to_expr ``(list.not_mem_nil %%x),
  pure (ff, pf)
| x (y :: ys) := do
  (is_head, head_pf) ← decide_eq x y,
  if is_head then do
    pf ← i_to_expr ``((list.mem_cons_iff %%x %%y _).mpr (or.inl %%head_pf)),
    pure (tt, pf)
  else do
    (mem_tail, tail_pf) ← list.decide_mem x ys,
    if mem_tail then do
      pf ← i_to_expr ``((list.mem_cons_iff %%x %%y _).mpr (or.inr %%tail_pf)),
      pure (tt, pf)
    else do
      pf ← i_to_expr ``(list.not_mem_cons %%head_pf %%tail_pf),
      pure (ff, pf)

lemma finset.insert_eq_coe_list_of_mem {α : Type*} [decidable_eq α] (x : α) (xs : finset α)
  {xs' : list α} (h : x ∈ xs') (nd_xs : xs'.nodup)
  (hxs' : xs = finset.mk ↑xs' (multiset.coe_nodup.mpr nd_xs)) :
  insert x xs = finset.mk ↑xs' (multiset.coe_nodup.mpr nd_xs) :=
have h : x ∈ xs, by simpa [hxs'] using h,
by rw [finset.insert_eq_of_mem h, hxs']

lemma finset.insert_eq_coe_list_cons {α : Type*} [decidable_eq α] (x : α) (xs : finset α)
  {xs' : list α} (h : x ∉ xs') (nd_xs : xs'.nodup) (nd_xxs : (x :: xs').nodup)
  (hxs' : xs = finset.mk ↑xs' (multiset.coe_nodup.mpr nd_xs)) :
  insert x xs = finset.mk ↑(x :: xs') (multiset.coe_nodup.mpr nd_xxs) :=
have h : x ∉ xs, by simpa [hxs'] using h,
by { rw [← finset.val_inj, finset.insert_val_of_not_mem h, hxs'], simp only [multiset.cons_coe] }

/-- Convert an expression denoting a finset to a list of elements,
a proof that this list is equal to the original finset,
and a proof that the list contains no duplicates.

We return a list rather than a finset, so we can more easily iterate over it
(without having to prove that our tactics are independent of the order of iteration,
which is in general not true).

`decide_eq` is a (partial) decision procedure for determining whether two
elements of the finset are equal, for example to parse `{2, 1, 2}` into `[2, 1]`.
-/
meta def eval_finset (decide_eq : expr → expr → tactic (bool × expr)) :
  expr → tactic (list expr × expr × expr)
| e@`(has_emptyc.emptyc) := do
  eq ← mk_eq_refl e,
  nd ← i_to_expr ``(list.nodup_nil),
  pure ([], eq, nd)
| e@`(has_singleton.singleton %%x) := do
  eq ← mk_eq_refl e,
  nd ← i_to_expr ``(list.nodup_singleton %%x),
  pure ([x], eq, nd)
| `(@@has_insert.insert (@@finset.has_insert %%dec) %%x %%xs) := do
  (exs, xs_eq, xs_nd) ← eval_finset xs,
  (is_mem, mem_pf) ← list.decide_mem decide_eq x exs,
  if is_mem then do
    pf ← i_to_expr ``(finset.insert_eq_coe_list_of_mem %%x %%xs %%mem_pf %%xs_nd %%xs_eq),
    pure (exs, pf, xs_nd)
  else do
    nd ← i_to_expr ``(list.nodup_cons.mpr ⟨%%mem_pf, %%xs_nd⟩),
    pf ← i_to_expr ``(finset.insert_eq_coe_list_cons %%x %%xs %%mem_pf %%xs_nd %%nd %%xs_eq),
    pure (x :: exs, pf, nd)
| `(@@finset.univ %%ft) := do
  -- Convert the fintype instance expression `ft` to a list of its elements.
  -- Unfold it to the `fintype.mk` constructor and a list of arguments.
  `fintype.mk ← get_app_fn_const_whnf ft
    | fail (to_fmt "Unknown fintype expression" ++ format.line ++ to_fmt ft),
  [_, args, _] ← get_app_args_whnf ft | fail (to_fmt "Expected 3 arguments to `fintype.mk`"),
  eval_finset args
| e@`(finset.range %%en) := do
  n ← expr.to_nat en,
  eis ← (list.range n).mmap (λ i, expr.of_nat `(ℕ) i),
  eq ← mk_eq_refl e,
  nd ← i_to_expr ``(list.nodup_range %%en),
  pure (eis, eq, nd)
| e@`(finset.fin_range %%en) := do
  n ← expr.to_nat en,
  eis ← (list.fin_range n).mmap (λ i, expr.of_nat `(fin %%en) i),
  eq ← mk_eq_refl e,
  nd ← i_to_expr ``(list.nodup_fin_range %%en),
  pure (eis, eq, nd)
| e := fail (to_fmt "Unknown finset expression" ++ format.line ++ to_fmt e)

lemma list.map_cons_congr {α β : Type*} (f : α → β) {x : α} {xs : list α} {fx : β} {fxs : list β}
  (h₁ : f x = fx) (h₂ : xs.map f = fxs) : (x :: xs).map f = fx :: fxs :=
by rw [list.map_cons, h₁, h₂]

/-- Apply `ef : α → β` to all elements of the list, constructing an equality proof.

`eval_f : expr → tactic (expr × expr)` is a conversion procedure for simplifying expressions
of the form `(%%ef %%x), where `ef : expr` is the function to apply and `x : expr` is a list
element.
-/
meta def eval_list_map (ef : expr) (eval_f : converter) :
  list expr → state_t context tactic (list expr × expr)
| [] := do
  eq ← lift $ i_to_expr ``(list.map_nil %%ef),
  pure ([], eq)
| (x :: xs) := do
  (fx, fx_eq) ← eval_f (expr.app ef x),
  (fxs, fxs_eq) ← eval_list_map xs,
  eq ← lift $ i_to_expr ``(list.map_cons_congr %%ef %%fx_eq %%fxs_eq),
  pure (fx :: fxs, eq)

lemma multiset.cons_congr {α : Type*} (x : α) {xs : multiset α} {xs' : list α}
  (xs_eq : (xs' : multiset α) = xs) : (list.cons x xs' : multiset α) = x ::ₘ xs :=
by rw [← xs_eq]; refl

lemma multiset.map_congr {α β : Type*} (f : α → β) {xs : multiset α}
  {xs' : list α} {ys : list β} (xs_eq : xs = (xs' : multiset α)) (ys_eq : xs'.map f = ys) :
  xs.map f = (ys : multiset β) :=
by rw [← ys_eq, ← multiset.coe_map, xs_eq]

/-- Convert an expression denoting a multiset to a list of elements.

We return a list rather than a finset, so we can more easily iterate over it
(without having to prove that our tactics are independent of the order of iteration,
which is in general not true).

-/
meta def eval_multiset : expr → state_t context tactic (list expr × expr)
| e@`(@has_zero.zero (multiset _) _) := do
  eq ← lift $ mk_eq_refl e,
  pure ([], eq)
| e@`(has_emptyc.emptyc) := do
  eq ← lift $ mk_eq_refl e,
  pure ([], eq)
| e@`(has_singleton.singleton %%x) := do
  eq ← lift $ mk_eq_refl e,
  pure ([x], eq)
| e@`(multiset.cons %%x %%xs) := do
  (xs, xs_eq) ← eval_multiset xs,
  eq ← lift $ i_to_expr ``(multiset.cons_congr %%x %%xs_eq),
  pure (x :: xs, eq)
| e@`(@@has_insert.insert multiset.has_insert %%x %%xs) := do
  (xs, xs_eq) ← eval_multiset xs,
  eq ← lift $ i_to_expr ``(multiset.cons_congr %%x %%xs_eq),
  pure (x :: xs, eq)
| e@`(multiset.range %%en) := do
  n ← lift $ expr.to_nat en,
  eis ← lift $ (list.range n).mmap (λ i, expr.of_nat `(ℕ) i),
  eq ← lift $ mk_eq_refl e,
  pure (eis, eq)
| `(@multiset.map %%α %%β %%ef %%exs) := do
  (xs, xs_eq) ← eval_multiset exs,
  (ys, ys_eq) ← eval_list_map ef (converter.or_refl $ converter.lift norm_num.derive) xs,
  eq ← lift $ i_to_expr ``(multiset.map_congr %%ef %%xs_eq %%ys_eq),
  pure (ys, eq)
| e := lift $ fail (to_fmt "Unknown multiset expression" ++ format.line ++ to_fmt e)

lemma list.cons_congr {α : Type*} (x : α) {xs : list α} {xs' : list α} (xs_eq : xs' = xs) :
  x :: xs' = x :: xs :=
by rw xs_eq

lemma list.map_congr {α β : Type*} (f : α → β) {xs xs' : list α}
  {ys : list β} (xs_eq : xs = xs') (ys_eq : xs'.map f = ys) :
  xs.map f = ys :=
by rw [← ys_eq, xs_eq]

/-- Convert an expression denoting a list to a list of elements. -/
meta def eval_list : expr → state_t context tactic (list expr × expr)
| e@`(list.nil) := do
  eq ← lift $ mk_eq_refl e,
  pure ([], eq)
| e@`(list.cons %%x %%xs) := do
  (xs, xs_eq) ← eval_list xs,
  eq ← lift $ i_to_expr ``(list.cons_congr %%x %%xs_eq),
  pure (x :: xs, eq)
| e@`(list.range %%en) := do
  n ← lift $ expr.to_nat en,
  eis ← lift $ (list.range n).mmap (λ i, expr.of_nat `(ℕ) i),
  eq ← lift $ mk_eq_refl e,
  pure (eis, eq)
| `(@list.map %%α %%β %%ef %%exs) := do
  (xs, xs_eq) ← eval_list exs,
  (ys, ys_eq) ← eval_list_map ef (converter.or_refl $ converter.lift norm_num.derive) xs,
  eq ← lift $ i_to_expr ``(list.map_congr %%ef %%xs_eq %%ys_eq),
  pure (ys, eq)
| e := lift $ fail (to_fmt "Unknown list expression" ++ format.line ++ to_fmt e)

@[to_additive]
lemma list.prod_cons_congr {α : Type*} [monoid α] (xs : list α) (x y z : α)
  (his : xs.prod = y) (hi : x * y = z) : (x :: xs).prod = z :=
by rw [list.prod_cons, his, hi]

/-- Evaluate `list.prod %%xs`,
producing the evaluated expression and an equality proof. -/
meta def list.prove_prod (α : expr) : list expr → tactic (expr × expr)
| [] := do
  result ← expr.of_nat α 1,
  proof ← i_to_expr ``(@list.prod_nil %%α _),
  pure (result, proof)
| (x :: xs) := do
  eval_xs ← list.prove_prod xs,
  xxs ← i_to_expr ``(%%x * %%eval_xs.1),
  eval_xxs ← or_refl_conv norm_num.derive xxs,
  exs ← expr.of_list α xs,
  proof ← i_to_expr
    ``(list.prod_cons_congr %%exs%%x %%eval_xs.1 %%eval_xxs.1 %%eval_xs.2 %%eval_xxs.2),
  pure (eval_xxs.1, proof)

/-- Evaluate `list.sum %%xs`,
sumucing the evaluated expression and an equality proof. -/
meta def list.prove_sum (α : expr) : list expr → tactic (expr × expr)
| [] := do
  result ← expr.of_nat α 0,
  proof ← i_to_expr ``(@list.sum_nil %%α _),
  pure (result, proof)
| (x :: xs) := do
  eval_xs ← list.prove_sum xs,
  xxs ← i_to_expr ``(%%x + %%eval_xs.1),
  eval_xxs ← or_refl_conv norm_num.derive xxs,
  exs ← expr.of_list α xs,
  proof ← i_to_expr
    ``(list.sum_cons_congr %%exs%%x %%eval_xs.1 %%eval_xxs.1 %%eval_xs.2 %%eval_xxs.2),
  pure (eval_xxs.1, proof)

@[to_additive] lemma list.prod_congr {α : Type*} [monoid α] {xs xs' : list α} {z : α}
  (h₁ : xs = xs') (h₂ : xs'.prod = z) : xs.prod = z := by cc

@[to_additive] lemma multiset.prod_congr {α : Type*} [comm_monoid α]
  {xs : multiset α} {xs' : list α} {z : α}
  (h₁ : xs = (xs' : multiset α)) (h₂ : xs'.prod = z) : xs.prod = z :=
by rw [← h₂, ← multiset.coe_prod, h₁]

/-- Evaluate `(%%xs.map (%%ef : %%α → %%β)).prod`,
producing the evaluated expression and an equality proof.

`eval_f : expr → tactic (expr × expr)` is a conversion procedure for simplifying expressions
of the form `(%%ef %%x), where `ef : expr` is the function to apply and `x : expr` is a list
element.
-/
meta def list.prove_prod_map (β ef : expr) (eval_f : converter)
  (xs : list expr) : state_t context tactic (expr × expr) := do
  (fxs, fxs_eq) ← eval_list_map ef eval_f xs,
  (prod, prod_eq) ← lift $ list.prove_prod β fxs,
  eq ← lift $ i_to_expr ``(list.prod_congr %%fxs_eq %%prod_eq),
  pure (prod, eq)

/-- Evaluate `(%%xs.map (%%ef : %%α → %%β)).sum`,
producing the evaluated expression and an equality proof.

`eval_f : expr → tactic (expr × expr)` is a conversion procedure for simplifying expressions
of the form `(%%ef %%x), where `ef : expr` is the function to apply and `x : expr` is a list
element.
-/
meta def list.prove_sum_map (β ef : expr) (eval_f : converter)
  (xs : list expr) : state_t context tactic (expr × expr) := do
  (fxs, fxs_eq) ← eval_list_map ef eval_f xs,
  (sum, sum_eq) ← lift $ list.prove_sum β fxs,
  eq ← lift $ i_to_expr ``(list.sum_congr %%fxs_eq %%sum_eq),
  pure (sum, eq)

@[to_additive]
lemma finset.eval_prod_of_list {β α : Type*} [comm_monoid β]
  (s : finset α) (f : α → β) {is : list α} (his : is.nodup)
  (hs : finset.mk ↑is (multiset.coe_nodup.mpr his) = s)
  {x : β} (hx : (is.map f).prod = x) :
  s.prod f = x :=
by rw [← hs, finset.prod_mk, multiset.coe_map, multiset.coe_prod, hx]

meta def eval_finset_sum (eval_f : converter) (β ef es : expr) :
  state_t context tactic (expr × expr) := do
  (xs, list_eq, nodup) ← lift $ eval_finset decide_eq es,
  (result, sum_eq) ← list.prove_sum_map β ef eval_f xs,
  pf ← lift $ i_to_expr ``(finset.eval_sum_of_list %%es %%ef %%nodup %%list_eq %%sum_eq),
  pf_ty ← lift $ infer_type pf,
  pure (result, pf)

meta def match_eval_finset_sum (eval_f : converter) : converter
| `(@finset.sum %%β %%α %%inst %%es %%ef) := eval_finset_sum eval_f β ef es
| _ := lift $ fail "march_eval_finset_sum: expected ∑ i in s, f i"

/-- `norm_num` plugin for evaluating big operators:
 * `list.prod`
 * `list.sum`
 * `multiset.prod`
 * `multiset.sum`
 * `finset.prod`
 * `finset.sum`
-/
meta def eval_big_operators : converter
| `(@list.prod %%α %%inst1 %%inst2 %%exs) :=
trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq) ← eval_list exs,
  (result, sum_eq) ← lift $ list.prove_prod α xs,
  pf ← lift $ i_to_expr ``(list.prod_congr %%list_eq %%sum_eq),
  pure (result, pf)
| `(@list.sum %%α %%inst1 %%inst2 %%exs) :=
trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq) ← eval_list exs,
  (result, sum_eq) ← lift $ list.prove_sum α xs,
  pf ← lift $ i_to_expr ``(list.sum_congr %%list_eq %%sum_eq),
  pure (result, pf)
| `(@multiset.prod %%α %%inst %%exs) :=
trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq) ← eval_multiset exs,
  (result, sum_eq) ← lift $ list.prove_prod α xs,
  pf ← lift $ i_to_expr ``(multiset.prod_congr %%list_eq %%sum_eq),
  pure (result, pf)
| `(@multiset.sum %%α %%inst %%exs) :=
trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq) ← eval_multiset exs,
  (result, sum_eq) ← lift $ list.prove_sum α xs,
  pf ← lift $ i_to_expr ``(multiset.sum_congr %%list_eq %%sum_eq),
  pure (result, pf)
| `(@finset.prod %%β %%α %%inst %%es %%ef) :=
trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq, nodup) ← lift $ eval_finset decide_eq es,
  (result, sum_eq) ← list.prove_prod_map β ef (converter.or_refl $ converter.lift norm_num.derive) xs,
  pf ← lift $ i_to_expr ``(finset.eval_prod_of_list %%es %%ef %%nodup %%list_eq %%sum_eq),
  pure (result, pf)
| `(@finset.sum %%β %%α %%inst %%es %%ef) :=
trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq, nodup) ← lift $ eval_finset decide_eq es,
  (result, sum_eq) ← list.prove_sum_map β ef (converter.or_refl $ converter.lift norm_num.derive) xs,
  pf ← lift $ i_to_expr ``(finset.eval_sum_of_list %%es %%ef %%nodup %%list_eq %%sum_eq),
  pure (result, pf)
| _ := lift $ failed

end tactic.norm_num

lemma eval_vec_cons_pf_zero {α : Type*} {n : ℕ} (x : α) (xs : fin n → α) :
  vec_cons x xs has_zero.zero = x := rfl
lemma eval_vec_cons_pf_succ {α : Type*} {n : ℕ} (i : fin n) (x y : α) (xs : fin n → α)
  (h : xs i = y) : vec_cons x xs (fin.succ i) = y :=
by rw [cons_val_succ, h]

/-- `eval_vec_cons n x xs` returns `(y, ⊢ vec_cons x xs n = y)` -/
meta def eval_vec_cons : ℕ → expr → expr → tactic (expr × expr)
| 0 x xs := do
  eq ← mk_app ``eval_vec_cons_pf_zero [x, xs],
  pure (x, eq)
| (n + 1) x' xxs@`(vec_cons %%x %%xs) := do
  (result, eq') ← eval_vec_cons n x xs,
  eq ← i_to_expr ``(eval_vec_cons_pf_succ _ %%x' %%result %%xxs %%eq'),
  pure (result, eq)
| (n + 1) x xs := trace xs >> fail "Expected vector of the form `vec_cons x y`"

open tactic.norm_fin

@[norm_num]
meta def norm_vec_cons : expr → tactic (expr × expr)
| `(vec_cons %%x %%xs %%i) := tactic.trace_error "Internal error in `norm_vec_cons`" $ do
  n ← i.to_nat,
  (y, pf) ← eval_vec_cons n x xs,
  pure (y, pf)
| e := pformat!"norm_vec_cons: expected `vec_cons x xs i`, got {e}" >>= fail

lemma foo' : ![1, 2, 3] 0 = 1 := by norm_num1
lemma foo'' : ![1, 2, 3] 1 = 2 := by norm_num1

end matrix

/-- Simplify expressions of the form `(t : times_table).basis.repr x k` using lemmas tagged
`@[times_table_simps]`. -/
-- @[norm_num]
meta def simp_times_table : converter
| e := do
  ctx ← get_context,
  (e', pf, _) ← state_t.lift $ simplify ctx.simps [] e <|>
    fail!"Failed to simplify {e}, are you missing a `@[times_table_simps]` lemma?",
  pure (e', pf)

protected lemma eval_vec_cons_pf {α ι : Type*} (t : ι → ι → ι → α) (i j k : ι)
  {ti : ι → ι → α} (ti_pf : t i = ti) {tij : ι → α} (tij_pf : ti j = tij) :
  t i j k = tij k :=
by rw [ti_pf, tij_pf]

/-- Evaluate `((t : times_table _ _ _).basis.repr e) k` using `norm_num`. -/
protected meta def eval (ι R S t k : expr) : converter
| `(0) := trace_error "zero" $ do
  e ← lift $ expr.of_nat R 0,
  pf ← lift $ i_to_expr ``(tactic.times_table.eval_repr_zero %%t %%k),
  pure (e, pf)
| `(bit0 %%e₁) := trace_error "bit0" $ do
  (e₁', e₁_eq) ← eval e₁,
  (e', e_eq) ← lift $ i_to_expr ``(%%e₁' + %%e₁') >>= or_refl_conv norm_num.derive,
  eq ← lift $ i_to_expr ``(tactic.times_table.eval_repr_bit0 %%t %%k %%e₁_eq %%e_eq),
  pure (e', eq)
| `(bit1 %%e₁) := trace_error "bit1" $ do
  (e₁', e₁_eq) ← eval e₁,
  (one', one_eq) ← (lift $ expr.of_nat S 1) >>= eval,
  (e', e_eq) ← lift $ i_to_expr ``(%%e₁' + %%e₁' + %%one') >>= or_refl_conv norm_num.derive,
  eq ← lift $ i_to_expr ``(tactic.times_table.eval_repr_bit1 %%t %%k %%e₁_eq %%one_eq %%e_eq),
  pure (e', eq)
| `(%%e₁ + %%e₂) := trace_error "add" $ do
  (e₁', e₁_eq) ← eval e₁,
  (e₂', e₂_eq) ← eval e₂,
  (e', e_eq) ← lift $ i_to_expr ``(%%e₁' + %%e₂') >>= or_refl_conv norm_num.derive,
  eq ← lift $ i_to_expr ``(tactic.times_table.eval_repr_add %%t %%k %%e₁_eq %%e₂_eq %%e_eq),
  pure (e', eq)
| `(%%e₁ - %%e₂) := trace_error "sub" $ do
  (e₁', e₁_eq) ← eval e₁,
  (e₂', e₂_eq) ← eval e₂,
  (e', e_eq) ← lift $ i_to_expr ``(%%e₁' - %%e₂') >>= or_refl_conv norm_num.derive,
  eq ← lift $ i_to_expr ``(tactic.times_table.eval_repr_sub %%t %%k %%e₁_eq %%e₂_eq %%e_eq),
  pure (e', eq)
| `(%%e₁ * %%e₂) := trace_error "mul" $ do
    -- TODO: optimize multiplication with numerals?
    -- Rewrite `repr (e₁ * e₂) k = ∑ i j, table i j k * repr e₁ i * repr e₂ j`,
    -- then use `norm_num.derive` to expand the sum.
    -- TODO: expand the sum here so we don't switch so much between tactics.
    e ← lift $ i_to_expr ``(∑ (i j : %%ι), (%%t).basis.repr %%e₁ i * (%%t).basis.repr %%e₂ j * (%%t).table i j %%k),
    (e', e_eq) ← tactic.norm_num.match_eval_finset_sum -- evaluates the sum over i
      (lift ∘ head_beta >=> tactic.norm_num.match_eval_finset_sum -- evaluates the sum over j
        (lift ∘ head_beta >=> λ term, match term with
          | `(%%e₁i * %%e₂j * %%tableij) := do
              (e₁i', e₁i_pf) ← simp_times_table.trans (converter.lift norm_vec_cons) e₁i,
              (e₂j', e₂j_pf) ← simp_times_table.trans (converter.lift norm_vec_cons) e₂j,
              (tableij', tableij_pf) ← simp_times_table.trans (λ e, match e with
              | (expr.app (expr.app ti@(expr.app t i) j) k) := do
                (ti', ti_pf) ← lift $ norm_vec_cons ti,
                (tij', tij_pf) ← lift $ norm_vec_cons (expr.app ti' j),
                pf ← lift $ i_to_expr ``(tactic.times_table.eval_vec_cons_pf %%t %%i %%j %%k %%ti_pf %%tij_pf),
                pure (expr.app tij' k, pf)
              | e := lift $ pformat!"expected `t.table i j k`, got {e}" >>= fail
              end) tableij,
              (e', e_pf) ← lift $ i_to_expr ``(%%e₁i' * %%e₂j' * %%tableij') >>= or_refl_conv norm_num.derive,
              pf ← lift $ i_to_expr ``(tactic.times_table.eval_repr_repr_table %%e₁i_pf %%e₂j_pf %%tableij_pf %%e_pf),
              pure (e', pf)
          | e := lift $ pformat!"expected `t.basis.repr e₁ i * t.basis.repr e₂ j * t.table i j k`, got {e}" >>= fail
          end))
      e,
    eq ← lift $ mk_app `tactic.times_table.eval_repr_mul [t, k, e₁, e₂, e', e_eq],
    pure (e', eq)
| `(%%e₁ ^ %%n) := trace_error "pow" $ do
  match norm_num.match_numeral n with
  | norm_num.match_numeral_result.zero := do
    one ← lift $ expr.of_nat S 1,
    (one', one_eq) ← eval one,
    eq ← lift $ i_to_expr ``(tactic.times_table.eval_pow_zero %%t %%k %%e₁ %%one_eq),
    pure (one', eq)
  | norm_num.match_numeral_result.one := do
    (e', e₁_eq) ← eval e₁,
    eq ← lift $ i_to_expr ``(tactic.times_table.eval_pow_one %%t %%k %%e₁_eq),
    pure (e', eq)
  | norm_num.match_numeral_result.bit0 b := do
    e₁' ← lift $ i_to_expr ``((%%e₁ ^ %%b) * (%%e₁ ^ %%b)),
    (e', e_eq) ← eval e₁',
    eq ← lift $ i_to_expr ``(tactic.times_table.eval_pow_bit0 %%t %%k %%b %%e_eq),
    pure (e', eq)
  | norm_num.match_numeral_result.bit1 b := do
    e₁' ← lift $ i_to_expr ``((%%e₁ ^ %%b) * (%%e₁ ^ %%b) * %%e₁),
    (e', e_eq) ← eval e₁',
    eq ← lift $ i_to_expr ``(tactic.times_table.eval_pow_bit1 %%t %%k %%b %%e_eq),
    pure (e', eq)

  | _ := lift $ failed
  end
| e := do
  full_e ← state_t.lift $ i_to_expr ``(basis.repr (times_table.basis %%t) %%e %%k),
  (e', pr) ← simp_times_table full_e,
  pure (e', pr)

meta def run_converter : converter → expr → tactic (expr × expr)
| c e := do
  (simps, _) ← mk_simp_set tt [`times_table_simps] [],
  (result, _) ← (c e).run { simps := simps },
  pure result

set_option eqn_compiler.max_steps 4096

/-- `norm_num` extension for expressions of the form `basis.repr (times_table.basis _) _` -/
@[norm_num]
protected meta def norm : expr → tactic (expr × expr)
| ek@(expr.app (expr.app coe_fn' (expr.app `(coe_fn (basis.repr (times_table.basis %%t))) e)) k) := do
  -- TODO: check that `coe_fn'` is indeed `⇑`
  ι ← infer_type k,
  S ← infer_type e,
  R ← infer_type ek,
  (e', pf) ← tactic.trace_error "Internal error in `tactic.times_table.eval`:" $ run_converter (tactic.times_table.eval ι R S t k) e,
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
        do (new_e, pr) ← step e,
           guard (¬ new_e =ₐ e) <|> (trace "rewriting was idempotent: " >> trace e >> trace " → " >> trace new_e >> failure),
           return ((), new_e, some pr, tt))
      `eq e,
    return (e', pr)

end tactic.times_table

namespace sqrt_2_sqrt_3

set_option profiler true
-- set_option trace.type_context.is_def_eq_detail true
-- set_option trace.class_instances true

example (x y : sqrt_2_sqrt_3) : x * y = y * x :=
begin
  cases x, cases y,
  apply sqrt_2_sqrt_3.times_table.basis.ext_elem (λ k, _),
  /-
  -- 2.2s
  do { (new_t, pr) ← tactic.target >>= (tactic.times_table.conv_subexpressions tactic.times_table.norm),
        tactic.infer_type pr >>= tactic.trace,
        tactic.replace_target new_t pr },
  -/
  norm_num1, -- 2.4s
  -- norm_num, -- 3.5s
  fin_cases k; ring
end

#exit

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

-- TODO: could generalize to infinite ι
noncomputable def has_mul_of_table {ι R S : Type*} [fintype ι] [semiring R]
  [hS : add_comm_monoid S] [module R S] (b : basis ι R S) (table : ι → ι → ι → R) :
    has_mul S :=
{ mul := λ x y, b.equiv_fun.symm (λ k, ∑ i j, b.repr x i * b.repr y j * table i j k) }

lemma mul_def' {ι R S : Type*} [fintype ι] [semiring R]
  [hS : add_comm_monoid S] [module R S] (b : basis ι R S) (table : ι → ι → ι → R)
  (x y : S) (k : ι) :
  b.repr (by { letI := has_mul_of_table b table; exact x * y }) k = ∑ i j, b.repr x i * b.repr y j * table i j k :=
show b.repr (b.equiv_fun.symm (λ k, ∑ i j, b.repr x i * b.repr y j * table i j k)) k =
  ∑ i j, b.repr x i * b.repr y j * table i j k,
by simp only [← b.equiv_fun_apply, b.equiv_fun.apply_symm_apply]

lemma mul_def {ι R S : Type*} [fintype ι] [semiring R]
  [hS : add_comm_monoid S] [module R S] (b : basis ι R S) (table : ι → ι → ι → R)
  (i j k : ι) :
  b.repr (by { letI := has_mul_of_table b table; exact b i * b j }) k = table i j k :=
begin
  letI := classical.dec_eq ι,
  rw [mul_def', fintype.sum_eq_single i, fintype.sum_eq_single j],
  { simp },
  { intros k hk, simp [finsupp.single_eq_of_ne hk.symm] },
  { intros k hk, simp [finsupp.single_eq_of_ne hk.symm] },
end

-- TODO: could generalize to infinite ι
-- See note [reducible non-instances]
@[reducible]
noncomputable def non_unital_non_assoc_semiring_of_table {ι R S : Type*} [fintype ι] [semiring R]
  [hS : add_comm_monoid S] [module R S] (b : basis ι R S) (table : ι → ι → ι → R) :
    non_unital_non_assoc_semiring S :=
{ zero := 0,
  add := (+),
  mul := λ x y, b.equiv_fun.symm (λ k, ∑ i j, b.repr x i * b.repr y j * table i j k),
  zero_mul := λ x, b.ext_elem (λ k, by { rw mul_def', simp only [_root_.map_zero, finsupp.zero_apply, zero_mul, finset.sum_const_zero] }),
  mul_zero := λ x, b.ext_elem (λ k, by { rw mul_def', simp only [_root_.map_zero, finsupp.zero_apply, mul_zero, zero_mul, finset.sum_const_zero] }),
  left_distrib := λ x y z, b.ext_elem (λ k, by { rw mul_def', simp only [_root_.map_add, finsupp.add_apply, mul_add, add_mul, finset.sum_add_distrib, ← b.equiv_fun_apply, b.equiv_fun.apply_symm_apply] }),
  right_distrib := λ x y z, b.ext_elem (λ k, by { rw mul_def', simp only [_root_.map_add, finsupp.add_apply, mul_add, add_mul, finset.sum_add_distrib, ← b.equiv_fun_apply, b.equiv_fun.apply_symm_apply] }),
  .. hS }

namespace sqrt_d

variables (d : ℚ)

def table : fin 2 → fin 2 → fin 2 → ℚ :=
![![![1, 0], ![0, 1]],
  ![![1, 0], ![0, d]]]

-- @[irreducible]
def sqrt_d (d : ℚ) := fin 2 → ℚ

section

local attribute [semireducible] sqrt_d

variables {d}

def mk (a b : ℚ) : sqrt_d d := ![a, b]

variables (d)

def sqrt : sqrt_d d := ![0, 1]

instance : add_comm_group (sqrt_d d) := pi.add_comm_group

noncomputable instance : non_unital_non_assoc_semiring (sqrt_d d) :=
non_unital_non_assoc_semiring_of_table (pi.basis_fun ℚ (fin 2)) (table d)

instance : module ℚ (sqrt_d d) := pi.module _ _ _

noncomputable abbreviation basis : basis (fin 2) ℚ (sqrt_d d) := pi.basis_fun ℚ (fin 2)

instance : smul_comm_class ℚ (sqrt_d d) (sqrt_d d) :=
⟨λ m n a, (basis d).ext_elem (λ k, by { rw [smul_eq_mul, smul_eq_mul, linear_equiv.map_smul, finsupp.smul_apply, mul_def', mul_def'], simp [finset.mul_sum], refine finset.sum_congr rfl (λ i _, finset.sum_congr rfl (λ j _, _)), ring })⟩
instance : is_scalar_tower ℚ (sqrt_d d) (sqrt_d d) :=
⟨λ m n a, (basis d).ext_elem (λ k, by { rw [smul_eq_mul, smul_eq_mul, linear_equiv.map_smul, finsupp.smul_apply, mul_def', mul_def'], simp [finset.mul_sum], refine finset.sum_congr rfl (λ i _, finset.sum_congr rfl (λ j _, _)), ring })⟩

noncomputable def times_table : times_table (fin 2) ℚ (sqrt_d d) :=
{ basis := by convert pi.basis_fun ℚ (fin 2),
  table := table d,
  mul_def := mul_def _ _ }

@[elab_as_eliminator]
lemma cases (x : sqrt_d d) (p : sqrt_d d → Prop) (h : p (mk (x 0) (x 1))) :
  p x :=
sorry

end

@[times_table_simps] lemma table_apply (i j k : fin 2) :
  (sqrt_d.times_table d).table i j k =
  ![![![1, 0], ![0, 1]],
    ![![1, 0], ![0, d]]] i j k := rfl

@[times_table_simps] lemma repr_mk (a b : ℚ) (i : fin 2) :
  (sqrt_d.times_table d).basis.repr (mk a b) i = ![a, b] i :=
rfl

example (x y : sqrt_d d) : x * y = y * x :=
begin
  refine cases _ x _ _, refine cases _ y _ _,
  apply (sqrt_d.times_table d).basis.ext_elem (λ k, _),
  do { (new_t, pr) ← tactic.target >>= (tactic.times_table.conv_subexpressions tactic.times_table.norm),
        tactic.replace_target new_t pr },
end

end sqrt_d
