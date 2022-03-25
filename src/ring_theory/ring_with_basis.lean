import data.nat.succ_pred
import linear_algebra.basis
import ring_theory.adjoin_root
import ring_theory.power_basis

open_locale big_operators

structure times_table (ι R S : Type*)
  [comm_semiring R] [semiring S] [algebra R S] :=
(basis : basis ι R S)
(table : ι → ι → ι → R)
(mul_def : ∀ i j k, basis.repr (basis i * basis j) k = table i j k)

section semiring
variables {ι R S : Type*} [comm_ring R] [comm_ring S] [algebra R S]

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
  simp only [algebra.smul_def, mul_assoc, mul_left_comm],
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

@[simp] lemma basis.repr_bit0 (b : basis ι R S) (x : S) (i : ι) :
  b.repr (bit0 x) i = bit0 (b.repr x i) :=
by { unfold bit0, simp only [_root_.map_add, finsupp.coe_add, pi.add_apply] }
@[simp] lemma basis.repr_bit1 (b : basis ι R S) (x : S) (i : ι) :
  b.repr (bit1 x) i = bit0 (b.repr x i) + b.repr 1 i :=
by { unfold bit0 bit1, simp only [_root_.map_add, finsupp.coe_add, pi.add_apply] }

noncomputable def times_table.reindex {ι' : Type*} (t : times_table ι R S) (e : ι ≃ ι') :
  times_table ι' R S :=
{ basis := t.basis.reindex e,
  table := λ i j k, t.table (e.symm i) (e.symm j) (e.symm k),
  mul_def := λ i j k, by simpa only [basis.reindex_apply, basis.reindex_repr]
    using t.mul_def (e.symm i) (e.symm j) (e.symm k) }

end semiring

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

@[simp] lemma repr_one (i : fin 4) :
  sqrt_2_sqrt_3.basis.repr 1 i = ![1, 0, 0, 0] i := rfl

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

@[simp] lemma repr_mk (a b c d : ℚ) (i : fin 4) : sqrt_2_sqrt_3.basis.repr ⟨a, b, c, d⟩ i = ![a, b, c, d] i := rfl

def sqrt_2 : sqrt_2_sqrt_3 := ⟨0, 1, 0, 0⟩
@[simp] lemma repr_sqrt_2 (i : fin 4) : sqrt_2_sqrt_3.basis.repr sqrt_2 i = ![0, 1, 0, 0] i := rfl
def sqrt_3 : sqrt_2_sqrt_3 := ⟨0, 0, 1, 0⟩
@[simp] lemma repr_sqrt_3 (i : fin 4) : sqrt_2_sqrt_3.basis.repr sqrt_3 i = ![0, 0, 1, 0] i := rfl

@[simp] lemma sqrt_2_mul_sqrt_3 : sqrt_2 * sqrt_3 = _ := _

set_option profiler true

-- Top-down: easier to do with `simp`, but produces huge terms
example : (sqrt_2 + sqrt_3)^3 - 9 * (sqrt_2 + sqrt_3) = 2 * sqrt_2 :=
begin
  -- Work coefficient-wise.
  apply sqrt_2_sqrt_3.times_table.basis.ext_elem (λ k, _),
  -- Write the term as a product (TODO: efficient handling of exponentiation?)
  /- repeat { ring_nf SOP }, -/ simp only [pow_succ, pow_zero, mul_one],
  -- Use the times table for multiplications.
  simp only [_root_.map_add, finsupp.coe_add, pi.add_apply,
    _root_.map_sub, finsupp.coe_sub, pi.sub_apply,
    pi.mul_apply, times_table.unfold_mul],
  -- Determine what the values in the table refer to.
  simp only [sqrt_2_sqrt_3.times_table, sqrt_2_sqrt_3.table,
    basis.repr_bit0, basis.repr_bit1, repr_one, repr_sqrt_2, repr_sqrt_3, repr_mk],
  -- Clean up the expression.
  -- TODO: invent a norm_num plugin for finite sums
  by { simp only [fin.sum_univ_succ, fin.sum_univ_zero, matrix.cons_val_succ, matrix.cons_val_zero,
    -- The following ensures that the term produced by `simp` isn't overwhelmingly big:
    mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one],
  -- Finish the proof coefficientwise.
  fin_cases k; norm_num }
end

end sqrt_2_sqrt_3

section norm_num

open tactic

#print expr.to_list
#check expr.list

#check (∅ : finset ℕ)
#check ({1} : finset ℕ)

#print list.range_core

lemma not_mem_range_pf {n : ℕ} (x : ℕ) (hx : x < n) (ys : finset (fin n))
  (h : ∀ y ∈ ys, x < ↑y) : (⟨x, hx⟩ : fin n) ∉ ys :=
λ hx, (h _ hx).ne rfl

lemma forall_lt_succ {n : ℕ} (x : ℕ) (hx : x < n) (ys : finset (fin n))
  (h : ∀ y ∈ ys, x + 1 < y) :
  ∀ y ∈ (finset.cons (⟨x + 1, hx⟩ : fin n) ys (not_mem_range_pf _ ys h)),
    (⟨x, (succ_order.lt_succ x).trans hx⟩ : fin n) < y :=
begin
  simp only [finset.mem_cons],
  rintros y (rfl | hy),
  { exact succ_order.lt_succ x },
  { exact (succ_order.le_succ x).trans_lt (h y hy) }
end

/-- Given `ty` `n` `xs` `h : ∀ x ∈ xs, n < x`, return `[(0, proof that 0 ∉ (1 .. n-1 ++ xs)) .. n-1] ++ xs` -/
meta def expr.finset.fin_range (ty : expr) : nat → list (expr × expr) → expr → tactic (list (expr × expr))
| 0 l h := pure l
| (n + 1) l h := do
  elem ← expr.of_nat ty n,
  -- Prove that `n` is not in `l`
  acc ← i_to_expr ``(forall_lt_succ %%elem _ %%h),
  pf ← i_to_expr ``(not_mem_range_pf %%elem _ %%acc),
  expr.finset.fin_range n ((elem, pf) :: l) acc

#check (finset.forall_mem_empty_iff _).mpr trivial
#print result

meta def with_trace_errors {α : Type*} (t : tactic α) : tactic α :=
λ s, match t s with
| (result.success x s) := result.success x s
| (result.exception (some msg) pos s) := (tactic.trace (msg ()) >> fail (msg ())) s
| (result.exception none pos s) := (tactic.trace "failed!" >> failure) s
end

set_option trace.app_builder true

/-- Convert an expression defining a finset to a list of its constituent elements,
along with a proof this element has not been inserted before.

We return a list since the order of insertion is relevant for the second proof.
-/
meta def expr.to_finset : expr → tactic (list (expr × expr))
| `(has_emptyc.emptyc) := pure []
| `(has_singleton.singleton %%x) := do
  pf ← i_to_expr ``(finset.not_mem_empty %%x),
  pure [(x, pf)]
| `(@finset.cons %%x %%xs %%h) := list.cons (x, h) <$> xs.to_finset
| `(@@has_insert.insert (@@finset.has_insert %%dec) %%x %%xs) := failed -- TODO
| `(@@finset.univ %%ft) := do
  -- Convert the fintype instance expression `ft` to a list of its elements.
  -- We'll use `whnf` while unfolding semireducibles, which gives us either the `fintype.mk` constructor,
  -- or give up.
  ft ← whnf ft transparency.semireducible,
  match ft with
  | `(fintype.mk %%elems %%_) := expr.to_finset elems
  | _ := failed
  end
| `(finset.fin_range %%en) := do
  n ← en.to_nat,
  with_trace_errors (do
    pf ← i_to_expr ``((finset.forall_mem_empty_iff _).mpr trivial),
    infer_type pf >>= trace,
    expr.finset.fin_range `(fin %%en) n [] pf)
| _ := failed

#check has_emptyc.emptyc
#check i_to_expr

meta def expr.of_finset (α : expr) : list (expr × expr) → tactic expr
| [] := do
  i_to_expr ``(@has_emptyc.emptyc (finset %%α) _)
| ((x, hx) :: xs) := do
  exs ← expr.of_finset xs,
  i_to_expr ``(@finset.cons %%α %%x %%exs %%hx)

lemma finset.eval_sum_cons {β α : Type*} [add_comm_monoid β]
  (f : α → β) (s : finset α) (i : α) (h : i ∉ s) (x y : β)
  (h₁ : s.sum f = x) (h₂ : f i + x = y) : (s.cons i h).sum f = y :=
by rw [finset.sum_cons, h₁, h₂]

meta def finset.prove_sum (β α inst ef : expr) : list (expr × expr) → tactic (expr × expr)
| [] := do
  result ← expr.of_nat β 0,
  proof ← i_to_expr ``(@finset.sum_empty %%β %%α %%inst %%ef),
  pure (result, proof)
| ((x, hx) :: xs) := do
  result_pf ← finset.prove_sum xs,
  result ← i_to_expr ``(%%ef %%x + %%result_pf.1),
  res_pf ← (norm_num.derive result <|> (prod.mk result <$> mk_eq_refl result)),
  es ← expr.of_finset α xs,
  -- TODO: pass around `nodup (x :: xs)` instead?
  proof ← i_to_expr ``(finset.eval_sum_cons %%ef %%es %%x %%hx %%result_pf.1 %%res_pf.1 %%result_pf.2 %%res_pf.2),
  pure (res_pf.1, proof)

/-- `norm_num` plugin for evaluating `finset.prod` and `finset.sum`, and perhaps more. -/
@[norm_num] meta def finset.eval_fold : expr → tactic (expr × expr)
| `(@finset.sum %%β %%α %%inst %%es %%ef) := do
  s ← es.to_finset,
  finset.prove_sum β α inst ef s
| _ := failed

variables {α : Type*} [comm_ring α]

example (f : fin 0 → α) : ∑ i : fin 0, f i = 0 := by norm_num
example (f : fin 3 → α) : ∑ i : fin 3, f i = f 0 + f 1 + f 2 := by norm_num; ring
example (f : fin 4 → α) : ∑ i : fin 4, f i = f 0 + f 1 + f 2 + f 3 := by norm_num; ring

end norm_num
