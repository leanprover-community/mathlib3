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

/-- Run `t` while tracing any errors that are raised during evaluation of `t`. -/
meta def with_trace_errors {α : Type*} (t : tactic α) : tactic α :=
λ s, match t s with
| (result.success x s) := result.success x s
| (result.exception (some msg) pos s) := (tactic.trace (msg ()) >> fail (msg ())) s
| (result.exception none pos s) := (tactic.trace "failed!" >> failure) s
end

#print finset.has_insert
#print decidable_rel
#print decidable

#check finset.insert_eq_of_mem
#check list.nodup_cons

lemma list.nodup_cons_of_coe_finset_eq {α : Type*} [decidable_eq α] (x : α) (xs : finset α)
  (h : x ∉ xs) {xs' : list α} (nd_xs : xs'.nodup)
  (hxs' : finset.mk ↑xs' (multiset.coe_nodup.mpr nd_xs) = xs) :
  (x :: xs').nodup :=
list.nodup_cons.mpr ⟨by simpa [← hxs'] using h, nd_xs⟩

lemma finset.coe_list_eq_insert_of_mem {α : Type*} [decidable_eq α] (x : α) (xs : finset α)
  (h : x ∉ xs) {xs' : list α} (nd_xs : xs'.nodup) (nd_xxs : (x :: xs').nodup)
  (hxs' : finset.mk ↑xs' (multiset.coe_nodup.mpr nd_xs) = xs) :
  finset.mk ↑(x :: xs') (multiset.coe_nodup.mpr nd_xxs) = insert x xs :=
by { rw [← finset.val_inj, finset.insert_val_of_not_mem h, ← hxs'], simp only [multiset.cons_coe] }

lemma finset.coe_list_cons_eq_insert {α : Type*} [decidable_eq α] (x : α) (xs : finset α)
  (h : x ∉ xs) {xs' : list α} (nd_xs : xs'.nodup) (nd_xxs : (x :: xs').nodup)
  (hxs' : finset.mk ↑xs' (multiset.coe_nodup.mpr nd_xs) = xs) :
  finset.mk ↑(x :: xs') (multiset.coe_nodup.mpr nd_xxs) = insert x xs :=
by { rw [← finset.val_inj, finset.insert_val_of_not_mem h, ← hxs'], simp only [multiset.cons_coe] }

/-- Convert an expression denoting a finset to a list of elements,
a proof that this list is equal to the original finset,
and a proof that the list contains no duplicates. -/
meta def expr.finset_to_list : expr → tactic (list expr × expr × expr)
| e@`(has_emptyc.emptyc) := do
  eq ← mk_eq_refl e,
  nd ← i_to_expr ``(list.nodup_nil),
  pure ([], eq, nd)
| e@`(has_singleton.singleton %%x) := do
  eq ← mk_eq_refl e,
  nd ← i_to_expr ``(list.nodup_singleton %%x),
  pure ([x], eq, nd)
| e@`(@finset.cons %%x %%xs %%h) := do
  eq ← mk_eq_refl e,
  nd ← i_to_expr ``(list.nodup_singleton %%x),
  pure ([x], eq, nd)
| `(@@has_insert.insert (@@finset.has_insert %%dec) %%x %%xs) := do
  -- Try and use `dec_trivial` to decide whether `x ∈ xs`
  -- TODO: we should be able to use `norm_num` itself for this!
  (exs, xs_eq, xs_nd) ← expr.finset_to_list xs,
  is_mem ← i_to_expr ``(decidable (%%x ∈ %%xs)) >>= mk_instance,
  dec_mem ← whnf is_mem transparency.semireducible,
  match dec_mem with
  | `(decidable.is_true %%mem) := do
    pf ← i_to_expr ``(eq.trans %%xs_eq $ eq.symm $ @finset.insert_eq_of_mem _ _ %%xs %%x %%mem),
    pure (exs, pf, xs_nd)
  | `(decidable.is_false %%nmem) := do
    nd ← i_to_expr ``(list.nodup_cons_of_coe_finset_eq %%x %%xs %%nmem %%xs_nd %%xs_eq),
    pf ← i_to_expr ``(finset.coe_list_cons_eq_insert %%x %%xs %%nmem %%xs_nd %%nd %%xs_eq),
    pure (x :: exs, pf, nd)
  | e := fail (to_fmt "Unknown decidable expression" ++ format.line ++ to_fmt dec_mem)
  end
| `(@@finset.univ %%ft) := do
  -- Convert the fintype instance expression `ft` to a list of its elements.
  -- We'll use `whnf` while unfolding semireducibles, which gives us either the `fintype.mk` constructor,
  -- or give up.
  ft ← whnf ft transparency.semireducible,
  match ft with
  | `(fintype.mk %%elems %%_) := expr.finset_to_list elems
  | _ := fail (to_fmt "Unknown fintype expression" ++ format.line ++ to_fmt ft)
  end
| e@`(finset.fin_range %%en) := do
  n ← expr.to_nat en,
  eis ← (list.fin_range n).mmap (λ i, expr.of_nat `(fin %%en) i),
  eq ← mk_eq_refl e,
  nd ← i_to_expr ``(list.nodup_fin_range %%en),
  pure (eis, eq, nd)
| e := fail (to_fmt "Unknown finset expression" ++ format.line ++ to_fmt e)

/-- Convert a list of expressions to an expression denoting the list of those expressions. -/
meta def expr.of_list (α : expr) : list expr → tactic expr
| [] := i_to_expr ``(@list.nil %%α)
| (x :: xs) := do
  exs ← expr.of_list xs,
  i_to_expr ``(@list.cons %%α %%x %%exs)

@[to_additive]
lemma list.prod_map_cons {β α : Type*} [monoid β] (f : α → β) (is : list α) (i : α)
  (x y : β) (his : (is.map f).prod = x) (hi : f i * x = y) : ((i :: is).map f).prod = y :=
by rw [list.map_cons, list.prod_cons, his, hi]

/-- Evaluate `(%%xs.map (%%ef : %%α → %%β)).sum`,
producing the evaluated expression and an equality proof. -/
meta def list.prove_sum_map (β α ef : expr) : list expr → tactic (expr × expr)
| [] := do
  result ← expr.of_nat β 0,
  proof ← i_to_expr ``(@list.sum_nil %%β _),
  pure (result, proof)
| (x :: xs) := do
  eval_xs ← list.prove_sum_map xs,
  xxs ← i_to_expr ``(%%ef %%x + %%eval_xs.1),
  eval_xxs ← (norm_num.derive xxs <|> (prod.mk xxs <$> mk_eq_refl xxs)),
  exs ← expr.of_list α xs,
  proof ← i_to_expr ``(list.sum_map_cons %%ef %%exs %%x %%eval_xs.1 %%eval_xxs.1 %%eval_xs.2 %%eval_xxs.2),
  pure (eval_xxs.1, proof)

@[to_additive]
lemma finset.eval_prod_of_list {β α : Type*} [comm_monoid β]
  (s : finset α) (f : α → β) {is : list α} (his : is.nodup)
  (hs : finset.mk ↑is (multiset.coe_nodup.mpr his) = s)
  {x : β} (hx : (is.map f).prod = x) :
  s.prod f = x :=
by rw [← hs, finset.prod_mk, multiset.coe_map, multiset.coe_prod, hx]

/-- `norm_num` plugin for evaluating `finset.prod` and `finset.sum`, and perhaps more. -/
@[norm_num] meta def finset.eval_fold : expr → tactic (expr × expr)
| `(@finset.sum %%β %%α %%inst %%es %%ef) := with_trace_errors $ do
  (xs, list_eq, nodup) ← es.finset_to_list,
  (result, sum_eq) ← list.prove_sum_map β α ef xs,
  pf ← i_to_expr ``(finset.eval_sum_of_list %%es %%ef %%nodup %%list_eq %%sum_eq),
  pure (result, pf)
| _ := failed

variables {α : Type*} [comm_ring α]

set_option profiler true

example (f : fin 0 → α) : ∑ i : fin 0, f i = 0 := by norm_num
example (f : ℕ → α) : ∑ i in (∅ : finset ℕ), f i = 0 := by norm_num
example (f : fin 3 → α) : ∑ i : fin 3, f i = f 0 + f 1 + f 2 := by norm_num; ring
example (f : fin 4 → α) : ∑ i : fin 4, f i = f 0 + f 1 + f 2 + f 3 := by norm_num; ring
example (f : ℕ → α) : ∑ i in {0, 1, 2}, f i = f 0 + f 1 + f 2 := by norm_num; ring
example (f : ℕ → α) : ∑ i in {0, 2, 2, 3, 1, 0}, f i = f 0 + f 1 + f 2 + f 3 := by norm_num; ring

end norm_num
