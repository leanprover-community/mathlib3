/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.big_operators.basic
import data.int.interval
import tactic.norm_num

/-! ### `norm_num` plugin for big operators

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This `norm_num` plugin provides support for computing sums and products of
lists, multisets and finsets.

Example goals this plugin can solve:

 * `∑ i in finset.range 10, (i^2 : ℕ) = 285`
 * `Π i in {1, 4, 9, 16}, nat.sqrt i = 24`
 * `([1, 2, 1, 3]).sum = 7`

## Implementation notes

The tactic works by first converting the expression denoting the collection
(list, multiset, finset) to a list of expressions denoting each element. For
finsets, this involves erasing duplicate elements (the tactic fails if equality
or disequality cannot be determined).

After rewriting the big operator to a product/sum of lists, we evaluate this
using `norm_num` itself to handle multiplication/addition.

Finally, we package up the result using some congruence lemmas.

-/

open tactic

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

lemma list.map_cons_congr {α β : Type*} (f : α → β) {x : α} {xs : list α} {fx : β} {fxs : list β}
  (h₁ : f x = fx) (h₂ : xs.map f = fxs) : (x :: xs).map f = fx :: fxs :=
by rw [list.map_cons, h₁, h₂]

/-- Apply `ef : α → β` to all elements of the list, constructing an equality proof. -/
meta def eval_list_map (ef : expr) : list expr → tactic (list expr × expr)
| [] := do
  eq ← i_to_expr ``(list.map_nil %%ef),
  pure ([], eq)
| (x :: xs) := do
  (fx, fx_eq) ← or_refl_conv norm_num.derive (expr.app ef x),
  (fxs, fxs_eq) ← eval_list_map xs,
  eq ← i_to_expr ``(list.map_cons_congr %%ef %%fx_eq %%fxs_eq),
  pure (fx :: fxs, eq)

lemma list.cons_congr {α : Type*} (x : α) {xs : list α} {xs' : list α} (xs_eq : xs' = xs) :
  x :: xs' = x :: xs :=
by rw xs_eq

lemma list.map_congr {α β : Type*} (f : α → β) {xs xs' : list α}
  {ys : list β} (xs_eq : xs = xs') (ys_eq : xs'.map f = ys) :
  xs.map f = ys :=
by rw [← ys_eq, xs_eq]

/-- Convert an expression denoting a list to a list of elements. -/
meta def eval_list : expr → tactic (list expr × expr)
| e@`(list.nil) := do
  eq ← mk_eq_refl e,
  pure ([], eq)
| e@`(list.cons %%x %%xs) := do
  (xs, xs_eq) ← eval_list xs,
  eq ← i_to_expr ``(list.cons_congr %%x %%xs_eq),
  pure (x :: xs, eq)
| e@`(list.range %%en) := do
  n ← expr.to_nat en,
  eis ← (list.range n).mmap (λ i, expr.of_nat `(ℕ) i),
  eq ← mk_eq_refl e,
  pure (eis, eq)
| `(@list.map %%α %%β %%ef %%exs) := do
  (xs, xs_eq) ← eval_list exs,
  (ys, ys_eq) ← eval_list_map ef xs,
  eq ← i_to_expr ``(list.map_congr %%ef %%xs_eq %%ys_eq),
  pure (ys, eq)
| e@`(@list.fin_range %%en) := do
  n ← expr.to_nat en,
  eis ← (list.fin_range n).mmap (λ i, expr.of_nat `(fin %%en) i),
  eq ← mk_eq_refl e,
  pure (eis, eq)
| e := fail (to_fmt "Unknown list expression" ++ format.line ++ to_fmt e)

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
meta def eval_multiset : expr → tactic (list expr × expr)
| e@`(@has_zero.zero (multiset _) _) := do
  eq ← mk_eq_refl e,
  pure ([], eq)
| e@`(has_emptyc.emptyc) := do
  eq ← mk_eq_refl e,
  pure ([], eq)
| e@`(has_singleton.singleton %%x) := do
  eq ← mk_eq_refl e,
  pure ([x], eq)
| e@`(multiset.cons %%x %%xs) := do
  (xs, xs_eq) ← eval_multiset xs,
  eq ← i_to_expr ``(multiset.cons_congr %%x %%xs_eq),
  pure (x :: xs, eq)
| e@`(@@has_insert.insert multiset.has_insert %%x %%xs) := do
  (xs, xs_eq) ← eval_multiset xs,
  eq ← i_to_expr ``(multiset.cons_congr %%x %%xs_eq),
  pure (x :: xs, eq)
| e@`(multiset.range %%en) := do
  n ← expr.to_nat en,
  eis ← (list.range n).mmap (λ i, expr.of_nat `(ℕ) i),
  eq ← mk_eq_refl e,
  pure (eis, eq)
| `(@@coe (@@coe_to_lift (@@coe_base (multiset.has_coe))) %%exs) := do
  (xs, xs_eq) ← eval_list exs,
  eq ← i_to_expr ``(congr_arg coe %%xs_eq),
  pure (xs, eq)
| `(@multiset.map %%α %%β %%ef %%exs) := do
  (xs, xs_eq) ← eval_multiset exs,
  (ys, ys_eq) ← eval_list_map ef xs,
  eq ← i_to_expr ``(multiset.map_congr %%ef %%xs_eq %%ys_eq),
  pure (ys, eq)
| e := fail (to_fmt "Unknown multiset expression" ++ format.line ++ to_fmt e)

lemma finset.mk_congr {α : Type*} {xs xs' : multiset α} (h : xs = xs') (nd nd') :
  finset.mk xs nd = finset.mk xs' nd' :=
by congr; assumption

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

/-- For now this only works on types that are contiguous subsets of the integers -/
meta def eval_finset_interval :
  expr → tactic (option (list expr × expr × expr))
| e@`(@finset.Icc %%α %%inst_1 %%inst_2 %%ea %%eb) := do
  a ← expr.to_int ea,
  b ← expr.to_int eb,
  eis ← (finset.Icc a b).val.unquot.mmap (λ i, expr.of_int α i),
  eq ← mk_eq_refl e,
  nd ← i_to_expr ``(finset.nodup %%e),
  pure (eis, eq, nd)
| e@`(@finset.Ico %%α %%inst_1 %%inst_2 %%ea %%eb) := do
  a ← expr.to_int ea,
  b ← expr.to_int eb,
  eis ← (finset.Ico a b).val.unquot.mmap (λ i, expr.of_int α i),
  eq ← mk_eq_refl e,
  nd ← i_to_expr ``(finset.nodup %%e),
  pure (eis, eq, nd)
| e@`(@finset.Ioc %%α %%inst_1 %%inst_2 %%ea %%eb) := do
  a ← expr.to_int ea,
  b ← expr.to_int eb,
  eis ← (finset.Ioc a b).val.unquot.mmap (λ i, expr.of_int α i),
  eq ← mk_eq_refl e,
  nd ← i_to_expr ``(finset.nodup %%e),
  pure (eis, eq, nd)
| e@`(@finset.Ioo %%α %%inst_1 %%inst_2 %%ea %%eb) := do
  a ← expr.to_int ea,
  b ← expr.to_int eb,
  eis ← (finset.Ioo a b).val.unquot.mmap (λ i, expr.of_int α i),
  eq ← mk_eq_refl e,
  nd ← i_to_expr ``(finset.nodup %%e),
  pure (eis, eq, nd)
| _ := pure none

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
| e@`(finset.mk %%val %%nd) := do
  (val', eq) ← eval_multiset val,
  eq' ← i_to_expr ``(finset.mk_congr %%eq _ _),
  pure (val', eq', nd)
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
| e := do
  -- try some other parsers
  some v ← eval_finset_interval e |
    fail (to_fmt "Unknown finset expression" ++ format.line ++ to_fmt e),
  pure v

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
producing the evaluated expression and an equality proof. -/
meta def list.prove_prod_map (β ef : expr) (xs : list expr) : tactic (expr × expr) := do
  (fxs, fxs_eq) ← eval_list_map ef xs,
  (prod, prod_eq) ← list.prove_prod β fxs,
  eq ← i_to_expr ``(list.prod_congr %%fxs_eq %%prod_eq),
  pure (prod, eq)

/-- Evaluate `(%%xs.map (%%ef : %%α → %%β)).sum`,
producing the evaluated expression and an equality proof. -/
meta def list.prove_sum_map (β ef : expr) (xs : list expr) : tactic (expr × expr) := do
  (fxs, fxs_eq) ← eval_list_map ef xs,
  (sum, sum_eq) ← list.prove_sum β fxs,
  eq ← i_to_expr ``(list.sum_congr %%fxs_eq %%sum_eq),
  pure (sum, eq)

@[to_additive]
lemma finset.eval_prod_of_list {β α : Type*} [comm_monoid β]
  (s : finset α) (f : α → β) {is : list α} (his : is.nodup)
  (hs : finset.mk ↑is (multiset.coe_nodup.mpr his) = s)
  {x : β} (hx : (is.map f).prod = x) :
  s.prod f = x :=
by rw [← hs, finset.prod_mk, multiset.coe_map, multiset.coe_prod, hx]

/-- `norm_num` plugin for evaluating big operators:
 * `list.prod`
 * `list.sum`
 * `multiset.prod`
 * `multiset.sum`
 * `finset.prod`
 * `finset.sum`
-/
@[norm_num] meta def eval_big_operators : expr → tactic (expr × expr)
| `(@list.prod %%α %%inst1 %%inst2 %%exs) :=
tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq) ← eval_list exs,
  (result, sum_eq) ← list.prove_prod α xs,
  pf ← i_to_expr ``(list.prod_congr %%list_eq %%sum_eq),
  pure (result, pf)
| `(@list.sum %%α %%inst1 %%inst2 %%exs) :=
tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq) ← eval_list exs,
  (result, sum_eq) ← list.prove_sum α xs,
  pf ← i_to_expr ``(list.sum_congr %%list_eq %%sum_eq),
  pure (result, pf)
| `(@multiset.prod %%α %%inst %%exs) :=
tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq) ← eval_multiset exs,
  (result, sum_eq) ← list.prove_prod α xs,
  pf ← i_to_expr ``(multiset.prod_congr %%list_eq %%sum_eq),
  pure (result, pf)
| `(@multiset.sum %%α %%inst %%exs) :=
tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq) ← eval_multiset exs,
  (result, sum_eq) ← list.prove_sum α xs,
  pf ← i_to_expr ``(multiset.sum_congr %%list_eq %%sum_eq),
  pure (result, pf)
| `(@finset.prod %%β %%α %%inst %%es %%ef) :=
tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq, nodup) ← eval_finset decide_eq es,
  (result, sum_eq) ← list.prove_prod_map β ef xs,
  pf ← i_to_expr ``(finset.eval_prod_of_list %%es %%ef %%nodup %%list_eq %%sum_eq),
  pure (result, pf)
| `(@finset.sum %%β %%α %%inst %%es %%ef) :=
tactic.trace_error "Internal error in `tactic.norm_num.eval_big_operators`:" $ do
  (xs, list_eq, nodup) ← eval_finset decide_eq es,
  (result, sum_eq) ← list.prove_sum_map β ef xs,
  pf ← i_to_expr ``(finset.eval_sum_of_list %%es %%ef %%nodup %%list_eq %%sum_eq),
  pure (result, pf)
| _ := failed

end tactic.norm_num
