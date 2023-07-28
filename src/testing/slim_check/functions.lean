/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import data.list.sigma
import data.int.range
import data.finsupp.defs
import data.finsupp.to_dfinsupp
import tactic.pretty_cases
import testing.slim_check.sampleable
import testing.slim_check.testable

/-!
## `slim_check`: generators for functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `sampleable` instances for `α → β` functions and
`ℤ → ℤ` injective functions.

Functions are generated by creating a list of pairs and one more value
using the list as a lookup table and resorting to the additional value
when a value is not found in the table.

Injective functions are generated by creating a list of numbers and
a permutation of that list. The permutation insures that every input
is mapped to a unique output. When an input is not found in the list
the input itself is used as an output.

Injective functions `f : α → α` could be generated easily instead of
`ℤ → ℤ` by generating a `list α`, removing duplicates and creating a
permutations. One has to be careful when generating the domain to make
if vast enough that, when generating arguments to apply `f` to,
they argument should be likely to lie in the domain of `f`. This is
the reason that injective functions `f : ℤ → ℤ` are generated by
fixing the domain to the range `[-2*size .. -2*size]`, with `size`
the size parameter of the `gen` monad.

Much of the machinery provided in this file is applicable to generate
injective functions of type `α → α` and new instances should be easy
to define.

Other classes of functions such as monotone functions can generated using
similar techniques. For monotone functions, generating two lists, sorting them
and matching them should suffice, with appropriate default values.
Some care must be taken for shrinking such functions to make sure
their defining property is invariant through shrinking. Injective
functions are an example of how complicated it can get.
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Sort w}

namespace slim_check

/-- Data structure specifying a total function using a list of pairs
and a default value returned when the input is not in the domain of
the partial function.

`with_default f y` encodes `x ↦ f x` when `x ∈ f` and `x ↦ y`
otherwise.

We use `Σ` to encode mappings instead of `×` because we
rely on the association list API defined in `data.list.sigma`.
 -/
inductive total_function (α : Type u) (β : Type v) : Type (max u v)
| with_default : list (Σ _ : α, β) → β → total_function

instance total_function.inhabited [inhabited β] : inhabited (total_function α β) :=
⟨ total_function.with_default ∅ default ⟩

namespace total_function

/-- Apply a total function to an argument. -/
def apply [decidable_eq α] : total_function α β → α → β
| (total_function.with_default m y) x := (m.lookup x).get_or_else y

/--
Implementation of `has_repr (total_function α β)`.

Creates a string for a given `finmap` and output, `x₀ ↦ y₀, .. xₙ ↦ yₙ`
for each of the entries. The brackets are provided by the calling function.
-/
def repr_aux [has_repr α] [has_repr β] (m : list (Σ _ : α, β)) : string :=
string.join $ list.qsort (λ x y, x < y)
  (m.map $ λ x, sformat!"{repr $ sigma.fst x} ↦ {repr $ sigma.snd x}, ")

/--
Produce a string for a given `total_function`.
The output is of the form `[x₀ ↦ f x₀, .. xₙ ↦ f xₙ, _ ↦ y]`.
-/
protected def repr [has_repr α] [has_repr β] : total_function α β → string
| (total_function.with_default m y) := sformat!"[{repr_aux m}_ ↦ {has_repr.repr y}]"

instance (α : Type u) (β : Type v) [has_repr α] [has_repr β] : has_repr (total_function α β) :=
⟨ total_function.repr ⟩

/-- Create a `finmap` from a list of pairs. -/
def list.to_finmap' (xs : list (α × β)) : list (Σ _ : α, β) :=
xs.map prod.to_sigma

section

variables [sampleable α] [sampleable β]

/-- Redefine `sizeof` to follow the structure of `sampleable` instances. -/
def total.sizeof : total_function α β → ℕ
| ⟨m, x⟩ := 1 + @sizeof _ sampleable.wf m + sizeof x

@[priority 2000]
instance : has_sizeof (total_function α β) :=
⟨ total.sizeof ⟩

variables [decidable_eq α]

/-- Shrink a total function by shrinking the lists that represent it. -/
protected def shrink : shrink_fn (total_function α β)
| ⟨m, x⟩ := (sampleable.shrink (m, x)).map $ λ ⟨⟨m', x'⟩, h⟩, ⟨⟨list.dedupkeys m', x'⟩,
            lt_of_le_of_lt
              (by unfold_wf; refine @list.sizeof_dedupkeys _ _ _ (@sampleable.wf _ _) _) h ⟩

variables [has_repr α] [has_repr β]

instance pi.sampleable_ext : sampleable_ext (α → β) :=
{ proxy_repr := total_function α β,
  interp := total_function.apply,
  sample := do
  { xs ← (sampleable.sample (list (α × β)) : gen ((list (α × β)))),
    ⟨x⟩ ← (uliftable.up $ sample β : gen (ulift.{max u v} β)),
    pure $ total_function.with_default (list.to_finmap' xs) x },
  shrink := total_function.shrink }

end

section finsupp

variables [has_zero β]
/-- Map a total_function to one whose default value is zero so that it represents a finsupp. -/
@[simp]
def zero_default : total_function α β → total_function α β
| (with_default A y) := with_default A 0

variables [decidable_eq α] [decidable_eq β]
/-- The support of a zero default `total_function`. -/
@[simp]
def zero_default_supp : total_function α β → finset α
| (with_default A y) :=
  list.to_finset $ (A.dedupkeys.filter (λ ab, sigma.snd ab ≠ 0)).map sigma.fst

/-- Create a finitely supported function from a total function by taking the default value to
zero. -/
def apply_finsupp (tf : total_function α β) : α →₀ β :=
{ support := zero_default_supp tf,
  to_fun := tf.zero_default.apply,
  mem_support_to_fun := begin
    intro a,
    rcases tf with ⟨A, y⟩,
    simp only [apply, zero_default_supp, list.mem_map, list.mem_filter, exists_and_distrib_right,
      list.mem_to_finset, exists_eq_right, sigma.exists, ne.def, zero_default],
    split,
    { rintro ⟨od, hval, hod⟩,
      have := list.mem_lookup (list.nodupkeys_dedupkeys A) hval,
      rw (_ : list.lookup a A = od),
      { simpa, },
      { simpa [list.lookup_dedupkeys, with_top.some_eq_coe], }, },
    { intro h,
      use (A.lookup a).get_or_else (0 : β),
      rw ← list.lookup_dedupkeys at h ⊢,
      simp only [h, ←list.mem_lookup_iff A.nodupkeys_dedupkeys,
        and_true, not_false_iff, option.mem_def],
      cases list.lookup a A.dedupkeys,
      { simpa using h, },
      { simp, }, }
  end }

variables [sampleable α] [sampleable β]
instance finsupp.sampleable_ext [has_repr α] [has_repr β] : sampleable_ext (α →₀ β) :=
{ proxy_repr := total_function α β,
  interp := total_function.apply_finsupp,
  sample := (do
    xs ← (sampleable.sample (list (α × β)) : gen (list (α × β))),
    ⟨x⟩ ← (uliftable.up $ sample β : gen (ulift.{max u v} β)),
    pure $ total_function.with_default (list.to_finmap' xs) x),
  shrink := total_function.shrink }

-- TODO: support a non-constant codomain type
instance dfinsupp.sampleable_ext [has_repr α] [has_repr β] : sampleable_ext (Π₀ a : α, β) :=
{ proxy_repr := total_function α β,
  interp := finsupp.to_dfinsupp ∘ total_function.apply_finsupp,
  sample := (do
    xs ← (sampleable.sample (list (α × β)) : gen (list (α × β))),
    ⟨x⟩ ← (uliftable.up $ sample β : gen (ulift.{max u v} β)),
    pure $ total_function.with_default (list.to_finmap' xs) x),
  shrink := total_function.shrink }

end finsupp

section sampleable_ext
open sampleable_ext

@[priority 2000]
instance pi_pred.sampleable_ext [sampleable_ext (α → bool)] :
  sampleable_ext.{u+1} (α → Prop) :=
{ proxy_repr := proxy_repr (α → bool),
  interp := λ m x, interp (α → bool) m x,
  sample := sample (α → bool),
  shrink := shrink }

@[priority 2000]
instance pi_uncurry.sampleable_ext
  [sampleable_ext (α × β → γ)] : sampleable_ext.{imax (u+1) (v+1) w} (α → β → γ) :=
{ proxy_repr := proxy_repr (α × β → γ),
  interp := λ m x y, interp (α × β → γ) m (x, y),
  sample := sample (α × β → γ),
  shrink := shrink }

end sampleable_ext

end total_function

/--
Data structure specifying a total function using a list of pairs
and a default value returned when the input is not in the domain of
the partial function.

`map_to_self f` encodes `x ↦ f x` when `x ∈ f` and `x ↦ x`,
i.e. `x` to itself, otherwise.

We use `Σ` to encode mappings instead of `×` because we
rely on the association list API defined in `data.list.sigma`.
-/
inductive injective_function (α : Type u) : Type u
| map_to_self (xs : list (Σ _ : α, α)) :
    xs.map sigma.fst ~ xs.map sigma.snd → list.nodup (xs.map sigma.snd) → injective_function

instance : inhabited (injective_function α) :=
⟨ ⟨ [], list.perm.nil, list.nodup_nil ⟩ ⟩

namespace injective_function

/-- Apply a total function to an argument. -/
def apply [decidable_eq α] : injective_function α → α → α
| (injective_function.map_to_self m _ _) x := (m.lookup x).get_or_else x

/--
Produce a string for a given `total_function`.
The output is of the form `[x₀ ↦ f x₀, .. xₙ ↦ f xₙ, x ↦ x]`.
Unlike for `total_function`, the default value is not a constant
but the identity function.
-/
protected def repr [has_repr α] : injective_function α → string
| (injective_function.map_to_self m _ _) := sformat!"[{total_function.repr_aux m}x ↦ x]"

instance (α : Type u) [has_repr α] : has_repr (injective_function α) :=
⟨ injective_function.repr ⟩

/-- Interpret a list of pairs as a total function, defaulting to
the identity function when no entries are found for a given function -/
def list.apply_id [decidable_eq α] (xs : list (α × α)) (x : α) : α :=
((xs.map prod.to_sigma).lookup x).get_or_else x

@[simp]
lemma list.apply_id_cons [decidable_eq α] (xs : list (α × α)) (x y z : α) :
  list.apply_id ((y, z) :: xs) x = if y = x then z else list.apply_id xs x :=
by simp only [list.apply_id, list.lookup, eq_rec_constant, prod.to_sigma, list.map]; split_ifs; refl

open function _root_.list _root_.prod (to_sigma)
open _root_.nat

lemma list.apply_id_zip_eq [decidable_eq α] {xs ys : list α} (h₀ : list.nodup xs)
  (h₁ : xs.length = ys.length) (x y : α) (i : ℕ)
  (h₂ : xs.nth i = some x) :
  list.apply_id.{u} (xs.zip ys) x = y ↔ ys.nth i = some y :=
begin
  induction xs generalizing ys i,
  case list.nil : ys i h₁ h₂
  { cases h₂ },
  case list.cons : x' xs xs_ih ys i h₁ h₂
  { cases i,
    { injection h₂ with h₀ h₁, subst h₀,
      cases ys,
      { cases h₁ },
      { simp only [list.apply_id, to_sigma, option.get_or_else_some, nth, lookup_cons_eq,
                   zip_cons_cons, list.map], } },
    { cases ys,
      { cases h₁ },
      { cases h₀ with _ _ h₀ h₁,
        simp only [nth, zip_cons_cons, list.apply_id_cons] at h₂ ⊢,
        rw if_neg,
        { apply xs_ih; solve_by_elim [succ.inj] },
        { apply h₀, apply nth_mem h₂ } } } }
end

lemma apply_id_mem_iff [decidable_eq α] {xs ys : list α} (h₀ : list.nodup xs)
  (h₁ : xs ~ ys)
  (x : α) :
  list.apply_id.{u} (xs.zip ys) x ∈ ys ↔ x ∈ xs :=
begin
  simp only [list.apply_id],
  cases h₃ : (lookup x (map prod.to_sigma (xs.zip ys))),
  { dsimp [option.get_or_else],
    rw h₁.mem_iff },
  { have h₂ : ys.nodup := h₁.nodup_iff.1 h₀,
    replace h₁ : xs.length = ys.length := h₁.length_eq,
    dsimp,
    induction xs generalizing ys,
    case list.nil : ys h₃ h₂ h₁
    { contradiction },
    case list.cons : x' xs xs_ih ys h₃ h₂ h₁
    { cases ys with y ys,
      { cases h₃ },
      dsimp [lookup] at h₃, split_ifs at h₃,
      { subst x', subst val,
        simp only [mem_cons_iff, true_or, eq_self_iff_true], },
      { cases h₀ with _ _ h₀ h₅,
        cases h₂ with _ _ h₂ h₄,
        have h₆ := nat.succ.inj h₁,
        specialize @xs_ih h₅ ys h₃ h₄ h₆,
        simp only [ne.symm h, xs_ih, mem_cons_iff, false_or],
        suffices : val ∈ ys, tauto!,
        erw [← option.mem_def, mem_lookup_iff] at h₃,
        simp only [to_sigma, mem_map, heq_iff_eq, prod.exists] at h₃,
        rcases h₃ with ⟨a, b, h₃, h₄, h₅⟩,
        subst a, subst b,
        apply (mem_zip h₃).2,
        simp only [nodupkeys, keys, comp, prod.fst_to_sigma, map_map],
        rwa map_fst_zip _ _ (le_of_eq h₆) } } }
end

lemma list.apply_id_eq_self [decidable_eq α] {xs ys : list α} (x : α) :
  x ∉ xs → list.apply_id.{u} (xs.zip ys) x = x :=
begin
  intro h,
  dsimp [list.apply_id],
  rw lookup_eq_none.2, refl,
  simp only [keys, not_exists, to_sigma, exists_and_distrib_right, exists_eq_right, mem_map,
             comp_app, map_map, prod.exists],
  intros y hy,
  exact h (mem_zip hy).1,
end

lemma apply_id_injective [decidable_eq α] {xs ys : list α} (h₀ : list.nodup xs)
  (h₁ : xs ~ ys) : injective.{u+1 u+1} (list.apply_id (xs.zip ys)) :=
begin
  intros x y h,
  by_cases hx : x ∈ xs;
    by_cases hy : y ∈ xs,
  { rw mem_iff_nth at hx hy,
    cases hx with i hx,
    cases hy with j hy,
    suffices : some x = some y,
    { injection this },
    have h₂ := h₁.length_eq,
    rw [list.apply_id_zip_eq h₀ h₂ _ _ _ hx] at h,
    rw [← hx, ← hy], congr,
    apply nth_injective _ (h₁.nodup_iff.1 h₀),
    { symmetry, rw h,
      rw ← list.apply_id_zip_eq; assumption },
    { rw ← h₁.length_eq,
      rw nth_eq_some at hx,
      cases hx with hx hx',
      exact hx } },
  { rw ← apply_id_mem_iff h₀ h₁ at hx hy,
    rw h at hx,
    contradiction, },
  { rw ← apply_id_mem_iff h₀ h₁ at hx hy,
    rw h at hx,
    contradiction, },
  { rwa [list.apply_id_eq_self, list.apply_id_eq_self] at h; assumption },
end

open total_function (list.to_finmap')
open sampleable

/--
Remove a slice of length `m` at index `n` in a list and a permutation, maintaining the property
that it is a permutation.
-/
def perm.slice [decidable_eq α] (n m : ℕ) :
  (Σ' xs ys : list α, xs ~ ys ∧ ys.nodup) → (Σ' xs ys : list α, xs ~ ys ∧ ys.nodup)
| ⟨xs, ys, h, h'⟩ :=
  let xs' := list.slice n m xs in
  have h₀ : xs' ~ ys.inter xs',
    from perm.slice_inter _ _ h h',
  ⟨xs', ys.inter xs', h₀, h'.inter _⟩

/--
A lazy list, in decreasing order, of sizes that should be
sliced off a list of length `n`
-/
def slice_sizes : ℕ → lazy_list ℕ+
| n :=
if h : 0 < n then
  have n / 2 < n, from div_lt_self h dec_trivial,
  lazy_list.cons ⟨_, h⟩ (slice_sizes $ n / 2)
else lazy_list.nil

/--
Shrink a permutation of a list, slicing a segment in the middle.

The sizes of the slice being removed start at `n` (with `n` the length
of the list) and then `n / 2`, then `n / 4`, etc down to 1. The slices
will be taken at index `0`, `n / k`, `2n / k`, `3n / k`, etc.
-/
protected def shrink_perm {α : Type} [decidable_eq α] [has_sizeof α] :
  shrink_fn (Σ' xs ys : list α, xs ~ ys ∧ ys.nodup)
| xs := do
  let k := xs.1.length,
  n ← slice_sizes k,
  i ← lazy_list.of_list $ list.fin_range $ k / n,
  have ↑i * ↑n < xs.1.length,
    from nat.lt_of_div_lt_div
      (lt_of_le_of_lt (by simp only [nat.mul_div_cancel, gt_iff_lt, fin.val_eq_coe, pnat.pos]) i.2),
  pure ⟨perm.slice (i*n) n xs,
    by rcases xs with ⟨a,b,c,d⟩; dsimp [sizeof_lt]; unfold_wf; simp only [perm.slice];
       unfold_wf; apply list.sizeof_slice_lt _ _ n.2 _ this⟩

instance [has_sizeof α] : has_sizeof (injective_function α) :=
⟨ λ ⟨xs,_,_⟩, sizeof (xs.map sigma.fst) ⟩

/--
Shrink an injective function slicing a segment in the middle of the domain and removing
the corresponding elements in the codomain, hence maintaining the property that
one is a permutation of the other.
-/
protected def shrink {α : Type} [has_sizeof α] [decidable_eq α] : shrink_fn (injective_function α)
| ⟨xs, h₀, h₁⟩ := do
  ⟨⟨xs', ys', h₀, h₁⟩, h₂⟩ ← injective_function.shrink_perm ⟨_, _, h₀, h₁⟩,
  have h₃ : xs'.length ≤ ys'.length, from le_of_eq (perm.length_eq h₀),
  have h₄ : ys'.length ≤ xs'.length, from le_of_eq (perm.length_eq h₀.symm),
  pure ⟨⟨(list.zip xs' ys').map prod.to_sigma,
    by simp only [comp, map_fst_zip, map_snd_zip, *, prod.fst_to_sigma, prod.snd_to_sigma, map_map],
    by simp only [comp, map_snd_zip, *, prod.snd_to_sigma, map_map] ⟩,
    by revert h₂; dsimp [sizeof_lt]; unfold_wf;
       simp only [has_sizeof._match_1, map_map, comp, map_fst_zip, *, prod.fst_to_sigma];
       unfold_wf; intro h₂; convert h₂ ⟩

/-- Create an injective function from one list and a permutation of that list. -/
protected def mk (xs ys : list α) (h : xs ~ ys) (h' : ys.nodup) : injective_function α :=
have h₀ : xs.length ≤ ys.length, from le_of_eq h.length_eq,
have h₁ : ys.length ≤ xs.length, from le_of_eq h.length_eq.symm,
injective_function.map_to_self (list.to_finmap' (xs.zip ys))
  (by { simp only [list.to_finmap', comp, map_fst_zip, map_snd_zip, *,
                   prod.fst_to_sigma, prod.snd_to_sigma, map_map] })
  (by { simp only [list.to_finmap', comp, map_snd_zip, *, prod.snd_to_sigma, map_map] })

protected lemma injective [decidable_eq α] (f : injective_function α) :
  injective (apply f) :=
begin
  cases f with xs hperm hnodup,
  generalize h₀ : map sigma.fst xs = xs₀,
  generalize h₁ : xs.map (@id ((Σ _ : α, α) → α) $ @sigma.snd α (λ _ : α, α)) = xs₁,
  dsimp [id] at h₁,
  have hxs : xs = total_function.list.to_finmap' (xs₀.zip xs₁),
  { rw [← h₀, ← h₁, list.to_finmap'], clear h₀ h₁ xs₀ xs₁ hperm hnodup,
    induction xs,
    case list.nil
    { simp only [zip_nil_right, map_nil] },
    case list.cons : xs_hd xs_tl xs_ih
    { simp only [true_and, to_sigma, eq_self_iff_true, sigma.eta, zip_cons_cons, list.map],
      exact xs_ih }, },
  revert hperm hnodup,
  rw hxs, intros,
  apply apply_id_injective,
  { rwa [← h₀, hxs, hperm.nodup_iff], },
  { rwa [← hxs, h₀, h₁] at hperm, },
end

instance pi_injective.sampleable_ext : sampleable_ext { f : ℤ → ℤ // function.injective f } :=
{ proxy_repr := injective_function ℤ,
  interp := λ f, ⟨ apply f, f.injective ⟩,
  sample := gen.sized $ λ sz, do
  { let xs' := int.range (-(2*sz+2)) (2*sz + 2),
    ys ← gen.permutation_of xs',
    have Hinj : injective (λ (r : ℕ), -(2*sz + 2 : ℤ) + ↑r),
      from λ x y h, int.coe_nat_inj (add_right_injective _ h),
    let r : injective_function ℤ :=
      injective_function.mk.{0} xs' ys.1 ys.2 (ys.2.nodup_iff.1 $ (nodup_range _).map Hinj) in
    pure r },
  shrink := @injective_function.shrink ℤ _ _ }

end injective_function

open function

instance injective.testable (f : α → β)
  [I : testable (named_binder "x" $
    ∀ x : α, named_binder "y" $ ∀ y : α, named_binder "H" $ f x = f y → x = y)] :
  testable (injective f) := I

instance monotone.testable [preorder α] [preorder β] (f : α → β)
  [I : testable (named_binder "x" $
    ∀ x : α, named_binder "y" $ ∀ y : α, named_binder "H" $ x ≤ y → f x ≤ f y)] :
  testable (monotone f) := I

instance antitone.testable [preorder α] [preorder β] (f : α → β)
  [I : testable (named_binder "x" $
    ∀ x : α, named_binder "y" $ ∀ y : α, named_binder "H" $ x ≤ y → f y ≤ f x)] :
  testable (antitone f) := I

end slim_check
