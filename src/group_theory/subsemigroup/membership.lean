/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov, Jireh Loreaux
-/
import group_theory.subsemigroup.operations
import algebra.big_operators.basic
import algebra.free_semigroup
import data.finset.noncomm_prod

/-!
# Subsemigroups: membership criteria

In this file we prove various facts about membership in a subsemigroup:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative subsemigroup, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive subsemigroup, then so does their sum;
* `pow_mem`, `nsmul_mem`: if `x ∈ S` where `S` is a multiplicative (resp., additive) subsemigroup and
  `n` is a natural number, then `x^n` (resp., `n • x`) belongs to `S`;
* `mem_supr_of_directed`, `coe_supr_of_directed`, `mem_Sup_of_directed_on`,
  `coe_Sup_of_directed_on`: the supremum of a directed collection of subsemigroup is their union.
* `sup_eq_range`, `mem_sup`: supremum of two subsemigroups `S`, `T` of a commutative semigroup is the set
  of products;
* `closure_singleton_eq`, `mem_closure_singleton`, `mem_closure_pair`: the multiplicative (resp.,
  additive) closure of `{x}` consists of powers (resp., natural multiples) of `x`, and a similar
  result holds for the closure of `{x, y}`.

## Tags
subsemigroup, subsemigroups
-/

open_locale big_operators

variables {M A B : Type*}

/-
Here, we can't have various product lemmas because we don't have a `1 : M`. Perhaps we need to
define a type of nonempty lists, and then products on those?
-/

section non_assoc
variables [mul_one_class M]

open set

namespace subsemigroup

-- TODO: this section can be generalized to `[mul_mem_class B M] [complete_lattice B]`
-- such that `complete_lattice.le` coincides with `set_like.le`

@[to_additive]
lemma mem_supr_of_directed {ι} {S : ι → subsemigroup M} (hS : directed (≤) S) {x : M} :
  x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (set_like.le_def.1 $ le_supr S i) hi⟩,
  suffices : x ∈ closure (⋃ i, (S i : set M)) → ∃ i, x ∈ S i,
    by simpa only [closure_Union, closure_eq (S _)] using this,
  refine (λ hx, closure_induction hx (λ y hy, mem_Union.mp hy) _),
  { rintros x y ⟨i, hi⟩ ⟨j, hj⟩,
    rcases hS i j with ⟨k, hki, hkj⟩,
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩ }
end

@[to_additive]
lemma coe_supr_of_directed {ι} {S : ι → subsemigroup M} (hS : directed (≤) S) :
  ((⨆ i, S i : subsemigroup M) : set M) = ⋃ i, ↑(S i) :=
set.ext $ λ x, by simp [mem_supr_of_directed hS]

@[to_additive]
lemma mem_Sup_of_directed_on {S : set (subsemigroup M)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) {x : M} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
by simp only [Sup_eq_supr', mem_supr_of_directed hS.directed_coe, set_coe.exists, subtype.coe_mk]

@[to_additive]
lemma coe_Sup_of_directed_on {S : set (subsemigroup M)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) :
  (↑(Sup S) : set M) = ⋃ s ∈ S, ↑s :=
set.ext $ λ x, by simp [mem_Sup_of_directed_on Sne hS]

@[to_additive]
lemma mem_sup_left {S T : subsemigroup M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

@[to_additive]
lemma mem_sup_right {S T : subsemigroup M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

@[to_additive]
lemma mul_mem_sup {S T : subsemigroup M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
mul_mem (mem_sup_left hx) (mem_sup_right hy)

@[to_additive]
lemma mem_supr_of_mem {ι : Sort*} {S : ι → subsemigroup M} (i : ι) :
  ∀ {x : M}, x ∈ S i → x ∈ supr S :=
show S i ≤ supr S, from le_supr _ _

@[to_additive]
lemma mem_Sup_of_mem {S : set (subsemigroup M)} {s : subsemigroup M}
  (hs : s ∈ S) : ∀ {x : M}, x ∈ s → x ∈ Sup S :=
show s ≤ Sup S, from le_Sup hs

/-- An induction principle for elements of `⨆ i, S i`.
If `C` holds all elements of `S i` for all `i`, and is preserved under multiplication,
then it holds for all elements of the supremum of `S`. -/
@[elab_as_eliminator, to_additive /-" An induction principle for elements of `⨆ i, S i`.
If `C` holds all elements of `S i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `S`. "-/]
lemma supr_induction {ι : Sort*} (S : ι → subsemigroup M) {C : M → Prop} {x : M} (hx : x ∈ ⨆ i, S i)
  (hp : ∀ i (x ∈ S i), C x)
  (hmul : ∀ x y, C x → C y → C (x * y)) : C x :=
begin
  rw supr_eq_closure at hx,
  refine closure_induction hx (λ x hx, _) hmul,
  obtain ⟨i, hi⟩ := set.mem_Union.mp hx,
  exact hp _ _ hi,
end

/-- A dependent version of `subsemigroup.supr_induction`. -/
@[elab_as_eliminator, to_additive /-"A dependent version of `add_subsemigroup.supr_induction`. "-/]
lemma supr_induction' {ι : Sort*} (S : ι → subsemigroup M) {C : Π x, (x ∈ ⨆ i, S i) → Prop}
  (hp : ∀ i (x ∈ S i), C x (mem_supr_of_mem i ‹_›))
  (hmul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem ‹_› ‹_›))
  {x : M} (hx : x ∈ ⨆ i, S i) : C x hx :=
begin
  refine exists.elim _ (λ (hx : x ∈ ⨆ i, S i) (hc : C x hx), hc),
  refine supr_induction S hx (λ i x hx, _) (λ x y, _),
  { exact ⟨_, hp _ _ hx⟩ },
  { rintro ⟨_, Cx⟩ ⟨_, Cy⟩,
    exact ⟨_, hmul _ _ _ _ Cx Cy⟩ },
end

end subsemigroup

end non_assoc

namespace free_semigroup

variables {α : Type*}

open subsemigroup

@[to_additive]
theorem closure_range_of : closure (set.range $ @of α) = ⊤ :=
eq_top_iff.2 $ λ x hx, free_semigroup.rec_on x (one_mem _) $ λ x xs hxs,
  mul_mem (subset_closure $ set.mem_range_self _) hxs

end free_semigroup

namespace subsemigroup

variables [semigroup M]

open semigroup_hom

lemma closure_singleton_eq (x : M) : closure ({x} : set M) = (powers_hom M x).mrange :=
closure_eq_of_le (set.singleton_subset_iff.2 ⟨multiplicative.of_add 1, pow_one x⟩) $
  λ x ⟨n, hn⟩, hn ▸ pow_mem (subset_closure $ set.mem_singleton _) _

/-- The subsemigroup generated by an element of a semigroup equals the set of natural number powers of
    the element. -/
lemma mem_closure_singleton {x y : M} : y ∈ closure ({x} : set M) ↔ ∃ n:ℕ, x^n=y :=
by rw [closure_singleton_eq, mem_mrange]; refl

lemma mem_closure_singleton_self {y : M} : y ∈ closure ({y} : set M) :=
mem_closure_singleton.2 ⟨1, pow_one y⟩

lemma closure_singleton_one : closure ({1} : set M) = ⊥ :=
by simp [eq_bot_iff_forall, mem_closure_singleton]

@[to_additive]
lemma closure_eq_mrange (s : set M) : closure s = (free_semigroup.lift (coe : s → M)).mrange :=
by rw [mrange_eq_map, ← free_semigroup.closure_range_of, map_mclosure, ← set.range_comp,
  free_semigroup.lift_comp_of, subtype.range_coe]

@[to_additive]
lemma exists_list_of_mem_closure {s : set M} {x : M} (hx : x ∈ closure s) :
  ∃ (l : list M) (hl : ∀ y ∈ l, y ∈ s), l.prod = x :=
begin
  rw [closure_eq_mrange, mem_mrange] at hx,
  rcases hx with ⟨l, hx⟩,
  exact ⟨list.map coe l, λ y hy, let ⟨z, hz, hy⟩ := list.mem_map.1 hy in hy ▸ z.2, hx⟩
end

@[to_additive]
lemma exists_multiset_of_mem_closure {M : Type*} [comm_semigroup M] {s : set M}
  {x : M} (hx : x ∈ closure s) : ∃ (l : multiset M) (hl : ∀ y ∈ l, y ∈ s), l.prod = x :=
begin
  obtain ⟨l, h1, h2⟩ := exists_list_of_mem_closure hx,
  exact ⟨l, h1, (multiset.coe_prod l).trans h2⟩,
end

@[to_additive]
lemma closure_induction_left {s : set M} {p : M → Prop} {x : M} (h : x ∈ closure s) (H1 : p 1)
  (Hmul : ∀ (x ∈ s) y, p y → p (x * y)) : p x :=
begin
  rw closure_eq_mrange at h,
  obtain ⟨l, rfl⟩ := h,
  induction l using free_semigroup.rec_on with x y ih,
  { exact H1 },
  { simpa only [map_mul, free_semigroup.lift_eval_of] using Hmul _ x.prop _ ih }
end

@[to_additive]
lemma closure_induction_right {s : set M} {p : M → Prop} {x : M} (h : x ∈ closure s) (H1 : p 1)
  (Hmul : ∀ x (y ∈ s), p x → p (x * y)) : p x :=
@closure_induction_left _ _ (mul_opposite.unop ⁻¹' s) (p ∘ mul_opposite.unop) (mul_opposite.op x)
  (closure_induction h (λ x hx, subset_closure hx) (one_mem _) (λ x y hx hy, mul_mem hy hx))
  H1 (λ x hx y, Hmul _ _ hx)

/-- The subsemigroup generated by an element. -/
def powers (n : M) : subsemigroup M :=
subsemigroup.copy (powers_hom M n).mrange (set.range ((^) n : ℕ → M)) $
set.ext (λ n, exists_congr $ λ i, by simp; refl)

@[simp] lemma mem_powers (n : M) : n ∈ powers n := ⟨1, pow_one _⟩

lemma mem_powers_iff (x z : M) : x ∈ powers z ↔ ∃ n : ℕ, z ^ n = x := iff.rfl

lemma powers_eq_closure (n : M) : powers n = closure {n} :=
by { ext, exact mem_closure_singleton.symm }

lemma powers_subset {n : M} {P : subsemigroup M} (h : n ∈ P) : powers n ≤ P :=
λ x hx, match x, hx with _, ⟨i, rfl⟩ := pow_mem h i end

/-- Exponentiation map from natural numbers to powers. -/
@[simps] def pow (n : M) (m : ℕ) : powers n :=
(powers_hom M n).mrange_restrict (multiplicative.of_add m)

lemma pow_apply (n : M) (m : ℕ) : subsemigroup.pow n m = ⟨n ^ m, m, rfl⟩ := rfl

/-- Logarithms from powers to natural numbers. -/
def log [decidable_eq M] {n : M} (p : powers n) : ℕ :=
nat.find $ (mem_powers_iff p.val n).mp p.prop

@[simp] theorem pow_log_eq_self [decidable_eq M] {n : M} (p : powers n) : pow n (log p) = p :=
subtype.ext $ nat.find_spec p.prop

lemma pow_right_injective_iff_pow_injective {n : M} :
  function.injective (λ m : ℕ, n ^ m) ↔ function.injective (pow n) :=
subtype.coe_injective.of_comp_iff (pow n)

@[simp] theorem log_pow_eq_self [decidable_eq M] {n : M} (h : function.injective (λ m : ℕ, n ^ m))
  (m : ℕ) : log (pow n m) = m :=
pow_right_injective_iff_pow_injective.mp h $ pow_log_eq_self _

/-- The exponentiation map is an isomorphism from the additive semigroup on natural numbers to powers
when it is injective. The inverse is given by the logarithms. -/
@[simps]
def pow_log_equiv [decidable_eq M] {n : M} (h : function.injective (λ m : ℕ, n ^ m)) :
  multiplicative ℕ ≃* powers n :=
{ to_fun := λ m, pow n m.to_add,
  inv_fun := λ m, multiplicative.of_add (log m),
  left_inv := log_pow_eq_self h,
  right_inv := pow_log_eq_self,
  map_mul' := λ _ _, by { simp only [pow, map_mul, of_add_add, to_add_mul] } }

lemma log_mul [decidable_eq M] {n : M} (h : function.injective (λ m : ℕ, n ^ m))
  (x y : powers (n : M)) : log (x * y) = log x + log y := (pow_log_equiv h).symm.map_mul x y

theorem log_pow_int_eq_self {x : ℤ} (h : 1 < x.nat_abs) (m : ℕ) : log (pow x m) = m :=
(pow_log_equiv (int.pow_right_injective h)).symm_apply_apply _

@[simp] lemma map_powers {N : Type*} [semigroup N] (f : M →* N) (m : M) :
  (powers m).map f = powers (f m) :=
by simp only [powers_eq_closure, f.map_mclosure, set.image_singleton]

/-- If all the elements of a set `s` commute, then `closure s` is a commutative semigroup. -/
@[to_additive "If all the elements of a set `s` commute, then `closure s` forms an additive
commutative semigroup."]
def closure_comm_semigroup_of_comm {s : set M} (hcomm : ∀ (a ∈ s) (b ∈ s), a * b = b * a) :
  comm_semigroup (closure s) :=
{ mul_comm := λ x y,
  begin
    ext,
    simp only [subsemigroup.coe_mul],
    exact closure_induction₂ x.prop y.prop hcomm
      (λ x, by simp only [mul_one, one_mul])
      (λ x, by simp only [mul_one, one_mul])
      (λ x y z h₁ h₂, by rw [mul_assoc, h₂, ←mul_assoc, h₁, mul_assoc])
      (λ x y z h₁ h₂, by rw [←mul_assoc, h₁, mul_assoc, h₂, ←mul_assoc]),
  end,
  ..(closure s).to_semigroup }

end subsemigroup

namespace subsemigroup

variables {N : Type*} [comm_semigroup N]

open semigroup_hom

@[to_additive]
lemma sup_eq_range (s t : subsemigroup N) : s ⊔ t = (s.subtype.coprod t.subtype).mrange :=
by rw [mrange_eq_map, ← mrange_inl_sup_mrange_inr, map_sup, map_mrange, coprod_comp_inl,
  map_mrange, coprod_comp_inr, range_subtype, range_subtype]

@[to_additive]
lemma mem_sup {s t : subsemigroup N} {x : N} :
  x ∈ s ⊔ t ↔ ∃ (y ∈ s) (z ∈ t), y * z = x :=
by simp only [sup_eq_range, mem_mrange, coprod_apply, prod.exists, set_like.exists,
  coe_subtype, subtype.coe_mk]

end subsemigroup

namespace add_subsemigroup

variables [add_semigroup A]

open set

lemma closure_singleton_eq (x : A) : closure ({x} : set A) = (multiples_hom A x).mrange :=
closure_eq_of_le (set.singleton_subset_iff.2 ⟨1, one_nsmul x⟩) $
  λ x ⟨n, hn⟩, hn ▸ nsmul_mem (subset_closure $ set.mem_singleton _) _

/-- The `add_subsemigroup` generated by an element of an `add_semigroup` equals the set of
natural number multiples of the element. -/
lemma mem_closure_singleton {x y : A} :
  y ∈ closure ({x} : set A) ↔ ∃ n:ℕ, n • x = y :=
by rw [closure_singleton_eq, add_semigroup_hom.mem_mrange]; refl

lemma closure_singleton_zero : closure ({0} : set A) = ⊥ :=
by simp [eq_bot_iff_forall, mem_closure_singleton, nsmul_zero]

/-- The additive subsemigroup generated by an element. -/
def multiples (x : A) : add_subsemigroup A :=
add_subsemigroup.copy (multiples_hom A x).mrange (set.range (λ i, i • x : ℕ → A)) $
set.ext (λ n, exists_congr $ λ i, by simp; refl)

@[simp] lemma mem_multiples (x : A) : x ∈ multiples x := ⟨1, one_nsmul _⟩

lemma mem_multiples_iff (x z : A) : x ∈ multiples z ↔ ∃ n : ℕ, n • z = x := iff.rfl

lemma multiples_eq_closure (x : A) : multiples x = closure {x} :=
by { ext, exact mem_closure_singleton.symm }

lemma multiples_subset {x : A} {P : add_subsemigroup A} (h : x ∈ P) : multiples x ≤ P :=
λ x hx, match x, hx with _, ⟨i, rfl⟩ := nsmul_mem h i end

attribute [to_additive add_subsemigroup.multiples] subsemigroup.powers
attribute [to_additive add_subsemigroup.mem_multiples] subsemigroup.mem_powers
attribute [to_additive add_subsemigroup.mem_multiples_iff] subsemigroup.mem_powers_iff
attribute [to_additive add_subsemigroup.multiples_eq_closure] subsemigroup.powers_eq_closure
attribute [to_additive add_subsemigroup.multiples_subset] subsemigroup.powers_subset

end add_subsemigroup

/-! Lemmas about additive closures of `subsemigroup`. -/
namespace subsemigroup

variables {R : Type*} [non_assoc_semiring R] (S : subsemigroup R) {a b : R}

/-- The product of an element of the additive closure of a multiplicative subsemigroup `M`
and an element of `M` is contained in the additive closure of `M`. -/
lemma mul_right_mem_add_closure
  (ha : a ∈ add_subsemigroup.closure (S : set R)) (hb : b ∈ S) :
  a * b ∈ add_subsemigroup.closure (S : set R) :=
begin
  revert b,
  refine add_subsemigroup.closure_induction ha _ _ _; clear ha a,
  { exact λ r hr b hb, add_subsemigroup.mem_closure.mpr (λ y hy, hy (S.mul_mem hr hb)) },
  { exact λ b hb, by simp only [zero_mul, (add_subsemigroup.closure (S : set R)).zero_mem] },
  { simp_rw add_mul,
    exact λ r s hr hs b hb, (add_subsemigroup.closure (S : set R)).add_mem (hr hb) (hs hb) }
end

/-- The product of two elements of the additive closure of a subsemigroup `M` is an element of the
additive closure of `M`. -/
lemma mul_mem_add_closure
  (ha : a ∈ add_subsemigroup.closure (S : set R)) (hb : b ∈ add_subsemigroup.closure (S : set R)) :
  a * b ∈ add_subsemigroup.closure (S : set R) :=
begin
  revert a,
  refine add_subsemigroup.closure_induction hb _ _ _; clear hb b,
  { exact λ r hr b hb, S.mul_right_mem_add_closure hb hr },
  { exact λ b hb, by simp only [mul_zero, (add_subsemigroup.closure (S : set R)).zero_mem] },
  { simp_rw mul_add,
    exact λ r s hr hs b hb, (add_subsemigroup.closure (S : set R)).add_mem (hr hb) (hs hb) }
end

/-- The product of an element of `S` and an element of the additive closure of a multiplicative
subsemigroup `S` is contained in the additive closure of `S`. -/
lemma mul_left_mem_add_closure (ha : a ∈ S) (hb : b ∈ add_subsemigroup.closure (S : set R)) :
  a * b ∈ add_subsemigroup.closure (S : set R) :=
S.mul_mem_add_closure (add_subsemigroup.mem_closure.mpr (λ sT hT, hT ha)) hb

/-- An element is in the closure of a two-element set if it is a linear combination of those two
elements. -/
@[to_additive "An element is in the closure of a two-element set if it is a linear combination of
those two elements."]
lemma mem_closure_pair {A : Type*} [comm_semigroup A] (a b c : A) :
  c ∈ subsemigroup.closure ({a, b} : set A) ↔ ∃ m n : ℕ, a ^ m * b ^ n = c :=
begin
  rw [←set.singleton_union, subsemigroup.closure_union, mem_sup],
  simp_rw [exists_prop, mem_closure_singleton, exists_exists_eq_and],
end

end subsemigroup

section mul_add

lemma of_mul_image_powers_eq_multiples_of_mul [semigroup M] {x : M} :
  additive.of_mul '' ((subsemigroup.powers x) : set M) = add_subsemigroup.multiples (additive.of_mul x) :=
begin
  ext,
  split,
  { rintros ⟨y, ⟨n, hy1⟩, hy2⟩,
    use n,
    simpa [← of_mul_pow, hy1] },
  { rintros ⟨n, hn⟩,
    refine ⟨x ^ n, ⟨n, rfl⟩, _⟩,
    rwa of_mul_pow }
end

lemma of_add_image_multiples_eq_powers_of_add [add_semigroup A] {x : A} :
  multiplicative.of_add '' ((add_subsemigroup.multiples x) : set A) =
  subsemigroup.powers (multiplicative.of_add x) :=
begin
  symmetry,
  rw equiv.eq_image_iff_symm_image_eq,
  exact of_mul_image_powers_eq_multiples_of_mul,
end

end mul_add
