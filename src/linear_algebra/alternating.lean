/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Wieser, Zhangir Azerbayev
-/

import linear_algebra.multilinear
import linear_algebra.multilinear_tensor
import group_theory.perm.sign
import data.equiv.fin
import linear_algebra.tensor_product
import ring_theory.algebra_tower

/-!
# Alternating Maps

We construct the bundled function `alternating_map`, which extends `multilinear_map` with all the
arguments of the same type.

## Main definitions
* `alternating_map R M N ι` is the space of `R`-linear alternating maps from `ι → M` to `N`.
* `f.map_eq_zero_of_eq` expresses that `f` is zero when two inputs are equal.
* `f.map_swap` expresses that `f` is negated when two inputs are swapped.
* `f.map_perm` expresses how `f` varies by a sign change under a permutation of its inputs.
* An `add_comm_monoid`, `add_comm_group`, and `semimodule` structure over `alternating_map`s that
  matches the definitions over `multilinear_map`s.

## Implementation notes
`alternating_map` is defined in terms of `map_eq_zero_of_eq`, as this is easier to work with than
using `map_swap` as a definition, and does not require `has_neg N`.
-/

-- semiring / add_comm_monoid
variables {R : Type*} [semiring R]
variables {M : Type*} [add_comm_monoid M] [semimodule R M]
variables {N : Type*} [add_comm_monoid N] [semimodule R N]

-- semiring / add_comm_group
variables {L : Type*} [add_comm_group L] [semimodule R L]

-- ring / add_comm_group
variables {R' : Type*} [ring R']
variables {M' : Type*} [add_comm_group M'] [semimodule R' M']
variables {N' : Type*} [add_comm_group N'] [semimodule R' N']

variables {ι : Type*} [decidable_eq ι]

set_option old_structure_cmd true

section
variables (R M N ι)
/--
An alternating map is a multilinear map that vanishes when two of its arguments are equal.
-/
structure alternating_map extends multilinear_map R (λ i : ι, M) N :=
(map_eq_zero_of_eq' : ∀ (v : ι → M) (i j : ι) (h : v i = v j) (hij : i ≠ j), to_fun v = 0)
end

/-- The multilinear map associated to an alternating map -/
add_decl_doc alternating_map.to_multilinear_map

namespace alternating_map

variables (f f' : alternating_map R M N ι)
variables (g' : alternating_map R' M' N' ι)
variables (v : ι → M) (v' : ι → M')
open function

/-! Basic coercion simp lemmas, largely copied from `ring_hom` and `multilinear_map` -/
section coercions

instance : has_coe_to_fun (alternating_map R M N ι) := ⟨_, λ x, x.to_fun⟩

initialize_simps_projections alternating_map (to_fun → apply)

@[simp] lemma to_fun_eq_coe : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : (ι → M) → N) (h₁ h₂ h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ :
  alternating_map R M N ι) = f := rfl

theorem congr_fun {f g : alternating_map R M N ι} (h : f = g) (x : ι → M) : f x = g x :=
congr_arg (λ h : alternating_map R M N ι, h x) h

theorem congr_arg (f : alternating_map R M N ι) {x y : ι → M} (h : x = y) : f x = f y :=
congr_arg (λ x : ι → M, f x) h

theorem coe_inj ⦃f g : alternating_map R M N ι⦄ (h : ⇑f = g) : f = g :=
by { cases f, cases g, cases h, refl }

@[ext] theorem ext {f f' : alternating_map R M N ι} (H : ∀ x, f x = f' x) : f = f' :=
coe_inj (funext H)

theorem ext_iff {f g : alternating_map R M N ι} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

instance : has_coe (alternating_map R M N ι) (multilinear_map R (λ i : ι, M) N) :=
⟨λ x, x.to_multilinear_map⟩

@[simp, norm_cast] lemma coe_multilinear_map : ⇑(f : multilinear_map R (λ i : ι, M) N) = f := rfl

@[simp] lemma to_multilinear_map_eq_coe : f.to_multilinear_map = f := rfl

@[simp] lemma coe_multilinear_map_mk (f : (ι → M) → N) (h₁ h₂ h₃) :
  ((⟨f, h₁, h₂, h₃⟩ : alternating_map R M N ι) :  multilinear_map R (λ i : ι, M) N) = ⟨f, h₁, h₂⟩ :=
rfl

end coercions

/-!
### Simp-normal forms of the structure fields

These are expressed in terms of `⇑f` instead of `f.to_fun`.
-/
@[simp] lemma map_add (i : ι) (x y : M) :
  f (update v i (x + y)) = f (update v i x) + f (update v i y) :=
f.to_multilinear_map.map_add' v i x y

@[simp] lemma map_sub (i : ι) (x y : M') :
  g' (update v' i (x - y)) = g' (update v' i x) - g' (update v' i y) :=
g'.to_multilinear_map.map_sub v' i x y

@[simp] lemma map_smul (i : ι) (r : R) (x : M) :
  f (update v i (r • x)) = r • f (update v i x) :=
f.to_multilinear_map.map_smul' v i r x

@[simp] lemma map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) :
  f v = 0 :=
f.map_eq_zero_of_eq' v i j h hij

/-!
### Algebraic structure inherited from `multilinear_map`

`alternating_map` carries the same `add_comm_monoid`, `add_comm_group`, and `semimodule` structure
as `multilinear_map`
-/

instance : has_add (alternating_map R M N ι) :=
⟨λ a b,
  { map_eq_zero_of_eq' :=
      λ v i j h hij, by simp [a.map_eq_zero_of_eq v h hij, b.map_eq_zero_of_eq v h hij],
    ..(a + b : multilinear_map R (λ i : ι, M) N)}⟩

@[simp] lemma add_apply : (f + f') v = f v + f' v := rfl

instance : has_zero (alternating_map R M N ι) :=
⟨{map_eq_zero_of_eq' := λ v i j h hij, by simp,
  ..(0 : multilinear_map R (λ i : ι, M) N)}⟩

@[simp] lemma zero_apply : (0 : alternating_map R M N ι) v = 0 := rfl

instance : inhabited (alternating_map R M N ι) := ⟨0⟩

instance : add_comm_monoid (alternating_map R M N ι) :=
by refine {zero := 0, add := (+), ..};
   intros; ext; simp [add_comm, add_left_comm]

instance : has_neg (alternating_map R' M' N' ι) :=
⟨λ f,
  { map_eq_zero_of_eq' := λ v i j h hij, by simp [f.map_eq_zero_of_eq v h hij],
    ..(-(f : multilinear_map R' (λ i : ι, M') N')) }⟩

@[simp] lemma neg_apply (m : ι → M') : (-g') m = - (g' m) := rfl

instance : add_comm_group (alternating_map R' M' N' ι) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..alternating_map.add_comm_monoid, ..};
   intros; ext; simp [add_comm, add_left_comm]

section semimodule

variables {S : Type*} [comm_semiring S] [algebra S R] [semimodule S N]
  [is_scalar_tower S R N]

instance : has_scalar S (alternating_map R M N ι) :=
⟨λ c f,
  { map_eq_zero_of_eq' := λ v i j h hij, by simp [f.map_eq_zero_of_eq v h hij],
    ..((c • f : multilinear_map R (λ i : ι, M) N)) }⟩

@[simp] lemma smul_apply (f : alternating_map R M N ι) (c : S) (m : ι → M) :
  (c • f) m = c • f m := rfl

/-- The space of multilinear maps over an algebra over `S` is a module over `S`, for the pointwise
addition and scalar multiplication. -/
instance : semimodule S (alternating_map R M N ι) :=
{ one_smul := λ f, ext $ λ x, one_smul _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul _ _ _,
  smul_zero := λ r, ext $ λ x, smul_zero _,
  smul_add := λ r f₁ f₂, ext $ λ x, smul_add _ _ _,
  add_smul := λ r₁ r₂ f, ext $ λ x, add_smul _ _ _,
  zero_smul := λ f, ext $ λ x, zero_smul _ _ }

end semimodule

/-!
### Theorems specific to alternating maps

Various properties of reordered and repeated inputs which follow from
`alternating_map.map_eq_zero_of_eq`.
-/

lemma map_update_self {i j : ι} (hij : i ≠ j) :
  f (function.update v i (v j)) = 0 :=
f.map_eq_zero_of_eq _ (by rw [function.update_same, function.update_noteq hij.symm]) hij

lemma map_update_update {i j : ι} (hij : i ≠ j) (m : M) :
  f (function.update (function.update v i m) j m) = 0 :=
f.map_eq_zero_of_eq _
  (by rw [function.update_same, function.update_noteq hij, function.update_same]) hij

lemma map_swap_add {i j : ι} (hij : i ≠ j) :
  f (v ∘ equiv.swap i j) + f v = 0 :=
begin
  rw equiv.comp_swap_eq_update,
  convert f.map_update_update v hij (v i + v j),
  simp [f.map_update_self _ hij,
        f.map_update_self _ hij.symm,
        function.update_comm hij (v i + v j) (v _) v,
        function.update_comm hij.symm (v i) (v i) v],
end

lemma map_add_swap {i j : ι} (hij : i ≠ j) :
  f v + f (v ∘ equiv.swap i j) = 0 :=
by { rw add_comm, exact f.map_swap_add v hij }

variable (g : alternating_map R M L ι)

lemma map_swap {i j : ι} (hij : i ≠ j) :
  g (v ∘ equiv.swap i j) = - g v  :=
eq_neg_of_add_eq_zero (g.map_swap_add v hij)

lemma map_perm [fintype ι] (v : ι → M) (σ : equiv.perm ι) :
  g (v ∘ σ) = (equiv.perm.sign σ : ℤ) • g v :=
begin
  apply equiv.perm.swap_induction_on' σ,
  { simp },
  { intros s x y hxy hI,
    simpa [g.map_swap (v ∘ s) hxy, equiv.perm.sign_swap hxy] using hI, }
end

lemma map_congr_perm [fintype ι] (σ : equiv.perm ι) :
  g v = (equiv.perm.sign σ : ℤ) • g (v ∘ σ) :=
by { rw [g.map_perm, smul_smul], simp }

end alternating_map

section

-- def fin_split {n m} (f : fin (n + m)) : fin n ⊕ fin m :=
-- if h : ↑f < n then sum.inl ⟨f, h⟩ else sum.inr (f.sub_nat n (le_of_not_lt h)))

def sum_split_func {α β γ : Type*} : (α ⊕ β → γ) ≃ (α → γ) × (β → γ) :=
{ to_fun := λ f, ⟨f ∘ sum.inl, f ∘ sum.inr⟩,
  inv_fun := λ F h, h.elim F.1 F.2,
  left_inv := sum.elim_comp_inl_inr,
  right_inv := λ f, by simp }

def finvec_split {n m} {α : Sort*} (f : fin (n + m) → α) : pprod (fin n → α) (fin m → α) := sorry

namespace function

def update_comp_equiv {α β γ : Sort*} [decidable_eq α] [decidable_eq γ]
  (f : α → β) (σ : γ ≃ α) (i : α) (v : β) :
  function.update f i v ∘ σ = function.update (f ∘ σ) (σ.symm i) v :=
begin
  conv_lhs {rw ← σ.apply_symm_apply i},
  rw function.update_comp,
  exact σ.injective,
end

lemma update_apply_equiv_apply {α β α' : Sort*} [decidable_eq α'] [decidable_eq α]
  (f : α → β) (g : α' ≃ α) (a : α) (v : β) (a' : α') :
  update f a v (g a') = update (f ∘ g) (g.symm a) v a' :=
congr_fun (update_comp_equiv f g a v) a'

end function

namespace multilinear_map

variables {M₂ M₃ : Type*} [add_comm_monoid M₂] [semimodule R M₂]
variables {ι₁ ι₂ : Type*} [decidable_eq ι₁] [decidable_eq ι₂] [add_comm_monoid M₃] [semimodule R M₃]

@[simps apply]
def dom_dom_congr
  (σ : ι₁ ≃ ι₂) (m : multilinear_map R (λ i : ι₁, M₂) M₃) : multilinear_map R (λ i : ι₂, M₂) M₃ :=
{ to_fun := λ v, m (λ i, v (σ i)),
  map_add' := λ v i a b, by { simp_rw function.update_apply_equiv_apply v, rw m.map_add, },
  map_smul' := λ v i a b, by { simp_rw function.update_apply_equiv_apply v, rw m.map_smul, }, }

variables (R)
/-- Transfer the equivalence between argument indices to an equivalence between maps
The naming is derived from `finsupp.dom_congr`, noting that here the permutation applies to the
domain of the domain. -/
@[simps]
def dom_dom_congr_equiv (σ : ι₁ ≃ ι₂) :
  multilinear_map R (λ i : ι₁, M₂) M₃ ≃+ multilinear_map R (λ i : ι₂, M₂) M₃ :=
{ to_fun := dom_dom_congr σ,
  inv_fun := dom_dom_congr σ.symm,
  left_inv := λ m, by {ext, simp},
  right_inv := λ m, by {ext, simp},
  map_add' := λ a b, by {ext, simp} }
variables {R}

end multilinear_map

/-- On non-dependent functions, `function.update` can be expressed as an `ite` -/
lemma function.update_def {α β : Sort*} [decidable_eq α] (f : α → β) (a' : α) (b : β) :
  function.update f a' b = λ a, if a = a' then b else f a :=
begin
  ext,
  apply function.update_apply,
end

def is_shuffle {m n} (p : fin m ⊕ fin n ≃ fin (m + n)) : Prop :=
monotone (p ∘ sum.inl) ∧ monotone (p ∘ sum.inr)

instance {m n : ℕ} : decidable_pred (@is_shuffle m n) :=
λ p, by {unfold is_shuffle monotone, apply_instance}

@[derive has_coe_to_fun]
def shuffle (m n) : Type* := {p : fin m ⊕ fin n ≃ fin (m + n) // is_shuffle p }

namespace shuffle

variables {m n : ℕ}

lemma coe_eq_val (s : shuffle m n) : ⇑s = s.val := rfl

def to_perm (s : shuffle m n) : (equiv.perm $ fin (m + n)) := sum_fin_sum_equiv.symm.trans s.val

instance : has_coe_t (shuffle m n) (equiv.perm $ fin (m + n)) := ⟨to_perm⟩


instance : fintype (shuffle m n) := subtype.fintype _

end shuffle

open_locale big_operators

namespace nat

instance {R M : Type*} [semiring R] [add_comm_monoid M] [semimodule R M] : smul_comm_class ℕ R M :=
{ smul_comm := λ n r m, begin
    simp only [nat.smul_def],
    induction n with n ih,
    { simp },
    { simp [succ_nsmul, ←ih, smul_add] },
  end }

end nat

namespace int

instance {R M : Type*} [semiring R] [add_comm_group M] [semimodule R M] : smul_comm_class ℤ R M :=
{ smul_comm := λ z r l, by cases z; simp [←gsmul_eq_smul, ←nat.smul_def, smul_comm] }

end int

example {α β : Type*} (val : α) :
  (sum.inl val : α ⊕ β) ∉ set.range (@sum.inr α β) := by simp

open_locale tensor_product

instance sum_elim.add_comm_monoid {ι₁ ι₂ : Type}
  {M : ι₁ → Type*} [∀ i, add_comm_monoid (M i)]
  {N : ι₂ → Type*} [∀ i, add_comm_monoid (N i)]
  (i : ι₁ ⊕ ι₂)
  : add_comm_monoid (i.elim M N) := by cases i; dsimp; apply_instance

instance sum_elim.semimodule {ι₁ ι₂ : Type} [decidable_eq ι₁] [decidable_eq ι₂]
  (R : Type*) [semiring R]
  {M : ι₁ → Type*} [∀ i, add_comm_monoid (M i)] [∀ i, semimodule R (M i)]
  {N : ι₂ → Type*} [∀ i, add_comm_monoid (N i)] [∀ i, semimodule R (N i)]
  (i : ι₁ ⊕ ι₂)
  : semimodule R (i.elim M N) := by cases i; dsimp; apply_instance

lemma sum.elim_const {α β γ : Sort*} (a : γ) : sum.elim (λ _ : α, a) (λ _ : β, a) = λ i, a :=
funext $ λ x, by cases x; refl

def mul_fin {n m} {R : Type*} {M N : Type*}
  [comm_semiring R] [ring N] [algebra R N] [add_comm_monoid M] [semimodule R M]
  (a : alternating_map R M N (fin m)) (b : alternating_map R M N (fin n)) :
  alternating_map R M N (fin (m + n)) :=
{ to_fun :=
  let ab := ((algebra.lmul' R).comp_multilinear_map (multilinear_map.of_tmul R
      (tensor_product.tmul R a.to_multilinear_map b.to_multilinear_map))),
      ab' : multilinear_map R (λ (i : fin m ⊕ fin n), M) N := by {
        simp_rw sum.elim_const at ab,
      } in
  λ (v : fin (m + n) → M),
  ∑ σ : shuffle m n,
    (σ.to_perm.sign : ℤ) • (ab.dom_dom_congr σ.val : multilinear_map R (λ i, M) N) v,
  map_add' := λ v i p q, begin
    dsimp only at v,
    simp_rw [←finset.sum_add_distrib, ←smul_add],
    congr,
    ext σ,
    congr,
    iterate 3 {rw [←function.comp.assoc _ _ sum.inr, ←function.comp.assoc _ _ sum.inl]},
    rw shuffle.coe_eq_val,
    repeat {rw function.update_comp_equiv v σ.val i},
    rw ←shuffle.coe_eq_val,
    cases h : σ.val.symm i,
    {
      have : ∀ {α β : Type*} (a : α),
        (sum.inl a : α ⊕ β) ∉ set.range (@sum.inr α β) := by simp,
      iterate 3 {
        rw [function.update_comp_eq_of_injective _ sum.injective_inl,
            function.update_comp_eq_of_not_mem_range _ _ (this val)],},
      rw [a.map_add, add_mul],
    },
    {
      have : ∀ {α β : Type*} (b : β),
        (sum.inr b : α ⊕ β) ∉ set.range (@sum.inl α β) := by simp,
      iterate 3 {
        rw [function.update_comp_eq_of_injective _ sum.injective_inr,
            function.update_comp_eq_of_not_mem_range _ _ (this val)]},
      rw [b.map_add, mul_add],
    }
  end,
  map_smul' := λ v i c p, begin
    dsimp only at v,
    simp_rw [finset.smul_sum],
    congr,
    ext σ,
    rw ←smul_comm,
    congr,
    iterate 2 {rw [←function.comp.assoc _ _ sum.inr, ←function.comp.assoc _ _ sum.inl]},
    rw shuffle.coe_eq_val,
    repeat {rw function.update_comp_equiv v σ.val i},
    rw ←shuffle.coe_eq_val,
    cases h : σ.val.symm i,
    {
      have : ∀ {α β : Type*} (a : α),
        (sum.inl a : α ⊕ β) ∉ set.range (@sum.inr α β) := by simp,
      iterate 2 {
        rw [function.update_comp_eq_of_injective _ sum.injective_inl,
            function.update_comp_eq_of_not_mem_range _ _ (this val)],},
      rw [a.map_smul, algebra.smul_mul_assoc],
    },
    {
      have : ∀ {α β : Type*} (b : β),
        (sum.inr b : α ⊕ β) ∉ set.range (@sum.inl α β) := by simp,
      iterate 2 {
        rw [function.update_comp_eq_of_injective _ sum.injective_inr,
            function.update_comp_eq_of_not_mem_range _ _ (this val)]},
      rw [b.map_smul, algebra.mul_smul_comm],
    },
  end,
  map_eq_zero_of_eq' := sorry }

end
