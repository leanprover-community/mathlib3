/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Zhangir Azerbayev
-/

import linear_algebra.multilinear.basis
import linear_algebra.multilinear.tensor_product
import linear_algebra.linear_independent
import group_theory.perm.sign
import group_theory.perm.subgroup
import data.equiv.fin
import group_theory.quotient_group

/-!
# Alternating Maps

We construct the bundled function `alternating_map`, which extends `multilinear_map` with all the
arguments of the same type.

## Main definitions
* `alternating_map R M N ι` is the space of `R`-linear alternating maps from `ι → M` to `N`.
* `f.map_eq_zero_of_eq` expresses that `f` is zero when two inputs are equal.
* `f.map_swap` expresses that `f` is negated when two inputs are swapped.
* `f.map_perm` expresses how `f` varies by a sign change under a permutation of its inputs.
* An `add_comm_monoid`, `add_comm_group`, and `module` structure over `alternating_map`s that
  matches the definitions over `multilinear_map`s.
* `multilinear_map.alternatization`, which makes an alternating map out of a non-alternating one.
* `alternating_map.dom_coprod`, which behaves as a product between two alternating maps.

## Implementation notes
`alternating_map` is defined in terms of `map_eq_zero_of_eq`, as this is easier to work with than
using `map_swap` as a definition, and does not require `has_neg N`.

`alternating_map`s are provided with a coercion to `multilinear_map`, along with a set of
`norm_cast` lemmas that act on the algebraic structure:

* `alternating_map.coe_add`
* `alternating_map.coe_zero`
* `alternating_map.coe_sub`
* `alternating_map.coe_neg`
* `alternating_map.coe_smul`
-/

-- semiring / add_comm_monoid
variables {R : Type*} [semiring R]
variables {M : Type*} [add_comm_monoid M] [module R M]
variables {N : Type*} [add_comm_monoid N] [module R N]

-- semiring / add_comm_group
variables {M' : Type*} [add_comm_group M'] [module R M']
variables {N' : Type*} [add_comm_group N'] [module R N']

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
variables (g g₂ : alternating_map R M N' ι)
variables (g' : alternating_map R M' N' ι)
variables (v : ι → M) (v' : ι → M')
open function

/-! Basic coercion simp lemmas, largely copied from `ring_hom` and `multilinear_map` -/
section coercions

instance : has_coe_to_fun (alternating_map R M N ι) (λ _, (ι → M) → N) := ⟨λ x, x.to_fun⟩

initialize_simps_projections alternating_map (to_fun → apply)

@[simp] lemma to_fun_eq_coe : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : (ι → M) → N) (h₁ h₂ h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ :
  alternating_map R M N ι) = f := rfl

theorem congr_fun {f g : alternating_map R M N ι} (h : f = g) (x : ι → M) : f x = g x :=
congr_arg (λ h : alternating_map R M N ι, h x) h

theorem congr_arg (f : alternating_map R M N ι) {x y : ι → M} (h : x = y) : f x = f y :=
congr_arg (λ x : ι → M, f x) h

theorem coe_injective : injective (coe_fn : alternating_map R M N ι → ((ι → M) → N)) :=
λ f g h, by { cases f, cases g, cases h, refl }

@[simp, norm_cast] theorem coe_inj {f g : alternating_map R M N ι} :
  (f : (ι → M) → N) = g ↔ f = g :=
coe_injective.eq_iff

@[ext] theorem ext {f f' : alternating_map R M N ι} (H : ∀ x, f x = f' x) : f = f' :=
coe_injective (funext H)

theorem ext_iff {f g : alternating_map R M N ι} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

instance : has_coe (alternating_map R M N ι) (multilinear_map R (λ i : ι, M) N) :=
⟨λ x, x.to_multilinear_map⟩

@[simp, norm_cast] lemma coe_multilinear_map : ⇑(f : multilinear_map R (λ i : ι, M) N) = f := rfl

lemma coe_multilinear_map_injective :
  function.injective (coe : alternating_map R M N ι → multilinear_map R (λ i : ι, M) N) :=
λ x y h, ext $ multilinear_map.congr_fun h

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

@[simp] lemma map_neg (i : ι) (x : M') :
  g' (update v' i (-x)) = -g' (update v' i x) :=
g'.to_multilinear_map.map_neg v' i x

@[simp] lemma map_smul (i : ι) (r : R) (x : M) :
  f (update v i (r • x)) = r • f (update v i x) :=
f.to_multilinear_map.map_smul' v i r x

@[simp] lemma map_eq_zero_of_eq (v : ι → M) {i j : ι} (h : v i = v j) (hij : i ≠ j) :
  f v = 0 :=
f.map_eq_zero_of_eq' v i j h hij

lemma map_coord_zero {m : ι → M} (i : ι) (h : m i = 0) : f m = 0 :=
f.to_multilinear_map.map_coord_zero i h

@[simp] lemma map_update_zero (m : ι → M) (i : ι) : f (update m i 0) = 0 :=
f.to_multilinear_map.map_update_zero m i

@[simp] lemma map_zero [nonempty ι] : f 0 = 0 :=
f.to_multilinear_map.map_zero

lemma map_eq_zero_of_not_injective (v : ι → M) (hv : ¬function.injective v) : f v = 0 :=
begin
  rw function.injective at hv,
  push_neg at hv,
  rcases hv with ⟨i₁, i₂, heq, hne⟩,
  exact f.map_eq_zero_of_eq v heq hne
end

/-!
### Algebraic structure inherited from `multilinear_map`

`alternating_map` carries the same `add_comm_monoid`, `add_comm_group`, and `module` structure
as `multilinear_map`
-/

instance : has_add (alternating_map R M N ι) :=
⟨λ a b,
  { map_eq_zero_of_eq' :=
      λ v i j h hij, by simp [a.map_eq_zero_of_eq v h hij, b.map_eq_zero_of_eq v h hij],
    ..(a + b : multilinear_map R (λ i : ι, M) N)}⟩

@[simp] lemma add_apply : (f + f') v = f v + f' v := rfl

@[norm_cast] lemma coe_add : (↑(f  + f') : multilinear_map R (λ i : ι, M) N) = f + f' := rfl

instance : has_zero (alternating_map R M N ι) :=
⟨{map_eq_zero_of_eq' := λ v i j h hij, by simp,
  ..(0 : multilinear_map R (λ i : ι, M) N)}⟩

@[simp] lemma zero_apply : (0 : alternating_map R M N ι) v = 0 := rfl

@[norm_cast] lemma coe_zero :
  ((0 : alternating_map R M N ι) : multilinear_map R (λ i : ι, M) N) = 0 := rfl

instance : inhabited (alternating_map R M N ι) := ⟨0⟩

instance : add_comm_monoid (alternating_map R M N ι) :=
{ zero := 0,
  add := (+),
  zero_add := by intros; ext; simp [add_comm, add_left_comm],
  add_zero := by intros; ext; simp [add_comm, add_left_comm],
  add_comm := by intros; ext; simp [add_comm, add_left_comm],
  add_assoc := by intros; ext; simp [add_comm, add_left_comm],
  nsmul := λ n f, { map_eq_zero_of_eq' := λ v i j h hij, by simp [f.map_eq_zero_of_eq v h hij],
    .. ((n • f : multilinear_map R (λ i : ι, M) N)) },
  nsmul_zero' := by { intros, ext, simp [add_smul], },
  nsmul_succ' := by { intros, ext, simp [add_smul, nat.succ_eq_one_add], } }

instance : has_neg (alternating_map R M N' ι) :=
⟨λ f,
  { map_eq_zero_of_eq' := λ v i j h hij, by simp [f.map_eq_zero_of_eq v h hij],
    ..(-(f : multilinear_map R (λ i : ι, M) N')) }⟩

@[simp] lemma neg_apply (m : ι → M) : (-g) m = -(g m) := rfl

@[norm_cast] lemma coe_neg :
  ((-g : alternating_map R M N' ι) : multilinear_map R (λ i : ι, M) N') = -g := rfl

instance : has_sub (alternating_map R M N' ι) :=
⟨λ f g,
  { map_eq_zero_of_eq' :=
      λ v i j h hij, by simp [f.map_eq_zero_of_eq v h hij, g.map_eq_zero_of_eq v h hij],
    ..(f - g : multilinear_map R (λ i : ι, M) N') }⟩

@[simp] lemma sub_apply (m : ι → M) : (g - g₂) m = g m - g₂ m := rfl

@[norm_cast] lemma coe_sub : (↑(g - g₂) : multilinear_map R (λ i : ι, M) N') = g - g₂ := rfl

instance : add_comm_group (alternating_map R M N' ι) :=
by refine
{ zero := 0,
  add := (+),
  neg := has_neg.neg,
  sub := has_sub.sub,
  sub_eq_add_neg := _,
  nsmul := λ n f, { map_eq_zero_of_eq' := λ v i j h hij, by simp [f.map_eq_zero_of_eq v h hij],
    .. ((n • f : multilinear_map R (λ i : ι, M) N')) },
  zsmul := λ n f, { map_eq_zero_of_eq' := λ v i j h hij, by simp [f.map_eq_zero_of_eq v h hij],
    .. ((n • f : multilinear_map R (λ i : ι, M) N')) },
  zsmul_zero' := _,
  zsmul_succ' := _,
  zsmul_neg' := _,
  .. alternating_map.add_comm_monoid, .. };
intros; ext;
simp [add_comm, add_left_comm, sub_eq_add_neg, add_smul, nat.succ_eq_add_one, coe_nat_zsmul]

section distrib_mul_action

variables {S : Type*} [monoid S] [distrib_mul_action S N] [smul_comm_class R S N]

instance : has_scalar S (alternating_map R M N ι) :=
⟨λ c f,
  { map_eq_zero_of_eq' := λ v i j h hij, by simp [f.map_eq_zero_of_eq v h hij],
    ..((c • f : multilinear_map R (λ i : ι, M) N)) }⟩

@[simp] lemma smul_apply (c : S) (m : ι → M) :
  (c • f) m = c • f m := rfl

@[norm_cast] lemma coe_smul (c : S):
  ((c • f : alternating_map R M N ι) : multilinear_map R (λ i : ι, M) N) = c • f := rfl

lemma coe_fn_smul (c : S) (f : alternating_map R M N ι) : ⇑(c • f) = c • f :=
rfl

instance : distrib_mul_action S (alternating_map R M N ι) :=
{ one_smul := λ f, ext $ λ x, one_smul _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul _ _ _,
  smul_zero := λ r, ext $ λ x, smul_zero _,
  smul_add := λ r f₁ f₂, ext $ λ x, smul_add _ _ _ }

end distrib_mul_action

section module

variables {S : Type*} [semiring S] [module S N] [smul_comm_class R S N]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
instance : module S (alternating_map R M N ι) :=
{ add_smul := λ r₁ r₂ f, ext $ λ x, add_smul _ _ _,
  zero_smul := λ f, ext $ λ x, zero_smul _ _ }

instance [no_zero_smul_divisors S N] : no_zero_smul_divisors S (alternating_map R M N ι) :=
coe_injective.no_zero_smul_divisors _ rfl coe_fn_smul

end module

section
variables (R N)

/-- The evaluation map from `ι → N` to `N` at a given `i` is alternating when `ι` is subsingleton.
-/
@[simps]
def of_subsingleton [subsingleton ι] (i : ι) : alternating_map R N N ι :=
{ to_fun := function.eval i,
  map_eq_zero_of_eq' := λ v i j hv hij, (hij $ subsingleton.elim _ _).elim,
  ..multilinear_map.of_subsingleton R N i }

end

end alternating_map

/-!
### Composition with linear maps
-/

namespace linear_map

variables {N₂ : Type*} [add_comm_monoid N₂] [module R N₂]

/-- Composing a alternating map with a linear map on the left gives again an alternating map. -/
def comp_alternating_map (g : N →ₗ[R] N₂) : alternating_map R M N ι →+ alternating_map R M N₂ ι :=
{ to_fun := λ f,
  { map_eq_zero_of_eq' := λ v i j h hij, by simp [f.map_eq_zero_of_eq v h hij],
              ..(g.comp_multilinear_map (f : multilinear_map R (λ _ : ι, M) N)) },
  map_zero' := by { ext, simp },
  map_add' := λ a b, by { ext, simp } }

@[simp] lemma coe_comp_alternating_map (g : N →ₗ[R] N₂) (f : alternating_map R M N ι) :
  ⇑(g.comp_alternating_map f) = g ∘ f := rfl

lemma comp_alternating_map_apply (g : N →ₗ[R] N₂) (f : alternating_map R M N ι) (m : ι → M) :
  g.comp_alternating_map f m = g (f m) := rfl

end linear_map

namespace alternating_map

variables {M₂ : Type*} [add_comm_monoid M₂] [module R M₂]
variables {M₃ : Type*} [add_comm_monoid M₃] [module R M₃]

/-- Composing a alternating map with the same linear map on each argument gives again an
alternating map. -/
def comp_linear_map (f : alternating_map R M N ι) (g : M₂ →ₗ[R] M) : alternating_map R M₂ N ι :=
{ map_eq_zero_of_eq' := λ v i j h hij, f.map_eq_zero_of_eq _ (linear_map.congr_arg h) hij,
  .. (f : multilinear_map R (λ _ : ι, M) N).comp_linear_map (λ _, g) }

lemma coe_comp_linear_map (f : alternating_map R M N ι) (g : M₂ →ₗ[R] M) :
  ⇑(f.comp_linear_map g) = f ∘ ((∘) g) := rfl

@[simp] lemma comp_linear_map_apply (f : alternating_map R M N ι) (g : M₂ →ₗ[R] M) (v : ι → M₂) :
  f.comp_linear_map g v = f (λ i, g (v i)) := rfl

/-- Composing an alternating map twice with the same linear map in each argument is
the same as composing with their composition. -/
lemma comp_linear_map_assoc (f : alternating_map R M N ι) (g₁ : M₂ →ₗ[R] M) (g₂ : M₃ →ₗ[R] M₂) :
  (f.comp_linear_map g₁).comp_linear_map g₂ = f.comp_linear_map (g₁ ∘ₗ g₂) :=
rfl

@[simp] lemma zero_comp_linear_map (g : M₂ →ₗ[R] M) :
  (0 : alternating_map R M N ι).comp_linear_map g = 0 :=
by { ext, simp only [comp_linear_map_apply, zero_apply] }

@[simp] lemma add_comp_linear_map (f₁ f₂ : alternating_map R M N ι) (g : M₂ →ₗ[R] M) :
  (f₁ + f₂).comp_linear_map g = f₁.comp_linear_map g + f₂.comp_linear_map g :=
by { ext, simp only [comp_linear_map_apply, add_apply] }

@[simp] lemma comp_linear_map_zero [nonempty ι] (f : alternating_map R M N ι) :
  f.comp_linear_map (0 : M₂ →ₗ[R] M) = 0 :=
begin
  ext,
  simp_rw [comp_linear_map_apply, linear_map.zero_apply, ←pi.zero_def, map_zero, zero_apply],
end

/-- Composing an alternating map with the identity linear map in each argument. -/
@[simp] lemma comp_linear_map_id (f : alternating_map R M N ι) :
  f.comp_linear_map linear_map.id = f :=
ext $ λ _, rfl

/-- Composing with a surjective linear map is injective. -/
lemma comp_linear_map_injective (f : M₂ →ₗ[R] M) (hf : function.surjective f) :
  function.injective (λ g : alternating_map R M N ι, g.comp_linear_map f) :=
λ g₁ g₂ h, ext $ λ x,
by simpa [function.surj_inv_eq hf] using ext_iff.mp h (function.surj_inv hf ∘ x)

lemma comp_linear_map_inj (f : M₂ →ₗ[R] M) (hf : function.surjective f)
  (g₁ g₂ : alternating_map R M N ι) : g₁.comp_linear_map f = g₂.comp_linear_map f ↔ g₁ = g₂ :=
(comp_linear_map_injective _ hf).eq_iff

section dom_lcongr

variables (ι R N) (S : Type*) [semiring S] [module S N] [smul_comm_class R S N]

/-- Construct a linear equivalence between maps from a linear equivalence between domains. -/
@[simps apply]
def dom_lcongr (e : M ≃ₗ[R] M₂) : alternating_map R M N ι ≃ₗ[S] alternating_map R M₂ N ι :=
{ to_fun := λ f, f.comp_linear_map e.symm,
  inv_fun := λ g, g.comp_linear_map e,
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl,
  left_inv := λ f, alternating_map.ext $ λ v, f.congr_arg $ funext $ λ i, e.symm_apply_apply _,
  right_inv := λ f, alternating_map.ext $ λ v, f.congr_arg $ funext $ λ i, e.apply_symm_apply _ }

@[simp] lemma dom_lcongr_refl :
  dom_lcongr R N ι S (linear_equiv.refl R M) = linear_equiv.refl S _ :=
linear_equiv.ext $ λ _, alternating_map.ext $ λ v, rfl

@[simp] lemma dom_lcongr_symm (e : M ≃ₗ[R] M₂) :
  (dom_lcongr R N ι S e).symm = dom_lcongr R N ι S e.symm :=
rfl

lemma dom_lcongr_trans (e : M ≃ₗ[R] M₂) (f : M₂ ≃ₗ[R] M₃):
  (dom_lcongr R N ι S e).trans (dom_lcongr R N ι S f) = dom_lcongr R N ι S (e.trans f) :=
rfl

end dom_lcongr

/-- Composing an alternating map with the same linear equiv on each argument gives the zero map
if and only if the alternating map is the zero map. -/
@[simp] lemma comp_linear_equiv_eq_zero_iff (f : alternating_map R M N ι) (g : M₂ ≃ₗ[R] M) :
  f.comp_linear_map (g : M₂ →ₗ[R] M) = 0 ↔ f = 0 :=
(dom_lcongr R N ι ℕ g.symm).map_eq_zero_iff

variables (f f' : alternating_map R M N ι)
variables (g g₂ : alternating_map R M N' ι)
variables (g' : alternating_map R M' N' ι)
variables (v : ι → M) (v' : ι → M')
open function

/-!
### Other lemmas from `multilinear_map`
-/
section

open_locale big_operators

lemma map_update_sum {α : Type*} (t : finset α) (i : ι) (g : α → M) (m : ι → M):
  f (update m i (∑ a in t, g a)) = ∑ a in t, f (update m i (g a)) :=
f.to_multilinear_map.map_update_sum t i g m

end

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

lemma map_swap {i j : ι} (hij : i ≠ j) :
  g (v ∘ equiv.swap i j) = - g v  :=
eq_neg_of_add_eq_zero (g.map_swap_add v hij)

lemma map_perm [fintype ι] (v : ι → M) (σ : equiv.perm ι) :
  g (v ∘ σ) = σ.sign • g v :=
begin
  apply equiv.perm.swap_induction_on' σ,
  { simp },
  { intros s x y hxy hI,
    simpa [g.map_swap (v ∘ s) hxy, equiv.perm.sign_swap hxy] using hI, }
end

lemma map_congr_perm [fintype ι] (σ : equiv.perm ι) :
  g v = σ.sign • g (v ∘ σ) :=
by { rw [g.map_perm, smul_smul], simp }

lemma coe_dom_dom_congr [fintype ι] (σ : equiv.perm ι) :
  (g : multilinear_map R (λ _ : ι, M) N').dom_dom_congr σ
    = σ.sign • (g : multilinear_map R (λ _ : ι, M) N') :=
multilinear_map.ext $ λ v, g.map_perm v σ

/-- If the arguments are linearly dependent then the result is `0`. -/
lemma map_linear_dependent
  {K : Type*} [ring K]
  {M : Type*} [add_comm_group M] [module K M]
  {N : Type*} [add_comm_group N] [module K N] [no_zero_smul_divisors K N]
  (f : alternating_map K M N ι) (v : ι → M)
  (h : ¬linear_independent K v) :
  f v = 0 :=
begin
  obtain ⟨s, g, h, i, hi, hz⟩ := not_linear_independent_iff.mp h,
  suffices : f (update v i (g i • v i)) = 0,
  { rw [f.map_smul, function.update_eq_self, smul_eq_zero] at this,
    exact or.resolve_left this hz, },
  conv at h in (g _ • v _) { rw ←if_t_t (i = x) (g _ • v _), },
  rw [finset.sum_ite, finset.filter_eq, finset.filter_ne, if_pos hi, finset.sum_singleton,
    add_eq_zero_iff_eq_neg] at h,
  rw [h, f.map_neg, f.map_update_sum, neg_eq_zero, finset.sum_eq_zero],
  intros j hj,
  obtain ⟨hij, _⟩ := finset.mem_erase.mp hj,
  rw [f.map_smul, f.map_update_self _ hij.symm, smul_zero],
end

end alternating_map

open_locale big_operators

namespace multilinear_map

open equiv

variables [fintype ι]

private lemma alternization_map_eq_zero_of_eq_aux
  (m : multilinear_map R (λ i : ι, M) N')
  (v : ι → M) (i j : ι) (i_ne_j : i ≠ j) (hv : v i = v j) :
  (∑ (σ : perm ι), σ.sign • m.dom_dom_congr σ) v = 0 :=
begin
  rw sum_apply,
  exact finset.sum_involution
    (λ σ _, swap i j * σ)
    (λ σ _, by simp [perm.sign_swap i_ne_j, apply_swap_eq_self hv])
    (λ σ _ _, (not_congr swap_mul_eq_iff).mpr i_ne_j)
    (λ σ _, finset.mem_univ _)
    (λ σ _, swap_mul_involutive i j σ)
end

/-- Produce an `alternating_map` out of a `multilinear_map`, by summing over all argument
permutations. -/
def alternatization : multilinear_map R (λ i : ι, M) N' →+ alternating_map R M N' ι :=
{ to_fun := λ m,
  { to_fun := ⇑(∑ (σ : perm ι), σ.sign • m.dom_dom_congr σ),
    map_eq_zero_of_eq' := λ v i j hvij hij, alternization_map_eq_zero_of_eq_aux m v i j hij hvij,
    .. (∑ (σ : perm ι), σ.sign • m.dom_dom_congr σ)},
  map_add' := λ a b, begin
    ext,
    simp only [
      finset.sum_add_distrib, smul_add, add_apply, dom_dom_congr_apply, alternating_map.add_apply,
      alternating_map.coe_mk, smul_apply, sum_apply],
  end,
  map_zero' := begin
    ext,
    simp only [
      finset.sum_const_zero, smul_zero, zero_apply, dom_dom_congr_apply, alternating_map.zero_apply,
      alternating_map.coe_mk, smul_apply, sum_apply],
  end }

lemma alternatization_def (m : multilinear_map R (λ i : ι, M) N') :
  ⇑(alternatization m) = (∑ (σ : perm ι), σ.sign • m.dom_dom_congr σ : _) :=
rfl

lemma alternatization_coe (m : multilinear_map R (λ i : ι, M) N') :
  ↑m.alternatization = (∑ (σ : perm ι), σ.sign • m.dom_dom_congr σ : _) :=
coe_injective rfl

lemma alternatization_apply (m : multilinear_map R (λ i : ι, M) N') (v : ι → M) :
  alternatization m v = ∑ (σ : perm ι), σ.sign • m.dom_dom_congr σ v :=
by simp only [alternatization_def, smul_apply, sum_apply]

end multilinear_map

namespace alternating_map

/-- Alternatizing a multilinear map that is already alternating results in a scale factor of `n!`,
where `n` is the number of inputs. -/
lemma coe_alternatization [fintype ι] (a : alternating_map R M N' ι) :
  (↑a : multilinear_map R (λ ι, M) N').alternatization = nat.factorial (fintype.card ι) • a :=
begin
  apply alternating_map.coe_injective,
  simp_rw [multilinear_map.alternatization_def, coe_dom_dom_congr, smul_smul,
    int.units_mul_self, one_smul, finset.sum_const, finset.card_univ, fintype.card_perm,
    ←coe_multilinear_map, coe_smul],
end

end alternating_map

namespace linear_map

variables {N'₂ : Type*} [add_comm_group N'₂] [module R N'₂] [fintype ι]

/-- Composition with a linear map before and after alternatization are equivalent. -/
lemma comp_multilinear_map_alternatization (g : N' →ₗ[R] N'₂)
  (f : multilinear_map R (λ _ : ι, M) N') :
  (g.comp_multilinear_map f).alternatization = g.comp_alternating_map (f.alternatization) :=
by { ext, simp [multilinear_map.alternatization_def] }

end linear_map

section coprod

open_locale big_operators
open_locale tensor_product

variables {ιa ιb : Type*} [decidable_eq ιa] [decidable_eq ιb] [fintype ιa] [fintype ιb]

variables
  {R' : Type*} {Mᵢ N₁ N₂ : Type*}
  [comm_semiring R']
  [add_comm_group N₁] [module R' N₁]
  [add_comm_group N₂] [module R' N₂]
  [add_comm_monoid Mᵢ] [module R' Mᵢ]

namespace equiv.perm

/-- Elements which are considered equivalent if they differ only by swaps within α or β  -/
abbreviation mod_sum_congr (α β : Type*) :=
_ ⧸ (equiv.perm.sum_congr_hom α β).range

lemma mod_sum_congr.swap_smul_involutive {α β : Type*} [decidable_eq (α ⊕ β)] (i j : α ⊕ β) :
  function.involutive (has_scalar.smul (equiv.swap i j) : mod_sum_congr α β → mod_sum_congr α β) :=
λ σ, begin
  apply σ.induction_on' (λ σ, _),
  exact _root_.congr_arg quotient.mk' (equiv.swap_mul_involutive i j σ)
end

end equiv.perm

namespace alternating_map
open equiv

/-- summand used in `alternating_map.dom_coprod` -/
def dom_coprod.summand
  (a : alternating_map R' Mᵢ N₁ ιa) (b : alternating_map R' Mᵢ N₂ ιb)
  (σ : perm.mod_sum_congr ιa ιb) :
  multilinear_map R' (λ _ : ιa ⊕ ιb, Mᵢ) (N₁ ⊗[R'] N₂) :=
quotient.lift_on' σ
  (λ σ,
    σ.sign •
      (multilinear_map.dom_coprod ↑a ↑b : multilinear_map R' (λ _, Mᵢ) (N₁ ⊗ N₂)).dom_dom_congr σ)
  (λ σ₁ σ₂ ⟨⟨sl, sr⟩, h⟩, begin
    ext v,
    simp only [multilinear_map.dom_dom_congr_apply, multilinear_map.dom_coprod_apply,
      coe_multilinear_map, multilinear_map.smul_apply],
    replace h := inv_mul_eq_iff_eq_mul.mp h.symm,
    have : (σ₁ * perm.sum_congr_hom _ _ (sl, sr)).sign = σ₁.sign * (sl.sign * sr.sign) :=
      by simp,
    rw [h, this, mul_smul, mul_smul, smul_left_cancel_iff,
      ←tensor_product.tmul_smul, tensor_product.smul_tmul'],
    simp only [sum.map_inr, perm.sum_congr_hom_apply, perm.sum_congr_apply, sum.map_inl,
              function.comp_app, perm.coe_mul],
    rw [←a.map_congr_perm (λ i, v (σ₁ _)), ←b.map_congr_perm (λ i, v (σ₁ _))],
  end)

lemma dom_coprod.summand_mk'
  (a : alternating_map R' Mᵢ N₁ ιa) (b : alternating_map R' Mᵢ N₂ ιb)
  (σ : equiv.perm (ιa ⊕ ιb)) :
  dom_coprod.summand a b (quotient.mk' σ) = σ.sign •
    (multilinear_map.dom_coprod ↑a ↑b : multilinear_map R' (λ _, Mᵢ) (N₁ ⊗ N₂)).dom_dom_congr σ :=
rfl

/-- Swapping elements in `σ` with equal values in `v` results in an addition that cancels -/
lemma dom_coprod.summand_add_swap_smul_eq_zero
  (a : alternating_map R' Mᵢ N₁ ιa) (b : alternating_map R' Mᵢ N₂ ιb)
  (σ : perm.mod_sum_congr ιa ιb)
  {v : ιa ⊕ ιb → Mᵢ} {i j : ιa ⊕ ιb} (hv : v i = v j) (hij : i ≠ j) :
  dom_coprod.summand a b σ v + dom_coprod.summand a b (swap i j • σ) v = 0 :=
begin
  apply σ.induction_on' (λ σ, _),
  dsimp only [quotient.lift_on'_mk', quotient.map'_mk', mul_action.quotient.smul_mk,
    dom_coprod.summand],
  rw [perm.sign_mul, perm.sign_swap hij],
  simp only [one_mul, units.neg_mul, function.comp_app, units.neg_smul, perm.coe_mul,
    units.coe_neg, multilinear_map.smul_apply, multilinear_map.neg_apply,
    multilinear_map.dom_dom_congr_apply, multilinear_map.dom_coprod_apply],
  convert add_right_neg _;
  { ext k, rw equiv.apply_swap_eq_self hv },
end

/-- Swapping elements in `σ` with equal values in `v` result in zero if the swap has no effect
on the quotient. -/
lemma dom_coprod.summand_eq_zero_of_smul_invariant
  (a : alternating_map R' Mᵢ N₁ ιa) (b : alternating_map R' Mᵢ N₂ ιb)
  (σ : perm.mod_sum_congr ιa ιb)
  {v : ιa ⊕ ιb → Mᵢ} {i j : ιa ⊕ ιb} (hv : v i = v j) (hij : i ≠ j) :
  swap i j • σ = σ → dom_coprod.summand a b σ v = 0 :=
begin
  apply σ.induction_on' (λ σ, _),
  dsimp only [quotient.lift_on'_mk', quotient.map'_mk', multilinear_map.smul_apply,
    multilinear_map.dom_dom_congr_apply, multilinear_map.dom_coprod_apply, dom_coprod.summand],
  intro hσ,
  with_cases
  { cases hi : σ⁻¹ i;
      cases hj : σ⁻¹ j;
      rw perm.inv_eq_iff_eq at hi hj;
      substs hi hj, },
  case [sum.inl sum.inr : i' j', sum.inr sum.inl : i' j']
  { -- the term pairs with and cancels another term
    all_goals { obtain ⟨⟨sl, sr⟩, hσ⟩ := quotient.exact' hσ, },
    work_on_goal 0 { replace hσ := equiv.congr_fun hσ (sum.inl i'), },
    work_on_goal 1 { replace hσ := equiv.congr_fun hσ (sum.inr i'), },
    all_goals
    { rw [←equiv.mul_swap_eq_swap_mul, mul_inv_rev, equiv.swap_inv, inv_mul_cancel_right] at hσ,
      simpa using hσ, }, },
  case [sum.inr sum.inr : i' j', sum.inl sum.inl : i' j']
  { -- the term does not pair but is zero
    all_goals { convert smul_zero _, },
    work_on_goal 0 { convert tensor_product.tmul_zero _ _, },
    work_on_goal 1 { convert tensor_product.zero_tmul _ _, },
    all_goals { exact alternating_map.map_eq_zero_of_eq _ _ hv (λ hij', hij (hij' ▸ rfl)), } },
end

/-- Like `multilinear_map.dom_coprod`, but ensures the result is also alternating.

Note that this is usually defined (for instance, as used in Proposition 22.24 in [Gallier2011Notes])
over integer indices `ιa = fin n` and `ιb = fin m`, as
$$
(f \wedge g)(u_1, \ldots, u_{m+n}) =
  \sum_{\operatorname{shuffle}(m, n)} \operatorname{sign}(\sigma)
    f(u_{\sigma(1)}, \ldots, u_{\sigma(m)}) g(u_{\sigma(m+1)}, \ldots, u_{\sigma(m+n)}),
$$
where $\operatorname{shuffle}(m, n)$ consists of all permutations of $[1, m+n]$ such that
$\sigma(1) < \cdots < \sigma(m)$ and $\sigma(m+1) < \cdots < \sigma(m+n)$.

Here, we generalize this by replacing:
* the product in the sum with a tensor product
* the filtering of $[1, m+n]$ to shuffles with an isomorphic quotient
* the additions in the subscripts of $\sigma$ with an index of type `sum`

The specialized version can be obtained by combining this definition with `fin_sum_fin_equiv` and
`algebra.lmul'`.
-/
@[simps]
def dom_coprod
  (a : alternating_map R' Mᵢ N₁ ιa) (b : alternating_map R' Mᵢ N₂ ιb) :
  alternating_map R' Mᵢ (N₁ ⊗[R'] N₂) (ιa ⊕ ιb) :=
{ to_fun := λ v, ⇑(∑ σ : perm.mod_sum_congr ιa ιb, dom_coprod.summand a b σ) v,
  map_eq_zero_of_eq' := λ v i j hv hij, begin
    dsimp only,
    rw multilinear_map.sum_apply,
    exact finset.sum_involution
      (λ σ _, equiv.swap i j • σ)
      (λ σ _, dom_coprod.summand_add_swap_smul_eq_zero a b σ hv hij)
      (λ σ _, mt $ dom_coprod.summand_eq_zero_of_smul_invariant a b σ hv hij)
      (λ σ _, finset.mem_univ _)
      (λ σ _, equiv.perm.mod_sum_congr.swap_smul_involutive i j σ),
  end,
  ..(∑ σ : perm.mod_sum_congr ιa ιb, dom_coprod.summand a b σ) }

lemma dom_coprod_coe (a : alternating_map R' Mᵢ N₁ ιa) (b : alternating_map R' Mᵢ N₂ ιb) :
  (↑(a.dom_coprod b) : multilinear_map R' (λ _, Mᵢ) _) =
    ∑ σ : perm.mod_sum_congr ιa ιb, dom_coprod.summand a b σ :=
multilinear_map.ext $ λ _, rfl

/-- A more bundled version of `alternating_map.dom_coprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
def dom_coprod' :
  (alternating_map R' Mᵢ N₁ ιa ⊗[R'] alternating_map R' Mᵢ N₂ ιb) →ₗ[R']
    alternating_map R' Mᵢ (N₁ ⊗[R'] N₂) (ιa ⊕ ιb) :=
tensor_product.lift $ by
  refine linear_map.mk₂ R' (dom_coprod)
    (λ m₁ m₂ n, _)
    (λ c m n, _)
    (λ m n₁ n₂, _)
    (λ c m n, _);
  { ext,
    simp only [dom_coprod_apply, add_apply, smul_apply, ←finset.sum_add_distrib,
      finset.smul_sum, multilinear_map.sum_apply, dom_coprod.summand],
    congr,
    ext σ,
    apply σ.induction_on' (λ σ, _),
    simp only [quotient.lift_on'_mk', coe_add, coe_smul, multilinear_map.smul_apply,
      ←multilinear_map.dom_coprod'_apply],
    simp only [tensor_product.add_tmul, ←tensor_product.smul_tmul',
      tensor_product.tmul_add, tensor_product.tmul_smul, linear_map.map_add, linear_map.map_smul],
    rw ←smul_add <|> rw smul_comm,
    congr }

@[simp]
lemma dom_coprod'_apply
  (a : alternating_map R' Mᵢ N₁ ιa) (b : alternating_map R' Mᵢ N₂ ιb) :
  dom_coprod' (a ⊗ₜ[R'] b) = dom_coprod a b :=
by simp only [dom_coprod', tensor_product.lift.tmul, linear_map.mk₂_apply]

end alternating_map

open equiv

/-- A helper lemma for `multilinear_map.dom_coprod_alternization`. -/
lemma multilinear_map.dom_coprod_alternization_coe
  (a : multilinear_map R' (λ _ : ιa, Mᵢ) N₁) (b : multilinear_map R' (λ _ : ιb, Mᵢ) N₂) :
  multilinear_map.dom_coprod ↑a.alternatization ↑b.alternatization =
    ∑ (σa : perm ιa) (σb : perm ιb), σa.sign • σb.sign •
      multilinear_map.dom_coprod (a.dom_dom_congr σa) (b.dom_dom_congr σb) :=
begin
  simp_rw [←multilinear_map.dom_coprod'_apply, multilinear_map.alternatization_coe],
  simp_rw [tensor_product.sum_tmul, tensor_product.tmul_sum, linear_map.map_sum,
    ←tensor_product.smul_tmul', tensor_product.tmul_smul, linear_map.map_smul_of_tower],
end

open alternating_map

/-- Computing the `multilinear_map.alternatization` of the `multilinear_map.dom_coprod` is the same
as computing the `alternating_map.dom_coprod` of the `multilinear_map.alternatization`s.
-/
lemma multilinear_map.dom_coprod_alternization
  (a : multilinear_map R' (λ _ : ιa, Mᵢ) N₁) (b : multilinear_map R' (λ _ : ιb, Mᵢ) N₂) :
  (multilinear_map.dom_coprod a b).alternatization =
    a.alternatization.dom_coprod b.alternatization :=
begin
  apply coe_multilinear_map_injective,
  rw [dom_coprod_coe, multilinear_map.alternatization_coe,
    finset.sum_partition (quotient_group.left_rel (perm.sum_congr_hom ιa ιb).range)],
  congr' 1,
  ext1 σ,
  apply σ.induction_on' (λ σ, _),

  -- unfold the quotient mess left by `finset.sum_partition`
  conv in (_ = quotient.mk' _)
  { change quotient.mk' _ = quotient.mk' _,
    rw quotient.eq',
    rw [quotient_group.left_rel],
    dsimp only [setoid.r] },

  -- eliminate a multiplication
  have : @finset.univ (perm (ιa ⊕ ιb)) _ = finset.univ.image ((*) σ) :=
    (finset.eq_univ_iff_forall.mpr $ λ a, let ⟨a', ha'⟩ := mul_left_surjective σ a in
      finset.mem_image.mpr ⟨a', finset.mem_univ _, ha'⟩).symm,
  rw [this, finset.image_filter],
  simp only [function.comp, mul_inv_rev, inv_mul_cancel_right, subgroup.inv_mem_iff],
  simp only [monoid_hom.mem_range], -- needs to be separate from the above `simp only`
  rw [finset.filter_congr_decidable,
    finset.univ_filter_exists (perm.sum_congr_hom ιa ιb),
    finset.sum_image (λ x _ y _ (h : _ = _), mul_right_injective _ h),
    finset.sum_image (λ x _ y _ (h : _ = _), perm.sum_congr_hom_injective h)],
  dsimp only,

  -- now we're ready to clean up the RHS, pulling out the summation
  rw [dom_coprod.summand_mk', multilinear_map.dom_coprod_alternization_coe,
    ←finset.sum_product', finset.univ_product_univ,
    ←multilinear_map.dom_dom_congr_equiv_apply, add_equiv.map_sum, finset.smul_sum],
  congr' 1,
  ext1 ⟨al, ar⟩,
  dsimp only,

  -- pull out the pair of smuls on the RHS, by rewriting to `_ →ₗ[ℤ] _` and back
  rw [←add_equiv.coe_to_add_monoid_hom, ←add_monoid_hom.coe_to_int_linear_map,
    linear_map.map_smul_of_tower,
    linear_map.map_smul_of_tower,
    add_monoid_hom.coe_to_int_linear_map, add_equiv.coe_to_add_monoid_hom,
    multilinear_map.dom_dom_congr_equiv_apply],

  -- pick up the pieces
  rw [multilinear_map.dom_dom_congr_mul, perm.sign_mul,
    perm.sum_congr_hom_apply, multilinear_map.dom_coprod_dom_dom_congr_sum_congr,
    perm.sign_sum_congr, mul_smul, mul_smul],
end

/-- Taking the `multilinear_map.alternatization` of the `multilinear_map.dom_coprod` of two
`alternating_map`s gives a scaled version of the `alternating_map.coprod` of those maps.
-/
lemma multilinear_map.dom_coprod_alternization_eq
  (a : alternating_map R' Mᵢ N₁ ιa) (b : alternating_map R' Mᵢ N₂ ιb) :
  (multilinear_map.dom_coprod a b : multilinear_map R' (λ _ : ιa ⊕ ιb, Mᵢ) (N₁ ⊗ N₂))
    .alternatization =
    ((fintype.card ιa).factorial * (fintype.card ιb).factorial) • a.dom_coprod b :=
begin
  rw [multilinear_map.dom_coprod_alternization, coe_alternatization, coe_alternatization, mul_smul,
    ←dom_coprod'_apply, ←dom_coprod'_apply, ←tensor_product.smul_tmul', tensor_product.tmul_smul,
    linear_map.map_smul_of_tower dom_coprod', linear_map.map_smul_of_tower dom_coprod'],
  -- typeclass resolution is a little confused here
  apply_instance, apply_instance,
end

end coprod

section basis

open alternating_map

variables {ι₁ : Type*} [fintype ι]
variables {R' : Type*} {N₁ N₂ : Type*} [comm_semiring R'] [add_comm_monoid N₁] [add_comm_monoid N₂]
variables [module R' N₁] [module R' N₂]

/-- Two alternating maps indexed by a `fintype` are equal if they are equal when all arguments
are distinct basis vectors. -/
lemma basis.ext_alternating {f g : alternating_map R' N₁ N₂ ι} (e : basis ι₁ R' N₁)
  (h : ∀ v : ι → ι₁, function.injective v → f (λ i, e (v i)) = g (λ i, e (v i))) : f = g :=
begin
  refine alternating_map.coe_multilinear_map_injective (basis.ext_multilinear e $ λ v, _),
  by_cases hi : function.injective v,
  { exact h v hi },
  { have : ¬function.injective (λ i, e (v i)) := hi.imp function.injective.of_comp,
    rw [coe_multilinear_map, coe_multilinear_map,
        f.map_eq_zero_of_not_injective _ this, g.map_eq_zero_of_not_injective _ this], }
end

end basis
