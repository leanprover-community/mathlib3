/-
Copyright (c) 2020 Zhangir Azerbayev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Wieser, Zhangir Azerbayev
-/

import linear_algebra.multilinear
import group_theory.perm.sign
import group_theory.perm.subgroup
import data.equiv.fin
import linear_algebra.tensor_product
import ring_theory.algebra_tower
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
* An `add_comm_monoid`, `add_comm_group`, and `semimodule` structure over `alternating_map`s that
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

-- TODO: move
section to_move

lemma semimodule.nsmul {M : Type*} [add_comm_monoid M] (i : semimodule ℕ M) (n : ℕ) (a : M) :
  n •ℕ a = n • a :=
begin
  have := subsingleton.elim add_comm_monoid.nat_semimodule i,
  rw ←nat.smul_def,
  rw this,
end

namespace tensor_product

open_locale tensor_product


theorem smul_tmul'_int {R : Type*} {M : Type*} {N : Type*}
  [comm_semiring R] [add_comm_group M] [add_comm_group N] [semimodule R M] [semimodule R N]
  [semimodule ℤ M] [semimodule ℤ N]
  (r : ℤ) (m : M) (n : N) :
  r • (m ⊗ₜ n : M ⊗[R] N) = (r • m) ⊗ₜ n :=
begin
  induction r using int.induction_on,
  case hz : { simp },
  case hp : n ih { simpa [add_smul, add_tmul] using ih },
  case hn : n ih { simpa [sub_smul, sub_tmul] using ih },
end

theorem tmul_smul_int {R : Type*} {M : Type*} {N : Type*}
  [comm_semiring R] [add_comm_group M] [add_comm_group N] [semimodule R M] [semimodule R N]
   [semimodule ℤ M] [semimodule ℤ N]
  (r : ℤ) (m : M) (n : N) :
  m ⊗ₜ (r • n) = r • (m ⊗ₜ n : M ⊗[R] N) :=
begin
  induction r using int.induction_on,
  case hz : { simp },
  case hp : n ih { simpa [add_smul, tmul_add] using ih },
  case hn : n ih { simpa [sub_smul, tmul_sub] using ih },
end

lemma smul_tmul_int {R : Type*} {M : Type*} {N : Type*}
  [comm_semiring R] [add_comm_group M] [add_comm_group N] [semimodule R M] [semimodule R N]
   [semimodule ℤ M] [semimodule ℤ N]
  (r : ℤ) (m : M) (n : N) : ((r • m) ⊗ₜ[R] n) = m ⊗ₜ[R] r • n :=
begin
  rw [tmul_smul_int, smul_tmul'_int]
end


end tensor_product

namespace tactic
namespace interactive

open lean.parser
open interactive

/-- Focus on the first `n` goals. -/
meta def first_n_goals : parse small_nat → itactic → tactic unit
| n t := do
  goals ← get_goals,
  let current_goals := goals.take n,
  let later_goals := goals.drop n,
  set_goals current_goals,
  t,
  new_goals ← get_goals,
  set_goals (new_goals ++ later_goals)

end interactive
end tactic

end to_move

-- semiring / add_comm_monoid
variables {R : Type*} [semiring R]
variables {M : Type*} [add_comm_monoid M] [semimodule R M]
variables {N : Type*} [add_comm_monoid N] [semimodule R N]

-- semiring / add_comm_group
variables {M' : Type*} [add_comm_group M'] [semimodule R M']
variables {N' : Type*} [add_comm_group N'] [semimodule R N']

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

@[simp] lemma map_neg (i : ι) (x : M') :
  g' (update v' i (-x)) = -g' (update v' i x) :=
g'.to_multilinear_map.map_neg v' i x

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

@[norm_cast] lemma coe_add : (↑(f  + f') : multilinear_map R (λ i : ι, M) N) = f + f' := rfl

instance : has_zero (alternating_map R M N ι) :=
⟨{map_eq_zero_of_eq' := λ v i j h hij, by simp,
  ..(0 : multilinear_map R (λ i : ι, M) N)}⟩

@[simp] lemma zero_apply : (0 : alternating_map R M N ι) v = 0 := rfl

@[norm_cast] lemma coe_zero :
  ((0 : alternating_map R M N ι) : multilinear_map R (λ i : ι, M) N) = 0 := rfl

instance : inhabited (alternating_map R M N ι) := ⟨0⟩

instance : add_comm_monoid (alternating_map R M N ι) :=
by refine {zero := 0, add := (+), ..};
   intros; ext; simp [add_comm, add_left_comm]

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
    ..(f - g : multilinear_map R (λ i : ι, M) N')  }⟩

@[simp] lemma sub_apply (m : ι → M) : (g - g₂) m = g m - g₂ m := rfl

@[norm_cast] lemma coe_sub : (↑(g - g₂) : multilinear_map R (λ i : ι, M) N') = g - g₂ := rfl

instance : add_comm_group (alternating_map R M N' ι) :=
by refine {zero := 0, add := (+), neg := has_neg.neg,
           sub := has_sub.sub, sub_eq_add_neg := _, ..};
   intros; ext; simp [add_comm, add_left_comm, sub_eq_add_neg]

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

instance : distrib_mul_action S (alternating_map R M N ι) :=
{ one_smul := λ f, ext $ λ x, one_smul _ _,
  mul_smul := λ c₁ c₂ f, ext $ λ x, mul_smul _ _ _,
  smul_zero := λ r, ext $ λ x, smul_zero _,
  smul_add := λ r f₁ f₂, ext $ λ x, smul_add _ _ _ }

end distrib_mul_action

section semimodule

variables {S : Type*} [semiring S] [semimodule S N] [smul_comm_class R S N]

/-- The space of multilinear maps over an algebra over `R` is a module over `R`, for the pointwise
addition and scalar multiplication. -/
instance : semimodule S (alternating_map R M N ι) :=
{ add_smul := λ r₁ r₂ f, ext $ λ x, add_smul _ _ _,
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

lemma coe_dom_dom_congr [fintype ι] (σ : equiv.perm ι) :
  (g : multilinear_map R (λ _ : ι, M) N').dom_dom_congr σ
    = (equiv.perm.sign σ : ℤ) • (g : multilinear_map R (λ _ : ι, M) N') :=
multilinear_map.ext $ λ v, g.map_perm v σ

end alternating_map

open_locale big_operators

namespace multilinear_map

open equiv

variables [fintype ι]

private lemma alternization_map_eq_zero_of_eq_aux
  (m : multilinear_map R (λ i : ι, M) N')
  (v : ι → M) (i j : ι) (i_ne_j : i ≠ j) (hv : v i = v j) :
  (∑ (σ : perm ι), (σ.sign : ℤ) • m.dom_dom_congr σ) v = 0 :=
begin
  rw sum_apply,
  exact finset.sum_involution
    (λ σ _, swap i j * σ)
    (λ σ _, begin
      convert add_right_neg (↑σ.sign • m.dom_dom_congr σ v),
      rw [perm.sign_mul, perm.sign_swap i_ne_j, ←neg_smul, smul_apply,
        dom_dom_congr_apply, dom_dom_congr_apply],
      congr' 2,
      { simp },
      { ext, simp [apply_swap_eq_self hv] },
    end)
    (λ σ _ _, (not_congr swap_mul_eq_iff).mpr i_ne_j)
    (λ σ _, finset.mem_univ _)
    (λ σ _, swap_mul_involutive i j σ)
end

/-- Produce an `alternating_map` out of a `multilinear_map`, by summing over all argument
permutations. -/
def alternatization : multilinear_map R (λ i : ι, M) N' →+ alternating_map R M N' ι :=
{ to_fun := λ m,
  { to_fun := ⇑(∑ (σ : perm ι), (σ.sign : ℤ) • m.dom_dom_congr σ),
    map_eq_zero_of_eq' := λ v i j hvij hij, alternization_map_eq_zero_of_eq_aux m v i j hij hvij,
    .. (∑ (σ : perm ι), (σ.sign : ℤ) • m.dom_dom_congr σ)},
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
  ⇑(alternatization m) = (∑ (σ : perm ι), (σ.sign : ℤ) • m.dom_dom_congr σ : _) :=
rfl

end multilinear_map

namespace alternating_map

/-- Alternatizing a multilinear map that is already alternating results in a scale factor of `n!`,
where `n` is the number of inputs. -/
lemma coe_alternatization [fintype ι] (a : alternating_map R M N' ι) :
  (↑a : multilinear_map R (λ ι, M) N').alternatization = nat.factorial (fintype.card ι) • a :=
begin
  apply alternating_map.coe_inj,
  rw multilinear_map.alternatization_def,
  simp_rw [coe_dom_dom_congr, smul_smul, int.units_coe_mul_self, one_smul,
    finset.sum_const, finset.card_univ, fintype.card_perm, ←nat.smul_def],
  rw [←coe_multilinear_map, coe_smul],
  -- ((•) : ℕ → _ → _) has a diamond we have to resolve
  rw subsingleton.elim add_comm_monoid.nat_semimodule,
  apply_instance,
end

end alternating_map

section coprod

namespace equiv.perm

/-- Elements which are considered equivalent if they differ only by swaps within α or β  -/
abbreviation mod_sum_congr (α β : Type*) :=
quotient_group.quotient (equiv.perm.sum_congr_hom α β).range

end equiv.perm

namespace alternating_map

open_locale big_operators
open_locale tensor_product
open equiv

variables {ιa ιb : Type*} [decidable_eq ιa] [decidable_eq ιb] [fintype ιa] [fintype ιb]

private def dom_coprod_aux
  {R : Type*} {M N₁ N₂ : Type*}
  [comm_semiring R]
  [add_comm_group N₁] [semimodule R N₁]
  [add_comm_group N₂] [semimodule R N₂]
  [add_comm_monoid M] [semimodule R M]
  (a : alternating_map R M N₁ ιa) (b : alternating_map R M N₂ ιb) :
  multilinear_map R (λ _ : ιa ⊕ ιb, M) (N₁ ⊗[R] N₂) :=
∑ σ : perm.mod_sum_congr ιa ιb, σ.lift_on' (λ σ,
  (σ.sign : ℤ) •
    (multilinear_map.dom_coprod a b : multilinear_map R (λ (_ : ιa ⊕ ιb), M) (N₁ ⊗ N₂))
      .dom_dom_congr σ)
(λ σ₁ σ₂ h, begin
  ext v,
  simp only [multilinear_map.dom_dom_congr_apply, multilinear_map.dom_coprod_apply,
    coe_multilinear_map, multilinear_map.smul_apply],
  obtain ⟨⟨sl, sr⟩, h⟩ := h,
  replace h := h.symm,
  rw inv_mul_eq_iff_eq_mul at h,
  have : ((σ₁ * perm.sum_congr_hom _ _ (sl, sr)).sign : ℤ) = σ₁.sign * (sl.sign * sr.sign) :=
    by simp,
  rw [h, this, mul_smul, mul_smul, units.smul_left_cancel, ←tensor_product.tmul_smul_int,
    tensor_product.smul_tmul'_int],
  simp only [sum.map_inr, perm.sum_congr_hom_apply, perm.sum_congr_apply, sum.map_inl,
             function.comp_app, perm.coe_mul],
  rw [←a.map_congr_perm (λ i, v (σ₁ _)), ←b.map_congr_perm (λ i, v (σ₁ _))],
end)

private lemma dom_coprod_aux_eq_zero_if_eq
  {R : Type*} {M N₁ N₂ : Type*}
  [comm_semiring R]
  [add_comm_group N₁] [semimodule R N₁]
  [add_comm_group N₂] [semimodule R N₂]
  [add_comm_monoid M] [semimodule R M]
  (a : alternating_map R M N₁ ιa) (b : alternating_map R M N₂ ιb)
  (v : ιa ⊕ ιb → M) (i j : ιa ⊕ ιb) (hv : v i = v j) (hij : i ≠ j) :
  dom_coprod_aux a b v = 0 :=
begin
  unfold dom_coprod_aux,
  dsimp only,
  rw multilinear_map.sum_apply,
  apply finset.sum_involution
    (λ σ _, (equiv.swap i j • σ : perm.mod_sum_congr ιa ιb))
    (λ σ, _)
    (λ σ, _)
    (λ σ _, finset.mem_univ _)
    (λ σ, _),
  all_goals {
    apply σ.induction_on' (λ σ, _),
    rintro _, },
  { dsimp only [quotient.lift_on'_beta, quotient.map'_mk', mul_action.quotient.smul_mk],
    rw [perm.sign_mul, perm.sign_swap hij],
    simp only [one_mul, units.neg_mul, function.comp_app, neg_smul, perm.coe_mul,
      units.coe_neg, multilinear_map.smul_apply, multilinear_map.neg_apply,
      multilinear_map.dom_dom_congr_apply, multilinear_map.dom_coprod_apply],
    convert add_right_neg _;
    { ext k, rw equiv.apply_swap_eq_self hv }, },
  { dsimp only [quotient.lift_on'_beta, quotient.map'_mk', multilinear_map.smul_apply,
      multilinear_map.dom_dom_congr_apply, multilinear_map.dom_coprod_apply],
    apply mt,
    intro hσ,
    cases hi : σ⁻¹ i with i' i';
      cases hj : σ⁻¹ j with j' j';
      rw perm.inv_eq_iff_eq at hi hj;
      substs hi hj,
    rotate,
    first_n_goals 2 { -- the term pairs with and cancels another term
      all_goals { obtain ⟨⟨sl, sr⟩, hσ⟩ := quotient.eq'.mp hσ, },
      work_on_goal 0 { replace hσ := equiv.congr_fun hσ (sum.inl i'), },
      work_on_goal 1 { replace hσ := equiv.congr_fun hσ (sum.inr i'), },
      all_goals {
        rw [←equiv.mul_swap_eq_swap_mul, mul_inv_rev, equiv.swap_inv, inv_mul_cancel_right] at hσ,
        simpa using hσ, }, },
    first_n_goals 2 { -- the term does not pair but is zero
      all_goals { convert smul_zero _, },
      work_on_goal 0 { convert tensor_product.tmul_zero _ _, },
      work_on_goal 1 { convert tensor_product.zero_tmul _ _, },
      all_goals { exact alternating_map.map_eq_zero_of_eq _ _ hv (λ hij', hij (hij' ▸ rfl)), },
      }, },
  { exact _root_.congr_arg (quot.mk _) (equiv.swap_mul_involutive i j σ), }
end

/-- Like `multilinear_map.dom_coprod`, but ensures the result is also alternating.

Note that this is usually defined over integer indices `ιa = fin n` and `ιb = fin m`, as
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
* the additions in the subscripts of $\sigma$ with a index of type `sum`
-/
@[simps]
def dom_coprod
  {R : Type*} {M N₁ N₂ : Type*}
  [comm_semiring R]
  [add_comm_group N₁] [semimodule R N₁]
  [add_comm_group N₂] [semimodule R N₂]
  [add_comm_monoid M] [semimodule R M]
  (a : alternating_map R M N₁ ιa) (b : alternating_map R M N₂ ιb) :
  alternating_map R M (N₁ ⊗[R] N₂) (ιa ⊕ ιb) :=
{ to_fun := dom_coprod_aux a b,
  map_eq_zero_of_eq' := dom_coprod_aux_eq_zero_if_eq a b,
  ..dom_coprod_aux a b }

-- /-- The usual definition of multiplication of alternating maps, over integer indices. -/
-- def mul_fin {n m} {R : Type*} {M N : Type*}
--   [comm_semiring R] [ring N] [algebra R N] [add_comm_monoid M] [semimodule R M]
--   (a : alternating_map R M N (fin m)) (b : alternating_map R M N (fin n)) :
--   alternating_map R M N (fin (m + n)) :=
-- (algebra.lmul' R).comp_multilinear_map $ (a.dom_coprod b).dom_dom_congr (fin_sum_fin_equiv)

/-- A more bundled version of `alternating_map.dom_coprod` that maps
`((ι₁ → N) → N₁) ⊗ ((ι₂ → N) → N₂)` to `(ι₁ ⊕ ι₂ → N) → N₁ ⊗ N₂`. -/
def dom_coprod'
  {R : Type*} {M N₁ N₂ : Type*}
  [comm_semiring R]
  [add_comm_group N₁] [semimodule R N₁]
  [add_comm_group N₂] [semimodule R N₂]
  [add_comm_monoid M] [semimodule R M] :
  (alternating_map R M N₁ ιa ⊗[R] alternating_map R M N₂ ιb) →ₗ[R]
    alternating_map R M (N₁ ⊗[R] N₂) (ιa ⊕ ιb) :=
tensor_product.lift $ by
  refine linear_map.mk₂ R (dom_coprod)
    (λ m₁ m₂ n, _)
    (λ c m n, _)
    (λ m n₁ n₂, _)
    (λ c m n, _);
  { ext,
    simp only [dom_coprod_apply, dom_coprod_aux, add_apply, smul_apply, ←finset.sum_add_distrib,
      finset.smul_sum, multilinear_map.sum_apply],
    congr,
    ext σ,
    apply σ.induction_on' (λ σ, _),
    simp only [quotient.lift_on'_beta, coe_add, coe_smul, multilinear_map.smul_apply,
      ←multilinear_map.dom_coprod'_apply],
    simp only [tensor_product.add_tmul, ←tensor_product.smul_tmul',
      tensor_product.tmul_add, tensor_product.tmul_smul, linear_map.map_add, linear_map.map_smul],
    rw ←smul_add <|> rw smul_comm,
    congr }

@[simp]
lemma dom_coprod'_apply
  {R : Type*} {M N₁ N₂ : Type*}
  [comm_semiring R]
  [add_comm_group N₁] [semimodule R N₁]
  [add_comm_group N₂] [semimodule R N₂]
  [add_comm_monoid M] [semimodule R M]
  (a : alternating_map R M N₁ ιa) (b : alternating_map R M N₂ ιb) :
  dom_coprod' (a ⊗ₜ[R] b) = dom_coprod a b :=
by simp only [dom_coprod', tensor_product.lift.tmul, linear_map.mk₂_apply]

/-- Computing the `multilinear_map.alternatization` of the `multilinear_map.dom_coprod` is the same
as computing the `alternating_map.dom_coprod` of the `multilinear_map.alternatization`s.
-/
lemma multilinear_map.dom_coprod_alternization
  {R : Type*} {M N₁ N₂ : Type*}
  [comm_semiring R]
  [add_comm_group N₁] [semimodule R N₁]
  [add_comm_group N₂] [semimodule R N₂]
  [add_comm_monoid M] [semimodule R M]
  (a : multilinear_map R (λ _ : ιa, M) N₁) (b : multilinear_map R (λ _ : ιb, M) N₂) :
  (multilinear_map.dom_coprod a b).alternatization =
    a.alternatization.dom_coprod b.alternatization :=
begin
  ext,
  dsimp only [dom_coprod_apply, smul_apply, multilinear_map.alternatization_def,
    alternating_map.dom_coprod_apply, dom_coprod_aux],
  simp_rw multilinear_map.sum_apply,
  rw finset.sum_partition (quotient_group.left_rel (perm.sum_congr_hom ιa ιb).range),
  congr' 1,
  ext σ,
  apply σ.induction_on' (λ σ, _),

  -- unfold the quotient mess
  dsimp only [quotient.lift_on'_beta],
  conv in (_ = quotient.mk' _) {
    change quotient.mk' _ = quotient.mk' _,
  },
  simp_rw (iff.intro quotient.exact' quotient.sound'),
  dunfold setoid.r quotient_group.left_rel,
  simp only,

  dsimp only [multilinear_map.dom_dom_congr_apply, multilinear_map.dom_coprod_apply,
    coe_multilinear_map, multilinear_map.smul_apply, multilinear_map.alternatization_def],
  simp only [multilinear_map.sum_apply, multilinear_map.smul_apply],
  simp_rw [tensor_product.sum_tmul, tensor_product.tmul_sum,
    ←tensor_product.smul_tmul'_int, tensor_product.tmul_smul_int],

  -- eliminate a multiplication
  have : @finset.univ (perm (ιa ⊕ ιb)) _ = finset.univ.image ((*) σ) := begin
    ext, simp only [true_iff, finset.mem_univ, exists_prop_of_true, finset.mem_image],
    use σ⁻¹ * a_1,
    simp,
  end,
  rw this,
  simp only,
  rw finset.image_filter,
  simp only [function.comp, mul_inv_rev, inv_mul_cancel_right, subgroup.inv_mem_iff],
  rw finset.sum_image (λ x hx y hy, (mul_right_inj σ).mp),
  rw finset.sum_subtype (λ x, show x ∈ _ ↔ x ∈ (perm.sum_congr_hom ιa ιb).range, from _),
  change ∑ (a_1 : (perm.sum_congr_hom ιa ιb).range), _ = _,
  swap, { simp only [finset.mem_filter, finset.mem_univ, true_and] },

  simp_rw [perm.sign_mul, units.coe_mul, mul_smul, finset.smul_sum],
  rw [←finset.sum_product', finset.univ_product_univ],
  symmetry,
  apply finset.sum_bij
    (λ a ha, (⟨perm.sum_congr_hom ιa ιb a, a, rfl⟩ : (perm.sum_congr_hom ιa ιb).range))
    (λ a ha, finset.mem_univ _)
    (λ a ha, _)
    (λ a₁ a₂ ha₁ ha₂ heq, perm.sum_congr_hom_injective (subtype.ext_iff.mp heq))
    (λ b hb, let ⟨⟨sl, sr⟩, hb⟩ := b.prop in ⟨(sl, sr), finset.mem_univ _, subtype.ext hb.symm⟩),
  dsimp only [subtype.coe_mk],
  obtain ⟨al, ar⟩ := a,
  simp_rw perm.sum_congr_hom_apply ιa ιb (al, ar),
  simp [perm.mul_apply, mul_smul],
  congr,
end

instance nat_is_scalar_tower {S : Type*} [semiring S] [semimodule S M] [semimodule ℕ M] :
  is_scalar_tower ℕ S M :=
{ smul_assoc := begin
    intros n x y,
    induction n with n ih,
    { simp only [zero_smul] },
    { simp only [nat.succ_eq_add_one, add_smul, one_smul, ih] }
  end }

  #check @alternating_map.nat_is_scalar_tower


/-- Taking the `multilinear_map.alternatization` of the `multilinear_map.dom_coprod` of two
`alternating_map`s gives a scaled version of the `alternating_map.coprod` of those maps.
-/
lemma multilinear_map.dom_coprod_alternization_eq
  {R : Type*} {M N₁ N₂ : Type*}
  [comm_semiring R]
  [add_comm_group N₁] [semimodule R N₁]
  [add_comm_group N₂] [semimodule R N₂]
  [add_comm_monoid M] [semimodule R M]
  (a : alternating_map R M N₁ ιa) (b : alternating_map R M N₂ ιb) :
  (multilinear_map.dom_coprod a b : multilinear_map R (λ _ : ιa ⊕ ιb, M) (N₁ ⊗ N₂))
    .alternatization =
    ((fintype.card ιa).factorial * (fintype.card ιb).factorial) • a.dom_coprod b :=
begin
  rw [multilinear_map.dom_coprod_alternization, coe_alternatization, coe_alternatization, mul_smul],
  rw [←dom_coprod'_apply, ←dom_coprod'_apply, ←tensor_product.smul_tmul', tensor_product.tmul_smul],
  rw [linear_map.map_smul_of_tower dom_coprod', linear_map.map_smul_of_tower dom_coprod'],
  -- typeclass resolution is a little confused here
  all_goals {try {apply_instance}},
  all_goals {
    convert alternating_map.nat_is_scalar_tower,
    change tensor_product.semimodule'.to_distrib_mul_action.to_mul_action.to_has_scalar = _,
    congr, }
end

end alternating_map

end coprod
