/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import algebra.big_operators.pi
import algebra.module.hom
import algebra.module.prod
import algebra.module.submodule.lattice
import data.dfinsupp.basic
import data.finsupp.basic
import order.compactly_generated

/-!
# Linear algebra

This file defines the basics of linear algebra. It sets up the "categorical/lattice structure" of
modules over a ring, submodules, and linear maps.

Many of the relevant definitions, including `module`, `submodule`, and `linear_map`, are found in
`src/algebra/module`.

## Main definitions

* Many constructors for (semi)linear maps
* The kernel `ker` and range `range` of a linear map are submodules of the domain and codomain
  respectively.
* The general linear group is defined to be the group of invertible linear maps from `M` to itself.

See `linear_algebra.span` for the span of a set (as a submodule),
and `linear_algebra.quotient` for quotients by submodules.

## Main theorems

See `linear_algebra.isomorphisms` for Noether's three isomorphism theorems for modules.

## Notations

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Implementation notes

We note that, when constructing linear maps, it is convenient to use operations defined on bundled
maps (`linear_map.prod`, `linear_map.coprod`, arithmetic operations like `+`) instead of defining a
function and proving it is linear.

## TODO

* Parts of this file have not yet been generalized to semilinear maps

## Tags
linear algebra, vector space, module

-/

open function
open_locale big_operators pointwise

variables {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*} {R₄ : Type*}
variables {S : Type*}
variables {K : Type*} {K₂ : Type*}
variables {M : Type*} {M' : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*} {M₄ : Type*}
variables {N : Type*} {N₂ : Type*}
variables {ι : Type*}
variables {V : Type*} {V₂ : Type*}

namespace finsupp

lemma smul_sum {α : Type*} {β : Type*} {R : Type*} {M : Type*}
  [has_zero β] [monoid R] [add_comm_monoid M] [distrib_mul_action R M]
  {v : α →₀ β} {c : R} {h : α → β → M} :
  c • (v.sum h) = v.sum (λa b, c • h a b) :=
finset.smul_sum

@[simp]
lemma sum_smul_index_linear_map' {α : Type*} {R : Type*} {M : Type*} {M₂ : Type*}
  [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid M₂] [module R M₂]
  {v : α →₀ M} {c : R} {h : α → M →ₗ[R] M₂} :
  (c • v).sum (λ a, h a) = c • (v.sum (λ a, h a)) :=
begin
  rw [finsupp.sum_smul_index', finsupp.smul_sum],
  { simp only [linear_map.map_smul], },
  { intro i, exact (h i).map_zero },
end

variables (α : Type*) [fintype α]
variables (R M) [add_comm_monoid M] [semiring R] [module R M]

/-- Given `fintype α`, `linear_equiv_fun_on_fintype R` is the natural `R`-linear equivalence between
`α →₀ β` and `α → β`. -/
@[simps apply] noncomputable def linear_equiv_fun_on_fintype :
  (α →₀ M) ≃ₗ[R] (α → M) :=
{ to_fun := coe_fn,
  map_add' := λ f g, by { ext, refl },
  map_smul' := λ c f, by { ext, refl },
  .. equiv_fun_on_fintype }

@[simp] lemma linear_equiv_fun_on_fintype_single [decidable_eq α] (x : α) (m : M) :
  (linear_equiv_fun_on_fintype R M α) (single x m) = pi.single x m :=
begin
  ext a,
  change (equiv_fun_on_fintype (single x m)) a = _,
  convert _root_.congr_fun (equiv_fun_on_fintype_single x m) a,
end

@[simp] lemma linear_equiv_fun_on_fintype_symm_single [decidable_eq α]
  (x : α) (m : M) : (linear_equiv_fun_on_fintype R M α).symm (pi.single x m) = single x m :=
begin
  ext a,
  change (equiv_fun_on_fintype.symm (pi.single x m)) a = _,
  convert congr_fun (equiv_fun_on_fintype_symm_single x m) a,
end

@[simp] lemma linear_equiv_fun_on_fintype_symm_coe (f : α →₀ M) :
  (linear_equiv_fun_on_fintype R M α).symm f = f :=
by { ext, simp [linear_equiv_fun_on_fintype], }

end finsupp

section
open_locale classical

/-- decomposing `x : ι → R` as a sum along the canonical basis -/
lemma pi_eq_sum_univ {ι : Type*} [fintype ι] {R : Type*} [semiring R] (x : ι → R) :
  x = ∑ i, x i • (λj, if i = j then 1 else 0) :=
by { ext, simp }

end

/-! ### Properties of linear maps -/
namespace linear_map

section add_comm_monoid
variables [semiring R] [semiring R₂] [semiring R₃] [semiring R₄]
variables [add_comm_monoid M] [add_comm_monoid M₁] [add_comm_monoid M₂]
variables [add_comm_monoid M₃] [add_comm_monoid M₄]
variables [module R M] [module R M₁] [module R₂ M₂] [module R₃ M₃] [module R₄ M₄]
variables {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₃₄ : R₃ →+* R₄}
variables {σ₁₃ : R →+* R₃} {σ₂₄ : R₂ →+* R₄} {σ₁₄ : R →+* R₄}
variables [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃] [ring_hom_comp_triple σ₂₃ σ₃₄ σ₂₄]
variables [ring_hom_comp_triple σ₁₃ σ₃₄ σ₁₄] [ring_hom_comp_triple σ₁₂ σ₂₄ σ₁₄]
variables (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)
include R R₂

theorem comp_assoc (h : M₃ →ₛₗ[σ₃₄] M₄) :
  ((h.comp g : M₂ →ₛₗ[σ₂₄] M₄).comp f : M →ₛₗ[σ₁₄] M₄)
  = h.comp (g.comp f : M →ₛₗ[σ₁₃] M₃) := rfl

omit R R₂

/-- The restriction of a linear map `f : M → M₂` to a submodule `p ⊆ M` gives a linear map
`p → M₂`. -/
def dom_restrict (f : M →ₛₗ[σ₁₂] M₂) (p : submodule R M) : p →ₛₗ[σ₁₂] M₂ := f.comp p.subtype

@[simp] lemma dom_restrict_apply (f : M →ₛₗ[σ₁₂] M₂) (p : submodule R M) (x : p) :
  f.dom_restrict p x = f x := rfl

/-- A linear map `f : M₂ → M` whose values lie in a submodule `p ⊆ M` can be restricted to a
linear map M₂ → p. -/
def cod_restrict (p : submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) (h : ∀c, f c ∈ p) : M →ₛₗ[σ₁₂] p :=
by refine {to_fun := λc, ⟨f c, h c⟩, ..}; intros; apply set_coe.ext; simp

@[simp] theorem cod_restrict_apply (p : submodule R₂ M₂) (f : M →ₛₗ[σ₁₂] M₂) {h} (x : M) :
  (cod_restrict p f h x : M₂) = f x := rfl

@[simp] lemma comp_cod_restrict (p : submodule R₃ M₃) (h : ∀b, g b ∈ p) :
  ((cod_restrict p g h).comp f : M →ₛₗ[σ₁₃] p) = cod_restrict p (g.comp f) (assume b, h _) :=
ext $ assume b, rfl

@[simp] lemma subtype_comp_cod_restrict (p : submodule R₂ M₂) (h : ∀b, f b ∈ p) :
  p.subtype.comp (cod_restrict p f h) = f :=
ext $ assume b, rfl

/-- Restrict domain and codomain of an endomorphism. -/
def restrict (f : M →ₗ[R] M) {p : submodule R M} (hf : ∀ x ∈ p, f x ∈ p) : p →ₗ[R] p :=
(f.dom_restrict p).cod_restrict p $ set_like.forall.2 hf

lemma restrict_apply
  {f : M →ₗ[R] M} {p : submodule R M} (hf : ∀ x ∈ p, f x ∈ p) (x : p) :
  f.restrict hf x = ⟨f x, hf x.1 x.2⟩ := rfl

lemma subtype_comp_restrict {f : M →ₗ[R] M} {p : submodule R M} (hf : ∀ x ∈ p, f x ∈ p) :
  p.subtype.comp (f.restrict hf) = f.dom_restrict p := rfl

lemma restrict_eq_cod_restrict_dom_restrict
  {f : M →ₗ[R] M} {p : submodule R M} (hf : ∀ x ∈ p, f x ∈ p) :
  f.restrict hf = (f.dom_restrict p).cod_restrict p (λ x, hf x.1 x.2) := rfl

lemma restrict_eq_dom_restrict_cod_restrict
  {f : M →ₗ[R] M} {p : submodule R M} (hf : ∀ x, f x ∈ p) :
  f.restrict (λ x _, hf x) = (f.cod_restrict p hf).dom_restrict p := rfl

instance unique_of_left [subsingleton M] : unique (M →ₛₗ[σ₁₂] M₂) :=
{ uniq := λ f, ext $ λ x, by rw [subsingleton.elim x 0, map_zero, map_zero],
  .. linear_map.inhabited }

instance unique_of_right [subsingleton M₂] : unique (M →ₛₗ[σ₁₂] M₂) :=
coe_injective.unique

/-- Evaluation of a `σ₁₂`-linear map at a fixed `a`, as an `add_monoid_hom`. -/
def eval_add_monoid_hom (a : M) : (M →ₛₗ[σ₁₂] M₂) →+ M₂ :=
{ to_fun := λ f, f a,
  map_add' := λ f g, linear_map.add_apply f g a,
  map_zero' := rfl }

/-- `linear_map.to_add_monoid_hom` promoted to an `add_monoid_hom` -/
def to_add_monoid_hom' : (M →ₛₗ[σ₁₂] M₂) →+ (M →+ M₂) :=
{ to_fun := to_add_monoid_hom,
  map_zero' := by ext; refl,
  map_add' := by intros; ext; refl }

lemma sum_apply (t : finset ι) (f : ι → M →ₛₗ[σ₁₂] M₂) (b : M) :
  (∑ d in t, f d) b = ∑ d in t, f d b :=
add_monoid_hom.map_sum ((add_monoid_hom.eval b).comp to_add_monoid_hom') f _

section smul_right

variables [semiring S] [module R S] [module S M] [is_scalar_tower R S M]

/-- When `f` is an `R`-linear map taking values in `S`, then `λb, f b • x` is an `R`-linear map. -/
def smul_right (f : M₁ →ₗ[R] S) (x : M) : M₁ →ₗ[R] M :=
{ to_fun := λb, f b • x,
  map_add' := λ x y, by rw [f.map_add, add_smul],
  map_smul' := λ b y, by dsimp; rw [f.map_smul, smul_assoc] }

@[simp] theorem coe_smul_right (f : M₁ →ₗ[R] S) (x : M) :
  (smul_right f x : M₁ → M) = λ c, f c • x := rfl

theorem smul_right_apply (f : M₁ →ₗ[R] S) (x : M) (c : M₁) :
  smul_right f x c = f c • x := rfl

end smul_right

instance [nontrivial M] : nontrivial (module.End R M) :=
begin
  obtain ⟨m, ne⟩ := (nontrivial_iff_exists_ne (0 : M)).mp infer_instance,
  exact nontrivial_of_ne 1 0 (λ p, ne (linear_map.congr_fun p m)),
end

@[simp, norm_cast] lemma coe_fn_sum {ι : Type*} (t : finset ι) (f : ι → M →ₛₗ[σ₁₂] M₂) :
  ⇑(∑ i in t, f i) = ∑ i in t, (f i : M → M₂) :=
add_monoid_hom.map_sum ⟨@to_fun R R₂ _ _ σ₁₂ M M₂ _ _ _ _, rfl, λ x y, rfl⟩ _ _

@[simp] lemma pow_apply (f : M →ₗ[R] M) (n : ℕ) (m : M) :
  (f^n) m = (f^[n] m) :=
begin
  induction n with n ih,
  { refl, },
  { simp only [function.comp_app, function.iterate_succ, linear_map.mul_apply, pow_succ, ih],
    exact (function.commute.iterate_self _ _ m).symm, },
end

lemma pow_map_zero_of_le
  {f : module.End R M} {m : M} {k l : ℕ} (hk : k ≤ l) (hm : (f^k) m = 0) : (f^l) m = 0 :=
by rw [← tsub_add_cancel_of_le hk, pow_add, mul_apply, hm, map_zero]

lemma commute_pow_left_of_commute
  {f : M →ₛₗ[σ₁₂] M₂} {g : module.End R M} {g₂ : module.End R₂ M₂}
  (h : g₂.comp f = f.comp g) (k : ℕ) : (g₂^k).comp f = f.comp (g^k) :=
begin
  induction k with k ih,
  { simpa only [pow_zero], },
  { rw [pow_succ, pow_succ, linear_map.mul_eq_comp, linear_map.comp_assoc, ih,
      ← linear_map.comp_assoc, h, linear_map.comp_assoc, linear_map.mul_eq_comp], },
end

lemma submodule_pow_eq_zero_of_pow_eq_zero {N : submodule R M}
  {g : module.End R N} {G : module.End R M} (h : G.comp N.subtype = N.subtype.comp g)
  {k : ℕ} (hG : G^k = 0) : g^k = 0 :=
begin
  ext m,
  have hg : N.subtype.comp (g^k) m = 0,
  { rw [← commute_pow_left_of_commute h, hG, zero_comp, zero_apply], },
  simp only [submodule.subtype_apply, comp_app, submodule.coe_eq_zero, coe_comp] at hg,
  rw [hg, linear_map.zero_apply],
end

lemma coe_pow (f : M →ₗ[R] M) (n : ℕ) : ⇑(f^n) = (f^[n]) :=
by { ext m, apply pow_apply, }

@[simp] lemma id_pow (n : ℕ) : (id : M →ₗ[R] M)^n = id := one_pow n

section
variables {f' : M →ₗ[R] M}

lemma iterate_succ (n : ℕ) : (f' ^ (n + 1)) = comp (f' ^ n) f' :=
by rw [pow_succ', mul_eq_comp]

lemma iterate_surjective (h : surjective f') : ∀ n : ℕ, surjective ⇑(f' ^ n)
| 0       := surjective_id
| (n + 1) := by { rw [iterate_succ], exact surjective.comp (iterate_surjective n) h, }

lemma iterate_injective (h : injective f') : ∀ n : ℕ, injective ⇑(f' ^ n)
| 0       := injective_id
| (n + 1) := by { rw [iterate_succ], exact injective.comp (iterate_injective n) h, }

lemma iterate_bijective (h : bijective f') : ∀ n : ℕ, bijective ⇑(f' ^ n)
| 0       := bijective_id
| (n + 1) := by { rw [iterate_succ], exact bijective.comp (iterate_bijective n) h, }

lemma injective_of_iterate_injective {n : ℕ} (hn : n ≠ 0) (h : injective ⇑(f' ^ n)) :
  injective f' :=
begin
  rw [← nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr hn), iterate_succ, coe_comp] at h,
  exact injective.of_comp h,
end

lemma surjective_of_iterate_surjective {n : ℕ} (hn : n ≠ 0) (h : surjective ⇑(f' ^ n)) :
  surjective f' :=
begin
  rw [← nat.succ_pred_eq_of_pos (pos_iff_ne_zero.mpr hn),
    nat.succ_eq_add_one, add_comm, pow_add] at h,
  exact surjective.of_comp h,
end

end

section
open_locale classical

/-- A linear map `f` applied to `x : ι → R` can be computed using the image under `f` of elements
of the canonical basis. -/
lemma pi_apply_eq_sum_univ [fintype ι] (f : (ι → R) →ₗ[R] M) (x : ι → R) :
  f x = ∑ i, x i • (f (λj, if i = j then 1 else 0)) :=
begin
  conv_lhs { rw [pi_eq_sum_univ x, f.map_sum] },
  apply finset.sum_congr rfl (λl hl, _),
  rw f.map_smul
end

end

end add_comm_monoid

section module

variables [semiring R] [semiring S]
  [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
  [module R M] [module R M₂] [module R M₃]
  [module S M₂] [module S M₃] [smul_comm_class R S M₂] [smul_comm_class R S M₃]
  (f : M →ₗ[R] M₂)

variable (S)

/-- Applying a linear map at `v : M`, seen as `S`-linear map from `M →ₗ[R] M₂` to `M₂`.

 See `linear_map.applyₗ` for a version where `S = R`. -/
@[simps]
def applyₗ' : M →+ (M →ₗ[R] M₂) →ₗ[S] M₂ :=
{ to_fun := λ v,
  { to_fun := λ f, f v,
    map_add' := λ f g, f.add_apply g v,
    map_smul' := λ x f, f.smul_apply x v },
  map_zero' := linear_map.ext $ λ f, f.map_zero,
  map_add' := λ x y, linear_map.ext $ λ f, f.map_add _ _ }

section
variables (R M)

/--
The equivalence between R-linear maps from `R` to `M`, and points of `M` itself.
This says that the forgetful functor from `R`-modules to types is representable, by `R`.

This as an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings].
-/
@[simps]
def ring_lmap_equiv_self [module S M] [smul_comm_class R S M] : (R →ₗ[R] M) ≃ₗ[S] M :=
{ to_fun := λ f, f 1,
  inv_fun := smul_right (1 : R →ₗ[R] R),
  left_inv := λ f, by { ext, simp },
  right_inv := λ x, by simp,
  .. applyₗ' S (1 : R) }

end

end module

section comm_semiring

variables [comm_semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [module R M] [module R M₂] [module R M₃]
variables (f g : M →ₗ[R] M₂)
include R

/-- Composition by `f : M₂ → M₃` is a linear map from the space of linear maps `M → M₂`
to the space of linear maps `M₂ → M₃`. -/
def comp_right (f : M₂ →ₗ[R] M₃) : (M →ₗ[R] M₂) →ₗ[R] (M →ₗ[R] M₃) :=
{ to_fun := f.comp,
  map_add' := λ _ _, linear_map.ext $ λ _, f.map_add _ _,
  map_smul' := λ _ _, linear_map.ext $ λ _, f.map_smul _ _ }

@[simp]
lemma comp_right_apply (f : M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂) :
  comp_right f g = f.comp g := rfl

/-- Applying a linear map at `v : M`, seen as a linear map from `M →ₗ[R] M₂` to `M₂`.
See also `linear_map.applyₗ'` for a version that works with two different semirings.

This is the `linear_map` version of `add_monoid_hom.eval`. -/
@[simps]
def applyₗ : M →ₗ[R] (M →ₗ[R] M₂) →ₗ[R] M₂ :=
{ to_fun := λ v, { to_fun := λ f, f v, ..applyₗ' R v },
  map_smul' := λ x y, linear_map.ext $ λ f, f.map_smul _ _,
  ..applyₗ' R }

/-- Alternative version of `dom_restrict` as a linear map. -/
def dom_restrict'
  (p : submodule R M) : (M →ₗ[R] M₂) →ₗ[R] (p →ₗ[R] M₂) :=
{ to_fun := λ φ, φ.dom_restrict p,
  map_add' := by simp [linear_map.ext_iff],
  map_smul' := by simp [linear_map.ext_iff] }

@[simp] lemma dom_restrict'_apply (f : M →ₗ[R] M₂) (p : submodule R M) (x : p) :
  dom_restrict' p f x = f x := rfl

end comm_semiring

section comm_ring
variables [comm_ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R M₂] [module R M₃]

/--
The family of linear maps `M₂ → M` parameterised by `f ∈ M₂ → R`, `x ∈ M`, is linear in `f`, `x`.
-/
def smul_rightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M :=
{ to_fun := λ f,
  { to_fun    := linear_map.smul_right f,
    map_add'  := λ m m', by { ext, apply smul_add, },
    map_smul' := λ c m, by { ext, apply smul_comm, } },
  map_add'  := λ f f', by { ext, apply add_smul, },
  map_smul' := λ c f, by { ext, apply mul_smul, } }

@[simp] lemma smul_rightₗ_apply (f : M₂ →ₗ[R] R) (x : M) (c : M₂) :
  (smul_rightₗ : (M₂ →ₗ[R] R) →ₗ[R] M →ₗ[R] M₂ →ₗ[R] M) f x c = (f c) • x := rfl

end comm_ring

end linear_map

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℕ`-linear morphisms `A →ₗ[ℕ] B`.
-/
@[simps]
def add_monoid_hom_lequiv_nat {A B : Type*} (R : Type*)
  [semiring R] [add_comm_monoid A] [add_comm_monoid B] [module R B] :
  (A →+ B) ≃ₗ[R] (A →ₗ[ℕ] B) :=
{ to_fun := add_monoid_hom.to_nat_linear_map,
  inv_fun := linear_map.to_add_monoid_hom,
  map_add' := by { intros, ext, refl },
  map_smul' := by { intros, ext, refl },
  left_inv := by { intros f, ext, refl },
  right_inv := by { intros f, ext, refl } }

/--
The `R`-linear equivalence between additive morphisms `A →+ B` and `ℤ`-linear morphisms `A →ₗ[ℤ] B`.
-/
@[simps]
def add_monoid_hom_lequiv_int {A B : Type*} (R : Type*)
  [semiring R] [add_comm_group A] [add_comm_group B] [module R B] :
  (A →+ B) ≃ₗ[R] (A →ₗ[ℤ] B) :=
{ to_fun := add_monoid_hom.to_int_linear_map,
  inv_fun := linear_map.to_add_monoid_hom,
  map_add' := by { intros, ext, refl },
  map_smul' := by { intros, ext, refl },
  left_inv := by { intros f, ext, refl },
  right_inv := by { intros f, ext, refl } }

/-! ### Properties of submodules -/

namespace submodule

section add_comm_monoid

variables [semiring R] [semiring R₂] [semiring R₃]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M']
variables [module R M] [module R M'] [module R₂ M₂] [module R₃ M₃]
variables {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variables {σ₂₁ : R₂ →+* R}
variables [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
variables [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]
variables (p p' : submodule R M) (q q' : submodule R₂ M₂)
variables (q₁ q₁' : submodule R M')
variables {r : R} {x y : M}
open set

variables {p p'}

/-- If two submodules `p` and `p'` satisfy `p ⊆ p'`, then `of_le p p'` is the linear map version of
this inclusion. -/
def of_le (h : p ≤ p') : p →ₗ[R] p' :=
p.subtype.cod_restrict p' $ λ ⟨x, hx⟩, h hx

@[simp] theorem coe_of_le (h : p ≤ p') (x : p) :
  (of_le h x : M) = x := rfl

theorem of_le_apply (h : p ≤ p') (x : p) : of_le h x = ⟨x, h x.2⟩ := rfl

theorem of_le_injective (h : p ≤ p') : function.injective (of_le h) :=
λ x y h, subtype.val_injective (subtype.mk.inj h)

variables (p p')

lemma subtype_comp_of_le (p q : submodule R M) (h : p ≤ q) :
  q.subtype.comp (of_le h) = p.subtype :=
by { ext ⟨b, hb⟩, refl }

variables (R)

@[simp] lemma subsingleton_iff : subsingleton (submodule R M) ↔ subsingleton M :=
have h : subsingleton (submodule R M) ↔ subsingleton (add_submonoid M),
{ rw [←subsingleton_iff_bot_eq_top, ←subsingleton_iff_bot_eq_top],
  convert to_add_submonoid_eq.symm; refl, },
h.trans add_submonoid.subsingleton_iff

@[simp] lemma nontrivial_iff : nontrivial (submodule R M) ↔ nontrivial M :=
not_iff_not.mp (
  (not_nontrivial_iff_subsingleton.trans $ subsingleton_iff R).trans
  not_nontrivial_iff_subsingleton.symm)

variables {R}

instance [subsingleton M] : unique (submodule R M) :=
⟨⟨⊥⟩, λ a, @subsingleton.elim _ ((subsingleton_iff R).mpr ‹_›) a _⟩

instance unique' [subsingleton R] : unique (submodule R M) :=
by haveI := module.subsingleton R M; apply_instance

instance [nontrivial M] : nontrivial (submodule R M) := (nontrivial_iff R).mpr ‹_›

theorem mem_right_iff_eq_zero_of_disjoint {p p' : submodule R M} (h : disjoint p p') {x : p} :
  (x:M) ∈ p' ↔ x = 0 :=
⟨λ hx, coe_eq_zero.1 $ disjoint_def.1 h x x.2 hx, λ h, h.symm ▸ p'.zero_mem⟩

theorem mem_left_iff_eq_zero_of_disjoint {p p' : submodule R M} (h : disjoint p p') {x : p'} :
  (x:M) ∈ p ↔ x = 0 :=
⟨λ hx, coe_eq_zero.1 $ disjoint_def.1 h x hx x.2, λ h, h.symm ▸ p.zero_mem⟩

section
variables [ring_hom_surjective σ₁₂]

/-- The pushforward of a submodule `p ⊆ M` by `f : M → M₂` -/
def map (f : M →ₛₗ[σ₁₂] M₂) (p : submodule R M) : submodule R₂ M₂ :=
{ carrier   := f '' p,
  smul_mem' :=
  begin
    rintro c x ⟨y, hy, rfl⟩,
    obtain ⟨a, rfl⟩ := σ₁₂.is_surjective c,
    exact ⟨_, p.smul_mem a hy, f.map_smulₛₗ _ _⟩,
  end,
  .. p.to_add_submonoid.map f.to_add_monoid_hom }

@[simp] lemma map_coe (f : M →ₛₗ[σ₁₂] M₂) (p : submodule R M) :
  (map f p : set M₂) = f '' p := rfl

lemma map_to_add_submonoid (f : M →ₛₗ[σ₁₂] M₂) (p : submodule R M) :
  (p.map f).to_add_submonoid = p.to_add_submonoid.map f :=
set_like.coe_injective rfl

@[simp] lemma mem_map {f : M →ₛₗ[σ₁₂] M₂} {p : submodule R M} {x : M₂} :
  x ∈ map f p ↔ ∃ y, y ∈ p ∧ f y = x := iff.rfl

theorem mem_map_of_mem {f : M →ₛₗ[σ₁₂] M₂} {p : submodule R M} {r} (h : r ∈ p) :
  f r ∈ map f p := set.mem_image_of_mem _ h

lemma apply_coe_mem_map (f : M →ₛₗ[σ₁₂] M₂) {p : submodule R M} (r : p) :
  f r ∈ map f p := mem_map_of_mem r.prop

@[simp] lemma map_id : map (linear_map.id : M →ₗ[R] M) p = p :=
submodule.ext $ λ a, by simp

lemma map_comp [ring_hom_surjective σ₂₃] [ring_hom_surjective σ₁₃]
  (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)
  (p : submodule R M) : map (g.comp f : M →ₛₗ[σ₁₃] M₃) p = map g (map f p) :=
set_like.coe_injective $ by simp [map_coe]; rw ← image_comp

lemma map_mono {f : M →ₛₗ[σ₁₂] M₂} {p p' : submodule R M} :
  p ≤ p' → map f p ≤ map f p' := image_subset _

@[simp] lemma map_zero : map (0 : M →ₛₗ[σ₁₂] M₂) p = ⊥ :=
have ∃ (x : M), x ∈ p := ⟨0, p.zero_mem⟩,
ext $ by simp [this, eq_comm]

lemma map_add_le (f g : M →ₛₗ[σ₁₂] M₂) : map (f + g) p ≤ map f p ⊔ map g p :=
begin
  rintros x ⟨m, hm, rfl⟩,
  exact add_mem_sup (mem_map_of_mem hm) (mem_map_of_mem hm),
end

lemma range_map_nonempty (N : submodule R M) :
  (set.range (λ ϕ, submodule.map ϕ N : (M →ₛₗ[σ₁₂] M₂) → submodule R₂ M₂)).nonempty :=
⟨_, set.mem_range.mpr ⟨0, rfl⟩⟩

end

include σ₂₁
/-- The pushforward of a submodule by an injective linear map is
linearly equivalent to the original submodule. See also `linear_equiv.submodule_map` for a
computable version when `f` has an explicit inverse. -/
noncomputable def equiv_map_of_injective (f : M →ₛₗ[σ₁₂] M₂) (i : injective f)
  (p : submodule R M) : p ≃ₛₗ[σ₁₂] p.map f :=
{ map_add' := by { intros, simp, refl, },
  map_smul' := by { intros, simp, refl, },
  ..(equiv.set.image f p i) }

@[simp] lemma coe_equiv_map_of_injective_apply (f : M →ₛₗ[σ₁₂] M₂) (i : injective f)
  (p : submodule R M) (x : p) :
  (equiv_map_of_injective f i p x : M₂) = f x := rfl
omit σ₂₁

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
def comap (f : M →ₛₗ[σ₁₂] M₂) (p : submodule R₂ M₂) : submodule R M :=
{ carrier   := f ⁻¹' p,
  smul_mem' := λ a x h, by simp [p.smul_mem _ h],
  .. p.to_add_submonoid.comap f.to_add_monoid_hom }

@[simp] lemma comap_coe (f : M →ₛₗ[σ₁₂] M₂) (p : submodule R₂ M₂) :
  (comap f p : set M) = f ⁻¹' p := rfl

@[simp] lemma mem_comap {f : M →ₛₗ[σ₁₂] M₂} {p : submodule R₂ M₂} :
  x ∈ comap f p ↔ f x ∈ p := iff.rfl

@[simp] lemma comap_id : comap linear_map.id p = p :=
set_like.coe_injective rfl

lemma comap_comp (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)
  (p : submodule R₃ M₃) : comap (g.comp f : M →ₛₗ[σ₁₃] M₃) p = comap f (comap g p) :=
rfl

lemma comap_mono {f : M →ₛₗ[σ₁₂] M₂} {q q' : submodule R₂ M₂} :
  q ≤ q' → comap f q ≤ comap f q' := preimage_mono

lemma le_comap_pow_of_le_comap (p : submodule R M) {f : M →ₗ[R] M} (h : p ≤ p.comap f) (k : ℕ) :
  p ≤ p.comap (f^k) :=
begin
  induction k with k ih,
  { simp [linear_map.one_eq_id], },
  { simp [linear_map.iterate_succ, comap_comp, h.trans (comap_mono ih)], },
end

section
variables [ring_hom_surjective σ₁₂]

lemma map_le_iff_le_comap {f : M →ₛₗ[σ₁₂] M₂} {p : submodule R M} {q : submodule R₂ M₂} :
  map f p ≤ q ↔ p ≤ comap f q := image_subset_iff

lemma gc_map_comap (f : M →ₛₗ[σ₁₂] M₂) : galois_connection (map f) (comap f)
| p q := map_le_iff_le_comap

@[simp] lemma map_bot (f : M →ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma map_sup (f : M →ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f p ⊔ map f p' :=
(gc_map_comap f).l_sup

@[simp] lemma map_supr {ι : Sort*} (f : M →ₛₗ[σ₁₂] M₂) (p : ι → submodule R M) :
  map f (⨆i, p i) = (⨆i, map f (p i)) :=
(gc_map_comap f).l_supr

end

@[simp] lemma comap_top (f : M →ₛₗ[σ₁₂] M₂) : comap f ⊤ = ⊤ := rfl

@[simp] lemma comap_inf (f : M →ₛₗ[σ₁₂] M₂) : comap f (q ⊓ q') = comap f q ⊓ comap f q' := rfl

@[simp] lemma comap_infi [ring_hom_surjective σ₁₂] {ι : Sort*} (f : M →ₛₗ[σ₁₂] M₂)
  (p : ι → submodule R₂ M₂) :
  comap f (⨅i, p i) = (⨅i, comap f (p i)) :=
(gc_map_comap f).u_infi

@[simp] lemma comap_zero : comap (0 : M →ₛₗ[σ₁₂] M₂) q = ⊤ :=
ext $ by simp

lemma map_comap_le [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (q : submodule R₂ M₂) :
  map f (comap f q) ≤ q :=
(gc_map_comap f).l_u_le _

lemma le_comap_map [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (p : submodule R M) :
  p ≤ comap f (map f p) :=
(gc_map_comap f).le_u_l _

section galois_insertion
variables {f : M →ₛₗ[σ₁₂] M₂} (hf : surjective f)
variables [ring_hom_surjective σ₁₂]
include hf

/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
def gi_map_comap : galois_insertion (map f) (comap f) :=
(gc_map_comap f).to_galois_insertion
  (λ S x hx, begin
    rcases hf x with ⟨y, rfl⟩,
    simp only [mem_map, mem_comap],
    exact ⟨y, hx, rfl⟩
  end)

lemma map_comap_eq_of_surjective (p : submodule R₂ M₂) : (p.comap f).map f = p :=
(gi_map_comap hf).l_u_eq _

lemma map_surjective_of_surjective : function.surjective (map f) :=
(gi_map_comap hf).l_surjective

lemma comap_injective_of_surjective : function.injective (comap f) :=
(gi_map_comap hf).u_injective

lemma map_sup_comap_of_surjective (p q : submodule R₂ M₂) :
  (p.comap f ⊔ q.comap f).map f = p ⊔ q :=
(gi_map_comap hf).l_sup_u _ _

lemma map_supr_comap_of_sujective {ι : Sort*} (S : ι → submodule R₂ M₂) :
  (⨆ i, (S i).comap f).map f = supr S :=
(gi_map_comap hf).l_supr_u _

lemma map_inf_comap_of_surjective (p q : submodule R₂ M₂) :
  (p.comap f ⊓ q.comap f).map f = p ⊓ q :=
(gi_map_comap hf).l_inf_u _ _

lemma map_infi_comap_of_surjective {ι : Sort*} (S : ι → submodule R₂ M₂) :
  (⨅ i, (S i).comap f).map f = infi S :=
(gi_map_comap hf).l_infi_u _

lemma comap_le_comap_iff_of_surjective (p q : submodule R₂ M₂) :
  p.comap f ≤ q.comap f ↔ p ≤ q :=
(gi_map_comap hf).u_le_u_iff

lemma comap_strict_mono_of_surjective : strict_mono (comap f) :=
(gi_map_comap hf).strict_mono_u

end galois_insertion

section galois_coinsertion
variables [ring_hom_surjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂} (hf : injective f)
include hf

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
def gci_map_comap : galois_coinsertion (map f) (comap f) :=
(gc_map_comap f).to_galois_coinsertion
  (λ S x, by simp [mem_comap, mem_map, hf.eq_iff])

lemma comap_map_eq_of_injective (p : submodule R M) : (p.map f).comap f = p :=
(gci_map_comap hf).u_l_eq _

lemma comap_surjective_of_injective : function.surjective (comap f) :=
(gci_map_comap hf).u_surjective

lemma map_injective_of_injective : function.injective (map f) :=
(gci_map_comap hf).l_injective

lemma comap_inf_map_of_injective (p q : submodule R M) : (p.map f ⊓ q.map f).comap f = p ⊓ q :=
(gci_map_comap hf).u_inf_l _ _

lemma comap_infi_map_of_injective {ι : Sort*} (S : ι → submodule R M) :
  (⨅ i, (S i).map f).comap f = infi S :=
(gci_map_comap hf).u_infi_l _

lemma comap_sup_map_of_injective (p q : submodule R M) : (p.map f ⊔ q.map f).comap f = p ⊔ q :=
(gci_map_comap hf).u_sup_l _ _

lemma comap_supr_map_of_injective {ι : Sort*} (S : ι → submodule R M) :
  (⨆ i, (S i).map f).comap f = supr S :=
(gci_map_comap hf).u_supr_l _

lemma map_le_map_iff_of_injective (p q : submodule R M) : p.map f ≤ q.map f ↔ p ≤ q :=
(gci_map_comap hf).l_le_l_iff

lemma map_strict_mono_of_injective : strict_mono (map f) :=
(gci_map_comap hf).strict_mono_l

end galois_coinsertion

--TODO(Mario): is there a way to prove this from order properties?
lemma map_inf_eq_map_inf_comap [ring_hom_surjective σ₁₂] {f : M →ₛₗ[σ₁₂] M₂}
  {p : submodule R M} {p' : submodule R₂ M₂} :
  map f p ⊓ p' = map f (p ⊓ comap f p') :=
le_antisymm
  (by rintro _ ⟨⟨x, h₁, rfl⟩, h₂⟩; exact ⟨_, ⟨h₁, h₂⟩, rfl⟩)
  (le_inf (map_mono inf_le_left) (map_le_iff_le_comap.2 inf_le_right))

lemma map_comap_subtype : map p.subtype (comap p.subtype p') = p ⊓ p' :=
ext $ λ x, ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩, ⟨⟨_, h₁⟩, h₂, rfl⟩⟩

lemma eq_zero_of_bot_submodule : ∀(b : (⊥ : submodule R M)), b = 0
| ⟨b', hb⟩ := subtype.eq $ show b' = 0, from (mem_bot R).1 hb

/-- The infimum of a family of invariant submodule of an endomorphism is also an invariant
submodule. -/
lemma _root_.linear_map.infi_invariant {σ : R →+* R} [ring_hom_surjective σ] {ι : Sort*}
  (f : M →ₛₗ[σ] M) {p : ι → submodule R M} (hf : ∀ i, ∀ v ∈ (p i), f v ∈ p i) :
  ∀ v ∈ infi p, f v ∈ infi p :=
begin
  have : ∀ i, (p i).map f ≤ p i,
  { rintros i - ⟨v, hv, rfl⟩,
    exact hf i v hv },
  suffices : (infi p).map f ≤ infi p,
  { exact λ v hv, this ⟨v, hv, rfl⟩, },
  exact le_infi (λ i, (submodule.map_mono (infi_le p i)).trans (this i)),
end

end add_comm_monoid

section add_comm_group

variables [ring R] [add_comm_group M] [module R M] (p : submodule R M)
variables [add_comm_group M₂] [module R M₂]

@[simp] lemma neg_coe : -(p : set M) = p := set.ext $ λ x, p.neg_mem_iff

@[simp] protected lemma map_neg (f : M →ₗ[R] M₂) : map (-f) p = map f p :=
ext $ λ y, ⟨λ ⟨x, hx, hy⟩, hy ▸ ⟨-x, show -x ∈ p, from neg_mem hx, map_neg f x⟩,
  λ ⟨x, hx, hy⟩, hy ▸ ⟨-x, show -x ∈ p, from neg_mem hx, (map_neg (-f) _).trans (neg_neg (f x))⟩⟩

end add_comm_group

end submodule

namespace submodule
variables [field K]
variables [add_comm_group V] [module K V]
variables [add_comm_group V₂] [module K V₂]

lemma comap_smul (f : V →ₗ[K] V₂) (p : submodule K V₂) (a : K) (h : a ≠ 0) :
  p.comap (a • f) = p.comap f :=
by ext b; simp only [submodule.mem_comap, p.smul_mem_iff h, linear_map.smul_apply]

lemma map_smul (f : V →ₗ[K] V₂) (p : submodule K V) (a : K) (h : a ≠ 0) :
  p.map (a • f) = p.map f :=
le_antisymm
  begin rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap], exact le_rfl end
  begin rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap], exact le_rfl end

lemma comap_smul' (f : V →ₗ[K] V₂) (p : submodule K V₂) (a : K) :
  p.comap (a • f) = (⨅ h : a ≠ 0, p.comap f) :=
by classical; by_cases a = 0; simp [h, comap_smul]

lemma map_smul' (f : V →ₗ[K] V₂) (p : submodule K V) (a : K) :
  p.map (a • f) = (⨆ h : a ≠ 0, p.map f) :=
by classical; by_cases a = 0; simp [h, map_smul]

end submodule

/-! ### Properties of linear maps -/
namespace linear_map

section add_comm_monoid

variables [semiring R] [semiring R₂] [semiring R₃]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variables [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]
variables [module R M] [module R₂ M₂] [module R₃ M₃]
include R
open submodule

section finsupp
variables {γ : Type*} [has_zero γ]

@[simp] lemma map_finsupp_sum (f : M →ₛₗ[σ₁₂] M₂) {t : ι →₀ γ} {g : ι → γ → M} :
  f (t.sum g) = t.sum (λ i d, f (g i d)) := f.map_sum

lemma coe_finsupp_sum (t : ι →₀ γ) (g : ι → γ → M →ₛₗ[σ₁₂] M₂) :
  ⇑(t.sum g) = t.sum (λ i d, g i d) := coe_fn_sum _ _

@[simp] lemma finsupp_sum_apply (t : ι →₀ γ) (g : ι → γ → M →ₛₗ[σ₁₂] M₂) (b : M) :
  (t.sum g) b = t.sum (λ i d, g i d b) := sum_apply _ _ _

end finsupp

section dfinsupp
open dfinsupp
variables {γ : ι → Type*} [decidable_eq ι]

section sum

variables [Π i, has_zero (γ i)] [Π i (x : γ i), decidable (x ≠ 0)]

@[simp] lemma map_dfinsupp_sum (f : M →ₛₗ[σ₁₂] M₂) {t : Π₀ i, γ i} {g : Π i, γ i → M} :
  f (t.sum g) = t.sum (λ i d, f (g i d)) := f.map_sum

lemma coe_dfinsupp_sum (t : Π₀ i, γ i) (g : Π i, γ i → M →ₛₗ[σ₁₂] M₂) :
  ⇑(t.sum g) = t.sum (λ i d, g i d) := coe_fn_sum _ _

@[simp] lemma dfinsupp_sum_apply (t : Π₀ i, γ i) (g : Π i, γ i → M →ₛₗ[σ₁₂] M₂) (b : M) :
  (t.sum g) b = t.sum (λ i d, g i d b) := sum_apply _ _ _

end sum

section sum_add_hom

variables [Π i, add_zero_class (γ i)]

@[simp] lemma map_dfinsupp_sum_add_hom (f : M →ₛₗ[σ₁₂] M₂) {t : Π₀ i, γ i} {g : Π i, γ i →+ M} :
  f (sum_add_hom g t) = sum_add_hom (λ i, f.to_add_monoid_hom.comp (g i)) t :=
f.to_add_monoid_hom.map_dfinsupp_sum_add_hom _ _

end sum_add_hom

end dfinsupp

variables {σ₂₁ : R₂ →+* R} {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variables [ring_hom_comp_triple τ₁₂ τ₂₃ τ₁₃]

theorem map_cod_restrict [ring_hom_surjective σ₂₁] (p : submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (h p') :
  submodule.map (cod_restrict p f h) p' = comap p.subtype (p'.map f) :=
submodule.ext $ λ ⟨x, hx⟩, by simp [subtype.ext_iff_val]

theorem comap_cod_restrict (p : submodule R M) (f : M₂ →ₛₗ[σ₂₁] M) (hf p') :
  submodule.comap (cod_restrict p f hf) p' = submodule.comap f (map p.subtype p') :=
submodule.ext $ λ x, ⟨λ h, ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩

section

/-- The range of a linear map `f : M → M₂` is a submodule of `M₂`.
See Note [range copy pattern]. -/
def range [ring_hom_surjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : submodule R₂ M₂ :=
(map f ⊤).copy (set.range f) set.image_univ.symm

theorem range_coe [ring_hom_surjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
  (range f : set M₂) = set.range f := rfl

lemma range_to_add_submonoid [ring_hom_surjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
  f.range.to_add_submonoid = f.to_add_monoid_hom.mrange := rfl

@[simp] theorem mem_range [ring_hom_surjective τ₁₂]
  {f : M →ₛₗ[τ₁₂] M₂} {x} : x ∈ range f ↔ ∃ y, f y = x :=
iff.rfl

lemma range_eq_map [ring_hom_surjective τ₁₂]
  (f : M →ₛₗ[τ₁₂] M₂) : f.range = map f ⊤ :=
by { ext, simp }

theorem mem_range_self [ring_hom_surjective τ₁₂]
  (f : M →ₛₗ[τ₁₂] M₂) (x : M) : f x ∈ f.range := ⟨x, rfl⟩

@[simp] theorem range_id : range (linear_map.id : M →ₗ[R] M) = ⊤ :=
set_like.coe_injective set.range_id

theorem range_comp [ring_hom_surjective τ₁₂] [ring_hom_surjective τ₂₃] [ring_hom_surjective τ₁₃]
  (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
  range (g.comp f : M →ₛₗ[τ₁₃] M₃) = map g (range f) :=
set_like.coe_injective (set.range_comp g f)

theorem range_comp_le_range [ring_hom_surjective τ₂₃] [ring_hom_surjective τ₁₃]
  (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
  range (g.comp f : M →ₛₗ[τ₁₃] M₃) ≤ range g :=
set_like.coe_mono (set.range_comp_subset_range f g)

theorem range_eq_top [ring_hom_surjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} :
  range f = ⊤ ↔ surjective f :=
by rw [set_like.ext'_iff, range_coe, top_coe, set.range_iff_surjective]

lemma range_le_iff_comap [ring_hom_surjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : submodule R₂ M₂} :
  range f ≤ p ↔ comap f p = ⊤ :=
by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

lemma map_le_range [ring_hom_surjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : submodule R M} :
  map f p ≤ range f :=
set_like.coe_mono (set.image_subset_range f p)

@[simp] lemma range_neg {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*}
  [semiring R] [ring R₂] [add_comm_monoid M] [add_comm_group M₂] [module R M] [module R₂ M₂]
  {τ₁₂ : R →+* R₂} [ring_hom_surjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
  (-f).range = f.range :=
begin
  change ((-linear_map.id : M₂ →ₗ[R₂] M₂).comp f).range = _,
  rw [range_comp, submodule.map_neg, submodule.map_id],
end

end

/--
The decreasing sequence of submodules consisting of the ranges of the iterates of a linear map.
-/
@[simps]
def iterate_range (f : M →ₗ[R] M) : ℕ →o (submodule R M)ᵒᵈ :=
⟨λ n, (f ^ n).range, λ n m w x h, begin
  obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w,
  rw linear_map.mem_range at h,
  obtain ⟨m, rfl⟩ := h,
  rw linear_map.mem_range,
  use (f ^ c) m,
  rw [pow_add, linear_map.mul_apply],
end⟩

/-- Restrict the codomain of a linear map `f` to `f.range`.

This is the bundled version of `set.range_factorization`. -/
@[reducible] def range_restrict [ring_hom_surjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
  M →ₛₗ[τ₁₂] f.range := f.cod_restrict f.range f.mem_range_self

/-- The range of a linear map is finite if the domain is finite.
Note: this instance can form a diamond with `subtype.fintype` in the
  presence of `fintype M₂`. -/
instance fintype_range [fintype M] [decidable_eq M₂] [ring_hom_surjective τ₁₂]
  (f : M →ₛₗ[τ₁₂] M₂) : fintype (range f) :=
set.fintype_range f

/-- The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
def ker (f : M →ₛₗ[τ₁₂] M₂) : submodule R M := comap f ⊥

@[simp] theorem mem_ker {f : M →ₛₗ[τ₁₂] M₂} {y} : y ∈ ker f ↔ f y = 0 := mem_bot R₂

@[simp] theorem ker_id : ker (linear_map.id : M →ₗ[R] M) = ⊥ := rfl

@[simp] theorem map_coe_ker (f : M →ₛₗ[τ₁₂] M₂) (x : ker f) : f x = 0 := mem_ker.1 x.2

lemma ker_to_add_submonoid (f : M →ₛₗ[τ₁₂] M₂) :
  f.ker.to_add_submonoid = f.to_add_monoid_hom.mker := rfl

lemma comp_ker_subtype (f : M →ₛₗ[τ₁₂] M₂) : f.comp f.ker.subtype = 0 :=
linear_map.ext $ λ x, suffices f x = 0, by simp [this], mem_ker.1 x.2

theorem ker_comp (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
  ker (g.comp f : M →ₛₗ[τ₁₃] M₃) = comap f (ker g) := rfl

theorem ker_le_ker_comp (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
  ker f ≤ ker (g.comp f : M →ₛₗ[τ₁₃] M₃) :=
by rw ker_comp; exact comap_mono bot_le

theorem disjoint_ker {f : M →ₛₗ[τ₁₂] M₂} {p : submodule R M} :
  disjoint p (ker f) ↔ ∀ x ∈ p, f x = 0 → x = 0 :=
by simp [disjoint_def]

theorem ker_eq_bot' {f : M →ₛₗ[τ₁₂] M₂} :
  ker f = ⊥ ↔ (∀ m, f m = 0 → m = 0) :=
by simpa [disjoint] using @disjoint_ker _ _ _ _ _ _ _ _ _ _ _ f ⊤

theorem ker_eq_bot_of_inverse {τ₂₁ : R₂ →+* R} [ring_hom_inv_pair τ₁₂ τ₂₁]
  {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₁] M} (h : (g.comp f : M →ₗ[R] M) = id) :
  ker f = ⊥ :=
ker_eq_bot'.2 $ λ m hm, by rw [← id_apply m, ← h, comp_apply, hm, g.map_zero]

lemma le_ker_iff_map [ring_hom_surjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : submodule R M} :
  p ≤ ker f ↔ map f p = ⊥ :=
by rw [ker, eq_bot_iff, map_le_iff_le_comap]

lemma ker_cod_restrict {τ₂₁ : R₂ →+* R} (p : submodule R M) (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
  ker (cod_restrict p f hf) = ker f :=
by rw [ker, comap_cod_restrict, map_bot]; refl

lemma range_cod_restrict {τ₂₁ : R₂ →+* R} [ring_hom_surjective τ₂₁] (p : submodule R M)
  (f : M₂ →ₛₗ[τ₂₁] M) (hf) :
  range (cod_restrict p f hf) = comap p.subtype f.range :=
by simpa only [range_eq_map] using map_cod_restrict _ _ _ _

lemma ker_restrict {p : submodule R M} {f : M →ₗ[R] M} (hf : ∀ x : M, x ∈ p → f x ∈ p) :
  ker (f.restrict hf) = (f.dom_restrict p).ker :=
by rw [restrict_eq_cod_restrict_dom_restrict, ker_cod_restrict]

lemma _root_.submodule.map_comap_eq [ring_hom_surjective τ₁₂]
  (f : M →ₛₗ[τ₁₂] M₂) (q : submodule R₂ M₂) : map f (comap f q) = range f ⊓ q :=
le_antisymm (le_inf map_le_range (map_comap_le _ _)) $
by rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩

lemma _root_.submodule.map_comap_eq_self [ring_hom_surjective τ₁₂]
  {f : M →ₛₗ[τ₁₂] M₂} {q : submodule R₂ M₂} (h : q ≤ range f) : map f (comap f q) = q :=
by rwa [submodule.map_comap_eq, inf_eq_right]

@[simp] theorem ker_zero : ker (0 : M →ₛₗ[τ₁₂] M₂) = ⊤ :=
eq_top_iff'.2 $ λ x, by simp

@[simp] theorem range_zero [ring_hom_surjective τ₁₂] : range (0 : M →ₛₗ[τ₁₂] M₂) = ⊥ :=
by simpa only [range_eq_map] using submodule.map_zero _

theorem ker_eq_top {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 0 :=
⟨λ h, ext $ λ x, mem_ker.1 $ h.symm ▸ trivial, λ h, h.symm ▸ ker_zero⟩

section
variables [ring_hom_surjective τ₁₂]

lemma range_le_bot_iff (f : M →ₛₗ[τ₁₂] M₂) : range f ≤ ⊥ ↔ f = 0 :=
by rw [range_le_iff_comap]; exact ker_eq_top

theorem range_eq_bot {f : M →ₛₗ[τ₁₂] M₂} : range f = ⊥ ↔ f = 0 :=
by rw [← range_le_bot_iff, le_bot_iff]

lemma range_le_ker_iff {f : M →ₛₗ[τ₁₂] M₂} {g : M₂ →ₛₗ[τ₂₃] M₃} :
  range f ≤ ker g ↔ (g.comp f : M →ₛₗ[τ₁₃] M₃) = 0 :=
⟨λ h, ker_eq_top.1 $ eq_top_iff'.2 $ λ x, h $ ⟨_, rfl⟩,
 λ h x hx, mem_ker.2 $ exists.elim hx $ λ y hy, by rw [←hy, ←comp_apply, h, zero_apply]⟩

theorem comap_le_comap_iff {f : M →ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p p'} :
  comap f p ≤ comap f p' ↔ p ≤ p' :=
⟨λ H x hx, by rcases range_eq_top.1 hf x with ⟨y, hy, rfl⟩; exact H hx, comap_mono⟩

theorem comap_injective {f : M →ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) : injective (comap f) :=
λ p p' h, le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h))
  ((comap_le_comap_iff hf).1 (ge_of_eq h))

end

theorem ker_eq_bot_of_injective {f : M →ₛₗ[τ₁₂] M₂} (hf : injective f) : ker f = ⊥ :=
begin
  have : disjoint ⊤ f.ker, by { rw [disjoint_ker, ← map_zero f], exact λ x hx H, hf H },
  simpa [disjoint]
end

/--
The increasing sequence of submodules consisting of the kernels of the iterates of a linear map.
-/
@[simps]
def iterate_ker (f : M →ₗ[R] M) : ℕ →o submodule R M :=
⟨λ n, (f ^ n).ker, λ n m w x h, begin
  obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w,
  rw linear_map.mem_ker at h,
  rw [linear_map.mem_ker, add_comm, pow_add, linear_map.mul_apply, h, linear_map.map_zero],
end⟩

end add_comm_monoid

section ring

variables [ring R] [ring R₂] [ring R₃]
variables [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R₂ M₂] [module R₃ M₃]
variables {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variables [ring_hom_comp_triple τ₁₂ τ₂₃ τ₁₃]
variables {f : M →ₛₗ[τ₁₂] M₂}
include R
open submodule

lemma range_to_add_subgroup [ring_hom_surjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) :
  f.range.to_add_subgroup = f.to_add_monoid_hom.range := rfl

lemma ker_to_add_subgroup (f : M →ₛₗ[τ₁₂] M₂) :
  f.ker.to_add_subgroup = f.to_add_monoid_hom.ker := rfl

theorem sub_mem_ker_iff {x y} : x - y ∈ f.ker ↔ f x = f y :=
by rw [mem_ker, map_sub, sub_eq_zero]

theorem disjoint_ker' {p : submodule R M} :
  disjoint p (ker f) ↔ ∀ x y ∈ p, f x = f y → x = y :=
disjoint_ker.trans
⟨λ H x hx y hy h, eq_of_sub_eq_zero $ H _ (sub_mem hx hy) (by simp [h]),
 λ H x h₁ h₂, H x h₁ 0 (zero_mem _) (by simpa using h₂)⟩

theorem inj_of_disjoint_ker {p : submodule R M}
  {s : set M} (h : s ⊆ p) (hd : disjoint p (ker f)) :
  ∀ x y ∈ s, f x = f y → x = y :=
λ x hx y hy, disjoint_ker'.1 hd _ (h hx) _ (h hy)

theorem ker_eq_bot : ker f = ⊥ ↔ injective f :=
by simpa [disjoint] using @disjoint_ker' _ _ _ _ _ _ _ _ _ _ _ f ⊤

lemma ker_le_iff [ring_hom_surjective τ₁₂] {p : submodule R M} :
  ker f ≤ p ↔ ∃ (y ∈ range f), f ⁻¹' {y} ⊆ p :=
begin
  split,
  { intros h, use 0, rw [← set_like.mem_coe, f.range_coe], exact ⟨⟨0, map_zero f⟩, h⟩, },
  { rintros ⟨y, h₁, h₂⟩,
    rw set_like.le_def, intros z hz, simp only [mem_ker, set_like.mem_coe] at hz,
    rw [← set_like.mem_coe, f.range_coe, set.mem_range] at h₁, obtain ⟨x, hx⟩ := h₁,
    have hx' : x ∈ p, { exact h₂ hx, },
    have hxz : z + x ∈ p, { apply h₂, simp [hx, hz], },
    suffices : z + x - x ∈ p, { simpa only [this, add_sub_cancel], },
    exact p.sub_mem hxz hx', },
end

end ring

section field

variables [field K] [field K₂]
variables [add_comm_group V] [module K V]
variables [add_comm_group V₂] [module K V₂]

lemma ker_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : ker (a • f) = ker f :=
submodule.comap_smul f _ a h

lemma ker_smul' (f : V →ₗ[K] V₂) (a : K) : ker (a • f) = ⨅(h : a ≠ 0), ker f :=
submodule.comap_smul' f _ a

lemma range_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : range (a • f) = range f :=
by simpa only [range_eq_map] using submodule.map_smul f _ a h

lemma range_smul' (f : V →ₗ[K] V₂) (a : K) : range (a • f) = ⨆(h : a ≠ 0), range f :=
by simpa only [range_eq_map] using submodule.map_smul' f _ a

end field

end linear_map


namespace is_linear_map

lemma is_linear_map_add [semiring R] [add_comm_monoid M] [module R M] :
  is_linear_map R (λ (x : M × M), x.1 + x.2) :=
begin
  apply is_linear_map.mk,
  { intros x y,
    simp, cc },
  { intros x y,
    simp [smul_add] }
end

lemma is_linear_map_sub {R M : Type*} [semiring R] [add_comm_group M] [module R M]:
  is_linear_map R (λ (x : M × M), x.1 - x.2) :=
begin
  apply is_linear_map.mk,
  { intros x y,
    simp [add_comm, add_left_comm, sub_eq_add_neg] },
  { intros x y,
    simp [smul_sub] }
end

end is_linear_map

namespace submodule

section add_comm_monoid

variables [semiring R] [semiring R₂] [add_comm_monoid M] [add_comm_monoid M₂]
variables [module R M] [module R₂ M₂]
variables (p p' : submodule R M) (q : submodule R₂ M₂)
variables {τ₁₂ : R →+* R₂}
open linear_map

@[simp] theorem map_top [ring_hom_surjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : map f ⊤ = range f :=
f.range_eq_map.symm

@[simp] theorem comap_bot (f : M →ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f := rfl

@[simp] theorem ker_subtype : p.subtype.ker = ⊥ :=
ker_eq_bot_of_injective $ λ x y, subtype.ext_val

@[simp] theorem range_subtype : p.subtype.range = p :=
by simpa using map_comap_subtype p ⊤

lemma map_subtype_le (p' : submodule R p) : map p.subtype p' ≤ p :=
by simpa using (map_le_range : map p.subtype p' ≤ p.subtype.range)

/-- Under the canonical linear map from a submodule `p` to the ambient space `M`, the image of the
maximal submodule of `p` is just `p `. -/
@[simp] lemma map_subtype_top : map p.subtype (⊤ : submodule R p) = p :=
by simp

@[simp] lemma comap_subtype_eq_top {p p' : submodule R M} :
  comap p.subtype p' = ⊤ ↔ p ≤ p' :=
eq_top_iff.trans $ map_le_iff_le_comap.symm.trans $ by rw [map_subtype_top]

@[simp] lemma comap_subtype_self : comap p.subtype p = ⊤ :=
comap_subtype_eq_top.2 le_rfl

@[simp] theorem ker_of_le (p p' : submodule R M) (h : p ≤ p') : (of_le h).ker = ⊥ :=
by rw [of_le, ker_cod_restrict, ker_subtype]

lemma range_of_le (p q : submodule R M) (h : p ≤ q) : (of_le h).range = comap q.subtype p :=
by rw [← map_top, of_le, linear_map.map_cod_restrict, map_top, range_subtype]

@[simp] lemma map_subtype_range_of_le {p p' : submodule R M} (h : p ≤ p') :
  map p'.subtype (of_le h).range = p :=
by simp [range_of_le, map_comap_eq, h]

lemma disjoint_iff_comap_eq_bot {p q : submodule R M} :
  disjoint p q ↔ comap p.subtype q = ⊥ :=
by rw [←(map_injective_of_injective (show injective p.subtype, from subtype.coe_injective)).eq_iff,
       map_comap_subtype, map_bot, disjoint_iff]

/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N` -/
def map_subtype.rel_iso : submodule R p ≃o {p' : submodule R M // p' ≤ p} :=
{ to_fun    := λ p', ⟨map p.subtype p', map_subtype_le p _⟩,
  inv_fun   := λ q, comap p.subtype q,
  left_inv  := λ p', comap_map_eq_of_injective subtype.coe_injective p',
  right_inv := λ ⟨q, hq⟩, subtype.ext_val $ by simp [map_comap_subtype p, inf_of_le_right hq],
  map_rel_iff'      := λ p₁ p₂, subtype.coe_le_coe.symm.trans begin
    dsimp,
    rw [map_le_iff_le_comap,
        comap_map_eq_of_injective (show injective p.subtype, from subtype.coe_injective) p₂],
  end }

/-- If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the ordering of
submodules of `M`. -/
def map_subtype.order_embedding : submodule R p ↪o submodule R M :=
(rel_iso.to_rel_embedding $ map_subtype.rel_iso p).trans (subtype.rel_embedding _ _)

@[simp] lemma map_subtype_embedding_eq (p' : submodule R p) :
  map_subtype.order_embedding p p' = map p.subtype p' := rfl

end add_comm_monoid

end submodule

namespace linear_map

section semiring

variables [semiring R] [semiring R₂] [semiring R₃]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [module R M] [module R₂ M₂] [module R₃ M₃]
variables {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variables [ring_hom_comp_triple τ₁₂ τ₂₃ τ₁₃]

/-- A monomorphism is injective. -/
lemma ker_eq_bot_of_cancel {f : M →ₛₗ[τ₁₂] M₂}
  (h : ∀ (u v : f.ker →ₗ[R] M), f.comp u = f.comp v → u = v) : f.ker = ⊥ :=
begin
  have h₁ : f.comp (0 : f.ker →ₗ[R] M) = 0 := comp_zero _,
  rw [←submodule.range_subtype f.ker, ←h 0 f.ker.subtype (eq.trans h₁ (comp_ker_subtype f).symm)],
  exact range_zero
end

lemma range_comp_of_range_eq_top [ring_hom_surjective τ₁₂] [ring_hom_surjective τ₂₃]
  [ring_hom_surjective τ₁₃]
  {f : M →ₛₗ[τ₁₂] M₂} (g : M₂ →ₛₗ[τ₂₃] M₃) (hf : range f = ⊤) :
  range (g.comp f : M →ₛₗ[τ₁₃] M₃) = range g :=
by rw [range_comp, hf, submodule.map_top]

lemma ker_comp_of_ker_eq_bot (f : M →ₛₗ[τ₁₂] M₂) {g : M₂ →ₛₗ[τ₂₃] M₃}
  (hg : ker g = ⊥) : ker (g.comp f : M →ₛₗ[τ₁₃] M₃) = ker f :=
by rw [ker_comp, hg, submodule.comap_bot]

section image

/-- If `O` is a submodule of `M`, and `Φ : O →ₗ M'` is a linear map,
then `(ϕ : O →ₗ M').submodule_image N` is `ϕ(N)` as a submodule of `M'` -/
def submodule_image {M' : Type*} [add_comm_monoid M'] [module R M']
  {O : submodule R M} (ϕ : O →ₗ[R] M') (N : submodule R M) : submodule R M' :=
(N.comap O.subtype).map ϕ

@[simp] lemma mem_submodule_image {M' : Type*} [add_comm_monoid M'] [module R M']
  {O : submodule R M} {ϕ : O →ₗ[R] M'} {N : submodule R M} {x : M'} :
  x ∈ ϕ.submodule_image N ↔ ∃ y (yO : y ∈ O) (yN : y ∈ N), ϕ ⟨y, yO⟩ = x :=
begin
  refine submodule.mem_map.trans ⟨_, _⟩; simp_rw submodule.mem_comap,
  { rintro ⟨⟨y, yO⟩, (yN : y ∈ N), h⟩,
    exact ⟨y, yO, yN, h⟩ },
  { rintro ⟨y, yO, yN, h⟩,
    exact ⟨⟨y, yO⟩, yN, h⟩ }
end

lemma mem_submodule_image_of_le {M' : Type*} [add_comm_monoid M'] [module R M']
  {O : submodule R M} {ϕ : O →ₗ[R] M'} {N : submodule R M} (hNO : N ≤ O) {x : M'} :
  x ∈ ϕ.submodule_image N ↔ ∃ y (yN : y ∈ N), ϕ ⟨y, hNO yN⟩ = x :=
begin
  refine mem_submodule_image.trans ⟨_, _⟩,
  { rintro ⟨y, yO, yN, h⟩,
    exact ⟨y, yN, h⟩ },
  { rintro ⟨y, yN, h⟩,
    exact ⟨y, hNO yN, yN, h⟩ }
end

lemma submodule_image_apply_of_le {M' : Type*} [add_comm_group M'] [module R M']
  {O : submodule R M} (ϕ : O →ₗ[R] M') (N : submodule R M) (hNO : N ≤ O) :
  ϕ.submodule_image N = (ϕ.comp (submodule.of_le hNO)).range :=
by rw [submodule_image, range_comp, submodule.range_of_le]

end image

end semiring

end linear_map

@[simp] lemma linear_map.range_range_restrict [semiring R] [add_comm_monoid M] [add_comm_monoid M₂]
  [module R M] [module R M₂] (f : M →ₗ[R] M₂) :
  f.range_restrict.range = ⊤ :=
by simp [f.range_cod_restrict _]

/-! ### Linear equivalences -/
namespace linear_equiv

section add_comm_monoid

section subsingleton
variables [semiring R] [semiring R₂] [semiring R₃] [semiring R₄]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄]
variables [module R M] [module R₂ M₂]
variables [subsingleton M] [subsingleton M₂]
variables {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variables [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]

include σ₂₁
/-- Between two zero modules, the zero map is an equivalence. -/
instance : has_zero (M ≃ₛₗ[σ₁₂] M₂) :=
⟨{ to_fun := 0,
   inv_fun := 0,
   right_inv := λ x, subsingleton.elim _ _,
   left_inv := λ x, subsingleton.elim _ _,
   ..(0 : M →ₛₗ[σ₁₂] M₂)}⟩
omit σ₂₁

-- Even though these are implied by `subsingleton.elim` via the `unique` instance below, they're
-- nice to have as `rfl`-lemmas for `dsimp`.
include σ₂₁
@[simp] lemma zero_symm : (0 : M ≃ₛₗ[σ₁₂] M₂).symm = 0 := rfl
@[simp] lemma coe_zero : ⇑(0 : M ≃ₛₗ[σ₁₂] M₂) = 0 := rfl
lemma zero_apply (x : M) : (0 : M ≃ₛₗ[σ₁₂] M₂) x = 0 := rfl

/-- Between two zero modules, the zero map is the only equivalence. -/
instance : unique (M ≃ₛₗ[σ₁₂] M₂) :=
{ uniq := λ f, to_linear_map_injective (subsingleton.elim _ _),
  default := 0 }
omit σ₂₁

end subsingleton

section
variables [semiring R] [semiring R₂] [semiring R₃] [semiring R₄]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄]
variables {module_M : module R M} {module_M₂ : module R₂ M₂}
variables {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variables {re₁₂ : ring_hom_inv_pair σ₁₂ σ₂₁} {re₂₁ : ring_hom_inv_pair σ₂₁ σ₁₂}
variables (e e' : M ≃ₛₗ[σ₁₂] M₂)

lemma map_eq_comap {p : submodule R M} :
  (p.map (e : M →ₛₗ[σ₁₂] M₂) : submodule R₂ M₂) = p.comap (e.symm : M₂ →ₛₗ[σ₂₁] M) :=
set_like.coe_injective $ by simp [e.image_eq_preimage]

/-- A linear equivalence of two modules restricts to a linear equivalence from any submodule
`p` of the domain onto the image of that submodule.

This is the linear version of `add_equiv.submonoid_map` and `add_equiv.subgroup_map`.

This is `linear_equiv.of_submodule'` but with `map` on the right instead of `comap` on the left. -/
def submodule_map (p : submodule R M) :
  p ≃ₛₗ[σ₁₂] ↥(p.map (e : M →ₛₗ[σ₁₂] M₂) : submodule R₂ M₂) :=
{ inv_fun   := λ y, ⟨(e.symm : M₂ →ₛₗ[σ₂₁] M) y, by
  { rcases y with ⟨y', hy⟩, rw submodule.mem_map at hy, rcases hy with ⟨x, hx, hxy⟩, subst hxy,
    simp only [symm_apply_apply, submodule.coe_mk, coe_coe, hx], }⟩,
  left_inv  := λ x, by simp only [linear_map.dom_restrict_apply, linear_map.cod_restrict_apply,
    linear_map.to_fun_eq_coe, linear_equiv.coe_coe, linear_equiv.symm_apply_apply, set_like.eta],
  right_inv := λ y, by { apply set_coe.ext, simp only [linear_map.dom_restrict_apply,
    linear_map.cod_restrict_apply, linear_map.to_fun_eq_coe, linear_equiv.coe_coe, set_like.coe_mk,
    linear_equiv.apply_symm_apply] },
  ..((e : M →ₛₗ[σ₁₂] M₂).dom_restrict p).cod_restrict (p.map (e : M →ₛₗ[σ₁₂] M₂))
  (λ x, ⟨x, by simp only [linear_map.dom_restrict_apply, eq_self_iff_true, and_true,
                          set_like.coe_mem, set_like.mem_coe]⟩) }

include σ₂₁
@[simp] lemma submodule_map_apply (p : submodule R M) (x : p) :
  ↑(e.submodule_map p x) = e x := rfl

@[simp] lemma submodule_map_symm_apply (p : submodule R M)
  (x : (p.map (e : M →ₛₗ[σ₁₂] M₂) : submodule R₂ M₂)) :
  ↑((e.submodule_map p).symm x) = e.symm x :=
rfl

omit σ₂₁

end

section finsupp
variables {γ : Type*}
variables [semiring R] [semiring R₂]
variables [add_comm_monoid M] [add_comm_monoid M₂]
variables [module R M] [module R₂ M₂] [has_zero γ]
variables {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}
variables [ring_hom_inv_pair τ₁₂ τ₂₁] [ring_hom_inv_pair τ₂₁ τ₁₂]

include τ₂₁
@[simp] lemma map_finsupp_sum (f : M ≃ₛₗ[τ₁₂] M₂) {t : ι →₀ γ} {g : ι → γ → M} :
  f (t.sum g) = t.sum (λ i d, f (g i d)) := f.map_sum _
omit τ₂₁

end finsupp

section dfinsupp
open dfinsupp

variables [semiring R] [semiring R₂]
variables [add_comm_monoid M] [add_comm_monoid M₂]
variables [module R M] [module R₂ M₂]
variables {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}
variables [ring_hom_inv_pair τ₁₂ τ₂₁] [ring_hom_inv_pair τ₂₁ τ₁₂]
variables {γ : ι → Type*} [decidable_eq ι]

include τ₂₁
@[simp] lemma map_dfinsupp_sum [Π i, has_zero (γ i)] [Π i (x : γ i), decidable (x ≠ 0)]
  (f : M ≃ₛₗ[τ₁₂] M₂) (t : Π₀ i, γ i) (g : Π i, γ i → M) :
  f (t.sum g) = t.sum (λ i d, f (g i d)) := f.map_sum _

@[simp] lemma map_dfinsupp_sum_add_hom [Π i, add_zero_class (γ i)] (f : M ≃ₛₗ[τ₁₂] M₂)
  (t : Π₀ i, γ i) (g : Π i, γ i →+ M) :
  f (sum_add_hom g t) = sum_add_hom (λ i, f.to_add_equiv.to_add_monoid_hom.comp (g i)) t :=
f.to_add_equiv.map_dfinsupp_sum_add_hom _ _

end dfinsupp

section uncurry
variables [semiring R] [semiring R₂] [semiring R₃] [semiring R₄]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄]

variables (V V₂ R)

/-- Linear equivalence between a curried and uncurried function.
  Differs from `tensor_product.curry`. -/
protected def curry :
  (V × V₂ → R) ≃ₗ[R] (V → V₂ → R) :=
{ map_add'  := λ _ _, by { ext, refl },
  map_smul' := λ _ _, by { ext, refl },
  .. equiv.curry _ _ _ }

@[simp] lemma coe_curry : ⇑(linear_equiv.curry R V V₂) = curry := rfl

@[simp] lemma coe_curry_symm : ⇑(linear_equiv.curry R V V₂).symm = uncurry := rfl

end uncurry

section
variables [semiring R] [semiring R₂] [semiring R₃] [semiring R₄]
variables [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃] [add_comm_monoid M₄]
variables {module_M : module R M} {module_M₂ : module R₂ M₂} {module_M₃ : module R₃ M₃}
variables {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variables {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [ring_hom_comp_triple σ₁₂ σ₂₃ σ₁₃]
variables {σ₃₂ : R₃ →+* R₂}
variables {re₁₂ : ring_hom_inv_pair σ₁₂ σ₂₁} {re₂₁ : ring_hom_inv_pair σ₂₁ σ₁₂}
variables {re₂₃ : ring_hom_inv_pair σ₂₃ σ₃₂} {re₃₂ : ring_hom_inv_pair σ₃₂ σ₂₃}
variables (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₁] M) (e : M ≃ₛₗ[σ₁₂] M₂) (h : M₂ →ₛₗ[σ₂₃] M₃)
variables (e'' : M₂ ≃ₛₗ[σ₂₃] M₃)

variables (p q : submodule R M)

/-- Linear equivalence between two equal submodules. -/
def of_eq (h : p = q) : p ≃ₗ[R] q :=
{ map_smul' := λ _ _, rfl, map_add' := λ _ _, rfl, .. equiv.set.of_eq (congr_arg _ h) }

variables {p q}

@[simp] lemma coe_of_eq_apply (h : p = q) (x : p) : (of_eq p q h x : M) = x := rfl

@[simp] lemma of_eq_symm (h : p = q) : (of_eq p q h).symm = of_eq q p h.symm := rfl

include σ₂₁
/-- A linear equivalence which maps a submodule of one module onto another, restricts to a linear
equivalence of the two submodules. -/
def of_submodules (p : submodule R M) (q : submodule R₂ M₂) (h : p.map (e : M →ₛₗ[σ₁₂] M₂) = q) :
p ≃ₛₗ[σ₁₂] q := (e.submodule_map p).trans (linear_equiv.of_eq _ _ h)


@[simp] lemma of_submodules_apply {p : submodule R M} {q : submodule R₂ M₂}
  (h : p.map ↑e = q) (x : p) : ↑(e.of_submodules p q h x) = e x := rfl

@[simp] lemma of_submodules_symm_apply {p : submodule R M} {q : submodule R₂ M₂}
  (h : p.map ↑e = q) (x : q) : ↑((e.of_submodules p q h).symm x) = e.symm x := rfl

include re₁₂ re₂₁
/-- A linear equivalence of two modules restricts to a linear equivalence from the preimage of any
submodule to that submodule.

This is `linear_equiv.of_submodule` but with `comap` on the left instead of `map` on the right. -/
def of_submodule' [module R M] [module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : submodule R₂ M₂) :
  U.comap (f : M →ₛₗ[σ₁₂] M₂) ≃ₛₗ[σ₁₂] U :=
(f.symm.of_submodules _ _ f.symm.map_eq_comap).symm

lemma of_submodule'_to_linear_map [module R M] [module R₂ M₂]
  (f : M ≃ₛₗ[σ₁₂] M₂) (U : submodule R₂ M₂) :
  (f.of_submodule' U).to_linear_map =
  (f.to_linear_map.dom_restrict _).cod_restrict _ subtype.prop :=
by { ext, refl }

@[simp]
lemma of_submodule'_apply [module R M] [module R₂ M₂]
  (f : M ≃ₛₗ[σ₁₂] M₂) (U : submodule R₂ M₂) (x : U.comap (f : M →ₛₗ[σ₁₂] M₂)) :
(f.of_submodule' U x : M₂) = f (x : M) := rfl

@[simp]
lemma of_submodule'_symm_apply [module R M] [module R₂ M₂]
  (f : M ≃ₛₗ[σ₁₂] M₂) (U : submodule R₂ M₂) (x : U) :
((f.of_submodule' U).symm x : M) = f.symm (x : M₂) := rfl

variable (p)

omit σ₂₁ re₁₂ re₂₁

/-- The top submodule of `M` is linearly equivalent to `M`. -/
def of_top (h : p = ⊤) : p ≃ₗ[R] M :=
{ inv_fun   := λ x, ⟨x, h.symm ▸ trivial⟩,
  left_inv  := λ ⟨x, h⟩, rfl,
  right_inv := λ x, rfl,
  .. p.subtype }

@[simp] theorem of_top_apply {h} (x : p) : of_top p h x = x := rfl

@[simp] theorem coe_of_top_symm_apply {h} (x : M) : ((of_top p h).symm x : M) = x := rfl

theorem of_top_symm_apply {h} (x : M) : (of_top p h).symm x = ⟨x, h.symm ▸ trivial⟩ := rfl

include σ₂₁ re₁₂ re₂₁
/-- If a linear map has an inverse, it is a linear equivalence. -/
def of_linear (h₁ : f.comp g = linear_map.id) (h₂ : g.comp f = linear_map.id) :
  M ≃ₛₗ[σ₁₂] M₂ :=
{ inv_fun   := g,
  left_inv  := linear_map.ext_iff.1 h₂,
  right_inv := linear_map.ext_iff.1 h₁,
  ..f }
omit σ₂₁ re₁₂ re₂₁

include σ₂₁ re₁₂ re₂₁
@[simp] theorem of_linear_apply {h₁ h₂} (x : M) : of_linear f g h₁ h₂ x = f x := rfl
omit σ₂₁ re₁₂ re₂₁

include σ₂₁ re₁₂ re₂₁
@[simp] theorem of_linear_symm_apply {h₁ h₂} (x : M₂) : (of_linear f g h₁ h₂).symm x = g x :=
rfl
omit σ₂₁ re₁₂ re₂₁

@[simp] protected theorem range : (e : M →ₛₗ[σ₁₂] M₂).range = ⊤ :=
linear_map.range_eq_top.2 e.to_equiv.surjective

include σ₂₁ re₁₂ re₂₁
lemma eq_bot_of_equiv [module R₂ M₂] (e : p ≃ₛₗ[σ₁₂] (⊥ : submodule R₂ M₂)) : p = ⊥ :=
begin
  refine bot_unique (set_like.le_def.2 $ assume b hb, (submodule.mem_bot R).2 _),
  rw [← p.mk_eq_zero hb, ← e.map_eq_zero_iff],
  apply submodule.eq_zero_of_bot_submodule
end
omit σ₂₁ re₁₂ re₂₁

@[simp] protected theorem ker : (e : M →ₛₗ[σ₁₂] M₂).ker = ⊥ :=
linear_map.ker_eq_bot_of_injective e.to_equiv.injective

@[simp] theorem range_comp [ring_hom_surjective σ₁₂] [ring_hom_surjective σ₂₃]
  [ring_hom_surjective σ₁₃] :
  (h.comp (e : M →ₛₗ[σ₁₂] M₂) : M →ₛₗ[σ₁₃] M₃).range = h.range :=
linear_map.range_comp_of_range_eq_top _ e.range

include module_M
@[simp] theorem ker_comp (l : M →ₛₗ[σ₁₂] M₂) :
  (((e'' : M₂ →ₛₗ[σ₂₃] M₃).comp l : M →ₛₗ[σ₁₃] M₃) : M →ₛₗ[σ₁₃] M₃).ker = l.ker :=
linear_map.ker_comp_of_ker_eq_bot _ e''.ker
omit module_M

variables {f g}

include σ₂₁
/-- An linear map `f : M →ₗ[R] M₂` with a left-inverse `g : M₂ →ₗ[R] M` defines a linear
equivalence between `M` and `f.range`.

This is a computable alternative to `linear_equiv.of_injective`, and a bidirectional version of
`linear_map.range_restrict`. -/
def of_left_inverse [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
  {g : M₂ → M} (h : function.left_inverse g f) : M ≃ₛₗ[σ₁₂] f.range :=
{ to_fun := f.range_restrict,
  inv_fun := g ∘ f.range.subtype,
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := linear_map.mem_range.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  .. f.range_restrict }
omit σ₂₁

@[simp] lemma of_left_inverse_apply [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
  (h : function.left_inverse g f) (x : M) :
  ↑(of_left_inverse h x) = f x := rfl

include σ₂₁
@[simp] lemma of_left_inverse_symm_apply [ring_hom_inv_pair σ₁₂ σ₂₁]
  [ring_hom_inv_pair σ₂₁ σ₁₂] (h : function.left_inverse g f) (x : f.range) :
  (of_left_inverse h).symm x = g x := rfl
omit σ₂₁

variables (f)

/-- An `injective` linear map `f : M →ₗ[R] M₂` defines a linear equivalence
between `M` and `f.range`. See also `linear_map.of_left_inverse`. -/
noncomputable def of_injective [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
  (h : injective f) : M ≃ₛₗ[σ₁₂] f.range :=
of_left_inverse $ classical.some_spec h.has_left_inverse

@[simp] theorem of_injective_apply [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
  {h : injective f} (x : M) : ↑(of_injective f h x) = f x := rfl

/-- A bijective linear map is a linear equivalence. -/
noncomputable def of_bijective [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
  (hf₁ : injective f) (hf₂ : surjective f) : M ≃ₛₗ[σ₁₂] M₂ :=
(of_injective f hf₁).trans (of_top _ $ linear_map.range_eq_top.2 hf₂)

@[simp] theorem of_bijective_apply [ring_hom_inv_pair σ₁₂ σ₂₁] [ring_hom_inv_pair σ₂₁ σ₁₂]
  {hf₁ hf₂} (x : M) : of_bijective f hf₁ hf₂ x = f x := rfl

end

end add_comm_monoid

section add_comm_group

variables [semiring R] [semiring R₂] [semiring R₃] [semiring R₄]
variables [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃] [add_comm_group M₄]
variables {module_M : module R M} {module_M₂ : module R₂ M₂}
variables {module_M₃ : module R₃ M₃} {module_M₄ : module R₄ M₄}
variables {σ₁₂ : R →+* R₂} {σ₃₄ : R₃ →+* R₄}
variables {σ₂₁ : R₂ →+* R} {σ₄₃ : R₄ →+* R₃}
variables {re₁₂ : ring_hom_inv_pair σ₁₂ σ₂₁} {re₂₁ : ring_hom_inv_pair σ₂₁ σ₁₂}
variables {re₃₄ : ring_hom_inv_pair σ₃₄ σ₄₃} {re₄₃ : ring_hom_inv_pair σ₄₃ σ₃₄}
variables (e e₁ : M ≃ₛₗ[σ₁₂] M₂) (e₂ : M₃ ≃ₛₗ[σ₃₄] M₄)

@[simp] theorem map_neg (a : M) : e (-a) = -e a := e.to_linear_map.map_neg a
@[simp] theorem map_sub (a b : M) : e (a - b) = e a - e b :=
e.to_linear_map.map_sub a b

end add_comm_group

section neg

variables (R) [semiring R] [add_comm_group M] [module R M]

/-- `x ↦ -x` as a `linear_equiv` -/
def neg : M ≃ₗ[R] M := { .. equiv.neg M, .. (-linear_map.id : M →ₗ[R] M) }

variable {R}

@[simp] lemma coe_neg : ⇑(neg R : M ≃ₗ[R] M) = -id := rfl

lemma neg_apply (x : M) : neg R x = -x := by simp

@[simp] lemma symm_neg : (neg R : M ≃ₗ[R] M).symm = neg R := rfl

end neg

section comm_semiring
variables [comm_semiring R] [add_comm_monoid M] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [module R M] [module R M₂] [module R M₃]
open _root_.linear_map

/-- Multiplying by a unit `a` of the ring `R` is a linear equivalence. -/
def smul_of_unit (a : Rˣ) : M ≃ₗ[R] M :=
distrib_mul_action.to_linear_equiv R M a

/-- A linear isomorphism between the domains and codomains of two spaces of linear maps gives a
linear isomorphism between the two function spaces. -/
def arrow_congr {R M₁ M₂ M₂₁ M₂₂ : Sort*} [comm_semiring R]
  [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₂₁] [add_comm_monoid M₂₂]
  [module R M₁] [module R M₂] [module R M₂₁] [module R M₂₂]
  (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) :
  (M₁ →ₗ[R] M₂₁) ≃ₗ[R] (M₂ →ₗ[R] M₂₂) :=
{ to_fun := λ f : M₁ →ₗ[R] M₂₁, (e₂ : M₂₁ →ₗ[R] M₂₂).comp $ f.comp (e₁.symm : M₂ →ₗ[R] M₁),
  inv_fun := λ f, (e₂.symm : M₂₂ →ₗ[R] M₂₁).comp $ f.comp (e₁ : M₁ →ₗ[R] M₂),
  left_inv := λ f, by { ext x, simp only [symm_apply_apply, comp_app, coe_comp, coe_coe]},
  right_inv := λ f, by { ext x, simp only [comp_app, apply_symm_apply, coe_comp, coe_coe]},
  map_add' := λ f g, by { ext x, simp only [map_add, add_apply, comp_app, coe_comp, coe_coe]},
  map_smul' := λ c f, by { ext x, simp only [smul_apply, comp_app, coe_comp, map_smulₛₗ, coe_coe]} }

@[simp] lemma arrow_congr_apply {R M₁ M₂ M₂₁ M₂₂ : Sort*} [comm_semiring R]
  [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₂₁] [add_comm_monoid M₂₂]
  [module R M₁] [module R M₂] [module R M₂₁] [module R M₂₂]
  (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) (f : M₁ →ₗ[R] M₂₁) (x : M₂) :
  arrow_congr e₁ e₂ f x = e₂ (f (e₁.symm x)) :=
rfl

@[simp] lemma arrow_congr_symm_apply {R M₁ M₂ M₂₁ M₂₂ : Sort*} [comm_semiring R]
  [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₂₁] [add_comm_monoid M₂₂]
  [module R M₁] [module R M₂] [module R M₂₁] [module R M₂₂]
  (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : M₂₁ ≃ₗ[R] M₂₂) (f : M₂ →ₗ[R] M₂₂) (x : M₁) :
  (arrow_congr e₁ e₂).symm f x = e₂.symm (f (e₁ x)) :=
rfl

lemma arrow_congr_comp {N N₂ N₃ : Sort*}
  [add_comm_monoid N] [add_comm_monoid N₂] [add_comm_monoid N₃]
  [module R N] [module R N₂] [module R N₃]
  (e₁ : M ≃ₗ[R] N) (e₂ : M₂ ≃ₗ[R] N₂) (e₃ : M₃ ≃ₗ[R] N₃) (f : M →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
  arrow_congr e₁ e₃ (g.comp f) = (arrow_congr e₂ e₃ g).comp (arrow_congr e₁ e₂ f) :=
by { ext, simp only [symm_apply_apply, arrow_congr_apply, linear_map.comp_apply], }

lemma arrow_congr_trans {M₁ M₂ M₃ N₁ N₂ N₃ : Sort*}
  [add_comm_monoid M₁] [module R M₁] [add_comm_monoid M₂] [module R M₂]
  [add_comm_monoid M₃] [module R M₃] [add_comm_monoid N₁] [module R N₁]
  [add_comm_monoid N₂] [module R N₂] [add_comm_monoid N₃] [module R N₃]
  (e₁ : M₁ ≃ₗ[R] M₂) (e₂ : N₁ ≃ₗ[R] N₂) (e₃ : M₂ ≃ₗ[R] M₃) (e₄ : N₂ ≃ₗ[R] N₃) :
  (arrow_congr e₁ e₂).trans (arrow_congr e₃ e₄) = arrow_congr (e₁.trans e₃) (e₂.trans e₄) :=
rfl

/-- If `M₂` and `M₃` are linearly isomorphic then the two spaces of linear maps from `M` into `M₂`
and `M` into `M₃` are linearly isomorphic. -/
def congr_right (f : M₂ ≃ₗ[R] M₃) : (M →ₗ[R] M₂) ≃ₗ[R] (M →ₗ[R] M₃) :=
arrow_congr (linear_equiv.refl R M) f

/-- If `M` and `M₂` are linearly isomorphic then the two spaces of linear maps from `M` and `M₂` to
themselves are linearly isomorphic. -/
def conj (e : M ≃ₗ[R] M₂) : (module.End R M) ≃ₗ[R] (module.End R M₂) := arrow_congr e e

lemma conj_apply (e : M ≃ₗ[R] M₂) (f : module.End R M) :
  e.conj f = ((↑e : M →ₗ[R] M₂).comp f).comp (e.symm : M₂ →ₗ[R] M) := rfl

lemma symm_conj_apply (e : M ≃ₗ[R] M₂) (f : module.End R M₂) :
  e.symm.conj f = ((↑e.symm : M₂ →ₗ[R] M).comp f).comp (e : M →ₗ[R] M₂) := rfl

lemma conj_comp (e : M ≃ₗ[R] M₂) (f g : module.End R M) :
  e.conj (g.comp f) = (e.conj g).comp (e.conj f) :=
arrow_congr_comp e e e f g

lemma conj_trans (e₁ : M ≃ₗ[R] M₂) (e₂ : M₂ ≃ₗ[R] M₃) :
  e₁.conj.trans e₂.conj = (e₁.trans e₂).conj :=
by { ext f x, refl, }

@[simp] lemma conj_id (e : M ≃ₗ[R] M₂) : e.conj linear_map.id = linear_map.id :=
by { ext, simp [conj_apply], }

end comm_semiring

section field

variables [field K] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module K M] [module K M₂] [module K M₃]
variables (K) (M)
open _root_.linear_map

/-- Multiplying by a nonzero element `a` of the field `K` is a linear equivalence. -/
@[simps] def smul_of_ne_zero (a : K) (ha : a ≠ 0) : M ≃ₗ[K] M :=
smul_of_unit $ units.mk0 a ha

end field

end linear_equiv

namespace submodule

section module

variables [semiring R] [add_comm_monoid M] [module R M]

/-- Given `p` a submodule of the module `M` and `q` a submodule of `p`, `p.equiv_subtype_map q`
is the natural `linear_equiv` between `q` and `q.map p.subtype`. -/
def equiv_subtype_map (p : submodule R M) (q : submodule R p) :
  q ≃ₗ[R] q.map p.subtype :=
{ inv_fun :=
    begin
      rintro ⟨x, hx⟩,
      refine ⟨⟨x, _⟩, _⟩;
      rcases hx with ⟨⟨_, h⟩, _, rfl⟩;
      assumption
    end,
  left_inv := λ ⟨⟨_, _⟩, _⟩, rfl,
  right_inv := λ ⟨x, ⟨_, h⟩, _, rfl⟩, rfl,
  .. (p.subtype.dom_restrict q).cod_restrict _
    begin
      rintro ⟨x, hx⟩,
      refine ⟨x, hx, rfl⟩,
    end }

@[simp]
lemma equiv_subtype_map_apply {p : submodule R M} {q : submodule R p} (x : q) :
  (p.equiv_subtype_map q x : M) = p.subtype.dom_restrict q x :=
rfl

@[simp]
lemma equiv_subtype_map_symm_apply {p : submodule R M} {q : submodule R p} (x : q.map p.subtype) :
  ((p.equiv_subtype_map q).symm x : M) = x :=
by { cases x, refl }

/-- If `s ≤ t`, then we can view `s` as a submodule of `t` by taking the comap
of `t.subtype`. -/
@[simps]
def comap_subtype_equiv_of_le {p q : submodule R M} (hpq : p ≤ q) :
  comap q.subtype p ≃ₗ[R] p :=
{ to_fun := λ x, ⟨x, x.2⟩,
  inv_fun := λ x, ⟨⟨x, hpq x.2⟩, x.2⟩,
  left_inv := λ x, by simp only [coe_mk, set_like.eta, coe_coe],
  right_inv := λ x, by simp only [subtype.coe_mk, set_like.eta, coe_coe],
  map_add' := λ x y, rfl,
  map_smul' := λ c x, rfl }

end module

end submodule

namespace submodule

variables [comm_semiring R] [comm_semiring R₂]
variables [add_comm_monoid M] [add_comm_monoid M₂] [module R M] [module R₂ M₂]
variables [add_comm_monoid N] [add_comm_monoid N₂] [module R N] [module R N₂]
variables {τ₁₂ : R →+* R₂} {τ₂₁ : R₂ →+* R}
variables [ring_hom_inv_pair τ₁₂ τ₂₁] [ring_hom_inv_pair τ₂₁ τ₁₂]
variables (p : submodule R M) (q : submodule R₂ M₂)
variables (pₗ : submodule R N) (qₗ : submodule R N₂)

include τ₂₁
@[simp] lemma mem_map_equiv {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂} : x ∈ p.map (e : M →ₛₗ[τ₁₂] M₂) ↔
  e.symm x ∈ p :=
begin
  rw submodule.mem_map, split,
  { rintros ⟨y, hy, hx⟩, simp [←hx, hy], },
  { intros hx, refine ⟨e.symm x, hx, by simp⟩, },
end
omit τ₂₁

lemma map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : submodule R M) :
  K.map (e : M →ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ →ₛₗ[τ₂₁] M) :=
submodule.ext (λ _, by rw [mem_map_equiv, mem_comap, linear_equiv.coe_coe])

lemma comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : submodule R₂ M₂) :
  K.comap (e : M →ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂ →ₛₗ[τ₂₁] M) :=
(map_equiv_eq_comap_symm e.symm K).symm

lemma comap_le_comap_smul (fₗ : N →ₗ[R] N₂) (c : R) :
  comap fₗ qₗ ≤ comap (c • fₗ) qₗ :=
begin
  rw set_like.le_def,
  intros m h,
  change c • (fₗ m) ∈ qₗ,
  change fₗ m ∈ qₗ at h,
  apply qₗ.smul_mem _ h,
end

lemma inf_comap_le_comap_add (f₁ f₂ : M →ₛₗ[τ₁₂] M₂) :
  comap f₁ q ⊓ comap f₂ q ≤ comap (f₁ + f₂) q :=
begin
  rw set_like.le_def,
  intros m h,
  change f₁ m + f₂ m ∈ q,
  change f₁ m ∈ q ∧ f₂ m ∈ q at h,
  apply q.add_mem h.1 h.2,
end

/-- Given modules `M`, `M₂` over a commutative ring, together with submodules `p ⊆ M`, `q ⊆ M₂`,
the set of maps $\{f ∈ Hom(M, M₂) | f(p) ⊆ q \}$ is a submodule of `Hom(M, M₂)`. -/
def compatible_maps : submodule R (N →ₗ[R] N₂) :=
{ carrier   := {fₗ | pₗ ≤ comap fₗ qₗ},
  zero_mem' := by { change pₗ ≤ comap 0 qₗ, rw comap_zero, refine le_top, },
  add_mem'  := λ f₁ f₂ h₁ h₂, by { apply le_trans _ (inf_comap_le_comap_add qₗ f₁ f₂),
                                 rw le_inf_iff, exact ⟨h₁, h₂⟩, },
  smul_mem' := λ c fₗ h, le_trans h (comap_le_comap_smul qₗ fₗ c), }

end submodule

namespace equiv
variables [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid M₂] [module R M₂]

/-- An equivalence whose underlying function is linear is a linear equivalence. -/
def to_linear_equiv (e : M ≃ M₂) (h : is_linear_map R (e : M → M₂)) : M ≃ₗ[R] M₂ :=
{ .. e, .. h.mk' e}

end equiv


section fun_left
variables (R M) [semiring R] [add_comm_monoid M] [module R M]
variables {m n p : Type*}

namespace linear_map

/-- Given an `R`-module `M` and a function `m → n` between arbitrary types,
construct a linear map `(n → M) →ₗ[R] (m → M)` -/
def fun_left (f : m → n) : (n → M) →ₗ[R] (m → M) :=
{ to_fun := (∘ f), map_add' := λ _ _, rfl, map_smul' := λ _ _, rfl }

@[simp] theorem fun_left_apply (f : m → n) (g : n → M) (i : m) : fun_left R M f g i = g (f i) :=
rfl

@[simp] theorem fun_left_id (g : n → M) : fun_left R M _root_.id g = g :=
rfl

theorem fun_left_comp (f₁ : n → p) (f₂ : m → n) :
  fun_left R M (f₁ ∘ f₂) = (fun_left R M f₂).comp (fun_left R M f₁) :=
rfl

theorem fun_left_surjective_of_injective (f : m → n) (hf : injective f) :
  surjective (fun_left R M f) :=
begin
  classical,
  intro g,
  refine ⟨λ x, if h : ∃ y, f y = x then g h.some else 0, _⟩,
  { ext,
    dsimp only [fun_left_apply],
    split_ifs with w,
    { congr,
      exact hf w.some_spec, },
    { simpa only [not_true, exists_apply_eq_apply] using w } },
end

theorem fun_left_injective_of_surjective (f : m → n) (hf : surjective f) :
  injective (fun_left R M f) :=
begin
  obtain ⟨g, hg⟩ := hf.has_right_inverse,
  suffices : left_inverse (fun_left R M g) (fun_left R M f),
  { exact this.injective },
  intro x,
  rw [←linear_map.comp_apply, ← fun_left_comp, hg.id, fun_left_id],
end

end linear_map

namespace linear_equiv
open _root_.linear_map

/-- Given an `R`-module `M` and an equivalence `m ≃ n` between arbitrary types,
construct a linear equivalence `(n → M) ≃ₗ[R] (m → M)` -/
def fun_congr_left (e : m ≃ n) : (n → M) ≃ₗ[R] (m → M) :=
linear_equiv.of_linear (fun_left R M e) (fun_left R M e.symm)
  (linear_map.ext $ λ x, funext $ λ i,
    by rw [id_apply, ← fun_left_comp, equiv.symm_comp_self, fun_left_id])
  (linear_map.ext $ λ x, funext $ λ i,
    by rw [id_apply, ← fun_left_comp, equiv.self_comp_symm, fun_left_id])

@[simp] theorem fun_congr_left_apply (e : m ≃ n) (x : n → M) :
  fun_congr_left R M e x = fun_left R M e x :=
rfl

@[simp] theorem fun_congr_left_id :
  fun_congr_left R M (equiv.refl n) = linear_equiv.refl R (n → M) :=
rfl

@[simp] theorem fun_congr_left_comp (e₁ : m ≃ n) (e₂ : n ≃ p) :
  fun_congr_left R M (equiv.trans e₁ e₂) =
    linear_equiv.trans (fun_congr_left R M e₂) (fun_congr_left R M e₁) :=
rfl

@[simp] lemma fun_congr_left_symm (e : m ≃ n) :
  (fun_congr_left R M e).symm = fun_congr_left R M e.symm :=
rfl

end linear_equiv

end fun_left

namespace linear_map

variables [semiring R] [add_comm_monoid M] [module R M]
variables (R M)

/-- The group of invertible linear maps from `M` to itself -/
@[reducible] def general_linear_group := (M →ₗ[R] M)ˣ

namespace general_linear_group
variables {R M}

instance : has_coe_to_fun (general_linear_group R M) (λ _, M → M) := by apply_instance

/-- An invertible linear map `f` determines an equivalence from `M` to itself. -/
def to_linear_equiv (f : general_linear_group R M) : (M ≃ₗ[R] M) :=
{ inv_fun := f.inv.to_fun,
  left_inv := λ m, show (f.inv * f.val) m = m,
    by erw f.inv_val; simp,
  right_inv := λ m, show (f.val * f.inv) m = m,
    by erw f.val_inv; simp,
  ..f.val }

/-- An equivalence from `M` to itself determines an invertible linear map. -/
def of_linear_equiv (f : (M ≃ₗ[R] M)) : general_linear_group R M :=
{ val := f,
  inv := (f.symm : M →ₗ[R] M),
  val_inv := linear_map.ext $ λ _, f.apply_symm_apply _,
  inv_val := linear_map.ext $ λ _, f.symm_apply_apply _ }

variables (R M)

/-- The general linear group on `R` and `M` is multiplicatively equivalent to the type of linear
equivalences between `M` and itself. -/
def general_linear_equiv : general_linear_group R M ≃* (M ≃ₗ[R] M) :=
{ to_fun := to_linear_equiv,
  inv_fun := of_linear_equiv,
  left_inv := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl },
  map_mul' := λ x y, by {ext, refl} }

@[simp] lemma general_linear_equiv_to_linear_map (f : general_linear_group R M) :
  (general_linear_equiv R M f : M →ₗ[R] M) = f :=
by {ext, refl}

@[simp] lemma coe_fn_general_linear_equiv (f : general_linear_group R M) :
  ⇑(general_linear_equiv R M f) = (f : M → M) :=
rfl

end general_linear_group

end linear_map
