/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import algebra.big_operators.pi
import algebra.module.hom
import algebra.module.prod
import algebra.module.submodule_lattice
import data.dfinsupp
import data.finsupp.basic
import order.compactly_generated
import order.omega_complete_partial_order

/-!
# Linear algebra

This file defines the basics of linear algebra. It sets up the "categorical/lattice structure" of
modules over a ring, submodules, and linear maps.

Many of the relevant definitions, including `module`, `submodule`, and `linear_map`, are found in
`src/algebra/module`.

## Main definitions

* Many constructors for (semi)linear maps
* `submodule.span s` is defined to be the smallest submodule containing the set `s`.
* The kernel `ker` and range `range` of a linear map are submodules of the domain and codomain
  respectively.
* The general linear group is defined to be the group of invertible linear maps from `M` to itself.

See `linear_algebra.quotient` for quotients by submodules.

## Main theorems

See `linear_algebra.isomorphisms` for Noether's three isomorphism theorems for modules.

## Notations

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).
* We introduce the notation `R ∙ v` for the span of a singleton, `submodule.span R {v}`.  This is
  `\.`, not the same as the scalar multiplication `•`/`\bub`.

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

variables {S : Type*} [semiring S] [module R S] [module S M] [is_scalar_tower R S M]

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
by rw [← nat.sub_add_cancel hk, pow_add, mul_apply, hm, map_zero]

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

variables {S : Type*} [semiring R] [semiring S]
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
{ to_fun := λ f, {
    to_fun    := linear_map.smul_right f,
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

theorem disjoint_def {p p' : submodule R M} :
  disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = (0:M) :=
show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : set M)) ↔ _, by simp

theorem disjoint_def' {p p' : submodule R M} :
  disjoint p p' ↔ ∀ (x ∈ p) (y ∈ p'), x = y → x = (0:M) :=
disjoint_def.trans ⟨λ h x hx y hy hxy, h x hx $ hxy.symm ▸ hy,
  λ h x hx hx', h _ hx x hx' rfl⟩

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
linearly equivalent to the original submodule. -/
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

lemma comap_id : comap linear_map.id p = p :=
set_like.coe_injective rfl

lemma comap_comp (f : M →ₛₗ[σ₁₂] M₂) (g : M₂ →ₛₗ[σ₂₃] M₃)
  (p : submodule R₃ M₃) : comap (g.comp f : M →ₛₗ[σ₁₃] M₃) p = comap f (comap g p) :=
rfl

lemma comap_mono {f : M →ₛₗ[σ₁₂] M₂} {q q' : submodule R₂ M₂} :
  q ≤ q' → comap f q ≤ comap f q' := preimage_mono

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

lemma map_supr_comap_of_sujective (S : ι → submodule R₂ M₂) :
  (⨆ i, (S i).comap f).map f = supr S :=
(gi_map_comap hf).l_supr_u _

lemma map_inf_comap_of_surjective (p q : submodule R₂ M₂) :
  (p.comap f ⊓ q.comap f).map f = p ⊓ q :=
(gi_map_comap hf).l_inf_u _ _

lemma map_infi_comap_of_surjective (S : ι → submodule R₂ M₂) :
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

lemma comap_infi_map_of_injective (S : ι → submodule R M) : (⨅ i, (S i).map f).comap f = infi S :=
(gci_map_comap hf).u_infi_l _

lemma comap_sup_map_of_injective (p q : submodule R M) : (p.map f ⊔ q.map f).comap f = p ⊔ q :=
(gci_map_comap hf).u_sup_l _ _

lemma comap_supr_map_of_injective (S : ι → submodule R M) : (⨆ i, (S i).map f).comap f = supr S :=
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

section
variables (R)

/-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
def span (s : set M) : submodule R M := Inf {p | s ⊆ p}
end

variables {s t : set M}
lemma mem_span : x ∈ span R s ↔ ∀ p : submodule R M, s ⊆ p → x ∈ p :=
mem_bInter_iff

lemma subset_span : s ⊆ span R s :=
λ x h, mem_span.2 $ λ p hp, hp h

lemma span_le {p} : span R s ≤ p ↔ s ⊆ p :=
⟨subset.trans subset_span, λ ss x h, mem_span.1 h _ ss⟩

lemma span_mono (h : s ⊆ t) : span R s ≤ span R t :=
span_le.2 $ subset.trans h subset_span

lemma span_eq_of_le (h₁ : s ⊆ p) (h₂ : p ≤ span R s) : span R s = p :=
le_antisymm (span_le.2 h₁) h₂

@[simp] lemma span_eq : span R (p : set M) = p :=
span_eq_of_le _ (subset.refl _) subset_span

lemma map_span [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (s : set M) :
  (span R s).map f = span R₂ (f '' s) :=
eq.symm $ span_eq_of_le _ (set.image_subset f subset_span) $
map_le_iff_le_comap.2 $ span_le.2 $ λ x hx, subset_span ⟨x, hx, rfl⟩

alias submodule.map_span ← linear_map.map_span

lemma map_span_le {R M M₂ : Type*} [semiring R] [add_comm_monoid M]
  [add_comm_monoid M₂] [module R M] [module R M₂] (f : M →ₗ[R] M₂)
  (s : set M) (N : submodule R M₂) : map f (span R s) ≤ N ↔ ∀ m ∈ s, f m ∈ N :=
begin
  rw [f.map_span, span_le, set.image_subset_iff],
  exact iff.rfl
end

alias submodule.map_span_le ← linear_map.map_span_le

/- See also `span_preimage_eq` below. -/
lemma span_preimage_le (f : M →ₛₗ[σ₁₂] M₂) (s : set M₂) :
  span R (f ⁻¹' s) ≤ (span R₂ s).comap f :=
by { rw [span_le, comap_coe], exact preimage_mono (subset_span), }

alias submodule.span_preimage_le  ← linear_map.span_preimage_le

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition and scalar multiplication, then `p` holds for all elements of the span of
`s`. -/
@[elab_as_eliminator] lemma span_induction {p : M → Prop} (h : x ∈ span R s)
  (Hs : ∀ x ∈ s, p x) (H0 : p 0)
  (H1 : ∀ x y, p x → p y → p (x + y))
  (H2 : ∀ (a:R) x, p x → p (a • x)) : p x :=
(@span_le _ _ _ _ _ _ ⟨p, H0, H1, H2⟩).2 Hs h

lemma span_nat_eq_add_submonoid_closure (s : set M) :
  (span ℕ s).to_add_submonoid = add_submonoid.closure s :=
begin
  refine eq.symm (add_submonoid.closure_eq_of_le subset_span _),
  apply add_submonoid.to_nat_submodule.symm.to_galois_connection.l_le _,
  rw span_le,
  exact add_submonoid.subset_closure,
end

@[simp] lemma span_nat_eq (s : add_submonoid M) : (span ℕ (s : set M)).to_add_submonoid = s :=
by rw [span_nat_eq_add_submonoid_closure, s.closure_eq]

lemma span_int_eq_add_subgroup_closure {M : Type*} [add_comm_group M] (s : set M) :
  (span ℤ s).to_add_subgroup = add_subgroup.closure s :=
eq.symm $ add_subgroup.closure_eq_of_le _ subset_span $ λ x hx, span_induction hx
  (λ x hx, add_subgroup.subset_closure hx) (add_subgroup.zero_mem _)
  (λ _ _, add_subgroup.add_mem _) (λ _ _ _, add_subgroup.gsmul_mem _ ‹_› _)

@[simp] lemma span_int_eq {M : Type*} [add_comm_group M] (s : add_subgroup M) :
  (span ℤ (s : set M)).to_add_subgroup = s :=
by rw [span_int_eq_add_subgroup_closure, s.closure_eq]

section
variables (R M)

/-- `span` forms a Galois insertion with the coercion from submodule to set. -/
protected def gi : galois_insertion (@span R M _ _ _) coe :=
{ choice := λ s _, span R s,
  gc := λ s t, span_le,
  le_l_u := λ s, subset_span,
  choice_eq := λ s h, rfl }

end

@[simp] lemma span_empty : span R (∅ : set M) = ⊥ :=
(submodule.gi R M).gc.l_bot

@[simp] lemma span_univ : span R (univ : set M) = ⊤ :=
eq_top_iff.2 $ set_like.le_def.2 $ subset_span

lemma span_union (s t : set M) : span R (s ∪ t) = span R s ⊔ span R t :=
(submodule.gi R M).gc.l_sup

lemma span_Union {ι} (s : ι → set M) : span R (⋃ i, s i) = ⨆ i, span R (s i) :=
(submodule.gi R M).gc.l_supr

lemma span_eq_supr_of_singleton_spans (s : set M) : span R s = ⨆ x ∈ s, span R {x} :=
by simp only [←span_Union, set.bUnion_of_singleton s]

@[simp] theorem coe_supr_of_directed {ι} [hι : nonempty ι]
  (S : ι → submodule R M) (H : directed (≤) S) :
  ((supr S : submodule R M) : set M) = ⋃ i, S i :=
begin
  refine subset.antisymm _ (Union_subset $ le_supr S),
  suffices : (span R (⋃ i, (S i : set M)) : set M) ⊆ ⋃ (i : ι), ↑(S i),
    by simpa only [span_Union, span_eq] using this,
  refine (λ x hx, span_induction hx (λ _, id) _ _ _);
    simp only [mem_Union, exists_imp_distrib],
  { exact hι.elim (λ i, ⟨i, (S i).zero_mem⟩) },
  { intros x y i hi j hj,
    rcases H i j with ⟨k, ik, jk⟩,
    exact ⟨k, add_mem _ (ik hi) (jk hj)⟩ },
  { exact λ a x i hi, ⟨i, smul_mem _ a hi⟩ },
end

@[simp] theorem mem_supr_of_directed {ι} [nonempty ι]
  (S : ι → submodule R M) (H : directed (≤) S) {x} :
  x ∈ supr S ↔ ∃ i, x ∈ S i :=
by { rw [← set_like.mem_coe, coe_supr_of_directed S H, mem_Union], refl }

theorem mem_Sup_of_directed {s : set (submodule R M)}
  {z} (hs : s.nonempty) (hdir : directed_on (≤) s) :
  z ∈ Sup s ↔ ∃ y ∈ s, z ∈ y :=
begin
  haveI : nonempty s := hs.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed _ hdir.directed_coe, set_coe.exists, subtype.coe_mk]
end

@[norm_cast, simp] lemma coe_supr_of_chain (a : ℕ →ₘ submodule R M) :
  (↑(⨆ k, a k) : set M) = ⋃ k, (a k : set M) :=
coe_supr_of_directed a a.monotone.directed_le

/-- We can regard `coe_supr_of_chain` as the statement that `coe : (submodule R M) → set M` is
Scott continuous for the ω-complete partial order induced by the complete lattice structures. -/
lemma coe_scott_continuous : omega_complete_partial_order.continuous'
  (coe : submodule R M → set M) :=
⟨set_like.coe_mono, coe_supr_of_chain⟩

@[simp] lemma mem_supr_of_chain (a : ℕ →ₘ submodule R M) (m : M) :
  m ∈ (⨆ k, a k) ↔ ∃ k, m ∈ a k :=
mem_supr_of_directed a a.monotone.directed_le

section

variables {p p'}

lemma mem_sup : x ∈ p ⊔ p' ↔ ∃ (y ∈ p) (z ∈ p'), y + z = x :=
⟨λ h, begin
  rw [← span_eq p, ← span_eq p', ← span_union] at h,
  apply span_induction h,
  { rintro y (h | h),
    { exact ⟨y, h, 0, by simp, by simp⟩ },
    { exact ⟨0, by simp, y, h, by simp⟩ } },
  { exact ⟨0, by simp, 0, by simp⟩ },
  { rintro _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩,
    exact ⟨_, add_mem _ hy₁ hy₂, _, add_mem _ hz₁ hz₂, by simp [add_assoc]; cc⟩ },
  { rintro a _ ⟨y, hy, z, hz, rfl⟩,
    exact ⟨_, smul_mem _ a hy, _, smul_mem _ a hz, by simp [smul_add]⟩ }
end,
by rintro ⟨y, hy, z, hz, rfl⟩; exact add_mem _
  ((le_sup_left : p ≤ p ⊔ p') hy)
  ((le_sup_right : p' ≤ p ⊔ p') hz)⟩

lemma mem_sup' : x ∈ p ⊔ p' ↔ ∃ (y : p) (z : p'), (y:M) + z = x :=
mem_sup.trans $ by simp only [set_like.exists, coe_mk]

lemma coe_sup : ↑(p ⊔ p') = (p + p' : set M) :=
by { ext, rw [set_like.mem_coe, mem_sup, set.mem_add], simp, }

end

/- This is the character `∙`, with escape sequence `\.`, and is thus different from the scalar
multiplication character `•`, with escape sequence `\bub`. -/
notation R`∙`:1000 x := span R (@singleton _ _ set.has_singleton x)

lemma mem_span_singleton_self (x : M) : x ∈ R ∙ x := subset_span rfl

lemma nontrivial_span_singleton {x : M} (h : x ≠ 0) : nontrivial (R ∙ x) :=
⟨begin
    use [0, x, submodule.mem_span_singleton_self x],
    intros H,
    rw [eq_comm, submodule.mk_eq_zero] at H,
    exact h H
end⟩

lemma mem_span_singleton {y : M} : x ∈ (R ∙ y) ↔ ∃ a:R, a • y = x :=
⟨λ h, begin
  apply span_induction h,
  { rintro y (rfl|⟨⟨⟩⟩), exact ⟨1, by simp⟩ },
  { exact ⟨0, by simp⟩ },
  { rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩,
    exact ⟨a + b, by simp [add_smul]⟩ },
  { rintro a _ ⟨b, rfl⟩,
    exact ⟨a * b, by simp [smul_smul]⟩ }
end,
by rintro ⟨a, y, rfl⟩; exact
  smul_mem _ _ (subset_span $ by simp)⟩

lemma le_span_singleton_iff {s : submodule R M} {v₀ : M} :
  s ≤ (R ∙ v₀) ↔ ∀ v ∈ s, ∃ r : R, r • v₀ = v :=
by simp_rw [set_like.le_def, mem_span_singleton]

lemma span_singleton_eq_top_iff (x : M) : (R ∙ x) = ⊤ ↔ ∀ v, ∃ r : R, r • x = v :=
begin
  rw [eq_top_iff, le_span_singleton_iff],
  finish,
end

@[simp] lemma span_zero_singleton : (R ∙ (0:M)) = ⊥ :=
by { ext, simp [mem_span_singleton, eq_comm] }

lemma span_singleton_eq_range (y : M) : ↑(R ∙ y) = range ((• y) : R → M) :=
set.ext $ λ x, mem_span_singleton

lemma span_singleton_smul_le (r : R) (x : M) : (R ∙ (r • x)) ≤ R ∙ x :=
begin
  rw [span_le, set.singleton_subset_iff, set_like.mem_coe],
  exact smul_mem _ _ (mem_span_singleton_self _)
end

lemma span_singleton_smul_eq {K E : Type*} [division_ring K] [add_comm_group E] [module K E]
  {r : K} (x : E) (hr : r ≠ 0) : (K ∙ (r • x)) = K ∙ x :=
begin
  refine le_antisymm (span_singleton_smul_le r x) _,
  convert span_singleton_smul_le r⁻¹ (r • x),
  exact (inv_smul_smul₀ hr _).symm
end

lemma disjoint_span_singleton {K E : Type*} [division_ring K] [add_comm_group E] [module K E]
  {s : submodule K E} {x : E} :
  disjoint s (K ∙ x) ↔ (x ∈ s → x = 0) :=
begin
  refine disjoint_def.trans ⟨λ H hx, H x hx $ subset_span $ mem_singleton x, _⟩,
  assume H y hy hyx,
  obtain ⟨c, hc⟩ := mem_span_singleton.1 hyx,
  subst y,
  classical, by_cases hc : c = 0, by simp only [hc, zero_smul],
  rw [s.smul_mem_iff hc] at hy,
  rw [H hy, smul_zero]
end

lemma disjoint_span_singleton' {K E : Type*} [division_ring K] [add_comm_group E] [module K E]
  {p : submodule K E} {x : E} (x0 : x ≠ 0) :
  disjoint p (K ∙ x) ↔ x ∉ p :=
disjoint_span_singleton.trans ⟨λ h₁ h₂, x0 (h₁ h₂), λ h₁ h₂, (h₁ h₂).elim⟩

lemma mem_span_insert {y} : x ∈ span R (insert y s) ↔ ∃ (a:R) (z ∈ span R s), x = a • y + z :=
begin
  simp only [← union_singleton, span_union, mem_sup, mem_span_singleton, exists_prop,
    exists_exists_eq_and],
  rw [exists_comm],
  simp only [eq_comm, add_comm, exists_and_distrib_left]
end

lemma span_insert_eq_span (h : x ∈ span R s) : span R (insert x s) = span R s :=
span_eq_of_le _ (set.insert_subset.mpr ⟨h, subset_span⟩) (span_mono $ subset_insert _ _)

lemma span_span : span R (span R s : set M) = span R s := span_eq _

lemma span_eq_bot : span R (s : set M) = ⊥ ↔ ∀ x ∈ s, (x:M) = 0 :=
eq_bot_iff.trans ⟨
  λ H x h, (mem_bot R).1 $ H $ subset_span h,
  λ H, span_le.2 (λ x h, (mem_bot R).2 $ H x h)⟩

@[simp] lemma span_singleton_eq_bot : (R ∙ x) = ⊥ ↔ x = 0 :=
span_eq_bot.trans $ by simp

@[simp] lemma span_zero : span R (0 : set M) = ⊥ := by rw [←singleton_zero, span_singleton_eq_bot]

@[simp] lemma span_image [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) :
  span R₂ (f '' s) = map f (span R s) :=
span_eq_of_le _ (image_subset _ subset_span) $ map_le_iff_le_comap.2 $
span_le.2 $ image_subset_iff.1 subset_span

lemma apply_mem_span_image_of_mem_span
   [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) {x : M} {s : set M} (h : x ∈ submodule.span R s) :
   f x ∈ submodule.span R₂ (f '' s) :=
begin
  rw submodule.span_image,
  exact submodule.mem_map_of_mem h
end

/-- `f` is an explicit argument so we can `apply` this theorem and obtain `h` as a new goal. -/
lemma not_mem_span_of_apply_not_mem_span_image
   [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) {x : M} {s : set M}
   (h : f x ∉ submodule.span R₂ (f '' s)) :
   x ∉ submodule.span R s :=
not.imp h (apply_mem_span_image_of_mem_span f)

lemma supr_eq_span {ι : Sort*} (p : ι → submodule R M) :
  (⨆ (i : ι), p i) = submodule.span R (⋃ (i : ι), ↑(p i)) :=
le_antisymm
  (supr_le $ assume i, subset.trans (assume m hm, set.mem_Union.mpr ⟨i, hm⟩) subset_span)
  (span_le.mpr $ Union_subset_iff.mpr $ assume i m hm, mem_supr_of_mem i hm)

lemma span_singleton_le_iff_mem (m : M) (p : submodule R M) : (R ∙ m) ≤ p ↔ m ∈ p :=
by rw [span_le, singleton_subset_iff, set_like.mem_coe]

lemma singleton_span_is_compact_element (x : M) :
  complete_lattice.is_compact_element (span R {x} : submodule R M) :=
begin
  rw complete_lattice.is_compact_element_iff_le_of_directed_Sup_le,
  intros d hemp hdir hsup,
  have : x ∈ Sup d, from (set_like.le_def.mp hsup) (mem_span_singleton_self x),
  obtain ⟨y, ⟨hyd, hxy⟩⟩ := (mem_Sup_of_directed hemp hdir).mp this,
  exact ⟨y, ⟨hyd, by simpa only [span_le, singleton_subset_iff]⟩⟩,
end

instance : is_compactly_generated (submodule R M) :=
⟨λ s, ⟨(λ x, span R {x}) '' s, ⟨λ t ht, begin
  rcases (set.mem_image _ _ _).1 ht with ⟨x, hx, rfl⟩,
  apply singleton_span_is_compact_element,
end, by rw [Sup_eq_supr, supr_image, ←span_eq_supr_of_singleton_spans, span_eq]⟩⟩⟩

lemma lt_sup_iff_not_mem {I : submodule R M} {a : M} : I < I ⊔ (R ∙ a) ↔ a ∉ I :=
begin
  split,
  { intro h,
    by_contra akey,
    have h1 : I ⊔ (R ∙ a) ≤ I,
    { simp only [sup_le_iff],
      split,
      { exact le_refl I, },
      { exact (span_singleton_le_iff_mem a I).mpr akey, } },
    have h2 := gt_of_ge_of_gt h1 h,
    exact lt_irrefl I h2, },
  { intro h,
    apply set_like.lt_iff_le_and_exists.mpr, split,
    simp only [le_sup_left],
    use a,
    split, swap, { assumption, },
    { have : (R ∙ a) ≤ I ⊔ (R ∙ a) := le_sup_right,
      exact this (mem_span_singleton_self a), } },
end

lemma mem_supr {ι : Sort*} (p : ι → submodule R M) {m : M} :
  (m ∈ ⨆ i, p i) ↔ (∀ N, (∀ i, p i ≤ N) → m ∈ N) :=
begin
  rw [← span_singleton_le_iff_mem, le_supr_iff],
  simp only [span_singleton_le_iff_mem],
end

section

open_locale classical

/-- For every element in the span of a set, there exists a finite subset of the set
such that the element is contained in the span of the subset. -/
lemma mem_span_finite_of_mem_span {S : set M} {x : M} (hx : x ∈ span R S) :
  ∃ T : finset M, ↑T ⊆ S ∧ x ∈ span R (T : set M) :=
begin
  refine span_induction hx (λ x hx, _) _ _ _,
  { refine ⟨{x}, _, _⟩,
    { rwa [finset.coe_singleton, set.singleton_subset_iff] },
    { rw finset.coe_singleton,
      exact submodule.mem_span_singleton_self x } },
  { use ∅, simp },
  { rintros x y ⟨X, hX, hxX⟩ ⟨Y, hY, hyY⟩,
    refine ⟨X ∪ Y, _, _⟩,
    { rw finset.coe_union,
      exact set.union_subset hX hY },
    rw [finset.coe_union, span_union, mem_sup],
    exact ⟨x, hxX, y, hyY, rfl⟩, },
  { rintros a x ⟨T, hT, h2⟩,
    exact ⟨T, hT, smul_mem _ _ h2⟩ }
end

end

/-- The product of two submodules is a submodule. -/
def prod : submodule R (M × M') :=
{ carrier   := set.prod p q₁,
  smul_mem' := by rintro a ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩,
  .. p.to_add_submonoid.prod q₁.to_add_submonoid }

@[simp] lemma prod_coe :
  (prod p q₁ : set (M × M')) = set.prod p q₁ := rfl

@[simp] lemma mem_prod {p : submodule R M} {q : submodule R M'} {x : M × M'} :
  x ∈ prod p q ↔ x.1 ∈ p ∧ x.2 ∈ q := set.mem_prod

lemma span_prod_le (s : set M) (t : set M') :
  span R (set.prod s t) ≤ prod (span R s) (span R t) :=
span_le.2 $ set.prod_mono subset_span subset_span

@[simp] lemma prod_top : (prod ⊤ ⊤ : submodule R (M × M')) = ⊤ :=
by ext; simp

@[simp] lemma prod_bot : (prod ⊥ ⊥ : submodule R (M × M')) = ⊥ :=
by ext ⟨x, y⟩; simp [prod.zero_eq_mk]

lemma prod_mono {p p' : submodule R M} {q q' : submodule R M'} :
  p ≤ p' → q ≤ q' → prod p q ≤ prod p' q' := prod_mono

@[simp] lemma prod_inf_prod : prod p q₁ ⊓ prod p' q₁' = prod (p ⊓ p') (q₁ ⊓ q₁') :=
set_like.coe_injective set.prod_inter_prod

@[simp] lemma prod_sup_prod : prod p q₁ ⊔ prod p' q₁' = prod (p ⊔ p') (q₁ ⊔ q₁') :=
begin
  refine le_antisymm (sup_le
    (prod_mono le_sup_left le_sup_left)
    (prod_mono le_sup_right le_sup_right)) _,
  simp [set_like.le_def], intros xx yy hxx hyy,
  rcases mem_sup.1 hxx with ⟨x, hx, x', hx', rfl⟩,
  rcases mem_sup.1 hyy with ⟨y, hy, y', hy', rfl⟩,
  refine mem_sup.2 ⟨(x, y), ⟨hx, hy⟩, (x', y'), ⟨hx', hy'⟩, rfl⟩
end

end add_comm_monoid

variables [ring R] [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R M₂] [module R M₃]
variables (p p' : submodule R M) (q q' : submodule R M₂)
variables {r : R} {x y : M}
open set

@[simp] lemma neg_coe : -(p : set M) = p := set.ext $ λ x, p.neg_mem_iff

@[simp] protected lemma map_neg (f : M →ₗ[R] M₂) : map (-f) p = map f p :=
ext $ λ y, ⟨λ ⟨x, hx, hy⟩, hy ▸ ⟨-x, neg_mem _ hx, f.map_neg x⟩,
  λ ⟨x, hx, hy⟩, hy ▸ ⟨-x, neg_mem _ hx, ((-f).map_neg _).trans (neg_neg (f x))⟩⟩

@[simp] lemma span_neg (s : set M) : span R (-s) = span R s :=
calc span R (-s) = span R ((-linear_map.id : M →ₗ[R] M) '' s) : by simp
 ... = map (-linear_map.id) (span R s) : ((-linear_map.id).map_span _).symm
... = span R s : by simp

lemma mem_span_insert' {y} {s : set M} : x ∈ span R (insert y s) ↔ ∃(a:R), x + a • y ∈ span R s :=
begin
  rw mem_span_insert, split,
  { rintro ⟨a, z, hz, rfl⟩, exact ⟨-a, by simp [hz, add_assoc]⟩ },
  { rintro ⟨a, h⟩, exact ⟨-a, _, h, by simp [add_comm, add_left_comm]⟩ }
end

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
  begin rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap], exact le_refl _ end
  begin rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap], exact le_refl _ end

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

/-- If two linear maps are equal on a set `s`, then they are equal on `submodule.span s`.

See also `linear_map.eq_on_span'` for a version using `set.eq_on`. -/
lemma eq_on_span {s : set M} {f g : M →ₛₗ[σ₁₂] M₂} (H : set.eq_on f g s) ⦃x⦄ (h : x ∈ span R s) :
  f x = g x :=
by apply span_induction h H; simp {contextual := tt}

/-- If two linear maps are equal on a set `s`, then they are equal on `submodule.span s`.

This version uses `set.eq_on`, and the hidden argument will expand to `h : x ∈ (span R s : set M)`.
See `linear_map.eq_on_span` for a version that takes `h : x ∈ span R s` as an argument. -/
lemma eq_on_span' {s : set M} {f g : M →ₛₗ[σ₁₂] M₂} (H : set.eq_on f g s) :
  set.eq_on f g (span R s : set M) :=
eq_on_span H

/-- If `s` generates the whole module and linear maps `f`, `g` are equal on `s`, then they are
equal. -/
lemma ext_on {s : set M} {f g : M →ₛₗ[σ₁₂] M₂} (hv : span R s = ⊤) (h : set.eq_on f g s) :
  f = g :=
linear_map.ext (λ x, eq_on_span h (eq_top_iff'.1 hv _))

/-- If the range of `v : ι → M` generates the whole module and linear maps `f`, `g` are equal at
each `v i`, then they are equal. -/
lemma ext_on_range {v : ι → M} {f g : M →ₛₗ[σ₁₂] M₂} (hv : span R (set.range v) = ⊤)
  (h : ∀i, f (v i) = g (v i)) : f = g :=
ext_on hv (set.forall_range_iff.2 h)

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

end

/--
The decreasing sequence of submodules consisting of the ranges of the iterates of a linear map.
-/
@[simps]
def iterate_range {R M} [ring R] [add_comm_group M] [module R M] (f : M →ₗ[R] M) :
  ℕ →ₘ order_dual (submodule R M) :=
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

--set_option trace.class_instances true
/-- The range of a linear map is finite if the domain is finite.
Note: this instance can form a diamond with `subtype.fintype` in the
  presence of `fintype M₂`. -/
instance fintype_range [fintype M] [decidable_eq M₂] [ring_hom_surjective τ₁₂]
  (f : M →ₛₗ[τ₁₂] M₂) : fintype (range f) :=
set.fintype_range f

section
variables (R) (M)

/-- Given an element `x` of a module `M` over `R`, the natural map from
    `R` to scalar multiples of `x`.-/
def to_span_singleton (x : M) : R →ₗ[R] M := linear_map.id.smul_right x

/-- The range of `to_span_singleton x` is the span of `x`.-/
lemma span_singleton_eq_range (x : M) : (R ∙ x) = (to_span_singleton R M x).range :=
submodule.ext $ λ y, by {refine iff.trans _ mem_range.symm, exact mem_span_singleton }

lemma to_span_singleton_one (x : M) : to_span_singleton R M x 1 = x := one_smul _ _

end

/-- The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
def ker (f : M →ₛₗ[τ₁₂] M₂) : submodule R M := comap f ⊥

@[simp] theorem mem_ker {f : M →ₛₗ[τ₁₂] M₂} {y} : y ∈ ker f ↔ f y = 0 := mem_bot R₂

@[simp] theorem ker_id : ker (linear_map.id : M →ₗ[R] M) = ⊥ := rfl

@[simp] theorem map_coe_ker (f : M →ₛₗ[τ₁₂] M₂) (x : ker f) : f x = 0 := mem_ker.1 x.2

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
def iterate_ker {R M} [ring R] [add_comm_group M] [module R M] (f : M →ₗ[R] M) :
  ℕ →ₘ submodule R M :=
⟨λ n, (f ^ n).ker, λ n m w x h, begin
  obtain ⟨c, rfl⟩ := le_iff_exists_add.mp w,
  rw linear_map.mem_ker at h,
  rw [linear_map.mem_ker, add_comm, pow_add, linear_map.mul_apply, h, linear_map.map_zero],
end⟩

end add_comm_monoid

section add_comm_group

variables [semiring R] [semiring R₂] [semiring R₃]
variables [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R₂ M₂] [module R₃ M₃]
variables {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variables [ring_hom_comp_triple τ₁₂ τ₂₃ τ₁₃] [ring_hom_surjective τ₁₂]
include R
open submodule

lemma _root_.submodule.comap_map_eq (f : M →ₛₗ[τ₁₂] M₂) (p : submodule R M) :
  comap f (map f p) = p ⊔ ker f :=
begin
  refine le_antisymm _ (sup_le (le_comap_map _ _) (comap_mono bot_le)),
  rintro x ⟨y, hy, e⟩,
  exact mem_sup.2 ⟨y, hy, x - y, by simpa using sub_eq_zero.2 e.symm, by simp⟩
end

lemma _root_.submodule.comap_map_eq_self {f : M →ₛₗ[τ₁₂] M₂} {p : submodule R M} (h : ker f ≤ p) :
  comap f (map f p) = p :=
by rw [submodule.comap_map_eq, sup_of_le_left h]

theorem map_le_map_iff (f : M →ₛₗ[τ₁₂] M₂) {p p'} :
  map f p ≤ map f p' ↔ p ≤ p' ⊔ ker f :=
by rw [map_le_iff_le_comap, submodule.comap_map_eq]

theorem map_le_map_iff' {f : M →ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥) {p p'} :
  map f p ≤ map f p' ↔ p ≤ p' :=
by rw [map_le_map_iff, hf, sup_bot_eq]

theorem map_injective {f : M →ₛₗ[τ₁₂] M₂} (hf : ker f = ⊥) : injective (map f) :=
λ p p' h, le_antisymm ((map_le_map_iff' hf).1 (le_of_eq h)) ((map_le_map_iff' hf).1 (ge_of_eq h))

theorem map_eq_top_iff {f : M →ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p : submodule R M} :
  p.map f = ⊤ ↔ p ⊔ f.ker = ⊤ :=
by simp_rw [← top_le_iff, ← hf, range_eq_map, map_le_map_iff]

end add_comm_group

section ring

variables [ring R] [ring R₂] [ring R₃]
variables [add_comm_group M] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M] [module R₂ M₂] [module R₃ M₃]
variables {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variables [ring_hom_comp_triple τ₁₂ τ₂₃ τ₁₃]
variables {f : M →ₛₗ[τ₁₂] M₂}
include R
open submodule

theorem sub_mem_ker_iff {x y} : x - y ∈ f.ker ↔ f x = f y :=
by rw [mem_ker, map_sub, sub_eq_zero]

theorem disjoint_ker' {p : submodule R M} :
  disjoint p (ker f) ↔ ∀ x y ∈ p, f x = f y → x = y :=
disjoint_ker.trans
⟨λ H x y hx hy h, eq_of_sub_eq_zero $ H _ (sub_mem _ hx hy) (by simp [h]),
 λ H x h₁ h₂, H x 0 h₁ (zero_mem _) (by simpa using h₂)⟩

theorem inj_of_disjoint_ker {p : submodule R M}
  {s : set M} (h : s ⊆ p) (hd : disjoint p (ker f)) :
  ∀ x y ∈ s, f x = f y → x = y :=
λ x y hx hy, disjoint_ker'.1 hd _ _ (h hx) (h hy)

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

lemma span_singleton_sup_ker_eq_top (f : V →ₗ[K] K) {x : V} (hx : f x ≠ 0) :
  (K ∙ x) ⊔ f.ker = ⊤ :=
eq_top_iff.2 (λ y hy, submodule.mem_sup.2 ⟨(f y * (f x)⁻¹) • x,
  submodule.mem_span_singleton.2 ⟨f y * (f x)⁻¹, rfl⟩,
    ⟨y - (f y * (f x)⁻¹) • x,
      by rw [linear_map.mem_ker, f.map_sub, f.map_smul, smul_eq_mul, mul_assoc,
             inv_mul_cancel hx, mul_one, sub_self],
      by simp only [add_sub_cancel'_right]⟩⟩)

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
comap_subtype_eq_top.2 (le_refl _)

@[simp] theorem ker_of_le (p p' : submodule R M) (h : p ≤ p') : (of_le h).ker = ⊥ :=
by rw [of_le, ker_cod_restrict, ker_subtype]

lemma range_of_le (p q : submodule R M) (h : p ≤ q) : (of_le h).range = comap q.subtype p :=
by rw [← map_top, of_le, linear_map.map_cod_restrict, map_top, range_subtype]

end add_comm_monoid

section ring

variables [ring R] [ring R₂] [add_comm_group M] [add_comm_group M₂] [module R M] [module R₂ M₂]
variables (p p' : submodule R M) (q : submodule R₂ M₂)
variables {τ₁₂ : R →+* R₂}

open linear_map

lemma disjoint_iff_comap_eq_bot {p q : submodule R M} :
  disjoint p q ↔ comap p.subtype q = ⊥ :=
by rw [eq_bot_iff, ← map_le_map_iff' p.ker_subtype, map_bot, map_comap_subtype, disjoint]

/-- If `N ⊆ M` then submodules of `N` are the same as submodules of `M` contained in `N` -/
def map_subtype.rel_iso :
  submodule R p ≃o {p' : submodule R M // p' ≤ p} :=
{ to_fun    := λ p', ⟨map p.subtype p', map_subtype_le p _⟩,
  inv_fun   := λ q, comap p.subtype q,
  left_inv  := λ p', comap_map_eq_self $ by simp,
  right_inv := λ ⟨q, hq⟩, subtype.ext_val $ by simp [map_comap_subtype p, inf_of_le_right hq],
  map_rel_iff'      := λ p₁ p₂, map_le_map_iff' (ker_subtype p) }

/-- If `p ⊆ M` is a submodule, the ordering of submodules of `p` is embedded in the ordering of
submodules of `M`. -/
def map_subtype.order_embedding :
  submodule R p ↪o submodule R M :=
(rel_iso.to_rel_embedding $ map_subtype.rel_iso p).trans (subtype.rel_embedding _ _)

@[simp] lemma map_subtype_embedding_eq (p' : submodule R p) :
  map_subtype.order_embedding p p' = map p.subtype p' := rfl

end ring

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

This is `linear_equiv.of_submodule'` but with `map` on the right instead of `comap` on the left. -/
def of_submodule (p : submodule R M) : p ≃ₛₗ[σ₁₂] ↥(p.map (e : M →ₛₗ[σ₁₂] M₂) : submodule R₂ M₂) :=
{ inv_fun   := λ y, ⟨(e.symm : M₂ →ₛₗ[σ₂₁] M) y, by {
    rcases y with ⟨y', hy⟩, rw submodule.mem_map at hy, rcases hy with ⟨x, hx, hxy⟩, subst hxy,
    simp only [symm_apply_apply, submodule.coe_mk, coe_coe, hx], }⟩,
  left_inv  := λ x, by simp,
  right_inv := λ y, by { apply set_coe.ext, simp, },
  ..((e : M →ₛₗ[σ₁₂] M₂).dom_restrict p).cod_restrict (p.map (e : M →ₛₗ[σ₁₂] M₂))
  (λ x, ⟨x, by simp⟩) }

include σ₂₁
@[simp] lemma of_submodule_apply (p : submodule R M) (x : p) :
  ↑(e.of_submodule p x) = e x := rfl

@[simp] lemma of_submodule_symm_apply (p : submodule R M)
  (x : (p.map (e : M →ₛₗ[σ₁₂] M₂) : submodule R₂ M₂)) : ↑((e.of_submodule p).symm x) = e.symm x :=
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
p ≃ₛₗ[σ₁₂] q := (e.of_submodule p).trans (linear_equiv.of_eq _ _ h)


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
open linear_map

/-- Multiplying by a unit `a` of the ring `R` is a linear equivalence. -/
def smul_of_unit (a : units R) : M ≃ₗ[R] M :=
of_linear ((a:R) • 1 : M →ₗ[R] M) (((a⁻¹ : units R) : R) • 1 : M →ₗ[R] M)
  (by rw [smul_comp, comp_smul, smul_smul, units.mul_inv, one_smul]; refl)
  (by rw [smul_comp, comp_smul, smul_smul, units.inv_mul, one_smul]; refl)

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
open linear_map

/-- Multiplying by a nonzero element `a` of the field `K` is a linear equivalence. -/
def smul_of_ne_zero (a : K) (ha : a ≠ 0) : M ≃ₗ[K] M :=
smul_of_unit $ units.mk0 a ha

section

noncomputable theory
open_locale classical

lemma ker_to_span_singleton {x : M} (h : x ≠ 0) : (to_span_singleton K M x).ker = ⊥ :=
begin
  ext c, split,
  { intros hc, rw submodule.mem_bot, rw mem_ker at hc, by_contra hc',
    have : x = 0,
      calc x = c⁻¹ • (c • x) : by rw [← mul_smul, inv_mul_cancel hc', one_smul]
      ... = c⁻¹ • ((to_span_singleton K M x) c) : rfl
      ... = 0 : by rw [hc, smul_zero],
    tauto },
  { rw [mem_ker, submodule.mem_bot], intros h, rw h, simp }
end

/-- Given a nonzero element `x` of a vector space `M` over a field `K`, the natural
    map from `K` to the span of `x`, with invertibility check to consider it as an
    isomorphism.-/
def to_span_nonzero_singleton (x : M) (h : x ≠ 0) : K ≃ₗ[K] (K ∙ x) :=
linear_equiv.trans
  (linear_equiv.of_injective (to_span_singleton K M x) (ker_eq_bot.1 $ ker_to_span_singleton K M h))
  (of_eq (to_span_singleton K M x).range (K ∙ x)
    (span_singleton_eq_range K M x).symm)

lemma to_span_nonzero_singleton_one (x : M) (h : x ≠ 0) : to_span_nonzero_singleton K M x h 1
  = (⟨x, submodule.mem_span_singleton_self x⟩ : K ∙ x) :=
begin
  apply set_like.coe_eq_coe.mp,
  have : ↑(to_span_nonzero_singleton K M x h 1) = to_span_singleton K M x 1 := rfl,
  rw [this, to_span_singleton_one, submodule.coe_mk],
end

/-- Given a nonzero element `x` of a vector space `M` over a field `K`, the natural map
    from the span of `x` to `K`.-/
abbreviation coord (x : M) (h : x ≠ 0) : (K ∙ x) ≃ₗ[K] K :=
(to_span_nonzero_singleton K M x h).symm

lemma coord_self (x : M) (h : x ≠ 0) :
  (coord K M x h) (⟨x, submodule.mem_span_singleton_self x⟩ : K ∙ x) = 1 :=
by rw [← to_span_nonzero_singleton_one K M x h, symm_apply_apply]

end

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

variables [comm_ring R] [comm_ring R₂]
variables [add_comm_group M] [add_comm_group M₂] [module R M] [module R₂ M₂]
variables [add_comm_group N] [add_comm_group N₂] [module R N] [module R N₂]
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

namespace add_equiv
variables [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid M₂] [module R M₂]

/-- An additive equivalence whose underlying function preserves `smul` is a linear equivalence. -/
def to_linear_equiv (e : M ≃+ M₂) (h : ∀ (c : R) x, e (c • x) = c • e x) : M ≃ₗ[R] M₂ :=
{ map_smul' := h, .. e, }

@[simp] lemma coe_to_linear_equiv (e : M ≃+ M₂) (h : ∀ (c : R) x, e (c • x) = c • e x) :
  ⇑(e.to_linear_equiv h) = e :=
rfl

@[simp] lemma coe_to_linear_equiv_symm (e : M ≃+ M₂) (h : ∀ (c : R) x, e (c • x) = c • e x) :
  ⇑(e.to_linear_equiv h).symm = e.symm :=
rfl

end add_equiv

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
open linear_map

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

namespace linear_equiv

variables [semiring R] [add_comm_monoid M] [module R M]
variables (R M)

instance automorphism_group : group (M ≃ₗ[R] M) :=
{ mul := λ f g, g.trans f,
  one := linear_equiv.refl R M,
  inv := λ f, f.symm,
  mul_assoc := λ f g h, by {ext, refl},
  mul_one := λ f, by {ext, refl},
  one_mul := λ f, by {ext, refl},
  mul_left_inv := λ f, by {ext, exact f.left_inv x} }

/-- Restriction from `R`-linear automorphisms of `M` to `R`-linear endomorphisms of `M`,
promoted to a monoid hom. -/
def automorphism_group.to_linear_map_monoid_hom :
  (M ≃ₗ[R] M) →* (M →ₗ[R] M) :=
{ to_fun := coe,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

/-- The tautological action by `M ≃ₗ[R] M` on `M`.

This generalizes `function.End.apply_mul_action`. -/
instance apply_distrib_mul_action : distrib_mul_action (M ≃ₗ[R] M) M :=
{ smul := ($),
  smul_zero := linear_equiv.map_zero,
  smul_add := linear_equiv.map_add,
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] protected lemma smul_def (f : M ≃ₗ[R] M) (a : M) :
  f • a = f a := rfl

/-- `linear_equiv.apply_distrib_mul_action` is faithful. -/
instance apply_has_faithful_scalar : has_faithful_scalar (M ≃ₗ[R] M) M :=
⟨λ _ _, linear_equiv.ext⟩

instance apply_smul_comm_class : smul_comm_class R (M ≃ₗ[R] M) M :=
{ smul_comm := λ r e m, (e.map_smul r m).symm }

instance apply_smul_comm_class' : smul_comm_class (M ≃ₗ[R] M) R M :=
{ smul_comm := linear_equiv.map_smul }

end linear_equiv

namespace linear_map

variables [semiring R] [add_comm_monoid M] [module R M]
variables (R M)

/-- The group of invertible linear maps from `M` to itself -/
@[reducible] def general_linear_group := units (M →ₗ[R] M)

namespace general_linear_group
variables {R M}

instance : has_coe_to_fun (general_linear_group R M) := by apply_instance

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

end general_linear_group

end linear_map

namespace submodule
variables [ring R] [add_comm_group M] [module R M]

instance : is_modular_lattice (submodule R M) :=
⟨λ x y z xz a ha, begin
  rw [mem_inf, mem_sup] at ha,
  rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩,
  rw mem_sup,
  refine ⟨b, hb, c, mem_inf.2 ⟨hc, _⟩, rfl⟩,
  rw [← add_sub_cancel c b, add_comm],
  apply z.sub_mem haz (xz hb),
end⟩

end submodule
