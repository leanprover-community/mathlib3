/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser
-/
import linear_algebra.basic

/-!
# Pi types of semimodules

This file defines constructors for linear maps whose domains or codomains are pi types.

It contains theorems relating these to each other, as well as to `linear_map.ker`.

## Main definitions

- pi types in the codomain:
  - `linear_map.proj`
  - `linear_map.pi`
- `linear_map.diag`

-/

universes u v w x y z u' v' w' y'
variables {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}
variables {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x}

namespace linear_map

open function
open submodule

universe i
variables (S : Type*) [semiring S]
variables [semiring R] [add_comm_monoid M₂] [semimodule R M₂] [add_comm_monoid M₃] [semimodule R M₃]
{φ : ι → Type i} [∀i, add_comm_monoid (φ i)] [∀i, semimodule R (φ i)]

/-- `pi` construction for linear functions. From a family of linear functions with the same domain
it produces a linear function into a family of modules. -/
def pi (f : Π i, M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (Π i, φ i) :=
⟨λc i, f i c, λ c d, funext $ λ i, (f i).map_add _ _, λ c d, funext $ λ i, (f i).map_smul _ _⟩

@[simp] lemma pi_apply (f : Π i, M₂ →ₗ[R] φ i) (c : M₂) (i : ι) :
  pi f c i = f i c := rfl

/-- The projections from a family of modules are linear maps. -/
def proj (i : ι) : (Π i, φ i) →ₗ[R] φ i :=
⟨ λa, a i, assume f g, rfl, assume c f, rfl ⟩

@[simp] lemma proj_apply (i : ι) (b : Π i, φ i) : (proj i : (Π i, φ i) →ₗ[R] φ i) b = b i := rfl

@[simp] lemma proj_comp_pi (f : Π i, M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
ext $ assume c, rfl

/-- This is the `pi` version of `linear_map.prod_equiv`. -/
def pi_equiv
  [semimodule S M₂] [Π i, semimodule S (φ i)] [∀ i, smul_comm_class R S (φ i)] :
  (Π i, M₂ →ₗ[R] φ i) ≃ₗ[S] (M₂ →ₗ[R] (Π i, φ i)) :=
{ to_fun := pi,
  inv_fun := λ f i, (proj i).comp f,
  left_inv := λ f, funext (proj_comp_pi _),
  right_inv := λ f, by { ext, refl },
  map_add' := λ a b, rfl,
  map_smul' := λ a b, rfl }

/-- co-`pi` construction for linear functions. From a family of linear functions with the same
codomain it produces a linear function from a family of modules. -/
def co_pi [fintype ι] (f : Π i, φ i →ₗ[R] M₂) : (Π i, φ i) →ₗ[R] M₂ :=
{ to_fun := λ c, finset.univ.sum (λ i, f i (c i)),
  map_add' := λ c d, begin
    rw [←finset.sum_add_distrib, finset.sum_congr rfl (λ x hx, _)],
    exact (f x).map_add _ _,
  end,
  map_smul' := λ c d, begin
    rw [finset.smul_sum, finset.sum_congr rfl (λ x hx, _)],
    exact (f x).map_smul _ _,
  end}

@[simp] lemma co_pi_apply [fintype ι] (f : Π i, φ i →ₗ[R] M₂) (x : Π i, φ i):
  (co_pi f : _ →ₗ[R] _) x = finset.univ.sum (λ i, f i (x i)) := rfl

/-- `pi.single` as a linear_map -/
def single [decidable_eq ι] (i : ι) : φ i →ₗ[R] (Π i, φ i) :=
{ to_fun := λ x, pi.single i x,
  map_add' := λ x y, begin
    ext j,
    by_cases h : j = i,
    { rw h, simp [h], },
    { simp [pi.single_eq_of_ne h], }
  end,
  map_smul' := λ x y, begin
    ext j,
    by_cases h : j = i,
    { rw h, simp [h], },
    { simp [pi.single_eq_of_ne h], }
  end}

@[simp] lemma single_apply [decidable_eq ι] (i : ι) (x : φ i) :
  (single i : _ →ₗ[R] _) x = pi.single i x := rfl

@[simp] lemma co_pi_comp_single [fintype ι] [decidable_eq ι] (f : Π i, φ i →ₗ[R] M₂) (i : ι) :
  (co_pi f).comp (single i) = f i :=
ext $ λ x, begin
  intros,
  simp only [single_apply, co_pi_apply, linear_map.comp_apply],
  rw ←finset.insert_erase (finset.mem_univ i),
  rw finset.sum_insert,
  { convert add_zero _,
    { apply finset.sum_eq_zero,
      simp {contextual := tt}, },
    simp },
  simp,
end

def co_pi_equiv
  [fintype ι] [decidable_eq ι]
  [semimodule S M₂] [Π i, semimodule S (φ i)] [smul_comm_class R S M₂] :
  (Π i, φ i →ₗ[R] M₂) ≃ₗ[S] (Π i, φ i) →ₗ[R] M₂ :=
{ to_fun := co_pi,
  inv_fun := λ f i, f.comp (single i),
  left_inv := λ f, funext (co_pi_comp_single _),
  right_inv := λ f, by { ext, simp },
  map_add' := λ a b, rfl,
  map_smul' := λ a b, rfl }

lemma ker_pi (f : Π i, M₂ →ₗ[R] φ i) : ker (pi f) = (⨅i:ι, ker (f i)) :=
by ext c; simp [funext_iff]; refl

lemma pi_eq_zero (f : Π i, M₂ →ₗ[R] φ i) : pi f = 0 ↔ (∀i, f i = 0) :=
by simp only [linear_map.ext_iff, pi_apply, funext_iff]; exact ⟨λh a b, h b a, λh a b, h b a⟩

lemma pi_zero : pi (λi, 0 : Π i, M₂ →ₗ[R] φ i) = 0 :=
by ext; refl

lemma pi_comp (f : Π i, M₂ →ₗ[R] φ i) (g : M₃ →ₗ[R] M₂) : (pi f).comp g = pi (λi, (f i).comp g) :=
rfl

lemma infi_ker_proj : (⨅i, ker (proj i) : submodule R (Π i, φ i)) = ⊥ :=
bot_unique $ submodule.le_def'.2 $ assume a h,
begin
  simp only [mem_infi, mem_ker, proj_apply] at h,
  exact (mem_bot _).2 (funext $ assume i, h i)
end

section
variables (R φ)

/-- If `I` and `J` are disjoint index sets, the product of the kernels of the `J`th projections of
`φ` is linearly equivalent to the product over `I`. -/
def infi_ker_proj_equiv {I J : set ι} [decidable_pred (λi, i ∈ I)]
  (hd : disjoint I J) (hu : set.univ ⊆ I ∪ J) :
  (⨅i ∈ J, ker (proj i) : submodule R (Π i, φ i)) ≃ₗ[R] (Π i:I, φ i) :=
begin
  refine linear_equiv.of_linear
    (pi $ λi, (proj (i:ι)).comp (submodule.subtype _))
    (cod_restrict _ (pi $ λi, if h : i ∈ I then proj (⟨i, h⟩ : I) else 0) _) _ _,
  { assume b,
    simp only [mem_infi, mem_ker, funext_iff, proj_apply, pi_apply],
    assume j hjJ,
    have : j ∉ I := assume hjI, hd ⟨hjI, hjJ⟩,
    rw [dif_neg this, zero_apply] },
  { simp only [pi_comp, comp_assoc, subtype_comp_cod_restrict, proj_pi, dif_pos, subtype.coe_prop],
    ext b ⟨j, hj⟩, refl },
  { ext1 ⟨b, hb⟩,
    apply subtype.ext,
    ext j,
    have hb : ∀i ∈ J, b i = 0,
    { simpa only [mem_infi, mem_ker, proj_apply] using (mem_infi _).1 hb },
    simp only [comp_apply, pi_apply, id_apply, proj_apply, subtype_apply, cod_restrict_apply],
    split_ifs,
    { refl },
    { exact (hb _ $ (hu trivial).resolve_left h).symm } }
end
end

section
variable [decidable_eq ι]

/-- `diag i j` is the identity map if `i = j`. Otherwise it is the constant 0 map. -/
def diag (i j : ι) : φ i →ₗ[R] φ j :=
@function.update ι (λj, φ i →ₗ[R] φ j) _ 0 i id j

lemma update_apply (f : Π i, M₂ →ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ →ₗ[R] φ i) :
  (update f i b j) c = update (λi, f i c) i (b c) j :=
begin
  by_cases j = i,
  { rw [h, update_same, update_same] },
  { rw [update_noteq h, update_noteq h] }
end

end

end linear_map
