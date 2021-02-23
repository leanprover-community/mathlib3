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
  - `linear_map.pi`
  - `linear_map.single`
- pi types in the domain:
  - `linear_map.proj`
- `linear_map.diag`

-/

universes u v w x y z u' v' w' y'
variables {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}
variables {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x}

namespace linear_map

open function submodule
open_locale big_operators

universe i
variables [semiring R] [add_comm_monoid M₂] [semimodule R M₂] [add_comm_monoid M₃] [semimodule R M₃]
{φ : ι → Type i} [∀i, add_comm_monoid (φ i)] [∀i, semimodule R (φ i)]

/-- `pi` construction for linear functions. From a family of linear functions it produces a linear
function into a family of modules. -/
def pi (f : Πi, M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (Πi, φ i) :=
⟨λc i, f i c, λ c d, funext $ λ i, (f i).map_add _ _, λ c d, funext $ λ i, (f i).map_smul _ _⟩

@[simp] lemma pi_apply (f : Πi, M₂ →ₗ[R] φ i) (c : M₂) (i : ι) :
  pi f c i = f i c := rfl

lemma ker_pi (f : Πi, M₂ →ₗ[R] φ i) : ker (pi f) = (⨅i:ι, ker (f i)) :=
by ext c; simp [funext_iff]; refl

lemma pi_eq_zero (f : Πi, M₂ →ₗ[R] φ i) : pi f = 0 ↔ (∀i, f i = 0) :=
by simp only [linear_map.ext_iff, pi_apply, funext_iff]; exact ⟨λh a b, h b a, λh a b, h b a⟩

lemma pi_zero : pi (λi, 0 : Πi, M₂ →ₗ[R] φ i) = 0 :=
by ext; refl

lemma pi_comp (f : Πi, M₂ →ₗ[R] φ i) (g : M₃ →ₗ[R] M₂) : (pi f).comp g = pi (λi, (f i).comp g) :=
rfl

/-- The projections from a family of modules are linear maps. -/
def proj (i : ι) : (Πi, φ i) →ₗ[R] φ i :=
⟨ λa, a i, assume f g, rfl, assume c f, rfl ⟩

@[simp] lemma proj_apply (i : ι) (b : Πi, φ i) : (proj i : (Πi, φ i) →ₗ[R] φ i) b = b i := rfl

lemma proj_pi (f : Πi, M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i :=
ext $ assume c, rfl

lemma infi_ker_proj : (⨅i, ker (proj i) : submodule R (Πi, φ i)) = ⊥ :=
bot_unique $ submodule.le_def'.2 $ assume a h,
begin
  simp only [mem_infi, mem_ker, proj_apply] at h,
  exact (mem_bot _).2 (funext $ assume i, h i)
end

lemma apply_single [add_comm_monoid M] [semimodule R M] [decidable_eq ι]
  (f : Π i, φ i →ₗ[R] M) (i j : ι) (x : φ i) :
  f j (pi.single i x j) = pi.single i (f i x) j :=
pi.apply_single (λ i, f i) (λ i, (f i).map_zero) _ _ _

/-- The `linear_map` version of `add_monoid_hom.single` and `pi.single`. -/
def single [decidable_eq ι] (i : ι) : φ i →ₗ[R] (Πi, φ i) :=
{ to_fun := pi.single i,
  map_smul' := pi.single_smul i,
  .. add_monoid_hom.single φ i}

@[simp] lemma coe_single [decidable_eq ι] (i : ι) :
  ⇑(single i : φ i →ₗ[R] (Π i, φ i)) = pi.single i := rfl

/-- The linear equivalence between linear functions on a finite product of modules and
families of functions on these modules. See note [bundled maps over different rings]. -/
def lsum (S) [add_comm_monoid M] [semimodule R M] [fintype ι] [decidable_eq ι]
  [semiring S] [semimodule S M]  [smul_comm_class R S M] :
  (Π i, φ i →ₗ[R] M) ≃ₗ[S] ((Π i, φ i) →ₗ[R] M) :=
{ to_fun := λ f, ∑ i : ι, (f i).comp (proj i),
  inv_fun := λ f i, f.comp (single i),
  map_add' := λ f g, by simp only [pi.add_apply, add_comp, finset.sum_add_distrib],
  map_smul' := λ c f, by simp only [pi.smul_apply, smul_comp, finset.smul_sum],
  left_inv := λ f,
    begin
      ext i x,
      suffices : ∑ j, pi.single i (f i x) j = f i x, by simpa [apply_single],
      exact (finset.sum_dite_eq' _ _ _).trans (if_pos $ finset.mem_univ i)
    end,
  right_inv := λ f,
    begin
      ext,
      suffices : f (∑ j, pi.single j (x j)) = f x, by simpa [apply_single],
      rw finset.univ_sum_single
    end }

section ext

variables [fintype ι] [decidable_eq ι] [add_comm_monoid M] [semimodule R M]
  {f g : (Π i, φ i) →ₗ[R] M}

lemma pi_ext (h : ∀ i x, f (pi.single i x) = g (pi.single i x)) :
  f = g :=
to_add_monoid_hom_injective $ add_monoid_hom.functions_ext _ _ _ h

lemma pi_ext_iff : f = g ↔ ∀ i x, f (pi.single i x) = g (pi.single i x) :=
⟨λ h i x, h ▸ rfl, pi_ext⟩

/-- This is used as the ext lemma instead of `linear_map.pi_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[ext] lemma pi_ext' (h : ∀ i, f.comp (single i) = g.comp (single i)) : f = g :=
begin
  refine pi_ext (λ i x, _),
  convert linear_map.congr_fun (h i) x
end

lemma pi_ext'_iff : f = g ↔ ∀ i, f.comp (single i) = g.comp (single i) :=
⟨λ h i, h ▸ rfl, pi_ext'⟩

end ext

section
variables (R φ)

/-- If `I` and `J` are disjoint index sets, the product of the kernels of the `J`th projections of
`φ` is linearly equivalent to the product over `I`. -/
def infi_ker_proj_equiv {I J : set ι} [decidable_pred (λi, i ∈ I)]
  (hd : disjoint I J) (hu : set.univ ⊆ I ∪ J) :
  (⨅i ∈ J, ker (proj i) : submodule R (Πi, φ i)) ≃ₗ[R] (Πi:I, φ i) :=
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

lemma update_apply (f : Πi, M₂ →ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ →ₗ[R] φ i) :
  (update f i b j) c = update (λi, f i c) i (b c) j :=
begin
  by_cases j = i,
  { rw [h, update_same, update_same] },
  { rw [update_noteq h, update_noteq h] }
end

end

end linear_map
