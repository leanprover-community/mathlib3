/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin
-/

import linear_algebra.tensor_product.construction
import linear_algebra.finsupp

noncomputable theory

open_locale tensor_product big_operators

namespace tensor_product

variables {R M N T Q Q' : Type*}
variables [comm_semiring R]
variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid T] [add_comm_monoid Q]
variables [add_comm_monoid Q']
variables [module R M] [module R N] [module R T] [module R Q] [module R Q']
variables [is_tensor_product R M N T]

section lift

open function (injective surjective)

include T

namespace construction

lemma lift_injective : injective (lift (tmul R M N) : M ⊗ₜ[R] N → T) :=
begin
  rintros ⟨t₁⟩ ⟨t₂⟩ h,
  erw [add_con.eq, ← @is_tensor_product.add_con R M N T _ _ _ _ _ _ _ _],
  exact h
end

lemma lift_surjective : surjective (lift (tmul R M N) : M ⊗ₜ[R] N → T) :=
begin
  intros t,
  have ht : t ∈ (⊤ : submodule R T) := submodule.mem_top,
  rw [← @is_tensor_product.span_tmul R M N T _ _ _ _ _ _ _ _, finsupp.mem_span_iff_total] at ht,
  obtain ⟨l, rfl⟩ := ht,
  letI := construction.is_tensor_product R M N,
  let c : {t : T | ∃ (x : M) (y : N), x ⊗ y = t} → (M ⊗ₜ[R] N) :=
    λ x, (x.2.some ⊗[R] x.2.some_spec.some : M ⊗ₜ[R] N),
  use finsupp.total _ (M ⊗ₜ[R] N) R c l,
  rw [← linear_map.comp_apply, ← finsupp.lmap_domain_total R id],
  { simp only [linear_map.comp_id, finsupp.lmap_domain_id], },
  { intro t,
    simp only [tmul_apply_apply, id.def, lift.tmul, subtype.coe_mk],
    exact t.2.some_spec.some_spec }
end

variables (R M N T)

/-- The canonical linear equivalence between the construction `M ⊗ₜ[R] N`
and a tensor product `T` provided by `is_tensor_product R M N T`. -/
def equiv : M ⊗ₜ[R] N ≃ₗ[R] T :=
linear_equiv.of_bijective (lift (tmul R M N)) lift_injective lift_surjective

@[simp] lemma coe_equiv : (equiv R M N T : M ⊗ₜ[R] N →ₗ[R] T) = lift (tmul R M N) := rfl

local attribute [instance] construction.is_tensor_product

@[simp] lemma equiv_apply (x : M) (y : N) : equiv R M N T (x ⊗[R] y) = x ⊗[R] y :=
lift.tmul x y

@[simp] lemma equiv_symm_apply (x : M) (y : N) : (equiv R M N T).symm (x ⊗[R] y) = x ⊗[R] y :=
by simp only [linear_equiv.symm_apply_eq, equiv_apply]

end construction

variables (T)

def lift (f : M →ₗ[R] N →ₗ[R] Q) : T →ₗ[R] Q :=
(construction.lift f) ∘ₗ (construction.equiv R M N T).symm

variables {T} (f : M →ₗ[R] N →ₗ[R] Q)

lemma lift_tmul : lift T (tmul R M N) = linear_map.id :=
by { ext1 t, exact (construction.equiv R M N T).apply_symm_apply t }

@[simp] lemma lift_apply (x y) : lift T f (x ⊗[R] y) = f x y :=
begin
  let φ := construction.equiv R M N T,
  show construction.lift f (φ.symm (x ⊗[R] y)) = f x y,
  letI := construction.is_tensor_product R M N,
  rw [← construction.equiv_apply, φ.symm_apply_apply],
  exact construction.lift.tmul x y
end

variables (M N)

lemma ext' (g h : T →ₗ[R] Q)
  (H : ∀ (x:M) (y:N), g (x ⊗[R] y) = h (x ⊗[R] y)) : g = h :=
begin
  let φ := construction.equiv R M N T,
  apply linear_map.ext, intro t,
  rcases φ.surjective t with ⟨t, rfl⟩,
  show (g ∘ₗ ↑φ) t = (h ∘ₗ ↑φ) t, congr' 1,
  apply construction.ext',
  simpa only [linear_map.comp_apply, construction.coe_equiv, construction.lift.tmul] using H
end

variables {M N}

lemma lift.unique (g : T →ₗ[R] Q) (H : ∀ x y, g (x ⊗[R] y) = f x y) :
  g = lift T f :=
ext' M N g (lift T f) $ λ m n , by rw [H, lift_apply]

lemma lift_compr₂ (g : Q →ₗ[R] Q') : lift T (f.compr₂ g) = g.comp (lift T f) :=
eq.symm $ lift.unique _ _ $ λ x y, by simp

variables (M N)

lemma lift_tmul_compr₂ (f : T →ₗ[R] Q) : lift T ((tmul R M N).compr₂ f) = f :=
ext' M N _ _ $ λ m n, by simp only [lift_apply, linear_map.compr₂_apply, tmul_apply_apply]

end lift

variables (M N)

lemma ext (g h : T →ₗ[R] Q) (H : (tmul R M N ).compr₂ g = (tmul R M N).compr₂ h) :
  g = h :=
by rw [← lift_tmul_compr₂ M N g, H, lift_tmul_compr₂]

variables {M N}

variables (R M N T Q)

/-- Linearly constructing a linear map `M ⊗[R] N → Q` given a bilinear map `M → N → Q`
with the property that its composition with the canonical bilinear map `M → N → M ⊗[R] N` is
the given bilinear map `M → N → Q`. -/
def uncurry : (M →ₗ[R] N →ₗ[R] Q) →ₗ[R] T →ₗ[R] Q :=
linear_map.flip $ lift T $ (linear_map.lflip _ _ _ _).comp linear_map.id.flip

variables {R M N T Q}

@[simp] lemma uncurry_apply (f : M →ₗ[R] N →ₗ[R] Q) (m : M) (n : N) :
  uncurry R M N T Q f (m ⊗[R] n) = f m n :=
by rw [uncurry, linear_map.flip_apply, lift_apply]; refl

variables (R M N T Q)

/-- A linear equivalence constructing a linear map `M ⊗[R] N → Q` given a bilinear map `M → N → Q`
with the property that its composition with the canonical bilinear map `M → N → M ⊗[R] N` is
the given bilinear map `M → N → Q`. -/
def lift.equiv : (M →ₗ[R] N →ₗ[R] Q) ≃ₗ[R] (T →ₗ[R] Q) :=
{ to_fun := uncurry R M N T Q,
  inv_fun := λ f, (tmul R M N).compr₂ f,
  left_inv := λ f, linear_map.ext₂ $ λ m n,
    by simp only [uncurry_apply, linear_map.compr₂_apply, tmul_apply_apply],
  right_inv := λ f, ext' M N _ _ $ λ m n,
    by simp only [uncurry_apply, linear_map.compr₂_apply, tmul_apply_apply],
  .. uncurry R M N T Q }

@[simp] lemma lift.equiv_apply (f : M →ₗ[R] N →ₗ[R] Q) (m : M) (n : N) :
  lift.equiv R M N T Q f (m ⊗[R] n) = f m n :=
uncurry_apply f m n

@[simp] lemma lift.equiv_symm_apply (f : T →ₗ[R] Q) (m : M) (n : N) :
  (lift.equiv R M N T Q).symm f m n = f (m ⊗[R] n) :=
rfl

/-- Given a linear map `M ⊗[R] N → P`, compose it with the canonical bilinear map `M → N → M ⊗[R] N` to
form a bilinear map `M → N → P`. -/
def lcurry : (T →ₗ[R] Q) →ₗ[R] M →ₗ[R] N →ₗ[R] Q :=
(lift.equiv R M N T Q).symm

variables {R M N T Q}

@[simp] lemma lcurry_apply (f : T →ₗ[R] Q) (m : M) (n : N) :
  lcurry R M N T Q f m n = f (m ⊗[R] n) := rfl

variables (M N)

/-- Given a linear map `M ⊗[R] N → P`, compose it with the canonical bilinear map `M → N → M ⊗[R] N` to
form a bilinear map `M → N → P`. -/
def curry (f : T →ₗ[R] Q) : M →ₗ[R] N →ₗ[R] Q := lcurry R M N T Q f

variables {M N}

@[simp] lemma curry_apply (f : T →ₗ[R] Q) (m : M) (n : N) :
  curry M N f m n = f (m ⊗[R] n) := rfl

lemma curry_injective : function.injective (curry M N : (T →ₗ[R] Q) → (M →ₗ[R] N →ₗ[R] Q)) :=
λ g h H, ext _ _ _ _ H

variables {S : Type*} [add_comm_monoid S] [module R S]

section
local attribute [instance] construction.is_tensor_product

lemma ext_threefold {g h : (M ⊗ₜ[R] N) ⊗ₜ[R] Q →ₗ[R] Q'}
  (H : ∀ (x:M) (y:N) (z:Q), g ((x ⊗[R] y) ⊗[R] z) = h ((x ⊗[R] y) ⊗[R] z)) : g = h :=
begin
  refine ext (M ⊗ₜ[R] N) Q g h _,
  refine ext M N _ _ _,
  ext x y z,
  exact H x y z
end

-- We'll need this one for checking the pentagon identity!
lemma ext_fourfold {g h : ((M ⊗ₜ[R] N) ⊗ₜ[R] Q) ⊗ₜ[R] Q' →ₗ[R] S}
  (H : ∀ (w:M) (x:N) (y:Q) (z:Q'),
    g (((w ⊗[R] x) ⊗[R] y) ⊗[R] z) = h (((w ⊗[R] x) ⊗[R] y) ⊗[R] z)) : g = h :=
begin
  refine ext ((M ⊗ₜ[R] N) ⊗ₜ[R] Q) Q' _ _ _,
  refine ext (M ⊗ₜ[R] N) Q _ _ _,
  refine ext M N _ _ _,
  ext w x y z,
  exact H w x y z,
end

end

variables (R M N T Q) [is_tensor_product R M N Q]

/-- If two modules `Q` and `S` are both an `R`-linear tensor product of `M` and `N`,
then they are canonically `R`-linearly isomorphic. -/
def equiv : T ≃ₗ[R] Q :=
(construction.equiv R M N T).symm ≪≫ₗ (construction.equiv R M N Q)

@[simp] lemma equiv_symm : (equiv R M N T Q).symm = equiv R M N Q T := rfl

@[simp] lemma equiv_apply (x : M) (y : N) : equiv R M N T Q (x ⊗[R] y) = x ⊗[R] y :=
by rw [equiv, linear_equiv.trans_apply, construction.equiv_symm_apply, construction.equiv_apply]

@[simp] lemma equiv_symm_apply (x : M) (y : N) : (equiv R M N T Q).symm (x ⊗[R] y) = x ⊗[R] y :=
equiv_apply R M N Q T x y

end tensor_product
