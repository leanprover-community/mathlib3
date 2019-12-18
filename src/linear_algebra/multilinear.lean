/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import linear_algebra.basic

/-!
# Multilinear maps

-/

open_locale classical
noncomputable theory

universes u v w u'
variables {α : Type*} {R : Type u} {ι : Type u'} {M₁ : Type v} {M₂ : Type w}

section replace_at

/-- `replace_at f i₀ x` is the function equal to `f`, except at `i₀` where it is equal to `x`. -/
def replace_at (f : ι → α) (i₀ : ι) (x : α) (i : ι) : α :=
if i = i₀ then x else f i

@[simp] lemma replace_at_of_ne (f : ι → α) {i j : ι} (h : j ≠ i) (x : α) :
  replace_at f i x j = f j :=
if_neg h

@[simp] lemma replace_at_of_eq (f : ι → α) {i j : ι} (h : j = i) (x : α) :
  replace_at f i x j = x :=
if_pos h

@[simp] lemma replace_at_eq (f : ι → α) (i : ι) (x : α) :
  replace_at f i x i = x :=
by simp

lemma replace_at_eq_self (f : ι → α) (i : ι) :
  replace_at f i (f i) = f :=
by { ext j, by_cases h : j = i; simp [h, replace_at_of_ne, replace_at_of_eq] }

end replace_at

/-- Multilinear maps over the ring `R`, from `(ι → M₁)` to `M₂` where `M₁` and `M₂` are modules
over `R`. -/
structure multilinear_map (R : Type u) (ι : Type u') (M₁ : Type v) (M₂ : Type w)
  [ring R] [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂] :=
(to_fun : (ι → M₁) → M₂)
(add : ∀f i x y,
  to_fun (replace_at f i (x + y)) = to_fun (replace_at f i x) + to_fun (replace_at f i y))
(smul : ∀f i x (c : R), to_fun (replace_at f i (c • x)) = c • to_fun (replace_at f i x))

namespace multilinear_map

section ring

variables [ring R] [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂]
(m m' : multilinear_map R ι M₁ M₂)

instance : has_coe_to_fun (multilinear_map R ι M₁ M₂) := ⟨_, to_fun⟩

@[ext] theorem ext {m m' : multilinear_map R ι M₁ M₂} (H : ∀ x, m x = m' x) : m = m' :=
by cases m; cases m'; congr'; exact funext H

@[simp] lemma map_add (f : ι → M₁) (i : ι) (x y : M₁) :
  m (replace_at f i (x + y)) = m (replace_at f i x) + m (replace_at f i y) :=
m.add f i x y

@[simp] lemma map_smul (f : ι → M₁) (i : ι) (x : M₁) (c : R) :
  m (replace_at f i (c • x)) = c • m (replace_at f i x) :=
m.smul f i x c

lemma map_coord_zero {f : ι → M₁} (i : ι) (h : f i = 0) : m f = 0 :=
begin
  have : (0 : R) • (0 : M₁) = 0, by simp,
  rw [← replace_at_eq_self f i, h, ← this, m.map_smul, zero_smul]
end

@[simp] lemma map_zero [nonempty ι] : m 0 = 0 :=
begin
  obtain ⟨i, _⟩ : ∃i:ι, i ∈ set.univ := set.exists_mem_of_nonempty ι,
  exact map_coord_zero m i rfl
end

instance : has_add (multilinear_map R ι M₁ M₂) :=
⟨λm m', ⟨λx, m x + m' x, λf i x y, by simp, λf i x c, by simp [smul_add]⟩⟩

@[simp] lemma add_apply (f : ι → M₁) : (m + m') f = m f + m' f := rfl

instance : has_neg (multilinear_map R ι M₁ M₂) :=
⟨λ m, ⟨λ f, - m f, λf i x y, by simp, λf i x c, by simp⟩⟩

@[simp] lemma neg_apply (f : ι → M₁) : (-m) f = - (m f) := rfl

instance : has_zero (multilinear_map R ι M₁ M₂) :=
⟨⟨λ _, 0, λf i x y, by simp, λf i x c, by simp⟩⟩

@[simp] lemma zero_apply (f : ι → M₁) : (0 : multilinear_map R ι M₁ M₂) f = 0 := rfl

instance : add_comm_group (multilinear_map R ι M₁ M₂) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..};
   intros; ext; simp

/-- If `m` is a multilinear map, then `m.to_linear_map f i` is the linear map obtained by fixing all
coordinates but `i` equal to those of `f`, and varying the `i`-th coordinate. -/
def to_linear_map (f : ι → M₁) (i : ι) : M₁ →ₗ[R] M₂ :=
{ to_fun := λx, m (replace_at f i x),
  add := λx y, by simp,
  smul := λx c, by simp }

end ring

section comm_ring

variables [comm_ring R] [add_comm_group M₁] [add_comm_group M₂]
[module R M₁] [module R M₂]
(m m' : multilinear_map R ι M₁ M₂)

instance : has_scalar R (multilinear_map R ι M₁ M₂) := ⟨λ c m,
  ⟨λ f, c • m f, λf i x y, by simp [smul_add], λf i x d, by simp [smul_smul, mul_comm]⟩⟩

@[simp] lemma smul_apply (c : R) (f : ι → M₁) : (c • m) f = c • m f := rfl

instance : module R (multilinear_map R ι M₁ M₂) :=
module.of_core $ by refine { smul := (•), ..};
  intros; ext; simp [smul_add, add_smul, smul_smul]

def zou (n : ℕ) : (M₁ →ₗ[R] (multilinear_map R (fin n) M₁ M₂)) ≃ₗ (multilinear_map R (fin (n+1)) M₁ M₂) :=
{ to_fun := λm, ⟨λf, m (f (fin.last n)) (f ∘ fin.cast_succ),
    λf i x y, begin
      by_cases h : i = fin.last n,
      { have : ∀z, replace_at f (fin.last n) z ∘ fin.cast_succ = replace_at f (fin.last n) x ∘ fin.cast_succ :=
        λz, by { ext j, simp [fin.cast_succ_ne_last j] },
        rw [h, this (x+y), this y, replace_at_eq, replace_at_eq, replace_at_eq, m.map_add],
        refl },
      { rw [replace_at_of_ne _ (ne.symm h), replace_at_of_ne _ (ne.symm h),
            replace_at_of_ne _ (ne.symm h)],
        simp,  }
    end, sorry⟩,

}

end comm_ring

end multilinear_map
