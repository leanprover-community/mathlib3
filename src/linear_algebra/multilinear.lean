/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import linear_algebra.basic

/-!
# Multilinear maps

We define multilinear maps as maps from `ι → M₁` to `M₂` which are linear in each coordinate. Here,
`M₁` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type (although some statements
will require it to be a fintype). This space, denoted by `multilinear_map R ι M₁ M₂`, inherits a
module structure by pointwise addition and multiplication.

## Main definitions

* `multilinear_map R ι M₁ M₂` is the space of multilinear maps from `ι → M₁` to `M₂`.
* `linear_to_multilinear_equiv_multilinear R M₁ M₂ n` registers the linear equivalence between
  the space of linear maps from `M₁` to the space of multilinear maps on `M₁^n`, and the space of
  multilinear maps on `M₁^(n+1)`, obtained by separating the first variable from the other ones.
* `multilinear_to_linear_equiv_multilinear R M₁ M₂ n` registers the linear equivalence between
  the space of multilinear maps on `M₁^n` to the space of linear maps on `M₁`, and the space of
  multilinear maps on `M₁^(n+1)`, obtained by separating the first variable from the other ones.

## Implementation notes

Expressing that a map is linear along the `i`-th coordinate when all other coordinates are fixed
can be done in two (equivalent) different ways:
* fixing a function `f : ι - i → M₂`, and then choosing separately the `i`-th coordinate
* fixing a function `f : ι → M₂`, and then modifying its `i`-th coordinate
The second way is more articial as the value of `f` at `i` is not relevant, but it has the advantage
of avoiding subtype inclusion issues. This is the definition we use, based on `function.update` that
allows to change the value of `f` at `i`.
-/

open function fin

universes u v w u'
variables {R : Type u} {ι : Type u'} {M₁ : Type v} {M₂ : Type w} [decidable_eq ι]

/-- Multilinear maps over the ring `R`, from `(ι → M₁)` to `M₂` where `M₁` and `M₂` are modules
over `R`. -/
structure multilinear_map (R : Type u) (ι : Type u') (M₁ : Type v) (M₂ : Type w)
  [decidable_eq ι] [ring R] [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂] :=
(to_fun : (ι → M₁) → M₂)
(add : ∀(f : ι → M₁) (i : ι) (x y : M₁),
  to_fun (update f i (x + y)) = to_fun (update f i x) + to_fun (update f i y))
(smul : ∀(f : ι → M₁) (i : ι) (x : M₁) (c : R),
  to_fun (update f i (c • x)) = c • to_fun (update f i x))

namespace multilinear_map

section ring

variables [ring R] [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂]
(m m' : multilinear_map R ι M₁ M₂)

instance : has_coe_to_fun (multilinear_map R ι M₁ M₂) := ⟨_, to_fun⟩

@[ext] theorem ext {m m' : multilinear_map R ι M₁ M₂} (H : ∀ x, m x = m' x) : m = m' :=
by cases m; cases m'; congr'; exact funext H

@[simp] lemma map_add (f : ι → M₁) (i : ι) (x y : M₁) :
  m (update f i (x + y)) = m (update f i x) + m (update f i y) :=
m.add f i x y

@[simp] lemma map_smul (f : ι → M₁) (i : ι) (x : M₁) (c : R) :
  m (update f i (c • x)) = c • m (update f i x) :=
m.smul f i x c

lemma map_coord_zero {f : ι → M₁} (i : ι) (h : f i = 0) : m f = 0 :=
begin
  have : (0 : R) • (0 : M₁) = 0, by simp,
  rw [← @update_eq_self _ _ _ i f, h, ← this, m.map_smul, zero_smul]
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
{ to_fun := λx, m (update f i x),
  add    := λx y, by simp,
  smul   := λx c, by simp }

/-- In the specific case of multilinear maps on `fin (n+1)` where one can build an element of
`M₁^(n+1)` using `cons`, one can express directly the additivity of a multilinear map along the
first variable. -/
lemma cons_add {n : ℕ} (m : multilinear_map R (fin (n+1)) M₁ M₂) (f : fin n → M₁) (x y : M₁) :
  m (cons (x+y) f) = m (cons x f) + m (cons y f) :=
by rw [← update_cons_zero f x (x+y), m.map_add, update_cons_zero, update_cons_zero]

/-- In the specific case of multilinear maps on `fin (n+1)` where one can build an element of
`M₁^(n+1)` using `cons`, one can express directly the multiplicativity of a multilinear map along
the first variable. -/
lemma cons_smul {n : ℕ} (m : multilinear_map R (fin (n+1)) M₁ M₂) (f : fin n → M₁) (c : R) (x : M₁) :
  m (cons (c • x) f) = c • m (cons x f) :=
by rw [← update_cons_zero f x (c • x), m.map_smul, update_cons_zero]

end ring

section comm_ring

variables [comm_ring R] [add_comm_group M₁] [add_comm_group M₂]
[module R M₁] [module R M₂]
(m m' : multilinear_map R ι M₁ M₂)

instance : has_scalar R (multilinear_map R ι M₁ M₂) := ⟨λ c m,
  ⟨λ f, c • m f, λf i x y, by simp [smul_add], λf i x d, by simp [smul_smul, mul_comm]⟩⟩

@[simp] lemma smul_apply (c : R) (f : ι → M₁) : (c • m) f = c • m f := rfl

/-- The space of multilinear maps is a module over `R`, for the pointwise addition and scalar
multiplication. -/
instance : module R (multilinear_map R ι M₁ M₂) :=
module.of_core $ by refine { smul := (•), ..};
  intros; ext; simp [smul_add, add_smul, smul_smul]

variables (R M₁ M₂)

/-- The space of multilinear maps on `M₁^(n+1)` is canonically isomorphic to the space of linear
maps from `M₁` to the space of multilinear maps on `M₁^n`, by separating the first variable. We
register this isomorphism in `linear_to_multilinear_equiv_multilinear R M₁ M₂ n`. -/
def linear_to_multilinear_equiv_multilinear (n : ℕ) :
  (M₁ →ₗ[R] (multilinear_map R (fin n) M₁ M₂)) ≃ₗ[R] (multilinear_map R (fin (n+1)) M₁ M₂) :=
{ to_fun  := λm,
    { -- define an `n+1` multilinear map from a linear map into `n` multilinear maps
      to_fun := λf, m (f 0) (tail f),
      add    := λf i x y, begin
        by_cases h : i = 0,
        { rw [h, update_same, update_same, update_same, m.map_add, add_apply,
              tail_update_zero, tail_update_zero, tail_update_zero] },
        { rw [update_noteq (ne.symm h), update_noteq (ne.symm h),
              update_noteq (ne.symm h), ← succ_pred i h, tail_update_succ, map_add,
              tail_update_succ, tail_update_succ] }
      end,
      smul := λf i x c, begin
        by_cases h : i = 0,
        { rw [h, update_same, update_same, tail_update_zero, tail_update_zero,
              ← smul_apply, m.map_smul] },
        { rw [update_noteq (ne.symm h), update_noteq (ne.symm h), ← succ_pred i h,
              tail_update_succ, tail_update_succ, map_smul] }
      end },
  add     := λm₁ m₂, by { ext f, refl },
  smul    := λc m, by { ext f, rw [smul_apply], refl },
  inv_fun := λm,
    { -- define a linear map into `n` multilinear maps from an `n+1` multilinear map
      to_fun := λx,
      { to_fun := λf, m (cons x f),
        add    := λf i y y', by simp,
        smul   := λf i y c, by simp },
      add := λx y, begin
        ext f,
        change m (cons (x + y) f) = m (cons x f) + m (cons y f),
        have A : ∀z, update (cons x f) 0 z = cons z f := λz, update_cons_zero _ _ _,
        rw [← A (x+y), m.map_add, A, A]
      end,
      smul := λc x, begin
        ext f,
        rw smul_apply,
        change m (cons (c • x) f) = c • m (cons x f),
        have A : ∀z, update (cons x f) 0 z = cons z f := λz, update_cons_zero _ _ _,
        rw [← A (c • x), m.map_smul, A]
      end },
  left_inv := λm, begin
    ext x f,
    change m (cons x f 0) (tail (cons x f)) = m x f,
    rw [cons_zero, tail_cons]
  end,
  right_inv := λm, begin
    ext f,
    change m (cons (f 0) (tail f)) = m f,
    rw cons_self_tail
  end }


/-- The space of multilinear maps on `M₁^(n+1)` is canonically isomorphic to the space of linear
maps from the space of multilinear maps on `M₁^n` to the space of linear maps on `M₁`, by
separating the first variable. We register this isomorphism in
`multilinear_to_linear_equiv_multilinear R M₁ M₂ n`. -/
def multilinear_to_linear_equiv_multilinear (n : ℕ) :
  (multilinear_map R (fin n) M₁ (M₁ →ₗ[R] M₂)) ≃ₗ[R] (multilinear_map R (fin (n+1)) M₁ M₂) :=
{ to_fun  := λm,
    { -- define an `n+1` multilinear map from an `n` multilinear map into linear maps
      to_fun := λf, m (tail f) (f 0),
      add    := λf i x y, begin
        by_cases h : i = 0,
        { rw [h, tail_update_zero, tail_update_zero, tail_update_zero, update_same,
              update_same, update_same, linear_map.map_add] },
        { rw [update_noteq (ne.symm h), update_noteq (ne.symm h),
              update_noteq (ne.symm h), ← succ_pred i h, tail_update_succ, map_add,
              tail_update_succ, tail_update_succ, linear_map.add_apply] }
      end,
      smul := λf i x c, begin
        by_cases h : i = 0,
        { rw [h, update_same, update_same, tail_update_zero, tail_update_zero, linear_map.map_smul] },
        { rw [update_noteq (ne.symm h), update_noteq (ne.symm h), ← succ_pred i h,
              tail_update_succ, tail_update_succ, map_smul, linear_map.smul_apply] }
      end },
  add     := λm₁ m₂, by { ext f, refl },
  smul    := λc m, by { ext f, rw [smul_apply], refl },
  inv_fun := λm,
    { -- define an `n` multilinear map into linear maps from an `n+1` multilinear map
      to_fun := λf,
      { to_fun := λx, m (cons x f),
        add    := λx y, by rw m.cons_add,
        smul   := λc x, by rw m.cons_smul },
      add := λf i x y, begin
        ext z,
        change m (cons z (update f i (x + y))) = m (cons z (update f i x)) + m (cons z (update f i y)),
        rw [cons_update, cons_update, cons_update, m.map_add]
      end,
      smul := λf i x c, begin
        ext z,
        change m (cons z (update f i (c • x))) = c • m (cons z (update f i x)),
        rw [cons_update, cons_update, m.map_smul]
      end },
  left_inv := λm, begin
    ext f x,
    change (m (tail (cons x f))) (cons x f 0) = m f x,
    rw [cons_zero, tail_cons]
  end,
  right_inv := λm, begin
    ext f,
    change m (cons (f 0) (tail f)) = m f,
    rw cons_self_tail
  end }

end comm_ring

end multilinear_map
