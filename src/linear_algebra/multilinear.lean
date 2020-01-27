/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import linear_algebra.basic

/-!
# Multilinear maps

We define multilinear maps as maps from `Π(i : ι), M₁ i` to `M₂` which are linear in each
coordinate. Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type
(although some statements will require it to be a fintype). This space, denoted by
`multilinear_map R M₁ M₂`, inherits a module structure by pointwise addition and multiplication.

## Main definitions

* `multilinear_map R M₁ M₂` is the space of multilinear maps from `Π(i : ι), M₁ i` to `M₂`.
* `f.map_smul` is the multiplicativity of the multilinear map `f` along each coordinate.
* `f.map_add` is the additivity of the multilinear map `f` along each coordinate.
* `f.map_smul_univ` expresses the multiplicativity of `f` over all coordinates at the same time,
  writing `f (λi, c i • m i)` as `univ.prod c • f m`.
* `f.map_add_univ` expresses the additivity of `f` over all coordinates at the same time, writing
  `f (m + m')` as the sum over all subsets `s` of `ι` of `f (s.piecewise m m')`.
* `linear_to_multilinear_equiv_multilinear R M₁ M₂` registers the linear equivalence between
  the space of linear maps from `M₁ 0` to the space of multilinear maps on `Π(i : fin n), M₁ i.succ`,
  and the space of multilinear maps on `Π(i : fin (n+1)), M₁ i`, obtained by separating the first
  variable from the other ones.
* `multilinear_to_linear_equiv_multilinear R M₁ M₂` registers the linear equivalence between
  the space of multilinear maps on `Π(i : fin n), M₁ i.succ` to the space of linear maps on `M₁ 0`,
  and the space of multilinear maps on `Π(i : fin (n+1)), M₁ i`, obtained by separating the first
  variable from the other ones.

## Implementation notes

Expressing that a map is linear along the `i`-th coordinate when all other coordinates are fixed
can be done in two (equivalent) different ways:
* fixing a vector `m : Π(j : ι - i), M₁ j.val`, and then choosing separately the `i`-th coordinate
* fixing a vector `m : Πj, M₁ j`, and then modifying its `i`-th coordinate
The second way is more artificial as the value of `m` at `i` is not relevant, but it has the
advantage of avoiding subtype inclusion issues. This is the definition we use, based on
`function.update` that allows to change the value of `m` at `i`.
-/

open function fin set

universes u v v' w u'
variables {R : Type u} {ι : Type u'} {n : ℕ} {M : fin n.succ → Type v'} {M₁ : ι → Type v} {M₂ : Type w}
[decidable_eq ι]

/-- Multilinear maps over the ring `R`, from `Πi, M₁ i` to `M₂` where `M₁ i` and `M₂` are modules
over `R`. -/
structure multilinear_map (R : Type u) {ι : Type u'} (M₁ : ι → Type v) (M₂ : Type w)
  [decidable_eq ι] [ring R] [∀i, add_comm_group (M₁ i)] [add_comm_group M₂] [∀i, module R (M₁ i)]
  [module R M₂] :=
(to_fun : (Πi, M₁ i) → M₂)
(add : ∀(m : Πi, M₁ i) (i : ι) (x y : M₁ i),
  to_fun (update m i (x + y)) = to_fun (update m i x) + to_fun (update m i y))
(smul : ∀(m : Πi, M₁ i) (i : ι) (x : M₁ i) (c : R),
  to_fun (update m i (c • x)) = c • to_fun (update m i x))

namespace multilinear_map

section ring

variables [ring R] [∀i, add_comm_group (M i)] [∀i, add_comm_group (M₁ i)] [add_comm_group M₂]
[∀i, module R (M i)] [∀i, module R (M₁ i)] [module R M₂]
(f f' : multilinear_map R M₁ M₂)

instance : has_coe_to_fun (multilinear_map R M₁ M₂) := ⟨_, to_fun⟩

@[ext] theorem ext {f f' : multilinear_map R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
by cases f; cases f'; congr'; exact funext H

@[simp] lemma map_add (m : Πi, M₁ i) (i : ι) (x y : M₁ i) :
  f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
f.add m i x y

@[simp] lemma map_smul (m : Πi, M₁ i) (i : ι) (x : M₁ i) (c : R) :
  f (update m i (c • x)) = c • f (update m i x) :=
f.smul m i x c

@[simp] lemma map_sub (m : Πi, M₁ i) (i : ι) (x y : M₁ i) :
  f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
by { simp only [map_add, add_left_inj, sub_eq_add_neg, (neg_one_smul R y).symm, map_smul], simp }

lemma map_coord_zero {m : Πi, M₁ i} (i : ι) (h : m i = 0) : f m = 0 :=
begin
  have : (0 : R) • (0 : M₁ i) = 0, by simp,
  rw [← update_eq_self i m, h, ← this, f.map_smul, zero_smul]
end

@[simp] lemma map_zero [nonempty ι] : f 0 = 0 :=
begin
  obtain ⟨i, _⟩ : ∃i:ι, i ∈ set.univ := set.exists_mem_of_nonempty ι,
  exact map_coord_zero f i rfl
end

instance : has_add (multilinear_map R M₁ M₂) :=
⟨λf f', ⟨λx, f x + f' x, λm i x y, by simp, λm i x c, by simp [smul_add]⟩⟩

@[simp] lemma add_apply (m : Πi, M₁ i) : (f + f') m = f m + f' m := rfl

instance : has_neg (multilinear_map R M₁ M₂) :=
⟨λ f, ⟨λ m, - f m, λm i x y, by simp, λm i x c, by simp⟩⟩

@[simp] lemma neg_apply (m : Πi, M₁ i) : (-f) m = - (f m) := rfl

instance : has_zero (multilinear_map R M₁ M₂) :=
⟨⟨λ _, 0, λm i x y, by simp, λm i x c, by simp⟩⟩

@[simp] lemma zero_apply (m : Πi, M₁ i) : (0 : multilinear_map R M₁ M₂) m = 0 := rfl

instance : add_comm_group (multilinear_map R M₁ M₂) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..};
   intros; ext; simp

/-- If `f` is a multilinear map, then `f.to_linear_map m i` is the linear map obtained by fixing all
coordinates but `i` equal to those of `m`, and varying the `i`-th coordinate. -/
def to_linear_map (m : Πi, M₁ i) (i : ι) : M₁ i →ₗ[R] M₂ :=
{ to_fun := λx, f (update m i x),
  add    := λx y, by simp,
  smul   := λx c, by simp }

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the additivity of a
multilinear map along the first variable. -/
lemma cons_add (f : multilinear_map R M M₂) (m : Π(i : fin n), M i.succ) (x y : M 0) :
  f (cons (x+y) m) = f (cons x m) + f (cons y m) :=
by rw [← update_cons_zero x m (x+y), f.map_add, update_cons_zero, update_cons_zero]

/-- In the specific case of multilinear maps on spaces indexed by `fin (n+1)`, where one can build
an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the multiplicativity
of a multilinear map along the first variable. -/
lemma cons_smul (f : multilinear_map R M M₂) (m : Π(i : fin n), M i.succ) (c : R) (x : M 0) :
  f (cons (c • x) m) = c • f (cons x m) :=
by rw [← update_cons_zero x m (c • x), f.map_smul, update_cons_zero]

end ring

section comm_ring

variables [comm_ring R] [∀i, add_comm_group (M₁ i)] [∀i, add_comm_group (M i)] [add_comm_group M₂]
[∀i, module R (M i)] [∀i, module R (M₁ i)] [module R M₂]
(f f' : multilinear_map R M₁ M₂)

/-- If one multiplies by `c i` the coordinates in a finset `s`, then the image under a multilinear
map is multiplied by `s.prod c`. This is mainly an auxiliary statement to prove the result when
`s = univ`, given in `map_smul_univ`, although it can be useful in its own right as it does not
require the index set `ι` to be finite. -/
lemma map_piecewise_smul (c : ι → R) (m : Πi, M₁ i) (s : finset ι) :
  f (s.piecewise (λi, c i • m i) m) = s.prod c • f m :=
begin
  refine s.induction_on (by simp) _,
  assume j s j_not_mem_s Hrec,
  have A : function.update (s.piecewise (λi, c i • m i) m) j (m j) =
           s.piecewise (λi, c i • m i) m,
  { ext i,
    by_cases h : i = j,
    { rw h, simp [j_not_mem_s] },
    { simp [h] } },
  rw [s.piecewise_insert, f.map_smul, A, Hrec],
  simp [j_not_mem_s, mul_smul]
end

/-- Multiplicativity of a multilinear map along all coordinates at the same time,
writing `f (λi, c i • m i)` as `univ.prod c • f m`. -/
lemma map_smul_univ [fintype ι] (c : ι → R) (m : Πi, M₁ i) :
  f (λi, c i • m i) = finset.univ.prod c • f m :=
by simpa using map_piecewise_smul f c m finset.univ

/-- If one adds to a vector `m'` another vector `m`, but only for coordinates in a finset `t`, then
the image under a multilinear map `f` is the sum of `f (s.piecewise m m')` along all subsets `s` of
`t`. This is mainly an auxiliary statement to prove the result when `t = univ`, given in
`map_add_univ`, although it can be useful in its own right as it does not require the index set `ι`
to be finite.-/
lemma map_piecewise_add (m m' : Πi, M₁ i) (t : finset ι) :
  f (t.piecewise (m + m') m') = t.powerset.sum (λs, f (s.piecewise m m')) :=
begin
  revert m',
  refine finset.induction_on t (by simp) _,
  assume i t hit Hrec m',
  have A : (insert i t).piecewise (m + m') m' = update (t.piecewise (m + m') m') i (m i + m' i) :=
    t.piecewise_insert _ _ _,
  have B : update (t.piecewise (m + m') m') i (m' i) = t.piecewise (m + m') m',
  { ext j,
    by_cases h : j = i,
    { rw h, simp [hit] },
    { simp [h] } },
  let m'' := update m' i (m i),
  have C : update (t.piecewise (m + m') m') i (m i) = t.piecewise (m + m'') m'',
  { ext j,
    by_cases h : j = i,
    { rw h, simp [m'', hit] },
    { by_cases h' : j ∈ t; simp [h, hit, m'', h'] } },
  rw [A, f.map_add, B, C, finset.sum_powerset_insert hit, Hrec, Hrec, add_comm],
  congr' 1,
  apply finset.sum_congr rfl (λs hs, _),
  have : (insert i s).piecewise m m' = s.piecewise m m'',
  { ext j,
    by_cases h : j = i,
    { rw h, simp [m'', finset.not_mem_of_mem_powerset_of_not_mem hs hit] },
    { by_cases h' : j ∈ s; simp [h, m'', h'] } },
  rw this
end

/-- Additivity of a multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum  of `f (s.piecewise m m')` over all sets `s`. -/
lemma map_add_univ [fintype ι] (m m' : Πi, M₁ i) :
  f (m + m') = (finset.univ : finset (finset ι)).sum (λs, f (s.piecewise m m')) :=
by simpa using f.map_piecewise_add m m' finset.univ

instance : has_scalar R (multilinear_map R M₁ M₂) := ⟨λ c f,
  ⟨λ m, c • f m, λm i x y, by simp [smul_add], λl i x d, by simp [smul_smul, mul_comm]⟩⟩

@[simp] lemma smul_apply (c : R) (m : Πi, M₁ i) : (c • f) m = c • f m := rfl

/-- The space of multilinear maps is a module over `R`, for the pointwise addition and scalar
multiplication. -/
instance : module R (multilinear_map R M₁ M₂) :=
module.of_core $ by refine { smul := (•), ..};
  intros; ext; simp [smul_add, add_smul, smul_smul]

end comm_ring

end multilinear_map


section isomorphisms
open multilinear_map

variables (R M M₂)
[comm_ring R] [∀i, add_comm_group (M i)] [add_comm_group M₂]
[∀i, module R (M i)] [module R M₂]

/-- The space of multilinear maps on `Π(i : fin (n+1)), M i` is canonically isomorphic to the space
of linear maps from `M 0` to the space of multilinear maps on `Π(i : fin n), M i.succ `, by
separating the first variable. We register this isomorphism in
`linear_to_multilinear_equiv_multilinear R M M₂`. -/
def linear_to_multilinear_equiv_multilinear :
  (M 0 →ₗ[R] (multilinear_map R (λ(i : fin n), M i.succ) M₂)) ≃ₗ[R] (multilinear_map R M M₂) :=
{ to_fun  := λf,
    { -- define an `n+1` multilinear map from a linear map into `n` multilinear maps
      to_fun := λm, f (m 0) (tail m),
      add    := λm i x y, begin
        by_cases h : i = 0,
        { revert x y,
          rw h,
          assume x y,
          rw [update_same, update_same, update_same, f.map_add, add_apply,
              tail_update_zero, tail_update_zero, tail_update_zero] },
        { rw [update_noteq (ne.symm h), update_noteq (ne.symm h), update_noteq (ne.symm h)],
          revert x y,
          rw ← succ_pred i h,
          assume x y,
          rw [tail_update_succ, map_add, tail_update_succ, tail_update_succ] }
      end,
      smul := λm i x c, begin
        by_cases h : i = 0,
        { revert x,
          rw h,
          assume x,
          rw [update_same, update_same, tail_update_zero, tail_update_zero,
              ← smul_apply, f.map_smul] },
        { rw [update_noteq (ne.symm h), update_noteq (ne.symm h)],
          revert x,
          rw ← succ_pred i h,
          assume x,
          rw [tail_update_succ, tail_update_succ, map_smul] }
      end },
  add     := λf₁ f₂, by { ext m, refl },
  smul    := λc f, by { ext m, rw [smul_apply], refl },
  inv_fun := λf,
    { -- define a linear map into `n` multilinear maps from an `n+1` multilinear map
      to_fun := λx,
      { to_fun := λm, f (cons x m),
        add    := λm i y y', by simp,
        smul   := λm i y c, by simp },
      add := λx y, by { ext m, exact cons_add f m x y },
      smul := λc x, by { ext m, exact cons_smul f m c x } },
  left_inv := λf, begin
    ext x m,
    change f (cons x m 0) (tail (cons x m)) = f x m,
    rw [cons_zero, tail_cons]
  end,
  right_inv := λf, begin
    ext m,
    change f (cons (m 0) (tail m)) = f m,
    rw cons_self_tail
  end }

/-- The space of multilinear maps on `Π(i : fin (n+1)), M i` is canonically isomorphic to the space
of linear maps from the space of multilinear maps on `Π(i : fin n), M i.succ` to the space of linear
maps on `M 0`, by separating the first variable. We register this isomorphism in
`multilinear_to_linear_equiv_multilinear R M M₂`. -/
def multilinear_to_linear_equiv_multilinear :
  (multilinear_map R (λ(i : fin n), M i.succ) ((M 0) →ₗ[R] M₂)) ≃ₗ[R] (multilinear_map R M M₂) :=
{ to_fun  := λf,
    { -- define an `n+1` multilinear map from an `n` multilinear map into linear maps
      to_fun := λm, f (tail m) (m 0),
      add    := λm i x y, begin
        by_cases h : i = 0,
        { revert x y,
          rw h,
          assume x y,
          rw [tail_update_zero, tail_update_zero, tail_update_zero, update_same,
              update_same, update_same, linear_map.map_add] },
        { rw [update_noteq (ne.symm h), update_noteq (ne.symm h), update_noteq (ne.symm h)],
          revert x y,
          rw  [← succ_pred i h],
          assume x y,
          rw [tail_update_succ, map_add, tail_update_succ, tail_update_succ, linear_map.add_apply] }
      end,
      smul := λm i x c, begin
        by_cases h : i = 0,
        { revert x,
          rw h,
          assume x,
          rw [update_same, update_same, tail_update_zero, tail_update_zero, linear_map.map_smul] },
        { rw [update_noteq (ne.symm h), update_noteq (ne.symm h)],
          revert x,
          rw [← succ_pred i h],
          assume x,
          rw [tail_update_succ, tail_update_succ, map_smul, linear_map.smul_apply] }
      end },
  add     := λf₁ f₂, by { ext m, refl },
  smul    := λc f, by { ext m, rw [smul_apply], refl },
  inv_fun := λf,
    { -- define an `n` multilinear map into linear maps from an `n+1` multilinear map
      to_fun := λm,
      { to_fun := λx, f (cons x m),
        add    := λx y, by rw f.cons_add,
        smul   := λc x, by rw f.cons_smul },
      add := λm i x y, begin
        ext z,
        change f (cons z (update m i (x + y))) = f (cons z (update m i x)) + f (cons z (update m i y)),
        rw [cons_update, cons_update, cons_update, f.map_add]
      end,
      smul := λm i x c, begin
        ext z,
        change f (cons z (update m i (c • x))) = c • f (cons z (update m i x)),
        rw [cons_update, cons_update, f.map_smul]
      end },
  left_inv := λf, begin
    ext m x,
    change (f (tail (cons x m))) (cons x m 0) = f m x,
    rw [cons_zero, tail_cons]
  end,
  right_inv := λf, begin
    ext m,
    change f (cons (m 0) (tail m)) = f m,
    rw cons_self_tail
  end }

end isomorphisms
