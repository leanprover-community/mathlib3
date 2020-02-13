/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import topology.algebra.module linear_algebra.multilinear

/-!
# Continuous multilinear maps

We define continuous multilinear maps as maps from `Π(i : ι), M₁ i` to `M₂` which are multilinear
and continuous, by extending the space of multilinear maps with a continuity assumption.
Here, `M₁ i` and `M₂` are modules over a ring `R`, and `ι` is an arbitrary type, and all these
spaces are also topological spaces.

## Main definitions

* `continuous_multilinear_map R M₁ M₂` is the space of continuous multilinear maps from
  `Π(i : ι), M₁ i` to `M₂`. We show that it is an `R`-module.

## Implementation notes

We mostly follow the API of multilinear maps.
-/

open function fin set

universes u v w w₁ w₂
variables {R : Type u} {ι : Type v} {n : ℕ}
{M : fin n.succ → Type w} {M₁ : ι → Type w₁} {M₂ : Type w₂}
[decidable_eq ι]

/-- Continuous multilinear maps over the ring `R`, from `Πi, M₁ i` to `M₂` where `M₁ i` and `M₂`
are modules over `R` with a topological structure. In applications, there will be compatibility
conditions between the algebraic and the topological structures, but this is not needed for the
definition. -/
structure continuous_multilinear_map (R : Type u) {ι : Type v} (M₁ : ι → Type w₁) (M₂ : Type w₂)
  [decidable_eq ι] [ring R] [∀i, add_comm_group (M₁ i)] [add_comm_group M₂] [∀i, module R (M₁ i)]
  [module R M₂] [∀i, topological_space (M₁ i)] [topological_space M₂]
  extends multilinear_map R M₁ M₂ :=
(cont : continuous to_fun)

namespace continuous_multilinear_map

section ring

variables [ring R] [∀i, add_comm_group (M i)] [∀i, add_comm_group (M₁ i)] [add_comm_group M₂]
[∀i, module R (M i)] [∀i, module R (M₁ i)] [module R M₂]
[∀i, topological_space (M i)] [∀i, topological_space (M₁ i)] [topological_space M₂]
(f f' : continuous_multilinear_map R M₁ M₂)

instance : has_coe_to_fun (continuous_multilinear_map R M₁ M₂) :=
⟨_, λ f, f.to_multilinear_map.to_fun⟩

@[ext] theorem ext {f f' : continuous_multilinear_map R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
by { cases f, cases f', congr, ext x, exact H x }

@[simp] lemma map_add (m : Πi, M₁ i) (i : ι) (x y : M₁ i) :
  f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
f.add m i x y

@[simp] lemma map_smul (m : Πi, M₁ i) (i : ι) (c : R) (x : M₁ i) :
  f (update m i (c • x)) = c • f (update m i x) :=
f.smul m i c x

@[simp] lemma map_sub (m : Πi, M₁ i) (i : ι) (x y : M₁ i) :
  f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
f.to_multilinear_map.map_sub _ _ _ _

lemma map_coord_zero {m : Πi, M₁ i} (i : ι) (h : m i = 0) : f m = 0 :=
f.to_multilinear_map.map_coord_zero i h

@[simp] lemma map_zero [nonempty ι] : f 0 = 0 :=
f.to_multilinear_map.map_zero

instance : has_zero (continuous_multilinear_map R M₁ M₂) :=
⟨{ cont := continuous_const, ..(0 : multilinear_map R M₁ M₂) }⟩

instance : inhabited (continuous_multilinear_map R M₁ M₂) := ⟨0⟩

@[simp] lemma zero_apply (m : Πi, M₁ i) : (0 : continuous_multilinear_map R M₁ M₂) m = 0 := rfl

section topological_add_group
variable [topological_add_group M₂]

instance : has_add (continuous_multilinear_map R M₁ M₂) :=
⟨λ f f', {cont := f.cont.add f'.cont, ..(f.to_multilinear_map + f'.to_multilinear_map)}⟩

@[simp] lemma add_apply (m : Πi, M₁ i) : (f + f') m = f m + f' m := rfl

instance : has_neg (continuous_multilinear_map R M₁ M₂) :=
⟨λ f, {cont := f.cont.neg, ..(-f.to_multilinear_map)}⟩

@[simp] lemma neg_apply (m : Πi, M₁ i) : (-f) m = - (f m) := rfl

instance : add_comm_group (continuous_multilinear_map R M₁ M₂) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..};
   intros; ext; simp

@[simp] lemma sub_apply (m : Πi, M₁ i) : (f - f') m = f m - f' m := rfl

end topological_add_group

/-- If `f` is a continuous multilinear map, then `f.to_continuous_linear_map m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
def to_continuous_linear_map (m : Πi, M₁ i) (i : ι) : M₁ i →L[R] M₂ :=
{ cont := f.cont.comp continuous_update, ..(f.to_multilinear_map.to_linear_map m i) }

/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
additivity of a multilinear map along the first variable. -/
lemma cons_add (f : continuous_multilinear_map R M M₂) (m : Π(i : fin n), M i.succ) (x y : M 0) :
  f (cons (x+y) m) = f (cons x m) + f (cons y m) :=
f.to_multilinear_map.cons_add m x y

/-- In the specific case of continuous multilinear maps on spaces indexed by `fin (n+1)`, where one
can build an element of `Π(i : fin (n+1)), M i` using `cons`, one can express directly the
multiplicativity of a multilinear map along the first variable. -/
lemma cons_smul
  (f : continuous_multilinear_map R M M₂) (m : Π(i : fin n), M i.succ) (c : R) (x : M 0) :
  f (cons (c • x) m) = c • f (cons x m) :=
f.to_multilinear_map.cons_smul m c x

end ring

section comm_ring

variables [comm_ring R]
[∀i, add_comm_group (M₁ i)] [add_comm_group M₂]
[∀i, module R (M₁ i)] [module R M₂]
[∀i, topological_space (M₁ i)] [topological_space M₂]
(f : continuous_multilinear_map R M₁ M₂)

lemma map_piecewise_smul (c : ι → R) (m : Πi, M₁ i) (s : finset ι) :
  f (s.piecewise (λ i, c i • m i) m) = s.prod c • f m :=
f.to_multilinear_map.map_piecewise_smul _ _ _

/-- Multiplicativity of a continuous multilinear map along all coordinates at the same time,
writing `f (λ i, c i • m i)` as `univ.prod c • f m`. -/
lemma map_smul_univ [fintype ι] (c : ι → R) (m : Πi, M₁ i) :
  f (λ i, c i • m i) = finset.univ.prod c • f m :=
f.to_multilinear_map.map_smul_univ _ _

lemma map_piecewise_add (m m' : Πi, M₁ i) (t : finset ι) :
  f (t.piecewise (m + m') m') = t.powerset.sum (λ s, f (s.piecewise m m')) :=
f.to_multilinear_map.map_piecewise_add _ _ _

/-- Additivity of a continuous multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum  of `f (s.piecewise m m')` over all sets `s`. -/
lemma map_add_univ [fintype ι] (m m' : Πi, M₁ i) :
  f (m + m') = (finset.univ : finset (finset ι)).sum (λ s, f (s.piecewise m m')) :=
f.to_multilinear_map.map_add_univ _ _

variables [topological_space R] [topological_module R M₂]

instance : has_scalar R (continuous_multilinear_map R M₁ M₂) :=
⟨λ c f, { cont := continuous.smul continuous_const f.cont, .. c • f.to_multilinear_map }⟩

@[simp] lemma smul_apply (c : R) (m : Πi, M₁ i) : (c • f) m = c • f m := rfl

/-- The space of continuous multilinear maps is a module over `R`, for the pointwise addition and
scalar multiplication. -/
instance [topological_add_group M₂] : module R (continuous_multilinear_map R M₁ M₂) :=
module.of_core $ by refine { smul := (•), ..};
  intros; ext; simp [smul_add, add_smul, smul_smul]

/-- Linear map version of the map `to_multilinear_map` associating to a continuous multilinear map
the corresponding multilinear map. -/
def to_multilinear_map_linear [topological_add_group M₂] :
  (continuous_multilinear_map R M₁ M₂) →ₗ[R] (multilinear_map R M₁ M₂) :=
{ to_fun := λ f, f.to_multilinear_map,
  add    := λ f g, rfl,
  smul   := λ c f, rfl }

end comm_ring

end continuous_multilinear_map
