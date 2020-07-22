/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.algebra.module
import linear_algebra.multilinear

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

## Notation

We introduce the notation `M [×n]→L[R] M'` for the space of continuous `n`-multilinear maps from
`M^n` to `M'`. This is a particular case of the general notion (where we allow varying dependent
types as the arguments of our continuous multilinear maps), but arguably the most important one,
especially when defining iterated derivatives.
-/

open function fin set
open_locale big_operators

universes u v w w₁ w₂ w₃ w₄
variables {R : Type u} {ι : Type v} {n : ℕ}
{M : fin n.succ → Type w} {M₁ : ι → Type w₁} {M₂ : Type w₂} {M₃ : Type w₃} {M₄ : Type w₄}
[decidable_eq ι]

/-- Continuous multilinear maps over the ring `R`, from `Πi, M₁ i` to `M₂` where `M₁ i` and `M₂`
are modules over `R` with a topological structure. In applications, there will be compatibility
conditions between the algebraic and the topological structures, but this is not needed for the
definition. -/
structure continuous_multilinear_map (R : Type u) {ι : Type v} (M₁ : ι → Type w₁) (M₂ : Type w₂)
  [decidable_eq ι] [semiring R] [∀i, add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [∀i, semimodule R (M₁ i)]
  [semimodule R M₂] [∀i, topological_space (M₁ i)] [topological_space M₂]
  extends multilinear_map R M₁ M₂ :=
(cont : continuous to_fun)

notation M `[×`:25 n `]→L[`:25 R `] ` M' := continuous_multilinear_map R (λ (i : fin n), M) M'

namespace continuous_multilinear_map

section semiring

variables [semiring R]
[∀i, add_comm_monoid (M i)] [∀i, add_comm_monoid (M₁ i)] [add_comm_monoid M₂] [add_comm_monoid M₃]
[add_comm_monoid M₄]
[∀i, semimodule R (M i)] [∀i, semimodule R (M₁ i)] [semimodule R M₂] [semimodule R M₃]
[semimodule R M₄]
[∀i, topological_space (M i)] [∀i, topological_space (M₁ i)] [topological_space M₂]
[topological_space M₃] [topological_space M₄]
(f f' : continuous_multilinear_map R M₁ M₂)

instance : has_coe_to_fun (continuous_multilinear_map R M₁ M₂) :=
⟨_, λ f, f.to_multilinear_map.to_fun⟩

@[simp] lemma coe_coe : (f.to_multilinear_map : (Π i, M₁ i) → M₂) = f := rfl

@[ext] theorem ext {f f' : continuous_multilinear_map R M₁ M₂} (H : ∀ x, f x = f' x) : f = f' :=
by { cases f, cases f', congr, ext x, exact H x }

@[simp] lemma map_add (m : Πi, M₁ i) (i : ι) (x y : M₁ i) :
  f (update m i (x + y)) = f (update m i x) + f (update m i y) :=
f.map_add' m i x y

@[simp] lemma map_smul (m : Πi, M₁ i) (i : ι) (c : R) (x : M₁ i) :
  f (update m i (c • x)) = c • f (update m i x) :=
f.map_smul' m i c x

lemma map_coord_zero {m : Πi, M₁ i} (i : ι) (h : m i = 0) : f m = 0 :=
f.to_multilinear_map.map_coord_zero i h

@[simp] lemma map_zero [nonempty ι] : f 0 = 0 :=
f.to_multilinear_map.map_zero

instance : has_zero (continuous_multilinear_map R M₁ M₂) :=
⟨{ cont := continuous_const, ..(0 : multilinear_map R M₁ M₂) }⟩

instance : inhabited (continuous_multilinear_map R M₁ M₂) := ⟨0⟩

@[simp] lemma zero_apply (m : Πi, M₁ i) : (0 : continuous_multilinear_map R M₁ M₂) m = 0 := rfl

section has_continuous_add
variable [has_continuous_add M₂]

instance : has_add (continuous_multilinear_map R M₁ M₂) :=
⟨λ f f', {cont := f.cont.add f'.cont, ..(f.to_multilinear_map + f'.to_multilinear_map)}⟩

@[simp] lemma add_apply (m : Πi, M₁ i) : (f + f') m = f m + f' m := rfl

instance add_comm_monoid : add_comm_monoid (continuous_multilinear_map R M₁ M₂) :=
by refine {zero := 0, add := (+), ..}; intros; ext; simp [add_comm, add_left_comm]

@[simp] lemma sum_apply {α : Type*} (f : α → continuous_multilinear_map R M₁ M₂)
  (m : Πi, M₁ i) : ∀ {s : finset α}, (∑ a in s, f a) m = ∑ a in s, f a m :=
begin
  classical,
  apply finset.induction,
  { rw finset.sum_empty, simp },
  { assume a s has H, rw finset.sum_insert has, simp [H, has] }
end

end has_continuous_add

/-- If `f` is a continuous multilinear map, then `f.to_continuous_linear_map m i` is the continuous
linear map obtained by fixing all coordinates but `i` equal to those of `m`, and varying the
`i`-th coordinate. -/
def to_continuous_linear_map (m : Πi, M₁ i) (i : ι) : M₁ i →L[R] M₂ :=
{ cont := f.cont.comp continuous_update, ..(f.to_multilinear_map.to_linear_map m i) }

/-- The cartesian product of two continuous multilinear maps, as a continuous multilinear map. -/
def prod (f : continuous_multilinear_map R M₁ M₂) (g : continuous_multilinear_map R M₁ M₃) :
  continuous_multilinear_map R M₁ (M₂ × M₃) :=
{ cont := f.cont.prod_mk g.cont,
  .. f.to_multilinear_map.prod g.to_multilinear_map }

@[simp] lemma prod_apply
  (f : continuous_multilinear_map R M₁ M₂) (g : continuous_multilinear_map R M₁ M₃) (m : Πi, M₁ i) :
  (f.prod g) m = (f m, g m) := rfl

/- If `R` and `M₃` are implicit in the next definition, Lean is never able to infer them, even
given `g` and `f`. Therefore, we make them explicit. -/
variables (R M₃)

/-- If `g` is continuous multilinear and `f` is continuous linear, then `g (f m₁, ..., f mₙ)` is
again a continuous multilinear map, that we call `g.comp_continuous_linear_map f`. -/
def comp_continuous_linear_map
  (g : continuous_multilinear_map R (λ (i : ι), M₃) M₄) (f : M₂ →L[R] M₃) :
  continuous_multilinear_map R (λ (i : ι), M₂) M₄ :=
{ cont := g.cont.comp $ continuous_pi $ λj, f.cont.comp $ continuous_apply _,
  .. g.to_multilinear_map.comp_linear_map R M₃ f.to_linear_map }
variables {R M₃}

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

lemma map_piecewise_add (m m' : Πi, M₁ i) (t : finset ι) :
  f (t.piecewise (m + m') m') = ∑ s in t.powerset, f (s.piecewise m m') :=
f.to_multilinear_map.map_piecewise_add _ _ _

/-- Additivity of a continuous multilinear map along all coordinates at the same time,
writing `f (m + m')` as the sum  of `f (s.piecewise m m')` over all sets `s`. -/
lemma map_add_univ [fintype ι] (m m' : Πi, M₁ i) :
  f (m + m') = ∑ s : finset ι, f (s.piecewise m m') :=
f.to_multilinear_map.map_add_univ _ _

section apply_sum

open fintype finset

variables {α : ι → Type*} [fintype ι] (g : Π i, α i → M₁ i) (A : Π i, finset (α i))

/-- If `f` is continuous multilinear, then `f (Σ_{j₁ ∈ A₁} g₁ j₁, ..., Σ_{jₙ ∈ Aₙ} gₙ jₙ)` is the sum
of `f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions with `r 1 ∈ A₁`, ...,
`r n ∈ Aₙ`. This follows from multilinearity by expanding successively with respect to each
coordinate. -/
lemma map_sum_finset  :
  f (λ i, ∑ j in A i, g i j) = ∑ r in pi_finset A, f (λ i, g i (r i)) :=
f.to_multilinear_map.map_sum_finset _ _

/-- If `f` is continuous multilinear, then `f (Σ_{j₁} g₁ j₁, ..., Σ_{jₙ} gₙ jₙ)` is the sum of
`f (g₁ (r 1), ..., gₙ (r n))` where `r` ranges over all functions `r`. This follows from
multilinearity by expanding successively with respect to each coordinate. -/
lemma map_sum [∀ i, fintype (α i)] :
  f (λ i, ∑ j, g i j) = ∑ r : Π i, α i, f (λ i, g i (r i)) :=
f.to_multilinear_map.map_sum _

end apply_sum

end semiring

section ring

variables [ring R] [∀i, add_comm_group (M₁ i)] [add_comm_group M₂]
[∀i, semimodule R (M₁ i)] [semimodule R M₂] [∀i, topological_space (M₁ i)] [topological_space M₂]
(f f' : continuous_multilinear_map R M₁ M₂)

@[simp] lemma map_sub (m : Πi, M₁ i) (i : ι) (x y : M₁ i) :
  f (update m i (x - y)) = f (update m i x) - f (update m i y) :=
f.to_multilinear_map.map_sub _ _ _ _

section topological_add_group
variable [topological_add_group M₂]

instance : has_neg (continuous_multilinear_map R M₁ M₂) :=
⟨λ f, {cont := f.cont.neg, ..(-f.to_multilinear_map)}⟩

@[simp] lemma neg_apply (m : Πi, M₁ i) : (-f) m = - (f m) := rfl

instance : add_comm_group (continuous_multilinear_map R M₁ M₂) :=
by refine {zero := 0, add := (+), neg := has_neg.neg, ..};
   intros; ext; simp [add_comm, add_left_comm]

@[simp] lemma sub_apply (m : Πi, M₁ i) : (f - f') m = f m - f' m := rfl

end topological_add_group

end ring

section comm_ring

variables [comm_ring R]
[∀i, add_comm_monoid (M₁ i)] [add_comm_monoid M₂]
[∀i, semimodule R (M₁ i)] [semimodule R M₂]
[∀i, topological_space (M₁ i)] [topological_space M₂]
(f : continuous_multilinear_map R M₁ M₂)

lemma map_piecewise_smul (c : ι → R) (m : Πi, M₁ i) (s : finset ι) :
  f (s.piecewise (λ i, c i • m i) m) = (∏ i in s, c i) • f m :=
f.to_multilinear_map.map_piecewise_smul _ _ _

/-- Multiplicativity of a continuous multilinear map along all coordinates at the same time,
writing `f (λ i, c i • m i)` as `(∏ i, c i) • f m`. -/
lemma map_smul_univ [fintype ι] (c : ι → R) (m : Πi, M₁ i) :
  f (λ i, c i • m i) = (∏ i, c i) • f m :=
f.to_multilinear_map.map_smul_univ _ _

variables [topological_space R] [topological_semimodule R M₂]

instance : has_scalar R (continuous_multilinear_map R M₁ M₂) :=
⟨λ c f, { cont := continuous.smul continuous_const f.cont, .. c • f.to_multilinear_map }⟩

@[simp] lemma smul_apply (c : R) (m : Πi, M₁ i) : (c • f) m = c • f m := rfl

end comm_ring

section comm_ring

variables [comm_ring R]
[∀i, add_comm_group (M₁ i)] [add_comm_group M₂]
[∀i, semimodule R (M₁ i)] [semimodule R M₂]
[∀i, topological_space (M₁ i)] [topological_space M₂] [topological_add_group M₂]
[topological_space R] [topological_semimodule R M₂]
(f : continuous_multilinear_map R M₁ M₂)

/-- The space of continuous multilinear maps is a module over `R`, for the pointwise addition and
scalar multiplication. -/
instance : semimodule R (continuous_multilinear_map R M₁ M₂) :=
semimodule.of_core $ by refine { smul := (•), .. };
  intros; ext; simp [smul_add, add_smul, smul_smul]

/-- Linear map version of the map `to_multilinear_map` associating to a continuous multilinear map
the corresponding multilinear map. -/
def to_multilinear_map_linear :
  (continuous_multilinear_map R M₁ M₂) →ₗ[R] (multilinear_map R M₁ M₂) :=
{ to_fun    := λ f, f.to_multilinear_map,
  map_add'  := λ f g, rfl,
  map_smul' := λ c f, rfl }

end comm_ring

end continuous_multilinear_map

namespace continuous_linear_map
variables [ring R] [∀i, add_comm_group (M₁ i)] [add_comm_group M₂] [add_comm_group M₃]
[∀i, module R (M₁ i)] [module R M₂] [module R M₃]
[∀i, topological_space (M₁ i)] [topological_space M₂] [topological_space M₃]

/-- Composing a continuous multilinear map with a continuous linear map gives again a
continuous multilinear map. -/
def comp_continuous_multilinear_map (g : M₂ →L[R] M₃) (f : continuous_multilinear_map R M₁ M₂) :
  continuous_multilinear_map R M₁ M₃ :=
{ cont := g.cont.comp f.cont,
  .. g.to_linear_map.comp_multilinear_map f.to_multilinear_map }

@[simp] lemma comp_continuous_multilinear_map_coe (g : M₂ →L[R] M₃) (f : continuous_multilinear_map R M₁ M₂) :
  ((g.comp_continuous_multilinear_map f) : (Πi, M₁ i) → M₃) =
  (g : M₂ → M₃) ∘ (f : (Πi, M₁ i) → M₂) :=
by { ext m, refl }

end continuous_linear_map
