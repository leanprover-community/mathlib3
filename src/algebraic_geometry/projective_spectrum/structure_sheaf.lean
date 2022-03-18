/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebraic_geometry.projective_spectrum.topology
import topology.sheaves.local_predicate
import ring_theory.localization.at_prime
import algebraic_geometry.locally_ringed_space

/-!
# The structure sheaf on `projective_spectrum 𝒜`.

In `src/algebraic_geometry/topology.lean`, we have given a topology on `projective_spectrum 𝒜`; in
this file we will construct a sheaf on `projective_spectrum 𝒜`.

## Notation
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ℕ → submodule R A` is the grading of `A`;
- `U` is opposite object of some open subset of `projective_spectrum.Top`.

## Main definitions and results
* `projective_spectrum.Top`: the topological space of `projective_spectrum 𝒜` endowed with the
  zariski topology
* `algebraic_geometry.projective_spectrum.structure_sheaf.homogeneous_localization`: given `x` in
  `projective_spectrum.Top 𝒜`, homogeneous localization at `x` is the subring of `Aₓ` (`A` localized
  at prime `x`) where the numerator and denominator have same grading.

Then we define the structure sheaf as the subsheaf of all dependent function
`f : Π x : U, homogeneous_localization x` such that `f` is locally expressible as ratio of two
elements of the *same grading*, i.e. `∀ y ∈ U, ∃ (V ⊆ U) (i : ℕ) (a b ∈ 𝒜 i), ∀ z ∈ V, f z = a / b`.

* `algebraic_geometry.projective_spectrum.structure_sheaf.is_locally_fraction`: the predicate that
  a dependent function is locally expressible as ration of two elements of the same grading.
* `algebraic_geometry.projective_spectrum.structure_sheaf.sections_subring`: the dependent functions
  satisfying the above local property forms a subring of all dependent functions
  `Π x : U, homogeneous_localization x`.
* `algebraic_geometry.Proj.structure_sheaf`: the sheaf with `U ↦ sections_subring U` and natural
  restriction map.

Then we establish that `Proj 𝒜` is a `LocallyRingedSpace`:
* `algebraic_geometry.homogeneous_localization.is_local`: for any `x : projective_spectrum 𝒜`,
  `homogeneous_localization x` is a local ring.
* `algebraic_geometry.Proj.stalk_iso'`: for any `x : projective_spectrum 𝒜`, the stalk of
  `Proj.structure_sheaf` at `x` is isomorphic to `homogeneous_localization x`.
* `algebraic_geometry.Proj.to_LocallyRingedSpace`: `Proj` as a locally ringed space.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

noncomputable theory

namespace algebraic_geometry

open_locale direct_sum big_operators pointwise
open direct_sum set_like

variables {R A: Type*}
variables [comm_ring R] [comm_ring A] [algebra R A]
variables (𝒜 : ℕ → submodule R A) [graded_algebra 𝒜]

local notation `at ` x := localization.at_prime x.as_homogeneous_ideal.to_ideal

open Top topological_space category_theory opposite

/--
The underlying topology of `Proj` is the projective spectrum of graded ring `A`.
-/
def projective_spectrum.Top : Top := Top.of (projective_spectrum 𝒜)

namespace projective_spectrum.structure_sheaf

namespace homogeneous_localization

open set_like.graded_monoid submodule

variables {𝒜} {x : projective_spectrum.Top 𝒜}

/--
If `x` is a point in `Proj 𝒜`, then `y ∈ Aₓ` is said to satisfy `num_denom_same_deg` if and only if
`y = a / b` where `a` and `b` are both in `𝒜 i` for some `i`.
-/
@[nolint has_inhabited_instance]
structure num_denom_same_deg (y : at x) :=
(deg : ℕ)
(num denom : 𝒜 deg)
(denom_not_mem : denom ∉ x.as_homogeneous_ideal)
(eq : (localization.mk num ⟨denom, denom_not_mem⟩ : at x) = y)

attribute [simp] num_denom_same_deg.eq

variable (x)
/--
Auxiliary definition of `homogeneous_localization`: its underlying set.
-/
def carrier : set (at x) :=
{y | nonempty (num_denom_same_deg y)}

variable {x}
lemma one_mem' : (1 : at x) ∈ carrier x := nonempty.intro
{ num := 1,
  denom := 1,
  denom_not_mem := (ideal.ne_top_iff_one _).mp x.is_prime.ne_top,
  deg := 0,
  num_mem := one_mem,
  denom_mem := one_mem,
  eq := by simp }

lemma zero_mem' : (0 : at x) ∈ carrier x := nonempty.intro
{ num := 0,
  denom := 1,
  denom_not_mem := (ideal.ne_top_iff_one _).mp x.is_prime.ne_top,
  deg := 0,
  num_mem := zero_mem _,
  denom_mem := one_mem,
  eq := by simp }

lemma mul_mem' {y1 y2} (hy1 : y1 ∈ carrier x) (hy2 : y2 ∈ carrier x) : y1 * y2 ∈ carrier x :=
match hy1, hy2 with
| ⟨c1⟩, ⟨c2⟩ := nonempty.intro
  { num := c1.num * c2.num,
    denom := c1.denom * c2.denom,
    denom_not_mem := λ r, or.elim (x.is_prime.mem_or_mem r) c1.denom_not_mem c2.denom_not_mem,
    deg := c1.deg + c2.deg,
    num_mem := mul_mem c1.num_mem c2.num_mem,
    denom_mem := mul_mem c1.denom_mem c2.denom_mem,
    eq := by simpa only [← c1.eq, ← c2.eq, localization.mk_mul] }
end

lemma add_mem' {y1 y2} (hy1 : y1 ∈ carrier x) (hy2 : y2 ∈ carrier x) : y1 + y2 ∈ carrier x :=
match hy1, hy2 with
| ⟨c1⟩, ⟨c2⟩ := nonempty.intro
  { num := c1.denom * c2.num + c2.denom * c1.num,
    denom := c1.denom * c2.denom,
    denom_not_mem := λ r, or.elim (x.is_prime.mem_or_mem r) c1.denom_not_mem c2.denom_not_mem,
    deg := c1.deg + c2.deg,
    num_mem := add_mem _ (mul_mem c1.denom_mem c2.num_mem)
      (add_comm c2.deg c1.deg ▸ mul_mem c2.denom_mem c1.num_mem),
    denom_mem := mul_mem c1.denom_mem c2.denom_mem,
    eq := by simpa only [← c1.eq, ← c2.eq, localization.add_mk] }
end

lemma neg_mem' {y} (hy : y ∈ carrier x) : -y ∈ carrier x :=
match hy with
| ⟨c⟩ := nonempty.intro
  { num := -c.num,
    denom := c.denom,
    denom_not_mem := c.denom_not_mem,
    deg := c.deg,
    num_mem := neg_mem _ c.num_mem,
    denom_mem := c.denom_mem,
    eq := by simp only [← c.eq, localization.neg_mk] }
end

end homogeneous_localization

section
variable {𝒜}
open homogeneous_localization

/-- given `x` in `projective_spectrum.Top 𝒜`, homogeneous localization at `x` is the subring of `Aₓ`
(`A` localized at prime `x`) where the numerator and denominator have same grading. -/
@[derive [comm_ring], nolint has_inhabited_instance]
def homogeneous_localization (x : projective_spectrum.Top 𝒜) : Type* :=
subring.mk (carrier x) (λ _ _, mul_mem') one_mem' (λ _ _, add_mem') zero_mem'  (λ _, neg_mem')

end

namespace homogeneous_localization
variables {𝒜} {x : projective_spectrum.Top 𝒜}

/-- numerator of an element in `homogeneous_localization x`-/
def num (f : homogeneous_localization x) : A := (nonempty.some f.2).num
/-- denominator of an element in `homogeneous_localization x`-/
def denom (f : homogeneous_localization x) : A := (nonempty.some f.2).denom
/-- For an element in `homogeneous_localization x`, degree is the natural number `i` such that
  `𝒜 i` contains both numerator and denominator. -/
def deg (f : homogeneous_localization x) : ℕ := (nonempty.some f.2).deg

lemma denom_not_mem (f : homogeneous_localization x) : f.denom ∉ x.as_homogeneous_ideal :=
(nonempty.some f.2).denom_not_mem

lemma num_mem (f : homogeneous_localization x) : f.num ∈ 𝒜 f.deg := (nonempty.some f.2).num_mem
lemma denom_mem (f : homogeneous_localization x) : f.denom ∈ 𝒜 f.deg :=
(nonempty.some f.2).denom_mem

lemma eq_num_div_denom (f : homogeneous_localization x) :
  f.1 = localization.mk f.num ⟨f.denom, f.denom_not_mem⟩ :=
(nonempty.some f.2).eq.symm

lemma val_add (f g : homogeneous_localization x) : (f + g).1 = f.val + g.val := rfl

lemma val_neg (f : homogeneous_localization x) : (-f).val = -f.val := rfl

lemma val_mul (f g : homogeneous_localization x) : (f * g).val = f.val * g.val := rfl

lemma val_sub (f g : homogeneous_localization x) : (f - g).val = f.val - g.val := rfl

lemma val_zero : (0 : homogeneous_localization x).val = localization.mk 0 1 :=
by rw localization.mk_zero; refl

lemma val_one : (1 : homogeneous_localization x).val = localization.mk 1 1 :=
by rw localization.mk_one; refl

lemma ext_iff_val (f g : homogeneous_localization x) : f = g ↔ f.1 = g.1:= subtype.ext_iff_val

end homogeneous_localization

end projective_spectrum.structure_sheaf

end algebraic_geometry
