/-
Copyright (c) 2022 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold.
-/

import tactic
import algebra.group.basic
import data.real.basic
import topology.continuous_function.bounded
import topology.category.Top
import topology.algebra.group
import algebra.group.defs

/-!
# Means on Groups

In this file, we introduce means on groups,
i.e. `averaging' maps that turn bounded (continuous) functions G → ℝ into a real number.


## Main Definitions

- `mean`              : Structure for means
- `mean_pushforward`  : Pushing forward a mean on $G$ via a map $G → H$ yields a mean on $H$.

## Implementation Notes

We will ultimately need this notion to define amenability of groups via
invariant means (in the file def_amenable).

This file defines means by regarding all groups with their discrete topology,
thus enabling us to use `bounded_continuous_function`.
If you want to consider means on (non-discrete)
topological groups, one needs to change some definitions.


## References
* <https://en.wikipedia.org/wiki/Amenable_group>
* [C. Löh, *Geometric Group Theory*, Proposition 9.1.1][loeh17]


## Tags
mean
-/

open classical
open bounded_continuous_function

variables (G:Type*) [topological_space G] [group G] [topological_group G]


/-- A mean on a group-/
structure mean := mk ::
(lin_map : (bounded_continuous_function G ℝ) →ₗ[ℝ] ℝ)
(normality : lin_map (bounded_continuous_function.const G (1:ℝ)) = 1)
(positivity: ∀ {f : bounded_continuous_function G ℝ},
                          (∀ (x:G), f x ≥ 0) → lin_map f ≥ 0)


instance : has_coe (mean G) ((bounded_continuous_function G ℝ) →ₗ[ℝ] ℝ) :=
  {coe := mean.lin_map}


/--Equality of means can be checked by evaluation -/
@[ext]
theorem ext {m n : mean G} (h: ∀ f, m f = n f) : m = n :=
begin
  cases m,
  cases n,
  simp,
  ext,
  exact h x,
end


namespace mean


section el_facts

/-!
### Elementary facts

We collect some elementary facts about means
-/

@[simp]
lemma mean_of_neg (m : mean G) {f: bounded_continuous_function G ℝ} : m (-f) = - m f :=
begin
  have : m (-f) + m f = 0,
  {calc   m (-f) + m f
        = m ((-f) +f )
         : by exact (m.lin_map.map_add' (-f) f).symm
    ... = m 0
          : by ring_nf
    ... = m ((0:ℝ) • 0)
          : by simp
    ... = (ring_hom.id ℝ) 0 • m 0
          : by exact m.lin_map.map_smul' 0 0
    ... = 0
          : by simp, },
  linarith,
end


lemma mean_bounded (m : mean G) {f: bounded_continuous_function G ℝ} {M : ℝ}
  (fbound : ∀ (x:G), f x ≤ M) : m f ≤ M :=
begin
  -- strategy of proof : (M-f) is a positive function
  let diff : bounded_continuous_function G ℝ := bounded_continuous_function.const G M  - f,

  have diffpos : ∀ (x:G), diff x ≥ 0,
  { assume (x:G),
    dsimp[diff],
    by linarith only [fbound x], },

  have mdiffpos : m diff ≥ 0 := m.positivity diffpos,

  have mean_const : m (bounded_continuous_function.const G M) = M,
  {calc   m (bounded_continuous_function.const G M)
        = m (M • bounded_continuous_function.const G 1)
          : by congr';
              begin
                ext (x:G),
                simp,
              end
    ... = M • m (bounded_continuous_function.const G 1)
          : by exact m.lin_map.map_smul' M _
    ... = M • 1
          : by congr'; exact m.normality
    ... = M
          : by simp,},


  have : m f + m diff = M := by
  calc  m f + m diff
      = m (f + diff)
        : by exact (m.lin_map.map_add' f diff).symm
  ... = m (f + bounded_continuous_function.const G M - f)
        : by simp[diff]
  ... = m (bounded_continuous_function.const G M )
        : by simp
  ... = M
        : by simp [mean_const],

  by linarith only [this, mdiffpos],
end



/--Essentially: W.r.t. the sup-norm, m has norm ≤ 1-/
lemma mean_bounded_abs (m : mean G) {f: bounded_continuous_function G ℝ}
  {M : ℝ} (fbound : ∀ (x:G), |f x| ≤ M) : |m f| ≤ M :=
begin
  have bound_le : m f ≤ M,
  { have fbound' :  ∀ (x:G), f x ≤ M := (λ x, (abs_le.mp (fbound x)).2),
    exact mean_bounded G m fbound',},

  have bound_ge : m f ≥ -M,
  { have negfbound' :  ∀ (x:G), (-f) x ≤ M,
    { assume x:G,
      simp,
      by linarith[(abs_le.mp (fbound x)).1], },
    have : m (-f) ≤ M := mean_bounded G m negfbound',
    have : m (-f) = - m f := mean_of_neg G m,
    by linarith, },
  exact abs_le.mpr (and.intro bound_ge bound_le),
end


@[simp]
lemma mean_add {m : mean G} {f g: bounded_continuous_function G ℝ} : m (f+g) = m f + m g :=
m.lin_map.map_add' f g



@[simp]
lemma mean_smul {m : mean G} {f: bounded_continuous_function G ℝ} {r :ℝ} :
  m (r•f) = r • (m f) :=
m.lin_map.map_smul' r f


/--Means are monotone functions-/
lemma mean_monotone {m : mean G} {f g: bounded_continuous_function G ℝ}
  (f_le_g : f ≤ g) : m f ≤ m g :=
begin
  have diff_pos: ∀ (x:G), (g-f) x ≥ 0,
  { assume x:G,
    have : (g-f) x = g x - f x
      := by refl,
    rw this,
    simp,
    exact f_le_g x, },
  calc  m f
      = m f + 0
        : by ring
  ... ≤  m f + m (g-f)
        : by {simp, exact m.positivity diff_pos,}
  ... = m (f+(g-f))
        : by rw mean_add
  ... = m g
        : by congr'; ring,
end





end el_facts



section pushforward_mean

/-!
### Pushforwards of Means

We will often use the following construction: If `m` is a mean on `H`
and `π : G → H` is any map, we can obtain a mean on `G`
by composing with `π`.

-/


variables {H : Type* } [topological_space H] [group H] [topological_group H]
(π: G → H)
(π_cont: continuous π)

variable {G}


/-- Precomposition with a map, when we have discrete topology-/
def bcont_precomp_discrete  {X Y: Type*}  [topological_space X] [discrete_topology X]
  [topological_space Y] (h : X → Y) (f : bounded_continuous_function Y ℝ) :
  bounded_continuous_function X ℝ :=
f.comp_continuous (continuous_map.mk h continuous_of_discrete_topology)



def comp_bcont (f: bounded_continuous_function H ℝ) : bounded_continuous_function G ℝ :=
f.comp_continuous (continuous_map.mk π π_cont)


@[simp]
lemma comp_bcont_eval (π : G → H) (π_cont: continuous π) (f: bounded_continuous_function H ℝ)
  (g :G) : comp_bcont π π_cont f g = f (π g) :=
by refl

@[simp]
def pull_bcont (π : G → H) (π_cont: continuous π) :
  (bounded_continuous_function H ℝ) →ₗ[ℝ] (bounded_continuous_function G ℝ) :=
{ to_fun    := (λ f, comp_bcont π π_cont f),
  map_add'  := by tauto,
  map_smul' := by tauto }



include π

@[simp]
noncomputable def mean_pushforward_linmap {π : G → H} (π_cont: continuous π)
  (m : mean G) : (bounded_continuous_function H ℝ) →ₗ[ℝ] ℝ :=
linear_map.comp m.lin_map (pull_bcont π π_cont)

lemma mean_pushforward_norm {π : G → H} (π_cont: continuous π) (m : mean G) :
  (mean_pushforward_linmap π_cont m) (bounded_continuous_function.const H (1:ℝ)) = 1 :=
begin
  -- the pushforward of the 1-function is the 1-function
  have  pull_of_one
        : (pull_bcont π π_cont) (bounded_continuous_function.const H (1:ℝ))
        = bounded_continuous_function.const G (1:ℝ),
  {ext (x:G), simp,},
  calc  (mean_pushforward_linmap π_cont m) (bounded_continuous_function.const H (1:ℝ))
      = m.lin_map (pull_bcont π π_cont (bounded_continuous_function.const H (1:ℝ)))
        : by tauto
  ... = m.lin_map (bounded_continuous_function.const G (1:ℝ))
        : by rw pull_of_one
  ... = 1
        : m.normality,
end

lemma mean_pushforward_pos {π : G → H} (π_cont: continuous π ) (m : mean G) :
  ∀ (f : bounded_continuous_function H ℝ),
  (∀ (x:H), f(x) ≥ 0) → (mean_pushforward_linmap π_cont m) f ≥ 0 :=
begin
  assume f fnonneg,

  apply m.positivity,
  -- key step: pull_bcont π f is also nonneg
  change ∀(x:G), (pull_bcont π π_cont f) x ≥ 0,

  assume (x:G),
  specialize fnonneg (π x),
  by tauto,
end

/-- The mean on H, induced by the mean on G-/
@[simp]
noncomputable def mean_pushforward (π : G → H) (π_cont: continuous π) (m : mean G) :
  mean H :=
{ lin_map     := mean_pushforward_linmap π_cont m,
  normality   := mean_pushforward_norm π_cont m,
  positivity  := mean_pushforward_pos π_cont m }


end pushforward_mean


end mean
