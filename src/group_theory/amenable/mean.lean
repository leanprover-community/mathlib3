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
import algebra.order.hom.monoid

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

variables (G:Type*) [uniform_space G] [group G] [topological_group G]


set_option old_structure_cmd true

structure mean extends
  bounded_continuous_function G ℝ →ₗ[ℝ] ℝ,
  one_hom (bounded_continuous_function G ℝ) ℝ,
  order_hom (bounded_continuous_function G ℝ) ℝ.

class mean_class (F : out_param Type*) (G : Type*) [uniform_space G] [group G] [topological_group G]
  extends
    semilinear_map_class F (ring_hom.id ℝ) (bounded_continuous_function G ℝ) ℝ,
    one_hom_class F (bounded_continuous_function G ℝ) ℝ,
    rel_hom_class F ((≤) : _ → bounded_continuous_function G ℝ → Prop) ((≤) : ℝ → ℝ → Prop).

instance mean.mean_class : mean_class (mean G) G :=
{ coe := mean.to_fun,
  coe_injective' := λ f g h, by { cases f, cases g, congr' },
  map_one := λ f, map_one f.to_one_hom,
  map_add := λ f, map_add f.to_linear_map,
  map_smulₛₗ := λ f, map_smul f.to_linear_map,
  map_rel := λ f, order_hom_class.monotone f.to_order_hom }


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



lemma mean_const {m : mean G} {M : ℝ} : m (bounded_continuous_function.const G M) = M :=
begin
  calc  m (bounded_continuous_function.const G M)
      = m (M• bounded_continuous_function.const G (1:ℝ))
        : by congr';
              begin
                ext (x:G),
                simp,
              end
  ... = M • m (bounded_continuous_function.const G (1:ℝ))
        : by norm_num
  ... = M • 1
        : by {congr' 1, exact m.to_one_hom.map_one',}
  ... = M
        : by simp,
end



lemma mean_bounded (m : mean G) {f: bounded_continuous_function G ℝ} {M : ℝ}
  (fbound : ∀ (x:G), f x ≤ M) : m f ≤ M :=
begin
  have fle  : f ≤ bounded_continuous_function.const G M := by {intro x,simp[fbound x],},
  calc  m f
      ≤ m (bounded_continuous_function.const G M) : by exact m.to_order_hom.monotone' fle
  ... = M                                         : mean_const _,
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
    have : m (-f) = - m f := map_neg m f,
    by linarith, },
  exact abs_le.mpr (and.intro bound_ge bound_le),
end


@[simp]
lemma mean_add {m : mean G} {f g: bounded_continuous_function G ℝ} : m (f+g) = m f + m g :=
m.to_linear_map.map_add' f g



@[simp]
lemma mean_smul {m : mean G} {f: bounded_continuous_function G ℝ} {r :ℝ} :
  m (r•f) = r • (m f) :=
m.to_linear_map.map_smul' r f


end el_facts



section pushforward_mean

/-!
### Pushforwards of Means

We will often use the following construction: If `m` is a mean on `H`
and `π : G → H` is any map, we can obtain a mean on `G`
by composing with `π`.

-/


variables {H : Type* } [uniform_space H] [group H] [topological_group H]
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
linear_map.comp m.to_linear_map (pull_bcont π π_cont)

lemma mean_pushforward_norm {π : G → H} (π_cont: continuous π) (m : mean G) :
  (mean_pushforward_linmap π_cont m) (bounded_continuous_function.const H (1:ℝ)) = 1 :=
begin
  -- the pushforward of the 1-function is the 1-function
  have  pull_of_one
        : (pull_bcont π π_cont) (bounded_continuous_function.const H (1:ℝ))
        = bounded_continuous_function.const G (1:ℝ),
  {ext (x:G), simp,},
  calc  (mean_pushforward_linmap π_cont m) (bounded_continuous_function.const H (1:ℝ))
      = m.to_linear_map (pull_bcont π π_cont (bounded_continuous_function.const H (1:ℝ)))
        : by tauto
  ... = m.to_linear_map (bounded_continuous_function.const G (1:ℝ))
        : by rw pull_of_one
  ... = 1
        : m.to_one_hom.map_one',
end


lemma mean_pushforward_mon {π : G → H} (π_cont: continuous π ) (m : mean G) :
  monotone (mean_pushforward_linmap π_cont m) :=
begin
  assume f g fleg,
  simp,
  apply m.to_order_hom.monotone',
  intro x,
  simp,
  exact fleg _,
end

/-- The mean on H, induced by the mean on G-/
@[simp]
noncomputable def mean_pushforward (π : G → H) (π_cont: continuous π) (m : mean G) :
  mean H :=
{ to_fun        :=  (mean_pushforward_linmap π_cont m),
  map_add'      :=  (mean_pushforward_linmap π_cont m).map_add',
  map_smul'     :=  (mean_pushforward_linmap π_cont m).map_smul',
  map_one'      := mean_pushforward_norm π_cont m,
  monotone'     := mean_pushforward_mon π_cont m, }



end pushforward_mean


end mean
