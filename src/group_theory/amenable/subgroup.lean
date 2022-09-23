/-
Copyright (c) 2022 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold.
-/

import .aux_lemmas_iso_range
import .quotient
import topology.continuous_function.bounded
import topology.continuous_function.basic


/-!
# Subgroups of Amenable groups

In this file, we prove that subgroups of amenable groups are again amenable

## Main Statements
- `amenable_of_subgroup`  : Subgroups of amenable Groups are amenable.
- `amenable_of_subgroup'` : alternative formulation for injective group homomorphisms

## Notations

We use the local notation `rrel` for the relation
defined by the right cosets of a subgroup H of G.

## References
* <https://en.wikipedia.org/wiki/Amenable_group>
* [C. Löh, *Geometric Group Theory*, Proposition 9.1.6 (1)][loeh17]
* [A.L.T. Paterson, *Amenability*, Proposition 0.16 (1)][Paterson1988]


## Tags
subgroup, inclusion, amenable, amenability
-/

open classical
open function


variables
{G:Type*}
[group G]
(H: subgroup G)


namespace amenable_subgroup



/-The right relation -/
local notation `rrel` := (quotient_group.right_rel H)


/--Choose one representative for each right coset-/
noncomputable def choose_rep
  : G → G
:=   (@quotient.out' G rrel) ∘ (@quotient.mk' G rrel)


lemma choos_rep_rel'
  {h :H} {g : G}
  : g*(h*g)⁻¹ ∈ H
:= by simp

/--related elements have the same image under choose_rep-/
lemma choose_rep_rel
  {h :H} {g : G}
  : choose_rep H (h*g) = choose_rep H g
:= begin
  unfold choose_rep,
  have : @quotient.mk' _ rrel (h*g)
      = @quotient.mk' _ rrel g,
  {
    have : (@setoid.r _ rrel) (h*g) g,
    {
      rw quotient_group.right_rel_apply,
      by simp,
    },
    exact quotient.eq'.mpr this,
  },
  by finish,
end

open setoid

lemma choose_rep_prop'
  (g:G)
  : (@setoid.r _ rrel) (@choose_rep G _ H g) g
:= begin
  have : (@quotient.mk' G rrel) (@choose_rep G _ H g) = (@quotient.mk' G rrel) g,
  {
    dsimp[choose_rep],
    simp,
    exact quotient.eq'.mp rfl,
  },
  exact quotient.eq'.mp this,
end


/-- Every element can be translated to its representative-/
lemma choose_rep_prop
  (g:G)
  : ∃(h:H), (h:G) * (choose_rep H g) = g
:= begin
  have : (@setoid.r _ rrel) (@choose_rep G _ H g) g
      := choose_rep_prop' H g,
  rw quotient_group.right_rel_apply at this,
  let h : H := ⟨g*(@choose_rep G _ H g)⁻¹, this⟩,
  use h,
  dsimp[h],
  by group,
end


/-- choose an element of H (the one we have to translate by to obtain
the representative)-/
noncomputable def choose_repH
  : G → H
:= (λ g, classical.some (choose_rep_prop H g))


lemma choose_repH_prop
  {g:G}
  : (choose_repH H g :G) * (choose_rep H g) = g
:= classical.some_spec (choose_rep_prop H g)

lemma choose_repH_lin
  (h :H) (g : G)
  : choose_repH H (h*g) = h*(choose_repH H g)
:= begin
  have : (choose_repH H (h*g) :G) * choose_rep H (h*g) = (h*(choose_repH H (g))) * choose_rep H (h*g),
  {
    calc  (choose_repH H (h*g) :G) * choose_rep H (h*g)
        = h*g
          : by exact choose_repH_prop H
    ... = h * ((choose_repH H g :G) * choose_rep H g)
          : by simp [choose_repH_prop]
    ... = (h * (choose_repH H g :G)) * choose_rep H g
          : by group
    ... = (h * (choose_repH H g :G)) * choose_rep H (h*g)
          : by simp[choose_rep_rel H],
  },
  -- Then, use uniqueness
  have eq_G: (choose_repH H (h*g):G) = (h*(choose_repH H g) :G)
        := (mul_left_inj (choose_rep H (↑h * g))).mp this,
  by exact subtype.ext eq_G,
end


open mean

/--We push forward the mean via the choose_repH-map-/
noncomputable def extend_mean
  (m : mean G)
  : mean H
:= mean_pushforward (choose_repH H) m

/--This mean is left-invariant.-/
lemma extend_inv_mean_inv
  (m : left_invariant_mean G)
  : ∀(h:H), ∀(f: bounded_continuous_function H ℝ),
      (extend_mean H m) (left_translate h f)
    = (extend_mean H m) f
:= begin
  assume h:H,
  assume  f: bounded_continuous_function H ℝ,
  -- left-translate commutes with pullback
  have pullb_left_transl
        : pull_bcont (choose_repH H) (left_translate h f)
        = left_translate h (pull_bcont (choose_repH H) f),
  {
    ext (x:G),
    calc    pull_bcont (choose_repH H) (left_translate h f) x
        = (left_translate h f) (choose_repH H x)
            : by tauto
    ... = f (h⁻¹ * (choose_repH H x))
            : by tauto
    ... = f (choose_repH H (h⁻¹*x))
            : by simp [(choose_repH_lin H h⁻¹ x).symm]
    ... = left_translate (h:G) (pull_bcont (choose_repH H) f) x
            : by tauto,
  },
  calc  (extend_mean H m) (left_translate h f)
      = m (pull_bcont (choose_repH H) (left_translate h f))
        : by tauto
  ... = m (left_translate h (pull_bcont (choose_repH H) f))
        : by rw pullb_left_transl
  ... = m (pull_bcont (choose_repH H) f)
        : by exact m.left_invariance _ _
  ... = (extend_mean H m) f
        : by tauto,
end

/--left-invariant mean for the subgroup-/
noncomputable def extend_inv_mean
  (m : left_invariant_mean G)
  : left_invariant_mean H
:= left_invariant_mean.mk (extend_mean H m) (extend_inv_mean_inv H m)


end amenable_subgroup


/--Subgroups of amenable groups are amenable-/
theorem amenable_of_subgroup
  (H : subgroup G)
  (G_am : amenable G)
  : amenable H
:= amenable_of_invmean (amenable_subgroup.extend_inv_mean H (invmean_of_amenable G_am))


/--Alternative formulation involving injective group homs-/
theorem amenable_of_subgroup'
  {H : Type*} [group H]
  {i : H →* G}
  (i_inj: injective i)
  (G_am : amenable G)
  : amenable H
:= begin
  have H_iso_range: H ≃* i.range
      := iso_range_of_injective i_inj,
  have i_range_am : amenable i.range
      := amenable_of_subgroup i.range G_am,
  exact amenable_of_iso H_iso_range.symm i_range_am,
end
