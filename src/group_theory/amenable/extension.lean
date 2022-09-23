/-
Copyright (c) 2022 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold.
-/

import .def_amenable
import .quotient
import .subgroup
import .aux_lemmas_sums
import .aux_lemmas_bounded
import topology.continuous_function.bounded
import topology.continuous_function.basic
import group_theory.quotient_group

/-!
# Extensions of Amenable Groups

We prove that extensions of amenable groups are again amenable.

## Main Statements
- `amenable_of_extension` : Group extensions of amenable groups are amenable,
                            i.e. if G is a group, N is a normal subgroup and
                            N and G/N are amenable, then so is G.
- `amenable_of_extension_iff` : A group extension G of a normal subgroup N
                                by the quotient G ⧸ N is amenable if and only
                                if N and G ⧸ N are.
## Implementation Notes

We follow the proof of [C. Löh, *Geometric Group Theory*, Proposition 9.1.6 (3)][loeh17].


## References
* [C. Löh, *Geometric Group Theory*, Proposition 9.1.6 (3)][loeh17]
* <https://en.wikipedia.org/wiki/Amenable_group>
* [A.L.T. Paterson, *Amenability*, Proposition 0.16 (3)][Paterson1988]


## Tags

amenable extension, amenable, extension

-/


open classical
open function


namespace amenable_of_extension

variables
{G:Type*}
[group G]
{N : subgroup G}
(nN : N.normal)




local notation `Q` := G ⧸ N

/--choose a split of the quotient map G → G/N -/
noncomputable def split
  (nN : N.normal)
  : Q → G
:= (λ q, classical.some (quotient_group.mk'_surjective N q))

@[simp]
lemma split_spec
  (nN : N.normal)
  {q : Q}
  : (quotient_group.mk' N) (split nN q) = q
:= begin
  unfold split,
  exact classical.some_spec (quotient_group.mk'_surjective N q),
end


/-! The main idea is the following:
  Choose means mN on N and mQ on Q := G / N,
  then we obtain a mean on G as follows:

  For any f: G → ℝ, we define a function Q → ℝ
  as follows:
  For q : Q, define its value by the
   mean mN of the function (n ↦  split (q)*n)

  Then, take the mQ-mean of that function Q → ℝ
   -/

/--The restriction to the left class on N-/
noncomputable def bound_cont_rest_N
  (mN: mean N)
  (f : bounded_continuous_function G ℝ)
  (q : Q)
  : bounded_continuous_function N ℝ
  := bounded_continuous_function.mk
          (continuous_map.mk (λ n:N, f((split nN q)*n))
                            -- proof that the map is continous
                            continuous_of_discrete_topology)
          -- proof of boundedness
          (begin
              rcases f.bounded with ⟨C, hbound⟩,
              use C,
              assume n m : N,
              simp,
              exact hbound _ _,
          end )

@[simp]
lemma bound_cont_rest_N_apply
  (mN: mean N)
  (f : bounded_continuous_function G ℝ)
  (q : Q)
  (n : N)
  : bound_cont_rest_N nN mN f q n = f((split nN q)*n)
:= by refl

@[simp]
noncomputable def fun_on_quotient
  (mN: mean N)
  (f : bounded_continuous_function G ℝ)
  : Q → ℝ
  := (λ q, mN (bound_cont_rest_N nN mN f q))


noncomputable def bounded_fun_on_quotient
  (mN: mean N)
  (nN : N.normal)
  (f : bounded_continuous_function G ℝ)
  : bounded_continuous_function Q ℝ
:= bounded_continuous_function.mk
        (continuous_map.mk (fun_on_quotient nN mN f) continuous_of_discrete_topology)
        (begin
          -- rw to classical formulation of boundedness
          have fbounded : ∃ (C:ℝ), ∀ (x:G), abs (f x) ≤ C
            := function_bounded_classical.mp f.bounded,
          rw function_bounded_classical,

          rcases fbounded with ⟨C, fbounded⟩,
          use C,
          assume x,
          simp,
          have : ∀ (n:N), |(bound_cont_rest_N nN mN f x) n| ≤ C,
          {
            assume n:N,
            dsimp[bound_cont_rest_N],
            exact fbounded ((split nN x)*n),
          },
          exact mean.mean_bounded_abs N mN this,
        end )

@[simp]
lemma bounded_fun_on_quotient_apply
  (mN: mean N)
  (nN : N.normal)
  (f : bounded_continuous_function G ℝ)
  (q : Q)
  : bounded_fun_on_quotient mN nN f q = mN (bound_cont_rest_N nN mN f q)
:= by refl

lemma bounded_fun_quot_add
  (mN: mean N)
  (nN : N.normal)
  (f g : bounded_continuous_function G ℝ)
  (q:Q)
  :   bound_cont_rest_N nN mN (f + g) q
    = bound_cont_rest_N nN mN f q
    + bound_cont_rest_N nN mN g q
:= begin
  ext (n:N),
  simp,
end

lemma bounded_fun_quot_smul
  (mN: mean N)
  (nN : N.normal)
  (f : bounded_continuous_function G ℝ)
  (r : ℝ)
  (q:Q)
  :   bound_cont_rest_N nN mN (r • f) q
    = r • bound_cont_rest_N nN mN f q
:= begin
  ext (n:N),
  simp,
end

noncomputable def to_bounded_fun_on_quotient
  (mN: mean N)
  : (bounded_continuous_function G ℝ) →ₗ[ℝ] (bounded_continuous_function Q ℝ)
:= linear_map.mk (λ f, bounded_fun_on_quotient mN nN f)
                  (begin
                    assume f g,
                    ext (q:Q),
                    simp,
                    rw bounded_fun_quot_add,
                    exact mN.lin_map.map_add' _ _,
                  end )
                  (begin
                    assume r f,
                    ext (q:Q),
                    simp,
                    rw bounded_fun_quot_smul,
                    exact mN.lin_map.map_smul' _ _,
                  end )
@[simp]
lemma to_bounded_fun_on_quotient_apply
  (mN: mean N)
  (f : bounded_continuous_function G ℝ)
  : to_bounded_fun_on_quotient nN mN f = bounded_fun_on_quotient mN nN f
:= by refl

/--The map that will become the mean on G-/
noncomputable def extension_mean_linmap
  (mN: mean N)
  (nN : N.normal)
  (mQ: mean Q)
  : (bounded_continuous_function G ℝ) →ₗ[ℝ] ℝ
:= linear_map.comp mQ.lin_map (to_bounded_fun_on_quotient nN mN)

lemma extension_mean_norm
  (mN: mean N)
  {nN : N.normal}
  (mQ: mean Q)
  : (extension_mean_linmap mN nN mQ) (bounded_continuous_function.const G (1:ℝ)) = (1:ℝ)
:= begin
  have : (to_bounded_fun_on_quotient nN mN) (bounded_continuous_function.const G (1:ℝ))
        = (bounded_continuous_function.const Q (1:ℝ)),
  {
    ext (q:Q),
    simp,
    have : bound_cont_rest_N nN mN (bounded_continuous_function.const G 1) q
          = bounded_continuous_function.const N 1,
    {
      ext (n:N),
      by simp,
    },
    rw this,
    exact mN.normality,
  },
  calc (extension_mean_linmap mN nN mQ) (bounded_continuous_function.const G (1:ℝ))
      = mQ ((to_bounded_fun_on_quotient nN mN) (bounded_continuous_function.const G (1:ℝ)))
      : by tauto
  ... = mQ (bounded_continuous_function.const Q (1:ℝ))
      : by congr'; exact this
  ... = (1:ℝ)
      : by exact mQ.normality,
end


lemma extension_mean_pos
  (mN: mean N)
  {nN : N.normal}
  (mQ: mean Q)
  : ∀ (f : bounded_continuous_function G ℝ),
                          (∀ (x:G), f x ≥ 0) → (extension_mean_linmap mN nN mQ) f ≥ 0
:= begin
  assume f fpos,

  have : ∀(q:Q), to_bounded_fun_on_quotient nN mN f q ≥ 0,
  {
    assume q:Q,
    simp,
    --we want to apply positivity of N here
    apply mN.positivity,
    assume n:N,
    simp,
    exact fpos _,
  },

  calc (extension_mean_linmap mN nN mQ) f
      = mQ ((to_bounded_fun_on_quotient nN mN) f)
      : by tauto
  ... ≥ 0
      : by exact mQ.positivity this,
end

/--the mean on G-/
noncomputable def extension_mean
  (mN: mean N)
  {nN : N.normal}
  (mQ: mean Q)
  : mean G
:= mean.mk (extension_mean_linmap mN nN mQ)
           (extension_mean_norm _ _ )
           (extension_mean_pos _ _)


/-! Some Lemmas for establishing left-invariance of extension_mean -/
lemma rw_ginv_splitq
  (g:G)
  (q:Q)
  : ∃ n':N, g⁻¹ * (split nN q) = (split nN ((quotient_group.mk' N g⁻¹)*q)) * n'⁻¹
:= begin
  let n : G := (split nN q)⁻¹ * g  * split nN ((quotient_group.mk' N g⁻¹)*q),
  have : quotient_group.mk' N n = 1,
  {
   calc  quotient_group.mk' N n
       = quotient_group.mk' N ((split nN q)⁻¹ * g  * split nN ((quotient_group.mk' N g⁻¹)*q))
          : by simp [n]
    ... = (quotient_group.mk' N ((split nN q)⁻¹ * g)) *
          (quotient_group.mk' N (split nN ((quotient_group.mk' N g⁻¹)*q)))
          : map_mul (quotient_group.mk' N) ((split nN q)⁻¹ * g) (split nN ((quotient_group.mk' N) g⁻¹ * q))
    ... = (quotient_group.mk' N ((split nN q)⁻¹))*
          (quotient_group.mk' N  g) *
          (quotient_group.mk' N (split nN ((quotient_group.mk' N g⁻¹)*q)))
          : by congr' 1;simp
    ... = (quotient_group.mk' N ((split nN q)⁻¹))*
          (quotient_group.mk' N  g) *
          ((quotient_group.mk' N g⁻¹)*q)
          : by simp
    ... = (quotient_group.mk' N (split nN q))⁻¹*
          (quotient_group.mk' N  g) *
          ((quotient_group.mk' N g⁻¹)*q)
          : by congr' 2; simp
    ... = q⁻¹* (quotient_group.mk' N  g) *
          ((quotient_group.mk' N g⁻¹)*q)
          : by congr' 2; simp
    ... = q⁻¹* (quotient_group.mk' N  g) *
          ((quotient_group.mk' N g)⁻¹*q)
          : by congr' 2; simp
    ... = 1
          : by group,
  },
  have ninN: n ∈ N,
  {
    rw ← quotient_group.eq_one_iff n,
    exact this,
  },
  use ⟨n, ninN⟩,
  dsimp[n],
  by group,
end


lemma bound_cont_rest_N_transl
  (mN: mean N)
  (f : bounded_continuous_function G ℝ)
  (q : Q)
  (g : G) -- element to translate by
  : ∃ (n' : N),
    bound_cont_rest_N  nN mN (left_translate g f) q
  = left_translate n' (bound_cont_rest_N nN mN f ((quotient_group.mk g⁻¹)*q))
:= begin
  have : ∃ n':N, g⁻¹ * (split nN q) = (split nN ((quotient_group.mk' N g⁻¹)*q)) * n'⁻¹
        := rw_ginv_splitq _ _ _,
  rcases this with ⟨n', hn'⟩,
  use n',
  ext (n:N),
  rw left_translate_eval,
  simp,
  congr' 1,
  change g⁻¹ * (split nN q * ↑n) = split nN (quotient_group.mk' N g⁻¹ * q) * ((↑n')⁻¹ * ↑n),
  calc  g⁻¹ * (split nN q * ↑n)
      = (g⁻¹ * split nN q) * ↑n
        : by group
  ... = ((split nN ((quotient_group.mk' N g⁻¹)*q)) * n'⁻¹)*n
        : by rw hn'
  ... = split nN (quotient_group.mk' N g⁻¹ * q) * ((↑n')⁻¹ * ↑n)
        : by rw mul_assoc,
end

lemma bounded_fun_on_quotient_transl
  (mN: left_invariant_mean N)
  (f : bounded_continuous_function G ℝ)
  (q : Q)
  (g : G) -- element to translate by
  : bounded_fun_on_quotient mN.to_mean nN (left_translate g f) q
  = bounded_fun_on_quotient mN.to_mean nN f ((quotient_group.mk g⁻¹)*q)
:= begin
  simp,
  rcases bound_cont_rest_N_transl nN mN f q g with ⟨n, nprop⟩,
  calc  mN.to_mean (bound_cont_rest_N nN mN.to_mean (left_translate g f) q)
      = mN.to_mean (left_translate n (bound_cont_rest_N nN mN f ((quotient_group.mk g⁻¹)*q)))
        : by {congr' 1,}
  ... = mN.to_mean (bound_cont_rest_N nN mN f ((quotient_group.mk g⁻¹)*q))
        : by exact mN.left_invariance n _,
end

/-- a left-translate version-/
lemma bounded_fun_on_quotient_transl'
  (mN: left_invariant_mean N)
  (f : bounded_continuous_function G ℝ)
  (g : G) -- element to translate by
  : bounded_fun_on_quotient mN.to_mean nN (left_translate g f)
  = left_translate (quotient_group.mk g⁻¹)⁻¹
      (bounded_fun_on_quotient mN.to_mean nN f)
:= begin
  ext (q:Q),
  by simp [bounded_fun_on_quotient_transl nN mN f q g],
end


lemma extension_mean_leftinv
  (mN: left_invariant_mean N)
  {nN : N.normal}
  (mQ: left_invariant_mean Q)
  : ∀(g:G), ∀(f: bounded_continuous_function G ℝ),
      (extension_mean mN.to_mean mQ) (left_translate g f)
    = (extension_mean mN.to_mean mQ) f
:= begin
  assume g:G,
  assume f: bounded_continuous_function G ℝ,
  calc  (extension_mean mN.to_mean mQ) (left_translate g f)
      = mQ (bounded_fun_on_quotient mN.to_mean nN (left_translate g f))
        : by tauto
  ... = mQ (left_translate (quotient_group.mk g⁻¹)⁻¹
      (bounded_fun_on_quotient mN.to_mean nN f))
        : by rw bounded_fun_on_quotient_transl'
  ... = mQ (bounded_fun_on_quotient mN.to_mean nN f)
        : by exact mQ.left_invariance (quotient_group.mk g⁻¹)⁻¹ _
  ... = (extension_mean mN.to_mean mQ) f
        : by tauto,
end

/--A left-invariant mean on G-/
noncomputable def extension_invmean
  (mN: left_invariant_mean N)
  {nN : N.normal}
  (mQ: left_invariant_mean Q)
  : left_invariant_mean G
:= left_invariant_mean.mk (extension_mean mN.to_mean mQ) (extension_mean_leftinv mN mQ)


end amenable_of_extension



/--Theorem: Extensions of amenable groups are amenable -/
theorem amenable_of_extension
  {G:Type*}
  [group G]
  {N : subgroup G}
  (N_am : amenable N)
  (nN : N.normal)
  (Q_am : amenable (G ⧸ N))
  : amenable G
:= amenable_of_invmean (amenable_of_extension.extension_invmean (invmean_of_amenable N_am)
                                         (invmean_of_amenable Q_am))


/--An extension is amenable iff a normal subgroup and its quotient are amenable-/
theorem amenable_of_extension_iff
  {G:Type*}
  [group G]
  {N : subgroup G}
  (nN : N.normal)
  : amenable G ↔ amenable N ∧ amenable (G⧸N)
:= begin
  have mp : amenable G →  amenable N ∧ amenable (G⧸N),
  {
    assume G_am : amenable G,
    exact ⟨amenable_of_subgroup N G_am,
            amenable_of_quotient nN G_am⟩,
  },
  have mpr : amenable N ∧ amenable (G⧸N) → amenable G
      := (λ h, amenable_of_extension h.1 nN h.2),
  exact ⟨mp, mpr⟩,
end
