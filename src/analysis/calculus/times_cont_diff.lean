/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.calculus.deriv

/-!
# Higher differentiability

A function is `C^1` on a domain if it is differentiable there, and its derivative is continuous.
By induction, it is `C^n` if it is `C^{n-1}` and its (n-1)-th derivative is `C^1` there or,
equivalently, if it is `C^1` and its derivative is `C^{n-1}`.
Finally, it is `C^∞` if it is `C^n` for all n.

We formalize these notions by defining iteratively the n-th derivative of a function at the
(n-1)-th derivative of the derivative. It is called `iterated_fderiv 𝕜 n f x` where `𝕜` is the
field, `n` is the number of iterations, `f` is the function and `x` is the point. We also define a
version `iterated_fderiv_within` relative to a domain, as well as predicates `times_cont_diff 𝕜 n f`
and `times_cont_diff_on 𝕜 n f s` saying that the function is `C^n`, respectively in the whole space
or on the set `s`.

We prove basic properties of these notions.

## Implementation notes

The n-th derivative of a function belongs to the space E →L[𝕜] (E →L[𝕜] (E ... F)...))),
where there are n iterations of `E →L[𝕜]`. We define this space inductively, call it
`iterated_continuous_linear_map 𝕜 n E F`, and denote it by `E [×n]→L[𝕜] F`. We can define
it inductively either from the left (i.e., saying that the
(n+1)-th space S_{n+1} is E →L[𝕜] S_n) or from the right (i.e., saying that
the (n+1)-th space associated to F, denoted by S_{n+1} (F), is equal to S_n (E →L[𝕜] F)).
For proofs, it turns out to be more convenient to use the latter approach (from the right),
as it means to prove things at the (n+1)-th step we only need to understand well enough the
derivative in E →L[𝕜] F (contrary to the approach from the left, where one would need to know
enough on the n-th derivative to deduce things on the (n+1)-th derivative).
In other words, one could define the (n+1)-th derivative either as the derivative of the n-th
derivative, or as the n-th derivative of the derivative. We use the latter definition.

A difficulty is related to universes: the first and second spaces in the sequence, for n=0
and 1, are F and E →L[𝕜] F. If E has universe u and F has universe v, then the first one lives in
v and the second one in max v u. Since they should live in the same universe (as all the other
spaces in the construction), it means that at the 0-th step we should not use F, but ulift it to
universe max v u. But we should also ulift its vector space structure and its normed space
structure. This can certainly be done, but I decided it was not worth it for now. Therefore, the
definition is only made when E and F live in the same universe.

Regarding the definition of `C^n` functions, there are two equivalent definitions:
* require by induction that the function is differentiable, and that its derivative is C^{n-1}
* or require that, for all m ≤ n, the m-th derivative is continuous, and for all m < n the m-th
derivative is differentiable.
The first definition is more efficient for many proofs by induction. The second definition is more
satisfactory as it gives concrete information about the n-th derivative (contrary to the first point
of view), and moreover it also makes sense for n = ∞.

Therefore, we give (and use) both definitions, named respectively `times_cont_diff_rec` and
`times_cont_diff` (as well as relativized versions on a set). We show that they are equivalent.
The first one is mainly auxiliary: in applications, one should always use `times_cont_diff`
(but the proofs below use heavily the equivalence to show that `times_cont_diff` is well behaved).

## Tags

derivative, differentiability, higher derivative, C^n

-/

noncomputable theory
local attribute [instance, priority 10] classical.decidable_inhabited classical.prop_decidable

universes u v w

open set

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type u} [normed_group E] [normed_space 𝕜 E]
{F : Type u} [normed_group F] [normed_space 𝕜 F]
{G : Type u} [normed_group G] [normed_space 𝕜 G]
{s s₁ u : set E} {f f₁ : E → F} {f' f₁' : E →L[𝕜] F} {f₂ : E → G}
{f₂' : E →L[𝕜] G} {g : F → G} {x : E} {c : F}
{L : filter E} {t : set F} {b : E × F → G} {sb : set (E × F)} {p : E × F}
{n : ℕ}

include 𝕜

/--
The space `iterated_continuous_linear_map 𝕜 n E F` is the space E →L[𝕜] (E →L[𝕜] (E ... F)...))),
defined inductively over `n`. This is the space to which the `n`-th derivative of a function
naturally belongs. It is only defined when `E` and `F` live in the same universe.
-/
def iterated_continuous_linear_map (𝕜 : Type w) [nondiscrete_normed_field 𝕜] :
  Π (n : ℕ) (E : Type u) [gE : normed_group E] [@normed_space 𝕜 E _ gE]
    (F : Type u) [gF : normed_group F] [@normed_space 𝕜 F _ gF], Type u
| 0     E _ _ F _ _ := F
| (n+1) E _ _ F _ _ := by { resetI, exact iterated_continuous_linear_map n E (E →L[𝕜] F) }

notation E `[×`:25 n `]→L[`:25 𝕜 `] ` F := iterated_continuous_linear_map 𝕜 n E F

/--
Define by induction a normed group structure on the space of iterated continuous linear
maps. To avoid `resetI` in the statement, use the @ version with all parameters. As the equation
compiler chokes on this one, we use the `nat.rec_on` version.
-/
def iterated_continuous_linear_map.normed_group_rec (𝕜 : Type w) [h𝕜 : nondiscrete_normed_field 𝕜]
  (n : ℕ) (E : Type u) [gE : normed_group E] [sE : normed_space 𝕜 E] :
  ∀(F : Type u) [nF : normed_group F] [sF : @normed_space 𝕜 F _ nF],
  normed_group (@iterated_continuous_linear_map 𝕜 h𝕜 n E gE sE F nF sF) :=
nat.rec_on n (λF nF sF, nF) (λn aux_n F nF sF, by { resetI, apply aux_n })

/--
Define by induction a normed space structure on the space of iterated continuous linear
maps. To avoid `resetI` in the statement, use the @ version with all parameters. As the equation
compiler chokes on this one, we use the `nat.rec_on` version.
-/
def iterated_continuous_linear_map.normed_space_rec (𝕜 : Type w) [h𝕜 : nondiscrete_normed_field 𝕜]
  (n : ℕ) (E : Type u) [gE : normed_group E] [sE : normed_space 𝕜 E] :
  ∀(F : Type u) [nF : normed_group F] [sF : @normed_space 𝕜 F _ nF],
  @normed_space 𝕜 (@iterated_continuous_linear_map 𝕜 h𝕜 n E gE sE F nF sF)
  _ (@iterated_continuous_linear_map.normed_group_rec 𝕜 h𝕜 n E gE sE F nF sF) :=
nat.rec_on n (λF nF sF, sF) (λn aux_n F nF sF, by { resetI, apply aux_n })

/--
Explicit normed group structure on the space of iterated continuous linear maps.
-/
instance iterated_continuous_linear_map.normed_group (n : ℕ)
  (𝕜 : Type w) [h𝕜 : nondiscrete_normed_field 𝕜]
  (E : Type u) [gE : normed_group E] [sE : normed_space 𝕜 E]
  (F : Type u) [gF : normed_group F] [sF : normed_space 𝕜 F] :
  normed_group (E [×n]→L[𝕜] F) :=
iterated_continuous_linear_map.normed_group_rec 𝕜 n E F

/--
Explicit normed space structure on the space of iterated continuous linear maps.
-/
instance iterated_continuous_linear_map.normed_space (n : ℕ)
  (𝕜 : Type w) [h𝕜 : nondiscrete_normed_field 𝕜]
  (E : Type u) [gE : normed_group E] [sE : normed_space 𝕜 E]
  (F : Type u) [gF : normed_group F] [sF : normed_space 𝕜 F] :
  normed_space 𝕜 (E [×n]→L[𝕜] F) :=
iterated_continuous_linear_map.normed_space_rec 𝕜 n E F

/--
The n-th derivative of a function, defined inductively by saying that the (n+1)-th
derivative of f is the n-th derivative of the derivative of f.
-/
def iterated_fderiv (𝕜 : Type w) [h𝕜 : nondiscrete_normed_field 𝕜] (n : ℕ)
  {E : Type u} [gE : normed_group E] [sE : normed_space 𝕜 E] :
  ∀{F : Type u} [gF : normed_group F] [sF : @normed_space 𝕜 F _ gF] (f : E → F),
  E → @iterated_continuous_linear_map 𝕜 h𝕜 n E gE sE F gF sF :=
nat.rec_on n (λF gF sF f, f) (λn rec F gF sF f, by { resetI, exact rec (fderiv 𝕜 f) })

@[simp] lemma iterated_fderiv_zero :
  iterated_fderiv 𝕜 0 f = f := rfl

@[simp] lemma iterated_fderiv_succ :
  iterated_fderiv 𝕜 (n+1) f = (iterated_fderiv 𝕜 n (λx, fderiv 𝕜 f x) : _) := rfl

/--
The n-th derivative of a function along a set, defined inductively by saying that the (n+1)-th
derivative of f is the n-th derivative of the derivative of f.
-/
def iterated_fderiv_within (𝕜 : Type w) [h𝕜 :nondiscrete_normed_field 𝕜] (n : ℕ)
  {E : Type u} [gE : normed_group E] [sE : normed_space 𝕜 E] :
  ∀{F : Type u} [gF : normed_group F] [sF : @normed_space 𝕜 F _ gF] (f : E → F) (s : set E),
  E → @iterated_continuous_linear_map 𝕜 h𝕜 n E gE sE F gF sF :=
nat.rec_on n (λF gF sF f s, f) (λn rec F gF sF f s, by { resetI, exact rec (fderiv_within 𝕜 f s) s})

@[simp] lemma iterated_fderiv_within_zero :
  iterated_fderiv_within 𝕜 0 f s = f := rfl

@[simp] lemma iterated_fderiv_within_succ :
  iterated_fderiv_within 𝕜 (n+1) f s
  = (iterated_fderiv_within 𝕜 n (λx, fderiv_within 𝕜 f s x) s : _) := rfl

theorem iterated_fderiv_within_univ {n : ℕ} :
  iterated_fderiv_within 𝕜 n f univ = iterated_fderiv 𝕜 n f :=
begin
  tactic.unfreeze_local_instances,
  induction n with n IH generalizing F,
  { refl },
  { simp [IH] }
end

/--
If two functions coincide on a set `s` of unique differentiability, then their iterated
differentials within this set coincide.
-/
lemma iterated_fderiv_within_congr (hs : unique_diff_on 𝕜 s)
  (hL : ∀y∈s, f₁ y = f y) (hx : x ∈ s) :
  iterated_fderiv_within 𝕜 n f₁ s x = iterated_fderiv_within 𝕜 n f s x :=
begin
  tactic.unfreeze_local_instances,
  induction n with n IH generalizing F f x,
  { simp [hL x hx] },
  { simp only [iterated_fderiv_within_succ],
    refine IH (λy hy, _) hx,
    apply fderiv_within_congr (hs y hy) hL (hL y hy) }
end

/--
The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with an open set containing `x`.
-/
lemma iterated_fderiv_within_inter_open (xu : x ∈ u) (hu : is_open u) (xs : x ∈ s)
  (hs : unique_diff_on 𝕜 (s ∩ u)) :
  iterated_fderiv_within 𝕜 n f (s ∩ u) x = iterated_fderiv_within 𝕜 n f s x :=
begin
  tactic.unfreeze_local_instances,
  induction n with n IH generalizing F f,
  { simp },
  { simp,
    rw ← IH,
    apply iterated_fderiv_within_congr hs (λy hy, _) ⟨xs, xu⟩,
    apply fderiv_within_inter (mem_nhds_sets hu hy.2),
    have := hs y hy,
    rwa unique_diff_within_at_inter (mem_nhds_sets hu hy.2) at this }
end

/--
The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x`.
-/
lemma iterated_fderiv_within_inter (hu : u ∈ nhds x) (xs : x ∈ s)
  (hs : unique_diff_on 𝕜 s) :
  iterated_fderiv_within 𝕜 n f (s ∩ u) x = iterated_fderiv_within 𝕜 n f s x :=
begin
  rcases mem_nhds_sets_iff.1 hu with ⟨v, vu, v_open, xv⟩,
  have A : (s ∩ u) ∩ v = s ∩ v,
  { apply subset.antisymm (inter_subset_inter (inter_subset_left _ _) (subset.refl _)),
    exact λ y ⟨ys, yv⟩, ⟨⟨ys, vu yv⟩, yv⟩ },
  have : iterated_fderiv_within 𝕜 n f (s ∩ v) x = iterated_fderiv_within 𝕜 n f s x :=
    iterated_fderiv_within_inter_open xv v_open xs (hs.inter v_open),
  rw ← this,
  have : iterated_fderiv_within 𝕜 n f ((s ∩ u) ∩ v) x = iterated_fderiv_within 𝕜 n f (s ∩ u) x,
  { refine iterated_fderiv_within_inter_open xv v_open ⟨xs, mem_of_nhds hu⟩ _,
    rw A,
    exact hs.inter v_open },
  rw A at this,
  rw ← this
end

/--
Auxiliary definition defining `C^n` functions by induction over `n`.
In applications, use `times_cont_diff` instead.
-/
def times_cont_diff_rec (𝕜 : Type w) [nondiscrete_normed_field 𝕜] :
  Π (n : ℕ) {E : Type u} [gE : normed_group E] [@normed_space 𝕜 E _ gE]
    {F : Type u} [gF : normed_group F] [@normed_space 𝕜 F _ gF] (f : E → F), Prop
| 0     E _ _ F _ _ f := by { resetI, exact continuous f }
| (n+1) E _ _ F _ _ f := by { resetI, exact differentiable 𝕜 f ∧ times_cont_diff_rec n (fderiv 𝕜 f) }

@[simp] lemma times_cont_diff_rec_zero :
  times_cont_diff_rec 𝕜 0 f ↔ continuous f :=
by refl

@[simp] lemma times_cont_diff_rec_succ :
  times_cont_diff_rec 𝕜 n.succ f ↔
  differentiable 𝕜 f ∧ times_cont_diff_rec 𝕜 n (λx, fderiv 𝕜 f x) :=
by refl

lemma times_cont_diff_rec.of_succ (h : times_cont_diff_rec 𝕜 n.succ f) :
  times_cont_diff_rec 𝕜 n f :=
begin
  tactic.unfreeze_local_instances,
  induction n with n IH generalizing F,
  { exact h.1.continuous },
  { rw times_cont_diff_rec_succ at h ⊢,
    exact ⟨h.1, IH h.2⟩ }
end

lemma times_cont_diff_rec.continuous (h : times_cont_diff_rec 𝕜 n f) :
  continuous (iterated_fderiv 𝕜 n f) :=
begin
  tactic.unfreeze_local_instances,
  induction n with n IH generalizing F f,
  { exact h },
  { rw iterated_fderiv_succ,
    exact IH (times_cont_diff_rec_succ.1 h).2 }
end

lemma times_cont_diff_rec.differentiable (h : times_cont_diff_rec 𝕜 (n+1) f) :
  differentiable 𝕜 (iterated_fderiv 𝕜 n f) :=
begin
  tactic.unfreeze_local_instances,
  induction n with n IH generalizing F f,
  { exact h.1 },
  { rw iterated_fderiv_succ,
    apply IH h.2 }
end

/--
Auxiliary definition defining `C^n` functions on a set by induction over `n`.
In applications, use `times_cont_diff_on` instead.
-/
def times_cont_diff_on_rec (𝕜 : Type w) [nondiscrete_normed_field 𝕜] :
  Π (n : ℕ) {E : Type u} [gE : normed_group E] [@normed_space 𝕜 E _ gE]
    {F : Type u} [gF : normed_group F] [@normed_space 𝕜 F _ gF] (f : E → F) (s : set E), Prop
| 0     E _ _ F _ _ f s := by { resetI, exact continuous_on f s }
| (n+1) E _ _ F _ _ f s := by { resetI,
                  exact differentiable_on 𝕜 f s ∧ times_cont_diff_on_rec n (fderiv_within 𝕜 f s) s}

@[simp] lemma times_cont_diff_on_rec_zero :
  times_cont_diff_on_rec 𝕜 0 f s ↔ continuous_on f s :=
by refl

@[simp] lemma times_cont_diff_on_rec_succ :
  times_cont_diff_on_rec 𝕜 n.succ f s ↔
  differentiable_on 𝕜 f s ∧ times_cont_diff_on_rec 𝕜 n (λx, fderiv_within 𝕜 f s x) s :=
by refl

lemma times_cont_diff_on_rec.of_succ (h : times_cont_diff_on_rec 𝕜 n.succ f s) :
  times_cont_diff_on_rec 𝕜 n f s :=
begin
  tactic.unfreeze_local_instances,
  induction n with n IH generalizing F,
  { exact h.1.continuous_on },
  { rw times_cont_diff_on_rec_succ at h ⊢,
    exact ⟨h.1, IH h.2⟩ }
end

lemma times_cont_diff_on_rec.continuous_on_iterated_fderiv_within
  (h : times_cont_diff_on_rec 𝕜 n f s) :
  continuous_on (iterated_fderiv_within 𝕜 n f s) s :=
begin
  tactic.unfreeze_local_instances,
  induction n with n IH generalizing F f,
  { exact h },
  { rw iterated_fderiv_within_succ,
    exact IH (times_cont_diff_on_rec_succ.1 h).2 }
end

lemma times_cont_diff_on_rec.differentiable_on (h : times_cont_diff_on_rec 𝕜 (n+1) f s) :
  differentiable_on 𝕜 (iterated_fderiv_within 𝕜 n f s) s :=
begin
  tactic.unfreeze_local_instances,
  induction n with n IH generalizing F f,
  { exact h.1 },
  { rw iterated_fderiv_within_succ,
    apply IH h.2 }
end

lemma times_cont_diff_on_rec_univ :
  times_cont_diff_on_rec 𝕜 n f univ ↔ times_cont_diff_rec 𝕜 n f :=
begin
  tactic.unfreeze_local_instances,
  induction n with n IH generalizing F f,
  { rw [times_cont_diff_on_rec_zero, times_cont_diff_rec_zero, continuous_iff_continuous_on_univ] },
  { rw [times_cont_diff_on_rec_succ, times_cont_diff_rec_succ, differentiable_on_univ, fderiv_within_univ, IH] }
end

/--
A function is `C^n` on a set, for `n : with_top ℕ`, if its derivatives of order at most `n`
are all well defined and continuous.
-/
def times_cont_diff_on (𝕜 : Type w) [nondiscrete_normed_field 𝕜] (n : with_top ℕ)
  {E F : Type u} [normed_group E] [normed_space 𝕜 E]
  [normed_group F] [normed_space 𝕜 F] (f : E → F) (s : set E) :=
(∀m:ℕ, (m : with_top ℕ) ≤ n → continuous_on (iterated_fderiv_within 𝕜 m f s) s)
∧ (∀m:ℕ, (m : with_top ℕ) < n → differentiable_on 𝕜 (iterated_fderiv_within 𝕜 m f s) s)

@[simp] lemma times_cont_diff_on_zero :
  times_cont_diff_on 𝕜 0 f s ↔ continuous_on f s :=
by simp [times_cont_diff_on]

/--
The two definitions of `C^n` functions on domains, directly in terms of continuity of all
derivatives, or by induction, are equivalent.
-/
theorem times_cont_diff_on_iff_times_cont_diff_on_rec :
  times_cont_diff_on 𝕜 n f s ↔ times_cont_diff_on_rec 𝕜 n f s :=
begin
  tactic.unfreeze_local_instances,
  induction n with n IH generalizing F f,
  { rw [with_top.coe_zero, times_cont_diff_on_rec_zero, times_cont_diff_on_zero] },
  { split,
    { assume H,
      rw times_cont_diff_on_rec_succ,
      refine ⟨H.2 0 (by simp only [with_top.zero_lt_coe, with_top.coe_zero, nat.succ_pos n]), _⟩,
      rw ← IH,
      split,
      { assume m hm,
        have : (m.succ : with_top nat) ≤ n.succ :=
          with_top.coe_le_coe.2 (nat.succ_le_succ (with_top.coe_le_coe.1 hm)),
        exact H.1 _ this },
      { assume m hm,
        have : (m.succ : with_top nat) < n.succ :=
          with_top.coe_lt_coe.2 (nat.succ_le_succ (with_top.coe_lt_coe.1 hm)),
        exact H.2 _ this } },
    { assume H,
      split,
      { assume m hm,
        simp only [with_top.coe_le_coe] at hm,
        cases nat.of_le_succ hm with h h,
        { have := H.of_succ,
          rw ← IH at this,
          exact this.1 _ (with_top.coe_le_coe.2 h) },
        { rw h,
          simp at H,
          exact H.2.continuous_on_iterated_fderiv_within } },
      { assume m hm,
        simp only [with_top.coe_lt_coe] at hm,
        cases nat.of_le_succ hm with h h,
        { have := H.of_succ,
          rw ← IH at this,
          exact this.2 _ (with_top.coe_lt_coe.2 h) },
        { rw nat.succ_inj h,
          exact H.differentiable_on } } } },
end

/- Next lemma is marked as a simp lemma as `C^(n+1)` functions appear mostly in inductions. -/
@[simp] lemma times_cont_diff_on_succ :
  times_cont_diff_on 𝕜 n.succ f s ↔
  differentiable_on 𝕜 f s ∧ times_cont_diff_on 𝕜 n (λx, fderiv_within 𝕜 f s x) s :=
by simp [times_cont_diff_on_iff_times_cont_diff_on_rec]

lemma times_cont_diff_on.of_le {m n : with_top ℕ}
 (h : times_cont_diff_on 𝕜 n f s) (le : m ≤ n) : times_cont_diff_on 𝕜 m f s :=
⟨λp hp, h.1 p (le_trans hp le), λp hp, h.2 p (lt_of_lt_of_le hp le)⟩

lemma times_cont_diff_on.of_succ (h : times_cont_diff_on 𝕜 n.succ f s) :
  times_cont_diff_on 𝕜 n f s :=
h.of_le (with_top.coe_le_coe.2 (nat.le_succ n))

lemma times_cont_diff_on.continuous_on {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) :
  continuous_on f s :=
h.1 0 (by simp)

lemma times_cont_diff_on.continuous_on_fderiv_within
  {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (hn : 1 ≤ n) :
  continuous_on (fderiv_within 𝕜 f s) s :=
h.1 1 hn

/-- If a function is at least C^1 on a set, it is differentiable there. -/
lemma times_cont_diff_on.differentiable_on
  {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (hn : 1 ≤ n) :
  differentiable_on 𝕜 f s :=
begin
  refine h.2 0 _,
  refine lt_of_lt_of_le _ hn,
  change ((0 : ℕ) : with_top ℕ) < (1 : ℕ),
  rw with_top.coe_lt_coe,
  exact zero_lt_one
end

set_option class.instance_max_depth 50

/--
If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous.
-/
lemma times_cont_diff_on.continuous_on_fderiv_within_apply
  {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (hn : 1 ≤ n) :
  continuous_on (λp : E × E, (fderiv_within 𝕜 f s p.1 : E → F) p.2) (set.prod s univ) :=
begin
  have A : continuous (λq : (E →L[𝕜] F) × E, q.1 q.2) := is_bounded_bilinear_map_apply.continuous,
  have B : continuous_on (λp : E × E, (fderiv_within 𝕜 f s p.1, p.2)) (set.prod s univ),
  { apply continuous_on.prod _ continuous_snd.continuous_on,
    exact continuous_on.comp (h.continuous_on_fderiv_within hn) continuous_fst.continuous_on
      (prod_subset_preimage_fst _ _) },
  exact A.comp_continuous_on B
end

lemma times_cont_diff_on_top :
  times_cont_diff_on 𝕜 ⊤ f s ↔ (∀n:ℕ, times_cont_diff_on 𝕜 n f s) :=
begin
  split,
  { assume h n,
    exact h.of_le lattice.le_top },
  { assume h,
    split,
    { exact λm hm, (h m).1 m (le_refl _) },
    { exact λ m hm, (h m.succ).2 m (with_top.coe_lt_coe.2 (lt_add_one m)) } }
end

lemma times_cont_diff_on_fderiv_within_nat {m n : ℕ}
  (hf : times_cont_diff_on 𝕜 n f s) (h : m + 1 ≤ n) :
  times_cont_diff_on 𝕜 m (λx, fderiv_within 𝕜 f s x) s :=
begin
  have : times_cont_diff_on 𝕜 m.succ f s :=
    hf.of_le (with_top.coe_le_coe.2 h),
  exact (times_cont_diff_on_succ.1 this).2
end

lemma times_cont_diff_on_fderiv_within {m n : with_top ℕ}
  (hf : times_cont_diff_on 𝕜 n f s) (h : m + 1 ≤ n) :
  times_cont_diff_on 𝕜 m (λx, fderiv_within 𝕜 f s x) s :=
begin
  cases m,
  { change ⊤ + 1 ≤ n at h,
    have : n = ⊤, by simpa using h,
    rw this at hf,
    change times_cont_diff_on 𝕜 ⊤ (λ (x : E), fderiv_within 𝕜 f s x) s,
    rw times_cont_diff_on_top at ⊢ hf,
    exact λm, times_cont_diff_on_fderiv_within_nat (hf (m + 1)) (le_refl _) },
  { have : times_cont_diff_on 𝕜 (m + 1) f s := hf.of_le h,
    exact times_cont_diff_on_fderiv_within_nat this (le_refl _) }
end

lemma times_cont_diff_on.congr_mono {n : with_top ℕ} (H : times_cont_diff_on 𝕜 n f s)
  (hs : unique_diff_on 𝕜 s₁) (h : ∀x ∈ s₁, f₁ x = f x) (h₁ : s₁ ⊆ s) :
  times_cont_diff_on 𝕜 n f₁ s₁ :=
begin
  tactic.unfreeze_local_instances,
  induction n using with_top.nat_induction with n IH Itop generalizing F,
  { rw times_cont_diff_on_zero at H ⊢,
    exact continuous_on.congr_mono H h h₁ },
  { rw times_cont_diff_on_succ at H ⊢,
    refine ⟨differentiable_on.congr_mono H.1 h h₁, IH H.2 (λx hx, _)⟩,
    apply differentiable_within_at.fderiv_within_congr_mono
      (H.1 x (h₁ hx)) h (h x hx) (hs x hx) h₁ },
  { rw times_cont_diff_on_top at H ⊢,
    assume n, exact Itop n (H n) h }
end

lemma times_cont_diff_on.congr {n : with_top ℕ} {s : set E} (H : times_cont_diff_on 𝕜 n f s)
  (hs : unique_diff_on 𝕜 s) (h : ∀x ∈ s, f₁ x = f x) :
  times_cont_diff_on 𝕜 n f₁ s :=
times_cont_diff_on.congr_mono H hs h (subset.refl _)

lemma times_cont_diff_on.congr_mono' {n m : with_top ℕ} {s : set E} (H : times_cont_diff_on 𝕜 n f s)
  (hs : unique_diff_on 𝕜 s₁) (h : ∀x ∈ s₁, f₁ x = f x) (h₁ : s₁ ⊆ s) (le : m ≤ n) :
  times_cont_diff_on 𝕜 m f₁ s₁ :=
times_cont_diff_on.of_le (H.congr_mono hs h h₁) le

lemma times_cont_diff_on.mono {n : with_top ℕ} {s t : set E} (h : times_cont_diff_on 𝕜 n f t)
  (hst : s ⊆ t) (hs : unique_diff_on 𝕜 s) : times_cont_diff_on 𝕜 n f s :=
times_cont_diff_on.congr_mono h hs (λx hx, rfl) hst

/--
Being `C^n` is a local property.
-/
lemma times_cont_diff_on_of_locally_times_cont_diff_on {n : with_top ℕ} {s : set E}
  (hs : unique_diff_on 𝕜 s) (h : ∀x∈s, ∃u, is_open u ∧ x ∈ u ∧ times_cont_diff_on 𝕜 n f (s ∩ u)) :
  times_cont_diff_on 𝕜 n f s :=
begin
  split,
  { assume m hm,
    apply continuous_on_of_locally_continuous_on (λx hx, _),
    rcases h x hx with ⟨u, u_open, xu, hu⟩,
    refine ⟨u, u_open, xu,_⟩,
    apply continuous_on.congr_mono (hu.1 m hm) (λy hy, _) (subset.refl _),
    symmetry,
    exact iterated_fderiv_within_inter_open hy.2 u_open hy.1 (hs.inter u_open) },
  { assume m hm,
    apply differentiable_on_of_locally_differentiable_on (λx hx, _),
    rcases h x hx with ⟨u, u_open, xu, hu⟩,
    refine ⟨u, u_open, xu,_⟩,
    apply differentiable_on.congr_mono (hu.2 m hm) (λy hy, _) (subset.refl _),
    symmetry,
    exact iterated_fderiv_within_inter_open hy.2 u_open hy.1 (hs.inter u_open) }
end

/--
A function is `C^n`, for `n : with_top ℕ`, if its derivatives of order at most `n` are all well
defined and continuous.
-/
def times_cont_diff (𝕜 : Type w) [nondiscrete_normed_field 𝕜] (n : with_top ℕ)
  {E F : Type u} [normed_group E] [normed_space 𝕜 E]
  [normed_group F] [normed_space 𝕜 F] (f : E → F) :=
(∀m:ℕ, (m : with_top ℕ) ≤ n → continuous (iterated_fderiv 𝕜 m f ))
∧ (∀m:ℕ, (m : with_top ℕ) < n → differentiable 𝕜 (iterated_fderiv 𝕜 m f))

lemma times_cont_diff_on_univ {n : with_top ℕ} :
  times_cont_diff_on 𝕜 n f univ ↔ times_cont_diff 𝕜 n f :=
by simp [times_cont_diff_on, times_cont_diff, iterated_fderiv_within_univ,
        continuous_iff_continuous_on_univ, differentiable_on_univ]

@[simp] lemma times_cont_diff_zero :
  times_cont_diff 𝕜 0 f ↔ continuous f :=
by simp [times_cont_diff]

theorem times_cont_diff_iff_times_cont_diff_rec :
  times_cont_diff 𝕜 n f ↔ times_cont_diff_rec 𝕜 n f :=
by simp [times_cont_diff_on_univ.symm, times_cont_diff_on_rec_univ.symm,
         times_cont_diff_on_iff_times_cont_diff_on_rec]

@[simp] lemma times_cont_diff_succ :
  times_cont_diff 𝕜 n.succ f ↔
  differentiable 𝕜 f ∧ times_cont_diff 𝕜 n (λx, fderiv 𝕜 f x) :=
by simp [times_cont_diff_iff_times_cont_diff_rec]

lemma times_cont_diff.of_le {m n : with_top ℕ} (h : times_cont_diff 𝕜 n f) (le : m ≤ n) :
  times_cont_diff 𝕜 m f :=
⟨λp hp, h.1 p (le_trans hp le), λp hp, h.2 p (lt_of_lt_of_le hp le)⟩

lemma times_cont_diff.of_succ (h : times_cont_diff 𝕜 n.succ f) : times_cont_diff 𝕜 n f :=
h.of_le (with_top.coe_le_coe.2 (nat.le_succ n))

lemma times_cont_diff.continuous {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) :
  continuous f :=
h.1 0 (by simp)

lemma times_cont_diff.continuous_fderiv {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) (hn : 1 ≤ n) :
  continuous (fderiv 𝕜 f) :=
h.1 1 hn

lemma times_cont_diff.continuous_fderiv_apply
  {n : with_top ℕ} (h : times_cont_diff 𝕜 n f) (hn : 1 ≤ n) :
  continuous (λp : E × E, (fderiv 𝕜 f p.1 : E → F) p.2) :=
begin
  have A : continuous (λq : (E →L[𝕜] F) × E, q.1 q.2) := is_bounded_bilinear_map_apply.continuous,
  have B : continuous (λp : E × E, (fderiv 𝕜 f p.1, p.2)),
  { apply continuous.prod_mk _ continuous_snd,
    exact continuous.comp (h.continuous_fderiv hn) continuous_fst },
  exact A.comp B
end

lemma times_cont_diff_top : times_cont_diff 𝕜 ⊤ f ↔ (∀n:ℕ, times_cont_diff 𝕜 n f) :=
by simp [times_cont_diff_on_univ.symm, times_cont_diff_on_rec_univ.symm,
        times_cont_diff_on_top]

lemma times_cont_diff.times_cont_diff_on {n : with_top ℕ} {s : set E}
  (h : times_cont_diff 𝕜 n f) (hs : unique_diff_on 𝕜 s) : times_cont_diff_on 𝕜 n f s :=
by { rw ← times_cont_diff_on_univ at h, apply times_cont_diff_on.mono h (subset_univ _) hs }

/--
Constants are C^∞.
-/
lemma times_cont_diff_const {n : with_top ℕ} {c : F} : times_cont_diff 𝕜 n (λx : E, c) :=
begin
  tactic.unfreeze_local_instances,
  induction n using with_top.nat_induction with n IH Itop generalizing F,
  { rw times_cont_diff_zero,
    apply continuous_const },
  { refine times_cont_diff_succ.2 ⟨differentiable_const _, _⟩,
    simp [fderiv_const],
    exact IH },
  { rw times_cont_diff_top,
    assume n, apply Itop }
end

/--
Linear functions are C^∞.
-/
lemma is_bounded_linear_map.times_cont_diff {n : with_top ℕ} (hf : is_bounded_linear_map 𝕜 f) :
  times_cont_diff 𝕜 n f :=
begin
  induction n using with_top.nat_induction with n IH Itop,
  { rw times_cont_diff_zero,
    exact hf.continuous },
  { refine times_cont_diff_succ.2 ⟨hf.differentiable, _⟩,
    simp [hf.fderiv],
    exact times_cont_diff_const },
  { rw times_cont_diff_top, apply Itop }
end

/--
The first projection in a product is C^∞.
-/
lemma times_cont_diff_fst {n : with_top ℕ} : times_cont_diff 𝕜 n (prod.fst : E × F → E) :=
is_bounded_linear_map.times_cont_diff is_bounded_linear_map.fst

/--
The second projection in a product is C^∞.
-/
lemma times_cont_diff_snd {n : with_top ℕ} : times_cont_diff 𝕜 n (prod.snd : E × F → F) :=
is_bounded_linear_map.times_cont_diff is_bounded_linear_map.snd

/--
The identity is C^∞.
-/
lemma times_cont_diff_id {n : with_top ℕ} : times_cont_diff 𝕜 n (id : E → E) :=
is_bounded_linear_map.id.times_cont_diff

/--
Bilinear functions are C^∞.
-/
lemma is_bounded_bilinear_map.times_cont_diff {n : with_top ℕ} (hb : is_bounded_bilinear_map 𝕜 b) :
  times_cont_diff 𝕜 n b :=
begin
  induction n using with_top.nat_induction with n IH Itop,
  { rw times_cont_diff_zero,
    exact hb.continuous },
  { refine times_cont_diff_succ.2 ⟨hb.differentiable, _⟩,
    simp [hb.fderiv],
    exact hb.is_bounded_linear_map_deriv.times_cont_diff },
  { rw times_cont_diff_top, apply Itop }
end

/--
Composition by bounded linear maps preserves `C^n` functions on domains.
-/
lemma times_cont_diff_on.comp_is_bounded_linear {n : with_top ℕ} {s : set E} {f : E → F} {g : F → G}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : is_bounded_linear_map 𝕜 g) (hs : unique_diff_on 𝕜 s) :
  times_cont_diff_on 𝕜 n (λx, g (f x)) s :=
begin
  tactic.unfreeze_local_instances,
  induction n using with_top.nat_induction with n IH Itop generalizing F G,
  { have : continuous_on g univ := hg.continuous.continuous_on,
    rw times_cont_diff_on_zero at hf ⊢,
    apply continuous_on.comp this hf (subset_univ _) },
  { rw times_cont_diff_on_succ at hf ⊢,
    refine ⟨differentiable_on.comp hg.differentiable_on hf.1 subset_preimage_univ, _⟩,
    let Φ : (E →L[𝕜] F) → (E →L[𝕜] G) := λu, continuous_linear_map.comp (hg.to_continuous_linear_map) u,
    have : ∀x∈s, fderiv_within 𝕜 (g ∘ f) s x = Φ (fderiv_within 𝕜 f s x),
    { assume x hx,
      rw [fderiv_within.comp x _ (hf.1 x hx) subset_preimage_univ (hs x hx),
          fderiv_within_univ, hg.fderiv],
      rw differentiable_within_at_univ,
      exact hg.differentiable_at },
    apply times_cont_diff_on.congr_mono _ hs this (subset.refl _),
    simp only [times_cont_diff_on_succ] at hf,
    exact IH hf.2 hg.to_continuous_linear_map.is_bounded_linear_map_comp_left },
  { rw times_cont_diff_on_top at hf ⊢,
    assume n,
    apply Itop n (hf n) hg }
end

/--
Composition by bounded linear maps preserves `C^n` functions.
-/
lemma times_cont_diff.comp_is_bounded_linear {n : with_top ℕ} {f : E → F} {g : F → G}
  (hf : times_cont_diff 𝕜 n f) (hg : is_bounded_linear_map 𝕜 g) :
  times_cont_diff 𝕜 n (λx, g (f x)) :=
times_cont_diff_on_univ.1 $ times_cont_diff_on.comp_is_bounded_linear (times_cont_diff_on_univ.2 hf)
  hg is_open_univ.unique_diff_on

/--
The cartesian product of `C^n` functions on domains is `C^n`.
-/
lemma times_cont_diff_on.prod {n : with_top ℕ} {s : set E} {f : E → F} {g : E → G}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) (hs : unique_diff_on 𝕜 s) :
  times_cont_diff_on 𝕜 n (λx:E, (f x, g x)) s :=
begin
  tactic.unfreeze_local_instances,
  induction n using with_top.nat_induction with n IH Itop generalizing F G,
  { rw times_cont_diff_on_zero at hf hg ⊢,
    exact continuous_on.prod hf hg },
  { rw times_cont_diff_on_succ at hf hg ⊢,
    refine ⟨differentiable_on.prod hf.1 hg.1, _⟩,
    let F₁ := λx : E, (fderiv_within 𝕜 f s x, fderiv_within 𝕜 g s x),
    let Φ : ((E →L[𝕜] F) × (E →L[𝕜] G)) → (E →L[𝕜] (F × G)) := λp, continuous_linear_map.prod p.1 p.2,
    have : times_cont_diff_on 𝕜 n (Φ ∘ F₁) s :=
      times_cont_diff_on.comp_is_bounded_linear (IH hf.2 hg.2) is_bounded_linear_map_prod_iso hs,
    apply times_cont_diff_on.congr_mono this hs (λx hx, _) (subset.refl _),
    apply differentiable_at.fderiv_within_prod (hf.1 x hx) (hg.1 x hx) (hs x hx) },
  { rw times_cont_diff_on_top at hf hg ⊢,
    assume n,
    apply Itop n (hf n) (hg n) }
end

/--
The cartesian product of `C^n` functions is `C^n`.
-/
lemma times_cont_diff.prod {n : with_top ℕ} {f : E → F} {g : E → G}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) :
  times_cont_diff 𝕜 n (λx:E, (f x, g x)) :=
times_cont_diff_on_univ.1 $ times_cont_diff_on.prod (times_cont_diff_on_univ.2 hf)
  (times_cont_diff_on_univ.2 hg) is_open_univ.unique_diff_on

/--
The composition of `C^n` functions on domains is `C^n`.
-/
lemma times_cont_diff_on.comp {n : with_top ℕ} {s : set E} {t : set F} {g : F → G} {f : E → F}
  (hg : times_cont_diff_on 𝕜 n g t) (hf : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s)
  (st : s ⊆ f ⁻¹' t) : times_cont_diff_on 𝕜 n (g ∘ f) s :=
begin
  tactic.unfreeze_local_instances,
  induction n using with_top.nat_induction with n IH Itop generalizing E F G,
  { rw times_cont_diff_on_zero at hf hg ⊢,
    exact continuous_on.comp hg hf st },
  { rw times_cont_diff_on_succ at hf hg ⊢,
    /- We have to show that the derivative of g ∘ f is C^n, given that g and f are C^(n+1).
    By the chain rule, this derivative is Dg(f x) ⬝ Df(x). This is the composition of
    x ↦ (Dg (f x), Df (x)) with the product of bounded linear maps, which is bilinear and therefore
    C^∞. By the induction assumption, it suffices to show that x ↦ (Dg (f x), Df (x)) is C^n. It
    is even enough to show that each component is C^n. This follows from the assumptions on f and g,
    and the inductive assumption.
    -/
    refine ⟨differentiable_on.comp hg.1 hf.1 st, _⟩,
    have : ∀x∈s, fderiv_within 𝕜 (g ∘ f) s x =
      continuous_linear_map.comp (fderiv_within 𝕜 g t (f x)) (fderiv_within 𝕜 f s x),
    { assume x hx,
      apply fderiv_within.comp x _ (hf.1 x hx) st (hs x hx),
      exact hg.1 _ (st hx) },
    apply times_cont_diff_on.congr _ hs this,
    have A : times_cont_diff_on 𝕜 n (λx, fderiv_within 𝕜 g t (f x)) s :=
      IH hg.2 (times_cont_diff_on_succ.2 hf).of_succ hs st,
    have B : times_cont_diff_on 𝕜 n (λx, fderiv_within 𝕜 f s x) s := hf.2,
    have C : times_cont_diff_on 𝕜 n (λx:E, (fderiv_within 𝕜 f s x, fderiv_within 𝕜 g t (f x))) s :=
      times_cont_diff_on.prod B A hs,
    have D : times_cont_diff_on 𝕜 n (λ(p : (E →L[𝕜] F) × (F →L[𝕜] G)), p.2.comp p.1) univ :=
      is_bounded_bilinear_map_comp.times_cont_diff.times_cont_diff_on is_open_univ.unique_diff_on,
    exact IH D C hs (subset_univ _) },
  { rw times_cont_diff_on_top at hf hg ⊢,
    assume n,
    apply Itop n (hg n) (hf n) hs st }
end

/--
The composition of `C^n` functions is `C^n`.
-/
lemma times_cont_diff.comp {n : with_top ℕ} {g : F → G} {f : E → F}
  (hg : times_cont_diff 𝕜 n g) (hf : times_cont_diff 𝕜 n f) :
  times_cont_diff 𝕜 n (g ∘ f) :=
times_cont_diff_on_univ.1 $ times_cont_diff_on.comp (times_cont_diff_on_univ.2 hg)
  (times_cont_diff_on_univ.2 hf) is_open_univ.unique_diff_on (subset_univ _)

/--
The bundled derivative of a `C^{n+1}` function is `C^n`.
-/
lemma times_cont_diff_on_fderiv_within_apply {m n : with_top  ℕ} {s : set E}
  {f : E → F} (hf : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hmn : m + 1 ≤ n) :
  times_cont_diff_on 𝕜 m (λp : E × E, (fderiv_within 𝕜 f s p.1 : E →L[𝕜] F) p.2) (set.prod s (univ : set E)) :=
begin
  have U : unique_diff_on 𝕜 (set.prod s (univ : set E)) :=
    hs.prod unique_diff_on_univ,
  have A : times_cont_diff_on 𝕜 m (λp : (E →L[𝕜] F) × E, p.1 p.2) univ,
  { rw times_cont_diff_on_univ,
    apply is_bounded_bilinear_map.times_cont_diff,
    exact is_bounded_bilinear_map_apply },
  have B : times_cont_diff_on 𝕜 m
    (λ (p : E × E), ((fderiv_within 𝕜 f s p.fst), p.snd)) (set.prod s univ),
  { apply times_cont_diff_on.prod _ _ U,
    { have I : times_cont_diff_on 𝕜 m (λ (x : E), fderiv_within 𝕜 f s x) s :=
        times_cont_diff_on_fderiv_within hf hmn,
      have J : times_cont_diff_on 𝕜 m (λ (x : E × E), x.1) (set.prod s univ) :=
        times_cont_diff_fst.times_cont_diff_on U,
      exact times_cont_diff_on.comp I J U (prod_subset_preimage_fst _ _) },
    { apply times_cont_diff.times_cont_diff_on _ U,
      apply is_bounded_linear_map.times_cont_diff,
      apply is_bounded_linear_map.snd } },
  apply times_cont_diff_on.comp A B U (subset_univ _),
end

/--
The bundled derivative of a `C^{n+1}` function is `C^n`.
-/
lemma times_cont_diff.times_cont_diff_fderiv_apply {n m : with_top ℕ} {s : set E} {f : E → F}
  (hf : times_cont_diff 𝕜 n f) (hmn : m + 1 ≤ n) :
  times_cont_diff 𝕜 m (λp : E × E, (fderiv 𝕜 f p.1 : E →L[𝕜] F) p.2) :=
begin
  rw ← times_cont_diff_on_univ at ⊢ hf,
  rw [← fderiv_within_univ, ← univ_prod_univ],
  exact times_cont_diff_on_fderiv_within_apply hf unique_diff_on_univ hmn
end
