/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import topology.homotopy.basic
import topology.path_connected
import analysis.convex.basic

/-!
# Homotopy between paths

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define a `homotopy` between two `path`s. In addition, we define a relation
`homotopic` on `path`s, and prove that it is an equivalence relation.

## Definitions

* `path.homotopy p₀ p₁` is the type of homotopies between paths `p₀` and `p₁`
* `path.homotopy.refl p` is the constant homotopy between `p` and itself
* `path.homotopy.symm F` is the `path.homotopy p₁ p₀` defined by reversing the homotopy
* `path.homotopy.trans F G`, where `F : path.homotopy p₀ p₁`, `G : path.homotopy p₁ p₂` is the
  `path.homotopy p₀ p₂` defined by putting the first homotopy on `[0, 1/2]` and the second on
  `[1/2, 1]`
* `path.homotopy.hcomp F G`, where `F : path.homotopy p₀ q₀` and `G : path.homotopy p₁ q₁` is
  a `path.homotopy (p₀.trans p₁) (q₀.trans q₁)`
* `path.homotopic p₀ p₁` is the relation saying that there is a homotopy between `p₀` and `p₁`
* `path.homotopic.setoid x₀ x₁` is the setoid on `path`s from `path.homotopic`
* `path.homotopic.quotient x₀ x₁` is the quotient type from `path x₀ x₀` by `path.homotopic.setoid`

-/

universes u v

variables {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]
variables {x₀ x₁ x₂ x₃ : X}

noncomputable theory

open_locale unit_interval

namespace path

/--
The type of homotopies between two paths.
-/
abbreviation homotopy (p₀ p₁ : path x₀ x₁) :=
continuous_map.homotopy_rel p₀.to_continuous_map p₁.to_continuous_map {0, 1}

namespace homotopy

section

variables {p₀ p₁ : path x₀ x₁}

instance : has_coe_to_fun (homotopy p₀ p₁) (λ _, I × I → X) := ⟨λ F, F.to_fun⟩

lemma coe_fn_injective : @function.injective (homotopy p₀ p₁) (I × I → X) coe_fn :=
continuous_map.homotopy_with.coe_fn_injective

@[simp]
lemma source (F : homotopy p₀ p₁) (t : I) : F (t, 0) = x₀ :=
begin
  simp_rw [←p₀.source],
  apply continuous_map.homotopy_rel.eq_fst,
  simp,
end

@[simp]
lemma target (F : homotopy p₀ p₁) (t : I) : F (t, 1) = x₁ :=
begin
  simp_rw [←p₁.target],
  apply continuous_map.homotopy_rel.eq_snd,
  simp,
end

/--
Evaluating a path homotopy at an intermediate point, giving us a `path`.
-/
def eval (F : homotopy p₀ p₁) (t : I) : path x₀ x₁ :=
{ to_fun := F.to_homotopy.curry t,
  source' := by simp,
  target' := by simp }

@[simp]
lemma eval_zero (F : homotopy p₀ p₁) : F.eval 0 = p₀ :=
begin
  ext t,
  simp [eval],
end

@[simp]
lemma eval_one (F : homotopy p₀ p₁) : F.eval 1 = p₁ :=
begin
  ext t,
  simp [eval],
end

end

section

variables {p₀ p₁ p₂ : path x₀ x₁}

/--
Given a path `p`, we can define a `homotopy p p` by `F (t, x) = p x`
-/
@[simps]
def refl (p : path x₀ x₁) : homotopy p p :=
continuous_map.homotopy_rel.refl p.to_continuous_map {0, 1}

/--
Given a `homotopy p₀ p₁`, we can define a `homotopy p₁ p₀` by reversing the homotopy.
-/
@[simps]
def symm (F : homotopy p₀ p₁) : homotopy p₁ p₀ :=
continuous_map.homotopy_rel.symm F

@[simp]
lemma symm_symm (F : homotopy p₀ p₁) : F.symm.symm = F :=
continuous_map.homotopy_rel.symm_symm F

/--
Given `homotopy p₀ p₁` and `homotopy p₁ p₂`, we can define a `homotopy p₀ p₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans (F : homotopy p₀ p₁) (G : homotopy p₁ p₂) : homotopy p₀ p₂ :=
continuous_map.homotopy_rel.trans F G

lemma trans_apply (F : homotopy p₀ p₁) (G : homotopy p₁ p₂) (x : I × I) :
  (F.trans G) x =
    if h : (x.1 : ℝ) ≤ 1/2 then
      F (⟨2 * x.1, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
    else
      G (⟨2 * x.1 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
continuous_map.homotopy_rel.trans_apply _ _ _

lemma symm_trans (F : homotopy p₀ p₁) (G : homotopy p₁ p₂) :
  (F.trans G).symm = G.symm.trans F.symm :=
continuous_map.homotopy_rel.symm_trans _ _

/--
Casting a `homotopy p₀ p₁` to a `homotopy q₀ q₁` where `p₀ = q₀` and `p₁ = q₁`.
-/
@[simps]
def cast {p₀ p₁ q₀ q₁ : path x₀ x₁} (F : homotopy p₀ p₁) (h₀ : p₀ = q₀) (h₁ : p₁ = q₁) :
  homotopy q₀ q₁ :=
continuous_map.homotopy_rel.cast F (congr_arg _ h₀) (congr_arg _ h₁)

end

section

variables {p₀ q₀ : path x₀ x₁} {p₁ q₁ : path x₁ x₂}

/--
Suppose `p₀` and `q₀` are paths from `x₀` to `x₁`, `p₁` and `q₁` are paths from `x₁` to `x₂`.
Furthermore, suppose `F : homotopy p₀ q₀` and `G : homotopy p₁ q₁`. Then we can define a homotopy
from `p₀.trans p₁` to `q₀.trans q₁`.
-/
def hcomp (F : homotopy p₀ q₀) (G : homotopy p₁ q₁) :
  homotopy (p₀.trans p₁) (q₀.trans q₁) :=
{ to_fun := λ x,
  if (x.2 : ℝ) ≤ 1/2 then
    (F.eval x.1).extend (2 * x.2)
  else
    (G.eval x.1).extend (2 * x.2 - 1),
  continuous_to_fun := begin
    refine continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const
      (F.to_homotopy.continuous.comp (by continuity)).continuous_on
      (G.to_homotopy.continuous.comp (by continuity)).continuous_on _,
    intros x hx,
    norm_num [hx]
  end,
  map_zero_left' := λ x, by norm_num [path.trans],
  map_one_left' := λ x, by norm_num [path.trans],
  prop' := begin
    rintros x t ht,
    cases ht,
    { rw ht,
      simp },
    { rw set.mem_singleton_iff at ht,
      rw ht,
      norm_num }
  end }

lemma hcomp_apply (F : homotopy p₀ q₀) (G : homotopy p₁ q₁) (x : I × I) :
  F.hcomp G x =
  if h : (x.2 : ℝ) ≤ 1/2 then
    F.eval x.1 ⟨2 * x.2, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.2.2.1, h⟩⟩
  else
    G.eval x.1 ⟨2 * x.2 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.2.2.2⟩⟩ :=
show ite _ _ _ = _, by split_ifs; exact path.extend_extends _ _

lemma hcomp_half (F : homotopy p₀ q₀) (G : homotopy p₁ q₁) (t : I) :
  F.hcomp G (t, ⟨1/2, by norm_num, by norm_num⟩) = x₁ :=
show ite _ _ _ = _, by norm_num

end

/--
Suppose `p` is a path, then we have a homotopy from `p` to `p.reparam f` by the convexity of `I`.
-/
def reparam (p  : path x₀ x₁) (f : I → I) (hf : continuous f) (hf₀ : f 0 = 0) (hf₁ : f 1 = 1) :
  homotopy p (p.reparam f hf hf₀ hf₁) :=
{ to_fun := λ x, p ⟨σ x.1 * x.2 + x.1 * f x.2,
    show (σ x.1 : ℝ) • (x.2 : ℝ) + (x.1 : ℝ) • (f x.2 : ℝ) ∈ I, from convex_Icc _ _ x.2.2 (f x.2).2
    (by unit_interval) (by unit_interval) (by simp)⟩,
  map_zero_left' := λ x, by norm_num,
  map_one_left' := λ x, by norm_num,
  prop' := λ t x hx,
  begin
    cases hx,
    { rw hx, norm_num [hf₀] },
    { rw set.mem_singleton_iff at hx,
      rw hx,
      norm_num [hf₁] }
  end }

/--
Suppose `F : homotopy p q`. Then we have a `homotopy p.symm q.symm` by reversing the second
argument.
-/
@[simps]
def symm₂ {p q : path x₀ x₁} (F : p.homotopy q) : p.symm.homotopy q.symm :=
{ to_fun := λ x, F ⟨x.1, σ x.2⟩,
  map_zero_left' := by simp [path.symm],
  map_one_left' := by simp [path.symm],
  prop' := λ t x hx, begin
    cases hx,
    { rw hx, simp },
    { rw set.mem_singleton_iff at hx,
      rw hx,
      simp }
  end }

/--
Given `F : homotopy p q`, and `f : C(X, Y)`, we can define a homotopy from `p.map f.continuous` to
`q.map f.continuous`.
-/
@[simps]
def map {p q : path x₀ x₁} (F : p.homotopy q) (f : C(X, Y)) :
  homotopy (p.map f.continuous) (q.map f.continuous) :=
{ to_fun := f ∘ F,
  map_zero_left' := by simp,
  map_one_left' := by simp,
  prop' := λ t x hx, begin
    cases hx,
    { simp [hx] },
    { rw set.mem_singleton_iff at hx,
      simp [hx] }
  end }

end homotopy

/--
Two paths `p₀` and `p₁` are `path.homotopic` if there exists a `homotopy` between them.
-/
def homotopic (p₀ p₁ : path x₀ x₁) : Prop := nonempty (p₀.homotopy p₁)

namespace homotopic

@[refl]
lemma refl (p : path x₀ x₁) : p.homotopic p := ⟨homotopy.refl p⟩

@[symm]
lemma symm ⦃p₀ p₁ : path x₀ x₁⦄ (h : p₀.homotopic p₁) : p₁.homotopic p₀ := h.map homotopy.symm

@[trans]
lemma trans ⦃p₀ p₁ p₂ : path x₀ x₁⦄ (h₀ : p₀.homotopic p₁) (h₁ : p₁.homotopic p₂) :
  p₀.homotopic p₂ := h₀.map2 homotopy.trans h₁

lemma equivalence : equivalence (@homotopic X _ x₀ x₁) := ⟨refl, symm, trans⟩

lemma map {p q : path x₀ x₁} (h : p.homotopic q) (f : C(X, Y)) :
  homotopic (p.map f.continuous) (q.map f.continuous) := h.map (λ F, F.map f)

lemma hcomp {p₀ p₁ : path x₀ x₁} {q₀ q₁ : path x₁ x₂} (hp : p₀.homotopic p₁)
  (hq : q₀.homotopic q₁) : (p₀.trans q₀).homotopic (p₁.trans q₁) := hp.map2 homotopy.hcomp hq

/--
The setoid on `path`s defined by the equivalence relation `path.homotopic`. That is, two paths are
equivalent if there is a `homotopy` between them.
-/
protected def setoid (x₀ x₁ : X) : setoid (path x₀ x₁) := ⟨homotopic, equivalence⟩

/--
The quotient on `path x₀ x₁` by the equivalence relation `path.homotopic`.
-/
protected def quotient (x₀ x₁ : X) := quotient (homotopic.setoid x₀ x₁)

local attribute [instance] homotopic.setoid

instance : inhabited (homotopic.quotient () ()) := ⟨quotient.mk $ path.refl ()⟩

/-- The composition of path homotopy classes. This is `path.trans` descended to the quotient. -/
def quotient.comp (P₀ : path.homotopic.quotient x₀ x₁) (P₁ : path.homotopic.quotient x₁ x₂) :
  path.homotopic.quotient x₀ x₂ :=
quotient.map₂ path.trans (λ (p₀ : path x₀ x₁) p₁ hp (q₀ : path x₁ x₂) q₁ hq, (hcomp hp hq)) P₀ P₁

lemma comp_lift (P₀ : path x₀ x₁) (P₁ : path x₁ x₂) : ⟦P₀.trans P₁⟧ = quotient.comp ⟦P₀⟧ ⟦P₁⟧ := rfl

/-- The image of a path homotopy class `P₀` under a map `f`.
    This is `path.map` descended to the quotient -/
def quotient.map_fn (P₀ : path.homotopic.quotient x₀ x₁) (f : C(X, Y)) :
  path.homotopic.quotient (f x₀) (f x₁) :=
quotient.map (λ (q : path x₀ x₁), q.map f.continuous) (λ p₀ p₁ h, path.homotopic.map h f) P₀

lemma map_lift (P₀ : path x₀ x₁) (f : C(X, Y)) :
  ⟦P₀.map f.continuous⟧ = quotient.map_fn ⟦P₀⟧ f := rfl

lemma hpath_hext {p₁ : path x₀ x₁} {p₂ : path x₂ x₃} (hp : ∀ t, p₁ t = p₂ t) : ⟦p₁⟧ == ⟦p₂⟧ :=
begin
  obtain rfl : x₀ = x₂ := by { convert hp 0; simp, },
  obtain rfl : x₁ = x₃ := by { convert hp 1; simp, },
  rw heq_iff_eq, congr, ext t, exact hp t,
end


end homotopic

end path


namespace continuous_map.homotopy

/--
Given a homotopy H: f ∼ g, get the path traced by the point `x` as it moves from
`f x` to `g x`
-/
def eval_at {X : Type*} {Y : Type*} [topological_space X] [topological_space Y] {f g : C(X, Y)}
  (H : continuous_map.homotopy f g) (x : X) : path (f x) (g x) :=
{ to_fun := λ t, H (t, x),
  source' := H.apply_zero x,
  target' := H.apply_one x, }

end continuous_map.homotopy
