/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import topology.homotopy.basic
import topology.path_connected

/-!
# Homotopy between paths

In this file, we define a `homotopy` between two `path`s. In addition, we define a relation
`homotopic` on `path`s, and prove that it is an equivalence relation.

## Definitions

* `path.homotopy p₀ p₁` is the type of homotopies between paths `p₀` and `p₁`
* `path.homotopy.refl p` is the constant homotopy between `p` and itself
* `path.homotopy.symm F` is the `path.homotopy p₁ p₀` defined by reversing the homotopy
* `path.homotopy.trans F G`, where `F : path.homotopy p₀ p₁`, `G : path.homotopy p₁ p₂` is the
  `path.homotopy p₀ p₂` defined by putting the first homotopy on `[0, 1/2]` and the second on
  `[1/2, 1]`
* `path.homotopic p₀ p₁` is the relation saying that there is a homotopy between `p₀` and `p₁`
* `path.homotopic.setoid x₀ x₁` is the setoid on `path`s from `path.homotopic`
* `path.homotopic.quotient x₀ x₁` is the quotient type from `path x₀ x₀` by `path.homotopic.setoid`

## Todos

Prove that `first_homotopy x₀` is a `group`.
-/

universes u v

variables {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]
variables {x₀ x₁ : X}

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

instance : has_coe_to_fun (homotopy p₀ p₁) := ⟨_, λ F, F.to_fun⟩

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

def eval (F : homotopy p₀ p₁) (t : I) : path x₀ x₁ :=
{ to_fun := λ u, F (t, u),
  source' := sorry,
  target' := sorry }

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

end

section

variables {x₂ : X}

def trans' {p₀ q₀ : path x₀ x₁} {p₁ q₁ : path x₁ x₂} (F : homotopy p₀ q₀) (G : homotopy p₁ q₁) :
  homotopy (p₀.trans p₁) (q₀.trans q₁) :=
{ to_fun := λ x,
  if (x.2 : ℝ) ≤ 1/2 then
    (F.eval x.1).extend (2 * x.2)
  else
    (G.eval x.1).extend (2 * x.2 - 1),
  continuous_to_fun := begin
    refine continuous_if_le (continuous_induced_dom.comp continuous_snd) continuous_const _ _ _,
    { apply continuous.continuous_on,
      apply continuous.comp,
     },
    -- { exact continuous_induced_dom.comp continuous_snd}
    -- continuity,
    -- continuity,
  end,
  to_fun_zero := _,
  to_fun_one := _,
  prop' := _ }

end

end homotopy

/--
Two paths `p₀` and `p₁` are `path.homotopic` if there exists a `homotopy` between them.
-/
def homotopic (p₀ p₁ : path x₀ x₁) : Prop := nonempty (p₀.homotopy p₁)

namespace homotopic

@[refl]
lemma refl (p : path x₀ x₁) : p.homotopic p := ⟨homotopy.refl p⟩

@[symm]
lemma symm ⦃p₀ p₁ : path x₀ x₁⦄ (h : p₀.homotopic p₁) : p₁.homotopic p₀ := ⟨h.some.symm⟩

@[trans]
lemma trans ⦃p₀ p₁ p₂ : path x₀ x₁⦄ (h₀ : p₀.homotopic p₁) (h₁ : p₁.homotopic p₂) :
  p₀.homotopic p₂ := ⟨h₀.some.trans h₁.some⟩

lemma equivalence : equivalence (@homotopic X _ x₀ x₁) := ⟨refl, symm, trans⟩

/--
The setoid on `path`s defined by the equivalence relation `path.homotopic`. That is, two paths are
equivalent if there is a `homotopy` between them.
-/
protected def setoid (x₀ x₁ : X) : setoid (path x₀ x₁) := ⟨homotopic, equivalence⟩

/--
The quotient on `path x₀ x₁` by the equivalence relation `path.homotopic`.
-/
protected def quotient (x₀ x₁ : X) := quotient (homotopic.setoid x₀ x₁)

instance : inhabited (homotopic.quotient () ()) :=
⟨@quotient.mk _ (homotopic.setoid _ _) $ path.refl ()⟩

end homotopic

end path
