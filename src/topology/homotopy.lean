/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import topology.unit_interval
import topology.algebra.ordered.proj_Icc
import topology.continuous_function.basic
import topology.compact_open

/-!
# Homotopy between functions

In this file, we define a `homotopy` between two functions `f₀` and `f₁`.

## Definitions

* `homotopy f₀ f₁` is the type of homotopies between `f₀` and `f₁`
* `homotopy.refl f₀` is the constant homotopy between `f₀` and `f₀`
* `homotopy.symm f₀ f₁` is a `homotopy f₁ f₀` defined by reversing the homotopy
* `homotopy.trans F G`, where `F : homotopy f₀ f₁`, `G : homotopy f₁ f₂` is a `homotopy f₀ f₂`
  defined by putting the first homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/

noncomputable theory

universes u v

variables {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]

open_locale unit_interval

namespace continuous_map

/--
The type of homotopies between two functions.
-/
structure homotopy (f₀ f₁ : C(X, Y)) extends C(I × X, Y) :=
(to_fun_zero : ∀ x, to_fun (0, x) = f₀ x)
(to_fun_one : ∀ x, to_fun (1, x) = f₁ x)

namespace homotopy

section

variables {f₀ f₁ : C(X, Y)}

instance : has_coe_to_fun (homotopy f₀ f₁) := ⟨_, λ F, F.to_fun⟩

@[ext]
lemma ext {F G : homotopy f₀ f₁} (h : ∀ x, F x = G x) : F = G :=
begin
  cases F, cases G,
  congr' 1,
  ext x,
  exact h x,
end

@[continuity]
protected lemma continuous (F : homotopy f₀ f₁) : continuous F := F.continuous_to_fun

@[simp]
lemma apply_zero (F : homotopy f₀ f₁) (x : X) : F (0, x) = f₀ x := F.to_fun_zero x
@[simp]
lemma apply_one (F : homotopy f₀ f₁) (x : X) : F (1, x) = f₁ x := F.to_fun_one x

@[simp]
lemma to_continuous_map_apply (F : homotopy f₀ f₁) (k : I × X) : F.to_continuous_map k = F k := rfl

/--
Currying a homotopy to a continuous function fron `I` to `C(X, Y)`.
-/
def curry (F : homotopy f₀ f₁) : C(I, C(X, Y)) := F.to_continuous_map.curry

/--
Continuously extending a curried homotopy to a function from `ℝ` to `C(X, Y)`.
-/
def extend (F : homotopy f₀ f₁) : C(ℝ, C(X, Y)) := F.curry.Icc_extend zero_le_one

@[simp]
lemma extend_apply_zero (F : homotopy f₀ f₁) (x : X) : F.extend 0 x = f₀ x :=
by simp [extend, curry]

@[simp]
lemma extend_apply_one (F : homotopy f₀ f₁) (x : X) : F.extend 1 x = f₁ x := by simp [extend, curry]

end

/--
Given a continuous function `f`, we can define a `homotopy f f` by `F (x, t) = f x`
-/
def refl (f : C(X, Y)) : homotopy f f :=
{ to_fun := λ x, f x.2,
  continuous_to_fun := by continuity,
  to_fun_zero := λ _, rfl,
  to_fun_one := λ _, rfl }

instance : inhabited (homotopy (continuous_map.id : C(X, X)) continuous_map.id) :=
  ⟨homotopy.refl continuous_map.id⟩

/--
Given a `homotopy f₀ f₁`, we can define a `homotopy f₁ f₀` by reversing the homotopy.
-/
def symm {f₀ f₁ : C(X, Y)} (F : homotopy f₀ f₁) : homotopy f₁ f₀ :=
{ to_fun := λ x, F (σ x.1, x.2),
  continuous_to_fun := by continuity,
  to_fun_zero := by norm_num,
  to_fun_one := by norm_num }

@[simp]
lemma symm_apply {f₀ f₁ : C(X, Y)} (F : homotopy f₀ f₁) (x : X) (t : I) :
  F.symm (t, x) = F (σ t, x) := rfl

@[simp]
lemma symm_symm {f₀ f₁ : C(X, Y)} (F : homotopy f₀ f₁) : F.symm.symm = F :=
begin
  ext x,
  cases x,
  simp,
end

/--
Given `homotopy f₀ f₁` and `homotopy f₁ f₂`, we can define a `homotopy f₀ f₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂) : homotopy f₀ f₂ :=
{ to_fun := λ x, if (x.1 : ℝ) ≤ 1/2 then F.extend (2 * x.1) x.2 else G.extend (2 * x.1 - 1) x.2,
  continuous_to_fun := begin
    refine continuous_if_le _ _ (continuous.continuous_on _) (continuous.continuous_on _) _,
    swap 5,
    { rintros x hx,
      norm_num [hx] },
    exact continuous_induced_dom.comp continuous_fst,
    exact continuous_const,
    -- TODO: Work out why `continuity` doesn't work here.
    exact (homotopy.continuous F).comp
      ((continuous_proj_Icc.comp (continuous_const.mul
        (continuous_induced_dom.comp continuous_fst))).prod_mk continuous_snd),
    exact (homotopy.continuous G).comp
      ((continuous_proj_Icc.comp
      ((continuous_const.mul
        (continuous_induced_dom.comp continuous_fst)).sub continuous_const)).prod_mk
          continuous_snd),
  end,
  to_fun_zero := λ x, by norm_num,
  to_fun_one := λ x, by norm_num }

lemma trans_apply {f₀ f₁ f₂ : C(X, Y)} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂) (x : I × X) :
  (F.trans G) x = if h : (x.1 : ℝ) ≤ 1/2 then
    F (⟨2 * x.1, (unit_interval.mul_pos_mem_iff zero_lt_two).2 ⟨x.1.2.1, h⟩⟩, x.2)
  else
    G (⟨2 * x.1 - 1, unit_interval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, x.1.2.2⟩⟩, x.2) :=
begin
  change ite _ _ _ = _,
  split_ifs,
  { rw [extend, continuous_map.coe_Icc_extend, set.Icc_extend_of_mem],
    refl },
  { rw [extend, continuous_map.coe_Icc_extend, set.Icc_extend_of_mem],
    refl }
end

lemma symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂) :
  (F.trans G).symm = G.symm.trans F.symm :=
begin
  ext,
  cases x with t x,
  simp only [symm_apply, trans_apply],
  split_ifs with h₁ h₂,
  { change (t : ℝ) ≤ _ at h₂,
    change (1 : ℝ) - t ≤ _ at h₁,
    have ht : (t : ℝ) = 1/2,
    { linarith },
    norm_num [ht] },
  { congr' 2,
    apply subtype.ext,
    simp only [unit_interval.coe_symm_eq, subtype.coe_mk],
    linarith },
  { congr' 2,
    apply subtype.ext,
    simp only [unit_interval.coe_symm_eq, subtype.coe_mk],
    linarith },
  { change ¬ (t : ℝ) ≤ _ at h,
    change ¬ (1 : ℝ) - t ≤ _ at h₁,
    exfalso, linarith }
end

end homotopy

end continuous_map
