/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/

import topology.unit_interval
import topology.algebra.ordered.proj_Icc
import topology.continuous_function.basic

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

/--
The type of homotopies between two functions.
-/

structure homotopy (f₀ f₁ : X → Y) extends C(X × I, Y) :=
(to_fun_zero : ∀ x, to_fun (x, 0) = f₀ x)
(to_fun_one : ∀ x, to_fun (x, 1) = f₁ x)

namespace homotopy

section

variables {f₀ f₁ : X → Y}

instance : has_coe_t (homotopy f₀ f₁) C(X × I, Y) := ⟨homotopy.to_continuous_map⟩
instance : has_coe_to_fun (homotopy f₀ f₁) := ⟨_, λ F, F.to_fun⟩

@[continuity]
protected lemma continuous (F : homotopy f₀ f₁) : continuous F := F.continuous_to_fun

@[simp]
lemma apply_zero (F : homotopy f₀ f₁) (x : X) : F (x, 0) = f₀ x := F.to_fun_zero x
@[simp]
lemma apply_one (F : homotopy f₀ f₁) (x : X) : F (x, 1) = f₁ x := F.to_fun_one x

/--
Currying a homotopy to give us a function `X → I → Y`.
-/
def curry (F : homotopy f₀ f₁) : X → I → Y := function.curry F

/--
Extending a curried homotopy to a function `X → ℝ → Y`.
-/
def extend (F : homotopy f₀ f₁) : X → ℝ → Y := λ x, set.Icc_extend zero_le_one (F.curry x)

@[simp]
lemma extend_apply_zero (F : homotopy f₀ f₁) (x : X) : F.extend x 0 = f₀ x :=
  by simp [extend, curry]
@[simp]
lemma extend_apply_one (F : homotopy f₀ f₁) (x : X) : F.extend x 1 = f₁ x := by simp [extend, curry]

end

/--
Given a continuous function `f`, we can define a `homotopy f f` by `F (x, t) = f x`
-/
def refl {f : X → Y} (hf : continuous f) : homotopy f f :=
{ to_fun := λ x, f x.1,
  continuous_to_fun := by continuity,
  to_fun_zero := λ _, rfl,
  to_fun_one := λ _, rfl }

instance : inhabited (homotopy (id : X → X) id) := ⟨homotopy.refl continuous_id⟩

/--
Given a `homotopy f₀ f₁`, we can define a `homotopy f₁ f₀` by reversing the homotopy.
-/
def symm {f₀ f₁ : X → Y} (F : homotopy f₀ f₁) : homotopy f₁ f₀ :=
{ to_fun := λ x, F (x.1, σ x.2),
  continuous_to_fun := by continuity,
  to_fun_zero := by norm_num,
  to_fun_one := by norm_num }

/--
Given `homotopy f₀ f₁` and `homotopy f₁ f₂`, we can define a `homotopy f₀ f₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {f₀ f₁ f₂ : X → Y} (F : homotopy f₀ f₁) (G : homotopy f₁ f₂) : homotopy f₀ f₂ :=
{ to_fun := λ x, if (x.2 : ℝ) ≤ 1/2 then F.extend x.1 (2 * x.2) else G.extend x.1 (2 * x.2 - 1),
  continuous_to_fun := begin
    refine continuous_if_le _ _ (continuous.continuous_on _) (continuous.continuous_on _) _,
    swap 5,
    { rintros x hx,
      norm_num [hx] },
    continuity,
  end,
  to_fun_zero := λ x, by norm_num,
  to_fun_one := λ x, by norm_num }

end homotopy
