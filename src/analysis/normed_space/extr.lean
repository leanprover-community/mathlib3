/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.normed_space.ray
import topology.local_extr

/-!
# (Local) maximums in a normed space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove the following lemma, see `is_max_filter.norm_add_same_ray`. If `f : α → E` is
a function such that `norm ∘ f` has a maximum along a filter `l` at a point `c` and `y` is a vector
on the same ray as `f c`, then the function `λ x, ‖f x + y‖` has a maximul along `l` at `c`.

Then we specialize it to the case `y = f c` and to different special cases of `is_max_filter`:
`is_max_on`, `is_local_max_on`, and `is_local_max`.

## Tags

local maximum, normed space
-/

variables {α X E : Type*} [seminormed_add_comm_group E] [normed_space ℝ E] [topological_space X]

section

variables {f : α → E} {l : filter α} {s : set α} {c : α} {y : E}

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum along a filter `l` at a point
`c` and `y` is a vector on the same ray as `f c`, then the function `λ x, ‖f x + y‖` has a maximul
along `l` at `c`. -/
lemma is_max_filter.norm_add_same_ray (h : is_max_filter (norm ∘ f) l c) (hy : same_ray ℝ (f c) y) :
  is_max_filter (λ x, ‖f x + y‖) l c :=
h.mono $ λ x hx,
calc ‖f x + y‖ ≤ ‖f x‖ + ‖y‖ : norm_add_le _ _
           ... ≤ ‖f c‖ + ‖y‖ : add_le_add_right hx _
           ... = ‖f c + y‖   : hy.norm_add.symm

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum along a filter `l` at a point
`c`, then the function `λ x, ‖f x + f c‖` has a maximul along `l` at `c`. -/
lemma is_max_filter.norm_add_self (h : is_max_filter (norm ∘ f) l c) :
  is_max_filter (λ x, ‖f x + f c‖) l c :=
h.norm_add_same_ray same_ray.rfl

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum on a set `s` at a point `c` and
`y` is a vector on the same ray as `f c`, then the function `λ x, ‖f x + y‖` has a maximul on `s` at
`c`. -/
lemma is_max_on.norm_add_same_ray (h : is_max_on (norm ∘ f) s c) (hy : same_ray ℝ (f c) y) :
  is_max_on (λ x, ‖f x + y‖) s c :=
h.norm_add_same_ray hy

/-- If `f : α → E` is a function such that `norm ∘ f` has a maximum on a set `s` at a point `c`,
then the function `λ x, ‖f x + f c‖` has a maximul on `s` at `c`. -/
lemma is_max_on.norm_add_self (h : is_max_on (norm ∘ f) s c) : is_max_on (λ x, ‖f x + f c‖) s c :=
h.norm_add_self

end

variables {f : X → E} {s : set X} {c : X} {y : E}

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum on a set `s` at a point
`c` and `y` is a vector on the same ray as `f c`, then the function `λ x, ‖f x + y‖` has a local
maximul on `s` at `c`. -/
lemma is_local_max_on.norm_add_same_ray (h : is_local_max_on (norm ∘ f) s c)
  (hy : same_ray ℝ (f c) y) : is_local_max_on (λ x, ‖f x + y‖) s c :=
h.norm_add_same_ray hy

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum on a set `s` at a point
`c`, then the function `λ x, ‖f x + f c‖` has a local maximul on `s` at `c`. -/
lemma is_local_max_on.norm_add_self (h : is_local_max_on (norm ∘ f) s c) :
  is_local_max_on (λ x, ‖f x + f c‖) s c :=
h.norm_add_self

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum at a point `c` and `y` is
a vector on the same ray as `f c`, then the function `λ x, ‖f x + y‖` has a local maximul at `c`. -/
lemma is_local_max.norm_add_same_ray (h : is_local_max (norm ∘ f) c)
  (hy : same_ray ℝ (f c) y) : is_local_max (λ x, ‖f x + y‖) c :=
h.norm_add_same_ray hy

/-- If `f : α → E` is a function such that `norm ∘ f` has a local maximum at a point `c`, then the
function `λ x, ‖f x + f c‖` has a local maximul at `c`. -/
lemma is_local_max.norm_add_self (h : is_local_max (norm ∘ f) c) :
  is_local_max (λ x, ‖f x + f c‖) c :=
h.norm_add_self
