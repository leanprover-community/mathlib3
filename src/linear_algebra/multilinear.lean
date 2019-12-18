/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import linear_algebra.basic

/-!
# Multilinear maps

-/

open_locale classical
noncomputable theory

universes u v w u'
variables {α : Type u} {β : Type v} {ι : Type u'}

/-- `replace_at f i₀ x` is the function equal to `f`, except at `i₀` where it is equal to `x`. -/
def replace_at (f : ι → α) (i₀ : ι) (x : α) (i : ι) : α :=
if i = i₀ then x else f i

structure multilinear_map (R : Type u) (ι : Type u') (M₁ : Type v) (M₂ : Type w)
  [ring R] [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂] :=
(to_fun : (ι → M₁) → M₂)
(add : ∀f i x y,
  to_fun (replace_at f i (x + y)) = to_fun (replace_at f i x) + to_fun (replace_at f i y))
(smul : ∀f i x (c : R), to_fun (replace_at f i (c • x)) = c • to_fun (replace_at f i x))
