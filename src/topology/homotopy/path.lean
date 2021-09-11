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
`homotopic` on `path`s`, and prove that it is an equivalence relation. Finally, we also define
(but do not yet prove that is a group) the fundamental group of a space.

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
* `first_homotopy x₀` is defined to be `path.homotopic.quotient x₀ x₀`. That is, the fundamental
  group of `X` based at `x₀`.

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
structure homotopy (p₀ p₁ : path x₀ x₁) extends
  continuous_map.homotopy p₀.to_continuous_map p₁.to_continuous_map :=
(source' : ∀ t, to_fun (t, 0) = x₀)
(target' : ∀ t, to_fun (t, 1) = x₁)

namespace homotopy

section

variables {p₀ p₁ : path x₀ x₁}

instance : has_coe_to_fun (homotopy p₀ p₁) := ⟨_, λ p, p.to_fun⟩

@[simp]
lemma to_homotopy_apply (h : homotopy p₀ p₁) {t : I × I} :
  h.to_homotopy t = h t := rfl

@[simp]
lemma source (F : homotopy p₀ p₁) {t : I} : F (t, 0) = x₀ := F.source' t

@[simp]
lemma target (F : homotopy p₀ p₁) {t : I} : F (t, 1) = x₁ := F.target' t

@[ext]
lemma ext {F G : homotopy p₀ p₁} (h : ∀ t, F t = G t) : F = G :=
begin
  cases F, cases G,
  congr' 1,
  ext x,
  exact h x,
end

lemma coe_fn_inj : @function.injective (homotopy p₀ p₁) (I × I → X) coe_fn :=
λ F G h, ext $ congr_fun h

@[simp]
lemma apply_zero (F : homotopy p₀ p₁) (x : I) : F (0, x) = p₀ x := F.to_fun_zero x

@[simp]
lemma apply_one (F : homotopy p₀ p₁) (x : I) : F (1, x) = p₁ x := F.to_fun_one x

end

/--
Given a path `p`, we can define a `homotopy p p` by `F (t, x) = p x`
-/
def refl (p : path x₀ x₁) : homotopy p p :=
{ source' := λ t, by simp,
  target' := λ t, by simp,
  ..continuous_map.homotopy.refl p.to_continuous_map }

/--
Given a `homotopy p₀ p₁`, we can define a `homotopy p₁ p₀` by reversing the homotopy.
-/
def symm {p₀ p₁ : path x₀ x₁} (F : homotopy p₀ p₁) : homotopy p₁ p₀ :=
{ source' := λ t, by simp,
  target' := λ t, by simp,
  ..F.to_homotopy.symm }

/--
Given `homotopy p₀ p₁` and `homotopy p₁ p₂`, we can define a `homotopy p₀ p₂` by putting the first
homotopy on `[0, 1/2]` and the second on `[1/2, 1]`.
-/
def trans {p₀ p₁ p₂ : path x₀ x₁} (h₀ : homotopy p₀ p₁) (h₁ : homotopy p₁ p₂) : homotopy p₀ p₂ :=
{ source' := λ t, by simp [continuous_map.homotopy.trans_apply],
  target' := λ t, by simp [continuous_map.homotopy.trans_apply],
  ..h₀.to_homotopy.trans h₁.to_homotopy }

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

end homotopic

end path

/--
The quotient on `path x₀ x₀` by the equivalence relation `path.homotopic`. That is, the fundamental
group of `X` based at `x₀`.
-/
def first_homotopy (x₀ : X) := path.homotopic.quotient x₀ x₀
