/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/

import algebraic_topology.fundamental_groupoid.fundamental_group

/-!
# `n`th homotopy group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define the `n`th homotopy group at `x`, `π n x`, as the equivalence classes
of functions from the nth dimensional cube to the topological space `X`
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are generalized loops `gen_loop n x`, in particular
`gen_loop 1 x ≃ path x x`

We show that `π 0 x` is equivalent to the path-conected components, and
that `π 1 x` is equivalent to the fundamental group at `x`.

## definitions

* `gen_loop n x` is the type of continous fuctions `I^n → X` that send the boundary to `x`
* `homotopy_group n x` denoted `π n x` is the quotient of `gen_loop n x` by homotopy relative
  to the boundary

TODO: show that `π n x` is a group when `n > 0` and abelian when `n > 1`. Show that
`pi1_equiv_fundamental_group` is an isomorphism of groups.

-/

open_locale unit_interval topology

noncomputable theory

universes u
variables {X : Type u} [topological_space X]
variables {n : ℕ} {x : X}

/--
The `n`-dimensional cube.
-/
@[derive [has_zero, has_one, topological_space]]
def cube (n : ℕ) : Type := fin n → I
local notation `I^` := cube

namespace cube

@[continuity] lemma proj_continuous (i : fin n) : continuous (λ f : I^n, f i) :=
continuous_apply i

/--
The points of the `n`-dimensional cube with at least one projection equal to 0 or 1.
-/
def boundary (n : ℕ) : set (I^n) := {y | ∃ i, y i = 0 ∨ y i = 1}

/--
The first projection of a positive-dimensional cube.
-/
@[simp] def head {n} : I^(n+1) → I := λ c, c 0

@[continuity] lemma head.continuous {n} : continuous (@head n) := proj_continuous 0

/--
The projection to the last `n` coordinates from an `n+1` dimensional cube.
-/
@[simp] def tail {n} : I^(n+1) → I^n := λ c, fin.tail c

instance unique_cube0 : unique (I^0) := pi.unique_of_is_empty _

lemma one_char (f : I^1) : f = λ _, f 0 := by convert eq_const_of_unique f

end cube

/--
The `n`-dimensional generalized loops; functions `I^n → X` that send the boundary to the base point.
-/
structure gen_loop (n : ℕ) (x : X) extends C(I^n, X) :=
(boundary : ∀ y ∈ cube.boundary n, to_fun y = x)

namespace gen_loop

instance fun_like : fun_like (gen_loop n x) (I^n) (λ _, X) :=
{ coe := λ f, f.1,
  coe_injective' := λ ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ h, by { congr, exact h } }

@[ext] lemma ext (f g : gen_loop n x) (H : ∀ y, f y = g y) : f = g := fun_like.ext f g H

@[simp] lemma mk_apply (f : C(I^n, X)) (H y) : (⟨f, H⟩ : gen_loop n x) y = f y := rfl

/--
The constant `gen_loop` at `x`.
-/
def const : gen_loop n x := ⟨continuous_map.const _ x, λ _ _, rfl⟩

instance inhabited : inhabited (gen_loop n x) := { default := const }

/--
The "homotopy relative to boundary" relation between `gen_loop`s.
-/
def homotopic (f g : gen_loop n x) : Prop :=
f.to_continuous_map.homotopic_rel g.to_continuous_map (cube.boundary n)

namespace homotopic
section
variables {f g h : gen_loop n x}

@[refl] lemma refl (f : gen_loop n x) : homotopic f f := continuous_map.homotopic_rel.refl _

@[symm] lemma symm (H : f.homotopic g) : g.homotopic f := H.symm

@[trans] lemma trans (H0 : f.homotopic g) (H1 : g.homotopic h) : f.homotopic h := H0.trans H1

lemma equiv : equivalence (@homotopic X _ n x) :=
⟨homotopic.refl, λ _ _, homotopic.symm, λ _ _ _, homotopic.trans⟩

instance setoid (n : ℕ) (x : X) : setoid (gen_loop n x) := ⟨homotopic, equiv⟩

end
end homotopic

end gen_loop

/--
The `n`th homotopy group at `x` defined as the quotient of `gen_loop n x` by the
`homotopic` relation.
-/
@[derive inhabited]
def homotopy_group (n : ℕ) (x : X) : Type _ := quotient (gen_loop.homotopic.setoid n x)
local notation `π` := homotopy_group

/-- The 0-dimensional generalized loops based at `x` are in 1-1 correspondence with `X`. -/
def gen_loop_zero_equiv : gen_loop 0 x ≃ X :=
{ to_fun := λ f, f 0,
  inv_fun := λ x, ⟨continuous_map.const _ x, λ _ ⟨f0,_⟩, f0.elim0⟩,
  left_inv := λ f, by { ext1, exact congr_arg f (subsingleton.elim _ _) },
  right_inv := λ _, rfl }

/--
The 0th homotopy "group" is equivalent to the path components of `X`, aka the `zeroth_homotopy`.
-/
def pi0_equiv_path_components : π 0 x ≃ zeroth_homotopy X :=
quotient.congr gen_loop_zero_equiv
begin
  -- joined iff homotopic
  intros, split; rintro ⟨H⟩,
  exacts
  [⟨{ to_fun := λ t, H ⟨t, fin.elim0⟩,
      source' := (H.apply_zero _).trans (congr_arg a₁ matrix.zero_empty.symm),
      target' := (H.apply_one _).trans (congr_arg a₂ matrix.zero_empty.symm) }⟩,
   ⟨{ to_fun := λ t0, H t0.fst,
      map_zero_left' := λ _, by convert H.source,
      map_one_left' := λ _, by convert H.target,
      prop' := λ _ _ ⟨i,_⟩, i.elim0 }⟩]
end

/-- The 1-dimensional generalized loops based at `x` are in 1-1 correspondence with
  paths from `x` to itself. -/
@[simps] def gen_loop_one_equiv_path_self : gen_loop 1 x ≃ path x x :=
{ to_fun := λ p, path.mk ⟨λ t, p (λ _, t), by {continuity, exact p.1.2}⟩
    (p.boundary (λ _, 0) ⟨0, or.inl rfl⟩)
    (p.boundary (λ _, 1) ⟨1, or.inr rfl⟩),
  inv_fun := λ p,
  { to_fun := λ c, p c.head,
    boundary := begin
      rintro y ⟨i, iH|iH⟩; cases unique.eq_default i;
      apply (congr_arg p iH).trans, exacts [p.source, p.target],
    end },
  left_inv := λ p, by { ext1, exact congr_arg p y.one_char.symm },
  right_inv := λ p, by { ext, refl } }

/--
The first homotopy group at `x` is equivalent to the fundamental group,
i.e. the loops based at `x` up to homotopy.
-/
def pi1_equiv_fundamental_group : π 1 x ≃ fundamental_group X x :=
begin
  refine equiv.trans _ (category_theory.groupoid.iso_equiv_hom _ _).symm,
  refine quotient.congr gen_loop_one_equiv_path_self _,
  -- homotopic iff homotopic
  intros, split; rintros ⟨H⟩,
  exacts
  [⟨{ to_fun := λ tx, H (tx.fst, λ _, tx.snd),
      map_zero_left' := λ _, by convert H.apply_zero _,
      map_one_left' := λ _, by convert H.apply_one _,
      prop' := λ t y iH, H.prop' _ _ ⟨0,iH⟩ }⟩,
   ⟨{ to_fun := λ tx, H (tx.fst, tx.snd.head),
      map_zero_left' := λ y, by { convert H.apply_zero _, exact y.one_char },
      map_one_left' := λ y, by { convert H.apply_one _, exact y.one_char },
      prop' := λ t y ⟨i, iH⟩, begin
        cases unique.eq_default i, split,
        { convert H.eq_fst _ _, exacts [y.one_char, iH] },
        { convert H.eq_snd _ _, exacts [y.one_char, iH] },
      end }⟩],
end
