/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/

import topology.homotopy.basic
import topology.path_connected
import topology.unit_interval
import algebraic_topology.fundamental_groupoid.basic
import logic.unique

/-!
# nth homotopy group

We define the nth homotopy group at x `π n x` as the equivalence classes
of functions from the nth dimensional cube to the topological space X
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are nth dimensional loops `nloop n x`, in particular
`nloop 1 x ≃ path x x`

We show that `π 0 x` is equivalent to the path-conected components, and
that `π 1 x` is equivalent to the fundamental grupoid at `x`.

## definitions

* `nloop n x` is the type of continous fuctions `I^n→X` that send the boundary to `x`
* `nth_homotopy_group n x` denoted `π n x` is the quotient of `nloop n x` up to homotopic
  equivalence

-/

open_locale unit_interval topological_space

noncomputable theory

universes u
variables {X:Type u} [topological_space X]
variables {n:nat} {x:X}

/--
The nth dimensional cube
-/
@[derive [has_zero, has_one]]
def cube (n:nat) := fin n → I
notation `I^` := cube

namespace cube
instance topology {n} : topological_space (I^n) :=
  Pi.topological_space

@[continuity] lemma proj_continuous {n} (i:fin n) : continuous (λ (f:I^n), f i) :=
begin
  apply continuous_infi_dom,
  apply continuous_def.2,
  intros s H,
  convert ((@is_open_induced_iff' _ _ _ _ (λ (f : I^n), f i)).2 ⟨s, ⟨H, by refl⟩⟩)
end

/--
The points of the nth dimensional cube with a projection set to 0 or 1
-/
def boundary (n:nat) : set (I^n) :=
  { y | ∃ i:fin n , y i = 0 ∨ y i = 1}

/--
The first projection of a non-zero dimensional cube
-/
@[simp] def head {n} : I^(n+1) → I := λ c, c 0

@[continuity] lemma head.continuous {n} : continuous (@head n) := proj_continuous 0

/--
The last `n` projections of an `n+1` dimensional cube
-/
@[simp] def tail {n} : I^(n+1) → I^n := λ c, fin.tail c

instance unique_cube0 : unique (I^0) :=
  { default := 0, uniq := by {intro a, ext1, exact x.elim0} }

lemma one_indep {α} (f : fin 1 → α) (i j : fin 1) : f i = f j :=
  by rw subsingleton.elim i j

lemma one_char {α} (x : fin 1 → α) : x = λ _, x 0 :=
  by { ext, apply one_indep }

end cube

/--
The nth dimensional loops; functions `I^n → X` that send the boundary to `x`
-/
structure nloop (n : nat) (x : X) extends C(I^n,X) :=
  (boundary : ∀ y ∈ cube.boundary n, to_fun y = x )

namespace nloop

instance fun_like : fun_like (nloop n x) (I^n) (λ _, X) :=
  { coe := λ f, f.1,
    coe_injective' :=
    begin
      intros f g hfg, cases f, cases g,
      congr, ext1, exact congr_fun hfg _,
    end }

@[ext] lemma ext (f g : nloop n x) (H : ∀ y, f y = g y) : f = g := fun_like.ext f g H

@[simp] lemma mk_apply (f : C(I^n, X)) (H y) : (⟨f, H⟩ : nloop n x)  y = f y := rfl

/--
The constant `nloop` at x
-/
def const : nloop n x := ⟨⟨λ_x,by continuity⟩,λ_ _,rfl⟩

instance inhabited : inhabited (nloop n x) :=
  { default := const }

/--
Boundary-preserving homotopic relation between `nloop`s
-/
def homotopic (f g : nloop n x) : Prop :=
  nonempty (f.to_continuous_map.homotopy_rel g.to_continuous_map (cube.boundary n))

namespace homotopic
section
variables {f g h : nloop n x}

@[refl] lemma refl (f : nloop n x) : homotopic f f :=
  ⟨continuous_map.homotopy_rel.refl _ _⟩

@[symm] lemma symm (H : f.homotopic g) : g.homotopic f :=
  H.map continuous_map.homotopy_rel.symm

@[trans] lemma trans (H0 : f.homotopic g) (H1 : g.homotopic h) : f.homotopic h :=
  H0.map2 continuous_map.homotopy_rel.trans H1

lemma equiv : equivalence (@homotopic X _ n x) :=
  ⟨homotopic.refl, λ _ _, homotopic.symm, λ _ _ _, homotopic.trans⟩

instance setoid (n : nat) (x : X) : setoid (nloop n x) :=
  ⟨homotopic, equiv⟩

end
end homotopic

end nloop

/--
The nth homotopy group at x defined as the quotient of base preserving functions up to homotopic
equivalence
-/
def nth_homotopy_group (n : nat) (x : X) := quotient (nloop.homotopic.setoid n x)
notation `π` := nth_homotopy_group

instance nth_homotopy_group.inhabited : inhabited (π n x) :=
  { default :=  quotient.mk' nloop.const }

/--
The 0th homotopy "group" is equivalent to the path components of `X`, aka the `zeroth_homotopy`
-/
def pi0_equiv_path_components : π 0 x ≃ zeroth_homotopy X :=
begin
  refine (quotient.congr _ _),
  -- nloop 0 x ≃ X
  exact
  { to_fun := λ f, f 0,
    inv_fun := λ x, ⟨continuous_map.const _ x, (λ _ ⟨f0,_⟩, fin.elim0 f0)⟩,
    left_inv := λ _, by { ext1, revert y, refine (unique.forall_iff.2 _), unfold default,
      simp only [nloop.mk_apply, continuous_map.const_apply] },
    right_inv := λ _, by simp },
  -- joined iff homotopic
  intros, split; rintros ⟨H⟩; constructor,
  exact
  { to_fun := λ t, H ⟨t, fin.elim0⟩,
    continuous_to_fun := by continuity,
    source' := by simpa only [matrix.zero_empty, continuous_map.homotopy_with.apply_zero],
    target' := by simpa only [matrix.zero_empty, continuous_map.homotopy_with.apply_one]},
  exact
  { to_fun := λ t0, H t0.fst,
    continuous_to_fun := by continuity,
    map_zero_left' := by {refine (unique.forall_iff.2 _), unfold default, simpa only [path.source]},
    map_one_left' := by {refine (unique.forall_iff.2 _), unfold default, simpa only [path.target]},
    prop' := λ _ _ ⟨i,_⟩, i.elim0 }
end

/--
The first homotopy group at x is equivalent to the fundamental grupoid,
i.e. the quotient of loops up to homotopy
-/
def pi1_equiv_fundamental_groupoid : π 1 x ≃ path.homotopic.quotient x x :=
begin
  refine (quotient.congr _ _),
  -- nloop 1 x ≃ path x x
  exact
  { to_fun := λ p, path.mk ⟨λ t, p (λ _, t), by {continuity, exact p.1.2}⟩
        (p.boundary (λ _, 0) ⟨0, by {left, refl}⟩)
        (p.boundary (λ _, 1) ⟨1, by {right, refl}⟩),
    inv_fun := λ p, {
      to_fun := λ c, p c.head,
      continuous_to_fun := by continuity,
      boundary :=
      begin
        intro y, rw (cube.one_char y),
        rintros ⟨i,iH⟩, simp only [cube.head] at iH ⊢,
        cases iH; rw iH, simp only [path.source], simp only [path.target],
      end },
    left_inv := by { intro p, ext1, rw (y.one_char),
      simp only [cube.head, path.coe_mk, nloop.mk_apply, continuous_map.coe_mk], },
    right_inv := by { intro p, ext1,
      simp only [cube.head, nloop.mk_apply, continuous_map.coe_mk, path.coe_mk], } },
  -- homotopic iff homotopic
  intros, split; rintros ⟨H⟩; constructor,
  exact
  { to_fun := λ tx, H (tx.fst, λ _, tx.snd),
    continuous_to_fun := by continuity,
    map_zero_left' := by { intros, simpa only [continuous_map.coe_mk,
      continuous_map.homotopy_with.apply_zero, equiv.coe_fn_mk] },
    map_one_left' := by {intros, simpa only [continuous_map.homotopy_with.apply_one]},
    prop' :=
    begin
      intros t y Hy, apply H.prop', use 0,
      cases Hy, rw Hy, left, refl,
      cases Hy, right, refl,
    end },
  refine
  ⟨{to_fun := λ tx, H (tx.fst, tx.snd.head),
    continuous_to_fun := by continuity,
    map_zero_left' := λ y, by {rw (cube.one_char y),
      simpa only [continuous_map.homotopy_with.apply_zero]},
    map_one_left' := λ y, by {rw (cube.one_char y),
      simpa only [continuous_map.homotopy_with.apply_one]} }, _⟩,
  rintros t y ⟨i,iH⟩,
  have hi : i = 0, { rcases i with ⟨⟨_,_⟩,iH'⟩,
    simp only [eq_iff_true_of_subsingleton],
    exfalso, revert iH', norm_num },
  subst hi,
  simp only [cube.head, continuous_map.coe_mk],
  split,
  { convert (H.eq_fst _ _), exact y.one_char, exact iH, },
  convert (H.eq_snd _ _), exact y.one_char, exact iH
end
