/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/

import topology.homotopy.basic
import topology.path_connected
import topology.unit_interval
import algebraic_topology.fundamental_groupoid.basic

/-!
# nth homotopy group

We define the nth homotopy group at x `π n x` as the equivalence classes
of functions from the nth dimensional cube to the topological space X
that send the boundary to the base point `x`, up to homotopic equivalence.

We show that `π 0 x` is equivalent to the path-conected components, and
that `π 1 x` is equivalent to the fundamental grupoid at `x`.

## definitions

* `pre_π n x` is the type of continous fuctions `I^n→X` that send the boundary to `x`
* `pre_π.homotopy` is the type of homotopies between such functions
* `π n x` the quotient of `pre_π n x` up to homotopic equivalence

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
The last `n` projection of an `n+1` dimensional cube
-/
@[simp] def tail {n} : I^(n+1) → I^n := λ c, fin.tail c

instance unique_cube0 : unique (I^0) :=
  { default := 0, uniq := by {intro a, ext1, exact x.elim0} }

lemma one_indep (f:I^1) (i j:fin 1) : f i = f j :=
begin
  rcases i with ⟨⟨_,_⟩,_⟩; rcases j with ⟨⟨_,_⟩,_⟩,
  reflexivity,
  { exfalso, exact (nat.not_lt_zero _ (nat.le_of_succ_le_succ j_property)) },
  all_goals { exfalso, exact (nat.not_lt_zero _ (nat.le_of_succ_le_succ i_property)) },
end

lemma one_char (x:I^1) : x = λ _, x 0 :=
begin
  ext1 i, rcases i with ⟨⟨_,_⟩,_⟩, reflexivity,
  exfalso, exact (nat.not_lt_zero _ (nat.le_of_succ_le_succ i_property))
end

end cube

/--
The continuous fuctions `I^n→X` that send the boundary to `x`
-/
structure pre_π (n : nat) (x : X) extends C(I^n,X) :=
  (boundary : ∀ y ∈ cube.boundary n, to_fun y = x )

namespace pre_π

instance fun_like : fun_like (pre_π n x) (I^n) (λ _, X) :=
  { coe := λ f, f.1,
    coe_injective' :=
    begin
      intros f g hfg, cases f, cases g,
      congr, ext1, exact congr_fun hfg _,
    end }

@[ext] lemma ext (f g : pre_π n x) (H : ∀ y, f y = g y) : f = g := fun_like.ext f g H

@[simp] lemma mk_apply (f : C(I^n, X)) (H y) : (⟨f, H⟩ : pre_π n x)  y = f y := rfl

/--
The constant `pre_π` at x
-/
def const : pre_π n x := ⟨⟨λ_x,by continuity⟩,λ_ _,rfl⟩

instance inhabited : inhabited (pre_π n x) :=
  { default := const }

/--
Homotopies are functions I×I^n → X
-/
abbreviation homotopy (f g : pre_π n x) :=
  f.to_continuous_map.homotopy_rel g.to_continuous_map (cube.boundary n)
infix `~`:50 := homotopy

namespace homotopy
section
variables  {f g h : pre_π n x} (H : f ~ g)

instance fun_like : fun_like (f ~ g) (I^(n+1)) (λ _, X) :=
  { coe := λ h c, h.1 (c 0, fin.tail c),
    coe_injective' :=
    begin
      rintros h1 h2 hfg, cases h1, cases h2,
      congr, ext1 ⟨x,y⟩, simpa only [fin.tail_cons] using congr_fun hfg (fin.cons x y),
    end }

@[continuity] lemma continuous : continuous H :=
  by { refine H.continuous.comp _, continuity; apply continuous_apply }

/--
The constant homotopy at f
-/
@[refl] def refl (f : pre_π n x) : f ~ f :=
  continuous_map.homotopy_rel.refl _ _

/--
Reversing of a homotopy
-/
@[symm] def symm : f ~ g → g ~ f :=
  continuous_map.homotopy_rel.symm

/--
Concatenation of homotopies by using them along `[0,2⁻¹]` and `[2⁻¹,1] `
-/
@[trans] def trans : f ~ g → g ~ h → f ~ h :=
  continuous_map.homotopy_rel.trans

/--
Eval an homotopy at an intermediate point, yielding a `pre_π`
-/
def eval (t:I) : pre_π n x :=
  { to_fun := H.to_homotopy.curry t,
    continuous_to_fun := by continuity,
    boundary :=
    begin
      intros y H,
      simp only [continuous_map.homotopy.curry_apply,
        continuous_map.homotopy_with.coe_to_homotopy],
      rw continuous_map.homotopy_rel.eq_fst,
      apply f.boundary,
      all_goals { assumption }
    end }

@[simp] lemma eval0 : H.eval 0 = f :=
begin
  ext, unfold eval,
  simp only [mk_apply, continuous_map.homotopy_with.apply_zero,
    continuous_map.coe_mk, continuous_map.homotopy.curry_apply,
    continuous_map.homotopy_with.coe_to_homotopy],
  reflexivity,
end

@[simp] lemma eval1 : H.eval 1 = g :=
begin
  ext, unfold eval,
  simp only [mk_apply, continuous_map.coe_mk,
    continuous_map.homotopy_with.apply_one, continuous_map.homotopy.curry_apply,
    continuous_map.homotopy_with.coe_to_homotopy],
  reflexivity,
end

@[simp] lemma at0 (y : I^n) : H ⟨0, y⟩ = f y :=
  by { convert H.apply_zero y }

@[simp] lemma at1 (y : I^n) : H ⟨1, y⟩ = g y :=
  by { convert H.apply_one y }

end

instance inhabited : inhabited ( (const:pre_π n x).homotopy const ) :=
  { default :=
    { to_fun := λ _, x,
      continuous_to_fun := by continuity,
      map_zero_left' := λ _, rfl,
      map_one_left' := λ _, rfl,
      prop' := λ _ _ _, ⟨rfl,rfl⟩ } }

end homotopy

/--
Homotopic relation between `pre_π`s
-/
def homotopic (f0 f1 : pre_π n x) : Prop := nonempty (f0 ~ f1)
namespace homotopic
section
variables {f g h : pre_π n x}

@[refl] lemma refl (f : pre_π n x) : homotopic f f :=
  ⟨homotopy.refl f⟩

@[symm] lemma symm (H : f.homotopic g) : g.homotopic f :=
  H.map homotopy.symm

@[trans] lemma trans (H0 : f.homotopic g) (H1 : g.homotopic h) : f.homotopic h :=
  H0.map2 homotopy.trans H1

lemma equiv : equivalence (@homotopic X _ n x) :=
  ⟨homotopic.refl, λ _ _, homotopic.symm, λ _ _ _, homotopic.trans⟩

instance setoid (n : nat) (x : X) : setoid (pre_π n x) :=
  ⟨homotopic, equiv⟩

end
end homotopic

end pre_π

/--
The nth homotopy group at x defined as the quotient of base preserving functions up to homotopic
equivalence
-/
def π (n : nat) (x : X) := quotient (pre_π.homotopic.setoid n x)

instance π.inhabited : inhabited (π n x) :=
  { default :=  quotient.mk' pre_π.const }

/--
The 0th homotopy "group" is equivalent to the path components of X aka the `zeroth_homotopy`
-/
def pi0_equiv_path_components : π 0 x ≃ zeroth_homotopy X :=
begin
  refine (quotient.congr _ _),
  -- pre_π 0 x ≃ X
  exact { to_fun := λ f, f 0,
    inv_fun := λ x, ⟨continuous_map.const _ x, (λ _ ⟨f0,_⟩, fin.elim0 f0)⟩,
    left_inv := λ _, by { ext1, revert y, refine (unique.forall_iff.2 _), unfold default,
      simp only [pre_π.mk_apply, continuous_map.const_apply] },
    right_inv := λ _, by simp },
  -- joined iff homotopic
  intros, split; rintros ⟨H⟩; constructor,
  exact { to_fun := λ t, H ⟨t, fin.elim0⟩,
    continuous_to_fun := by continuity,
    source' := by simpa only [matrix.zero_empty, pre_π.homotopy.at0],
    target' := by simpa only [matrix.zero_empty, pre_π.homotopy.at1] },
  exact { to_fun := λ t0, H t0.fst,
    continuous_to_fun := by continuity,
    map_zero_left' := by {refine (unique.forall_iff.2 _), unfold default, simpa only [path.source]},
    map_one_left' := by {refine (unique.forall_iff.2 _), unfold default, simpa only [path.target]},
    prop' := λ _ _ ⟨i,_⟩, i.elim0 }
end

/--
The first homotopy group at x is equivalent to the endomorphisms of x in the fundamental grupoid
-/
def pi1_equiv_fundamental_group : π 1 x ≃ path.homotopic.quotient x x :=
begin
  refine (quotient.congr _ _),
  exact {
    to_fun := λ p, path.mk ⟨λ t, p (λ _, t), by {continuity, exact p.1.2}⟩
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
      simp only [cube.head, path.coe_mk, pre_π.mk_apply, continuous_map.coe_mk], },
    right_inv := by { intro p, ext1,
      simp only [cube.head, pre_π.mk_apply, continuous_map.coe_mk, path.coe_mk], } },
  intros, split; rintros ⟨H⟩; constructor,
  exact {
    to_fun := λ tx, H (tx.fst, λ _, tx.snd),
    continuous_to_fun := by continuity,
    map_zero_left' := by simp only [continuous_map.coe_mk, pre_π.homotopy.at0, equiv.coe_fn_mk,
      eq_self_iff_true, forall_const],
    map_one_left' := by simp only [continuous_map.coe_mk, pre_π.homotopy.at1, equiv.coe_fn_mk,
      eq_self_iff_true, forall_const],
    prop' :=
    begin
      intros t y Hy, apply H.prop', use 0,
      cases Hy, rw Hy, left, refl,
      cases Hy, right, refl,
    end },
  exact {
    to_fun := λ tx, H (tx.fst, tx.snd.head),
    continuous_to_fun := by continuity,
    map_zero_left' := λ y, by {rw (cube.one_char y), simpa only [cube.head, continuous_map.coe_mk,
      continuous_map.homotopy_with.apply_zero, equiv.coe_fn_mk]},
    map_one_left' := λ y, by {rw (cube.one_char y),
      simpa only [continuous_map.homotopy_with.apply_one]},
    prop' :=
    begin
      rintros t y ⟨i,iH⟩,
      have hi : i = 0,
        { rcases i with ⟨⟨_,_⟩,iH'⟩,
          simp only [eq_iff_true_of_subsingleton],
          exfalso, revert iH', norm_num },
      simp only [cube.head, continuous_map.coe_mk],
      split,
      { convert (H.eq_fst _ _), exact y.one_char, rw ← hi, exact iH, },
      convert (H.eq_snd _ _), exact y.one_char, rw ← hi, exact iH,
    end  },
end
