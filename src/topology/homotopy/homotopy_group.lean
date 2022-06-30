/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/

import algebraic_topology.fundamental_groupoid.fundamental_group
import group_theory.eckmann_hilton

/-!
# `n`th homotopy group

We define the `n`th homotopy group at `x`, `π_n x`, as the equivalence classes
of functions from the nth dimensional cube to the topological space `X`
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are generalized loops `gen_loop n x`, in particular
`gen_loop 1 x ≃ path x x`

We show that `π_0 x` is equivalent to the path-conected components, and
that `π_1 x` is equivalent to the fundamental group at `x`.
We give a group instance lifting the path concatenation structure.

## definitions

* `gen_loop n x` is the type of continous fuctions `I^n → X` that send the boundary to `x`
* `homotopy_group n x` denoted `π_ n x` is the quotient of `gen_loop n x` by homotopy relative
  to the boundary

TODO: show that `π_ n x` is a group when `n > 0` and abelian when `n > 1`. Show that
`pi1_equiv_fundamental_group` is an isomorphism of groups.

-/

open_locale unit_interval topological_space

noncomputable theory

universes u
variables {X : Type u} [topological_space X]
variables {n : ℕ} {x : X}

/-- The `n`-dimensional cube. -/
@[derive [has_zero, has_one, topological_space, metric_space]]
def cube (n : ℕ) : Type := fin n → I
notation `I^` := cube

namespace cube

instance compact_space : compact_space (I^n) :=
by {have H : compact_space I := by apply_instance, exact (@pi.compact_space _ _ _ (λ_,H))}

instance locally_compact_space : locally_compact_space (I^n) := locally_compact_of_proper

@[continuity] lemma proj_continuous (i : fin n) : continuous (λ f : I^n, f i) :=
continuous_apply i

/-- The `i`th projection as a continuous_map -/
def proj (i : fin n) : C(I^n,I) := ⟨λ t, t i, proj_continuous i⟩

/-- The points of the `n`-dimensional cube with at least one projection equal to 0 or 1. -/
def boundary (n : ℕ) : set (I^n) := {y | ∃ i, y i = 0 ∨ y i = 1}

/-- The first projection of a positive-dimensional cube. -/
@[simp] def head : I^(n+1) → I := λ c, c 0

@[continuity] lemma head.continuous : continuous (@head n) := proj_continuous 0

/-- The projection to the last `n` coordinates from an `n+1` dimensional cube. -/
@[simp] def tail : I^(n+1) → I^n := λ c, fin.tail c

@[continuity] lemma tail.continuous : continuous (@tail n) :=
(continuous_map.pi (λ i:fin n, ⟨λ f:I^(n+1), f i.succ, continuous_apply i.succ⟩)).2

@[simp] lemma cons_head_tail {t : I^(n+1)} : ((fin.cons t.head t.tail) : I^(n+1)) = t:=
begin
  ext1, revert x, refine (fin.cases (by {rw fin.cons_zero, refl}) _),
  intro, rw fin.cons_succ, refl,
end

instance unique_cube0 : unique (I^0) := pi.unique_of_is_empty _

lemma one_char (f : I^1) : f = λ _, f 0 := by convert eq_const_of_unique f

/-- Continuous cons map -/
def fold : C(I×I^n, I^(n+1)) :=
{ to_fun := λ t, fin.cons t.fst t.snd,
  continuous_to_fun :=
  begin
    refine (continuous_map.pi (λ i:fin (n+1), ⟨λ t:I×I^n, (fin.cons t.fst t.snd : I^(n+1)) i,_⟩)).2,
    revert i, refine (fin.cases _ _); simp only [fin.cons_zero, fin.cons_succ, auto_param_eq],
    exacts [continuous_fst, λ i, (continuous_map.comp (proj i) ⟨_,continuous_snd⟩).2],
  end }

@[simp] lemma fold_apply (x₀:I) (xn:I^n): fold ⟨x₀,xn⟩ = fin.cons x₀ xn := rfl

/-- Continuous `head`×`τail` map -/
def unfold : C(I^(n+1), I×I^n) :=
continuous_map.prod_mk ⟨head,head.continuous⟩ ⟨tail,tail.continuous⟩

@[simp] lemma unfold_apply (xn:I^(n+1)): unfold xn = ⟨xn.head,xn.tail⟩ := rfl

@[simp] lemma unfold_fold (t : I×I^n) : unfold (fold t) = t :=
by { rcases t with ⟨t,tn⟩, unfold fold, unfold unfold, simp only [head, tail, continuous_map.coe_mk,
  continuous_map.prod_eval, fin.cons_zero, fin.tail_cons]}

@[simp] lemma fold_unfold (t : I^(n+1)) : fold (unfold t) = t :=
by {unfold fold, unfold unfold, simp only [head, tail, continuous_map.prod_eval,
  continuous_map.coe_mk, fin.cons_self_tail]}

/-- Product with `I` homeomorphism -/
def fold.homeomorph : I×I^n ≃ₜ I^(n+1) :=
{ to_fun := fold,
  inv_fun := unfold,
  left_inv := unfold_fold,
  right_inv := fold_unfold,
  continuous_to_fun := fold.2,
  continuous_inv_fun := unfold.2 }

end cube

/-- Paths fixed at both ends -/
@[simp] def loop_space (X : Type*) [topological_space X] (x:X) := path x x
local notation `Ω` := loop_space

/-- The `n`-dimensional generalized loops; functions `I^n → X` fixed at the boundary. -/
def gen_loop (n : ℕ) (x : X) : set C(I^n, X) := { p | ∀ y ∈ cube.boundary n, p y = x}

namespace gen_loop

lemma boundary (f : gen_loop n x) : ∀ y ∈ cube.boundary n, f y = x := f.2

instance fun_like : fun_like (gen_loop n x) (I^n) (λ _, X) :=
{ coe := λ f, f.1,
  coe_injective' := λ ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ h, by { congr, exact h } }

@[ext] lemma ext (f g : gen_loop n x) (H : ∀ y, f y = g y) : f = g := fun_like.ext f g H

@[simp] lemma mk_apply (f : C(I^n, X)) (H y) : (⟨f, H⟩ : gen_loop n x) y = f y := rfl

/-- The constant `gen_loop` at `x`. -/
def const : gen_loop n x := ⟨continuous_map.const _ x, λ _ _, rfl⟩

@[simp] lemma const_eq {t} : (@const X _ n x) t = x := rfl

instance inhabited : inhabited (gen_loop n x) := { default := const }

/-- The "homotopy relative to boundary" relation between `gen_loop`s. -/
def homotopic (f g : gen_loop n x) : Prop := f.1.homotopic_rel g.1 (cube.boundary n)

namespace homotopic
section
variables {f g h : gen_loop n x}

@[refl] lemma refl (f : gen_loop n x) : homotopic f f := continuous_map.homotopic_rel.refl _

@[symm] lemma symm (H : homotopic f g) : homotopic g f := H.symm

@[trans] lemma trans (H0 : homotopic f g) (H1 : homotopic g h) : homotopic f h := H0.trans H1

lemma equiv : equivalence (@homotopic X _ n x) :=
⟨homotopic.refl, λ _ _, homotopic.symm, λ _ _ _, homotopic.trans⟩

instance setoid (n : ℕ) (x : X) : setoid (gen_loop n x) := ⟨homotopic, equiv⟩

end
end homotopic

/-- Path from a generalized loop by `unfold`-ing of `I^(n+1)` -/
def to_path : gen_loop (n+1) x → Ω (gen_loop n x) const :=
begin
  rintros ⟨g,gH⟩, refine path.mk ⟨_,_⟩ _ _,
  { intro t, refine ⟨(g.comp cube.fold).curry t,_⟩,
    rintros y ⟨i,iH⟩,
    simp only [continuous_map.curry_apply, continuous_map.comp_apply, cube.fold_apply],
    apply gH, use i.succ, simpa},
  { simp only [auto_param_eq], continuity },
  all_goals {simp only, ext,
    simp only [continuous_map.curry_apply, continuous_map.comp_apply, cube.fold_apply, mk_apply,
      const_eq],
    apply gH, use 0 },
  left, refl,
  right, refl
end

/-- Generalized loop from a path by `fold`-ing of `I×I^n` -/
def from_path : Ω (gen_loop n x) const → gen_loop (n+1) x :=
begin
  rintros ⟨p,H₀,H₁⟩, refine ⟨_,_⟩,
  refine continuous_map.comp _ cube.unfold,
  refine continuous_map.uncurry ⟨λ t, (p t).1, by continuity⟩,
  rintros y ⟨i,iH⟩, unfold cube.unfold, unfold continuous_map.uncurry,
  simp only [cube.head, cube.tail, continuous_map.coe_mk, continuous_map.to_fun_eq_coe,
    continuous_map.comp_apply, continuous_map.prod_eval, function.uncurry_apply_pair],
  revert i iH, refine (fin.cases _ _); intros,
  { simp only [continuous_map.to_fun_eq_coe] at H₀ H₁,
    cases iH; rw iH, rw H₀, exact (@const_eq _ _ n x y.tail),
    rw H₁, exact (@const_eq _ _ n x y.tail) },
  apply gen_loop.boundary, exact ⟨i,iH⟩
end

lemma from_to (p : gen_loop (n+1) x) : from_path (to_path p) = p :=
begin
  rcases p with ⟨⟨p,Hc⟩,Hb⟩,
  ext,
  unfold to_path, unfold from_path, unfold continuous_map.comp, unfold function.comp,
  unfold continuous_map.curry, unfold continuous_map.uncurry, unfold function.uncurry,
  simp only [continuous_map.coe_mk, mk_apply],
  unfold continuous_map.curry', unfold function.curry,
  simp only [continuous_map.coe_mk, prod.mk.eta, cube.fold_unfold],
end

lemma to_from (p : Ω (gen_loop n x) const) : to_path (from_path p) = p :=
begin
  rcases p with ⟨⟨p,Hc⟩,Hs,Ht⟩,
  ext,
  unfold from_path, unfold to_path, unfold continuous_map.comp, unfold function.comp,
  unfold continuous_map.curry, unfold continuous_map.uncurry, unfold function.uncurry,
  simp only [continuous_map.coe_mk, cube.unfold_fold, path.coe_mk, mk_apply],
  unfold continuous_map.curry', unfold function.curry,
  simpa only [continuous_map.coe_mk]
end

/-- Loop space equivalence -/
def path_equiv : gen_loop (n+1) x ≃ Ω (gen_loop n x) const  :=
{ to_fun := to_path,
  inv_fun := from_path,
  left_inv := from_to,
  right_inv := to_from }

lemma curry_to_path {p : gen_loop (n+1) x} {t:I} {tn:I^n} :
  p (fin.cons t tn) = (to_path p).to_fun t tn :=
by {rcases p with ⟨p,pH⟩, unfold to_path, simp}

@[simp] lemma uncurry_helper (f : C(I, C(I, C(I^n, X)))) (t : I×I) (y : I^n) :
  f.uncurry t y = f t.fst t.snd y :=
by {unfold continuous_map.uncurry, unfold function.uncurry, simp only [continuous_map.coe_mk]}

@[simp] lemma uncurry_helper' (f : C(I, C(I×I^n, X))) (t : I) (y : I×I^n) :
  f.uncurry ⟨t, y⟩ = f t y :=
by {unfold continuous_map.uncurry, unfold function.uncurry, simp only [continuous_map.coe_mk]}

@[simp] lemma uncurry_helper'' (f : C(I,C(I^n, X))) (t : I) (y : I^n) : f.uncurry (t, y) = f t y :=
by {unfold continuous_map.uncurry, unfold function.uncurry, simp only [continuous_map.coe_mk]}

abbreviation continuous_currying : C(C(I × I^n, X),C(I, C(I^n, X))) :=
⟨continuous_map.curry,continuous_map.continuous_curry⟩

abbreviation continuous_uncurrying : C(C(I, C(I^n, X)),C(I × I^n, X)) :=
⟨continuous_map.uncurry,continuous_map.continuous_uncurry⟩

abbreviation continuous_to_cont : C(gen_loop n x, C(I^n,X)) :=
⟨λ p, p.val, by continuity⟩

lemma homotopic_to {p q : gen_loop (n+1) x} : homotopic p q → (to_path p).homotopic (to_path q) :=
begin
  let cf:C(C(I^(n+1), X), C(I×I^n, X)) := ⟨λ f, f.comp cube.fold, by sorry⟩,
  apply nonempty.map, rintros H,
  refine ⟨⟨_,_,_⟩,_⟩,
  { refine ⟨λ t, ⟨(continuous_currying.comp (cf.comp H.to_continuous_map.curry)).uncurry t,_⟩,_⟩,
    { rintros y ⟨i,iH⟩,
      simp only [uncurry_helper, continuous_map.comp_apply, continuous_map.coe_mk,
        continuous_map.curry_apply, cube.fold_apply,
        continuous_map.homotopy_with.coe_to_continuous_map],
      rw H.eq_fst, rw p.property, all_goals {use i.succ, rwa fin.cons_succ} },
    simp only [auto_param_eq], continuity },
  show ∀ _ _ _, _,
  { intros t y yH,
    split; ext1; simp only [uncurry_helper, continuous_map.comp_apply, continuous_map.coe_mk,
      continuous_map.curry_apply, cube.fold_apply,
      continuous_map.homotopy_with.coe_to_continuous_map, mk_apply, path.coe_to_continuous_map],
    rw H.eq_fst, exact curry_to_path, use 0, rwa fin.cons_zero,
    rw H.eq_snd, exact curry_to_path, use 0, rwa fin.cons_zero, },
  all_goals {intro t, ext1,
    simp only [uncurry_helper, continuous_map.comp_apply, continuous_map.coe_mk,
      continuous_map.curry_apply, cube.fold_apply,
      continuous_map.homotopy_with.coe_to_continuous_map, mk_apply,
      continuous_map.homotopy_with.apply_zero, continuous_map.homotopy_with.apply_one,
      subtype.val_eq_coe, path.coe_to_continuous_map],
    exact curry_to_path}
end

@[simp] lemma prod_map_eval {α₁ α₂ β₁ β₂ : Type*} [topological_space α₁] [topological_space β₁]
[topological_space α₂] [topological_space β₂] (f : C(α₁, α₂)) (g : C(β₁, β₂)) (x:α₁) (y:β₁) :
f.prod_map g ⟨x,y⟩ = ⟨f x, g y⟩ := rfl

lemma homotopic_from {p q : gen_loop (n+1) x} : (to_path p).homotopic (to_path q) → homotopic p q :=
begin
  apply nonempty.map, rintros H,
  refine ⟨⟨_,_,_⟩,_⟩,
  { refine (continuous_map.comp _ ((continuous_map.id I).prod_map cube.unfold)),
    refine continuous_map.uncurry _,
    refine continuous_map.comp continuous_uncurrying _,
    exact (continuous_to_cont.comp H.to_continuous_map).curry},
  show ∀ _ _ _, _,
  { rintros t y ⟨i,iH⟩,
    simp only [continuous_map.to_fun_eq_coe, continuous_map.comp_apply, prod_map_eval,
      continuous_map.id_apply, cube.head, cube.tail,
      cube.unfold_apply, uncurry_helper', continuous_map.coe_mk, uncurry_helper'',
      continuous_map.curry_apply, continuous_map.homotopy_with.coe_to_continuous_map,
      subtype.val_eq_coe],
    -- rw boundary (H (t, y 0)),
    revert i iH, refine fin.cases _ _; intros,
    { cases iH; rw iH; simp only [path.homotopy.source, path.homotopy.target]; unfold const;
      simp only [subtype.coe_mk, continuous_map.const_apply]; split; symmetry,
      exacts [boundary _ _ ⟨0,or.inl iH⟩,boundary _ _ ⟨0,or.inl iH⟩,
        boundary _ _ ⟨0,or.inr iH⟩,boundary _ _ ⟨0,or.inr iH⟩] },
    rcases (H (t, y 0)), simp only [subtype.coe_mk],
    rw property,
    split; symmetry; convert boundary _ _ _; exact ⟨i.succ,iH⟩,
    exact ⟨i,iH⟩ },
  all_goals
  { intros y,
    simp only [continuous_map.to_fun_eq_coe, continuous_map.comp_apply, prod_map_eval,
      continuous_map.id_apply, cube.head, cube.tail, cube.unfold_apply, uncurry_helper',
      continuous_map.coe_mk, uncurry_helper'', continuous_map.curry_apply,
      continuous_map.homotopy_with.coe_to_continuous_map, continuous_map.homotopy_with.apply_zero,
      continuous_map.homotopy_with.apply_one, path.coe_to_continuous_map, subtype.val_eq_coe],
    symmetry, convert curry_to_path, symmetry, exact cube.cons_head_tail },
end

/-- Concatenation of `gen_loop`s by transitivity as paths -/
def concat : gen_loop (n+1) x → gen_loop (n+1) x → gen_loop (n+1) x :=
λ p q, from_path ((to_path p).trans (to_path q))

lemma concat2trans (p q : gen_loop (n+1) x) : to_path (concat p q) = (to_path p).trans (to_path q):=
by { unfold concat, rw to_from}

lemma const_to_refl : to_path (@const _ _ (n+1) x) = path.refl (@const _ _ n x) :=
begin
  ext, unfold const, unfold to_path,
  simp only [continuous_map.const_comp, path.coe_mk, mk_apply, continuous_map.curry_apply,
    continuous_map.const_apply, path.refl_apply, const_eq],
end
end gen_loop

/-- The `n`th homotopy group at `x` defined as the quotient of `gen_loop n x` by the
  `homotopic` relation. -/
@[derive inhabited]
def homotopy_group (n : ℕ) (X : Type*) [topological_space X] (x : X) : Type _ :=
quotient (gen_loop.homotopic.setoid n x)
local notation `π_` := homotopy_group

namespace homotopy_group

/-- The 0-dimensional generalized loops based at `x` are in 1-1 correspondence with `X`. -/
def gen_loop_zero_equiv : gen_loop 0 x ≃ X :=
{ to_fun := λ f, f 0,
  inv_fun := λ x, ⟨continuous_map.const _ x, λ _ ⟨f0,_⟩, f0.elim0⟩,
  left_inv := λ f, by { ext1, exact congr_arg f (subsingleton.elim _ _) },
  right_inv := λ _, rfl }

/-- The 0th homotopy "group" is equivalent to the path components of `X`, aka the `zeroth_homotopy`.
  -/
def pi0_equiv_path_components : π_ 0 X x ≃ zeroth_homotopy X :=
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

/-- The 1-dimensional generalized loops based at `x` are in 1-1 correspondence with paths from `x`
  to itself. -/
@[simps] def gen_loop_one_equiv_path_self : gen_loop 1 x ≃ path x x :=
{ to_fun := λ p, path.mk ⟨λ t, p (λ _, t), by continuity⟩
    (gen_loop.boundary p (λ _, 0) ⟨0, or.inl rfl⟩)
    (gen_loop.boundary p (λ _, 1) ⟨1, or.inr rfl⟩),
  inv_fun := λ p,
  begin
    refine ⟨⟨λ (c : I^1), p c.head,by continuity⟩,_⟩,
    rintro y ⟨i, iH|iH⟩; cases unique.eq_default i;
    apply (congr_arg p iH).trans, exacts [p.source, p.target],
  end,
  left_inv := λ p, by { ext1, exact congr_arg p y.one_char.symm },
  right_inv := λ p, by { ext, refl } }

/-- The first homotopy group at `x` is equivalent to the fundamental group, i.e. the loops based at
  `x` up to homotopy. -/
def pi1_equiv_fundamental_group : π_ 1 X x ≃ fundamental_group X x :=
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

def concat : π_(n+1) X x → π_(n+1) X x → π_(n+1) X x :=
begin
  refine (quotient.map₂' gen_loop.concat _),
  rintros p₀ p₁ Hp q₀ q₁ Hq,
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.concat2trans},
  apply path.homotopic.hcomp; apply gen_loop.homotopic_to,
  exacts [Hp, Hq],
end
instance has_mul : has_mul (π_(n+1) X x) := ⟨concat⟩
local infix `⋆`:60 := concat

def concat_assoc (p q r : π_(n+1) X x) : ((p ⋆ q) ⋆ r) = (p ⋆ (q ⋆ r)) :=
begin
  refine (quotient.induction_on₃ p q r _),
  intros a b c, refine (quotient.sound _),
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.concat2trans},
  constructor,
  apply path.homotopy.trans_assoc
end

def const : π_ n X x := quotient.mk' gen_loop.const

instance has_one : has_one (π_ n X x) := ⟨const⟩

local notation `𝟙` := const

lemma concat_const (p: π_(n+1) X x) : p ⋆ 𝟙 = p :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.concat2trans},
  rw gen_loop.const_to_refl,
  constructor,
  apply path.homotopy.trans_refl,
end

lemma const_concat (p: π_(n+1) X x) : 𝟙 ⋆ p = p :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.concat2trans},
  rw gen_loop.const_to_refl,
  constructor,
  apply path.homotopy.refl_trans,
end

def reverse {n':nat} : π_(n'+1) X x → π_(n'+1) X x :=
begin
  refine (quotient.map' (λ p, gen_loop.from_path ((gen_loop.to_path p).symm)) _),
  intros p q H,
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.to_from},
  apply nonempty.map path.homotopy.symm₂,
  exact gen_loop.homotopic_to H
end
instance has_inv : has_inv (π_(n+1) X x) := ⟨reverse⟩
local postfix `⁻¹`:65 := has_inv.inv

lemma reverse_concat (p: π_(n+1) X x) : p⁻¹ ⋆ p = 𝟙 :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.concat2trans},
  rw gen_loop.const_to_refl,
  repeat {rw gen_loop.to_from},
  symmetry, constructor,
  apply  path.homotopy.refl_symm_trans
end
lemma concat_reverse (p: π_(n+1) X x) : p ⋆ p⁻¹  = 𝟙 :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.concat2trans},
  rw gen_loop.const_to_refl,
  repeat {rw gen_loop.to_from},
  symmetry, constructor,
  apply  path.homotopy.refl_trans_symm
end

def is_group : group (π_(n+1) X x) :=
{ mul := concat,
  mul_assoc := concat_assoc,
  one := const,
  one_mul := const_concat,
  mul_one := concat_const,
  npow := npow_rec,
  npow_zero' := λ _, rfl,
  npow_succ' := λ _ _, rfl,
  inv := reverse,
  div := λ a b, a⋆(b⁻¹),
  div_eq_mul_inv := λ _ _, rfl,
  zpow := zpow_rec,
  zpow_zero' := λ _, rfl,
  zpow_succ' := λ _ _, rfl,
  zpow_neg' := λ _ _, rfl,
  mul_left_inv := reverse_concat }

-- def m₂ : π_(n+2) X x → π_(n+2) X x → π_(n+2) X x :=
-- begin
--   refine (quotient.map₂' _ _),
--   {rintros H0 H1, refine ⟨_,_⟩; sorry},
--   rintros p₀ p₁ Hp q₀ q₁ Hq,
--   sorry
-- end

-- def unital : @eckmann_hilton.is_unital (π_(n+2) X x) m₂ const :=
-- sorry

-- instance comm_group : comm_group (π_(n+2) X x) :=
-- begin
--   apply @eckmann_hilton.comm_group _ _ _ unital is_group,
--   intros a b c d,
--   sorry
-- end

end homotopy_group
#lint
