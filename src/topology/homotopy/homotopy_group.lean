/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/

import algebraic_topology.fundamental_groupoid.fundamental_group
import group_theory.eckmann_hilton

/-!
# `n`th homotopy group

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

open_locale unit_interval topological_space

noncomputable theory

universes u
variables {X : Type u} [topological_space X]
variables {n : ℕ} {x : X}

/--
The `n`-dimensional cube.
-/
@[derive [has_zero, has_one, topological_space]]
def cube (n : ℕ) : Type := fin n → I
notation `I^` := cube

namespace cube

instance locally_compact_space : locally_compact_space (I^ n) := sorry

@[continuity] lemma proj_continuous (i : fin n) : continuous (λ f : I^n, f i) :=
continuous_apply i

/--
The points of the `n`-dimensional cube with at least one projection equal to 0 or 1.
-/
def boundary (n : ℕ) : set (I^n) := {y | ∃ i, y i = 0 ∨ y i = 1}

/--
The first projection of a positive-dimensional cube.
-/
@[simp] def head : I^(n+1) → I := λ c, c 0

@[continuity] lemma head.continuous : continuous (@head n) := proj_continuous 0

/--
The projection to the last `n` coordinates from an `n+1` dimensional cube.
-/
@[simp] def tail : I^(n+1) → I^n := λ c, fin.tail c

@[continuity] lemma tail.continuous : continuous (@tail n) := sorry
-- begin continuity, end

instance unique_cube0 : unique (I^0) := pi.unique_of_is_empty _

lemma one_char (f : I^1) : f = λ _, f 0 := by convert eq_const_of_unique f

def fold : I×I^n ≃ₜ I^(n+1) :=
begin
  refine
  { to_fun := λ t, fin.cons t.fst t.snd,
    inv_fun := λ tn, ⟨tn.head, tn.tail⟩,
    left_inv := by {rintros ⟨t,tn⟩, simp only [head, tail, fin.cons_zero, fin.tail_cons]},
    right_inv := by {rintros t, simp only [head, tail, fin.cons_self_tail]},
    continuous_to_fun := _,
    continuous_inv_fun := _ },
  all_goals {sorry}
end

end cube

def loop_space (X) [topological_space X] (x:X) := path x x
local notation `Ω` := loop_space

/--
The `n`-dimensional generalized loops; functions `I^n → X` that send the boundary to the base point.
-/
structure gen_loop (n : ℕ) (x : X) extends C(I^n, X) :=
(boundary : ∀ y ∈ cube.boundary n, to_fun y = x)

namespace gen_loop

instance topological_space : topological_space (gen_loop n x) :=
by exact topological_space.induced (gen_loop.to_continuous_map) (by apply_instance)

instance fun_like : fun_like (gen_loop n x) (I^n) (λ _, X) :=
{ coe := λ f, f.1,
  coe_injective' := λ ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ h, by { congr, exact h } }

@[continuity] lemma fun_like_cont (f : gen_loop n x): continuous (f.to_fun) := f.1.2

@[ext] lemma ext (f g : gen_loop n x) (H : ∀ y, f y = g y) : f = g := fun_like.ext f g H

@[simp] lemma mk_apply (f : C(I^n, X)) (H y) : (⟨f, H⟩ : gen_loop n x) y = f y := rfl

/--
The constant `gen_loop` at `x`.
-/
def const : gen_loop n x := ⟨continuous_map.const _ x, λ _ _, rfl⟩

@[simp] lemma const_eq {t} : (@const X _ n x) t = x := rfl

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

def to_path : gen_loop (n+1) x → Ω (gen_loop n x) const :=
begin
  rintros ⟨g,gH⟩, refine path.mk ⟨_,_⟩ _ _,
  intro t, refine
  ⟨continuous_map.curry (continuous_map.comp g ⟨cube.fold.to_fun,cube.fold.continuous_to_fun⟩) t,_⟩,
  rintros y ⟨i,iH⟩, simp, apply gH, use i.succ, unfold cube.fold, simpa,
  simp, --rw continuous_def, intros s sH, unfold is_open, unfold set.preimage, simp,
  sorry,
  simp, ext, simp, apply gH, use 0, left, refl,
  simp, ext, simp, apply gH, use 0, right, refl,
end

def from_path : Ω (gen_loop n x) const → gen_loop (n+1) x := --sorry
begin
  rintros ⟨p,H₀,H₁⟩, refine ⟨_,_⟩,
  refine continuous_map.comp _ ⟨cube.fold.inv_fun,cube.fold.continuous_inv_fun⟩,
  refine continuous_map.uncurry ⟨λ t, (p t).to_continuous_map, by continuity⟩,
  rintros y ⟨i,iH⟩, simp, sorry
end

lemma to_from (p : gen_loop (n+1) x) : from_path (to_path p) = p := sorry
lemma from_to (p : Ω (gen_loop n x) const) : to_path (from_path p) = p := sorry

def path_equiv : gen_loop (n+1) x ≃ Ω (gen_loop n x) const  :=
{ to_fun := to_path,
  inv_fun := from_path,
  left_inv := to_from, --λ _, by { ext, unfold to_path, unfold from_path,
    -- simp only [mk_apply, continuous_map.coe_mk,
    -- cube.head, cube.tail, path.coe_mk, fin.cons_self_tail]} ,
  right_inv := from_to --λ _, by { ext, unfold to_path, unfold from_path,
    -- simp only [cube.head, cube.tail, mk_apply, continuous_map.coe_mk,
    -- fin.cons_zero, fin.tail_cons, path.coe_mk] }
    }

lemma homotopic_iff {p q : gen_loop (n+1) x} : p.homotopic q ↔ p.to_path.homotopic q.to_path :=
begin
  split,
  { rintros Hpq, cases Hpq, constructor,
    exact
    { to_fun := λ t,
      { to_fun := λ tn, Hpq ⟨t.fst,fin.cons t.snd tn⟩,
        continuous_to_fun := sorry,
        boundary :=
        begin
          rintros tn ⟨i,iH⟩, simp only,
          rw Hpq.eq_fst,
          apply p.boundary,
          all_goals {use i.succ, rwa fin.cons_succ}
        end },
      continuous_to_fun := sorry,
      map_zero_left' := by {intro, ext, unfold to_path, simp, sorry},
      map_one_left' := by {intro, ext, unfold to_path, simp, sorry},
      prop' :=
      begin
        rintros t₀ t₁ ⟨H|H⟩,
        { simp, ext, simp, rw Hpq.eq_fst,
          apply p.boundary, all_goals {use 0, rw fin.cons_zero, left, refl}},
        cases H, simp, ext, simp, rw Hpq.eq_fst,
        apply p.boundary, all_goals {use 0, rw fin.cons_zero, right, refl}
      end },
  },
  { rintros Hpq, cases Hpq, constructor, refine
    { to_fun := _,
      continuous_to_fun := _,
      map_zero_left' := _,
      map_one_left' := _,
      prop' := _ },
      rintros ⟨t,tn⟩, refine Hpq ⟨t,tn.head⟩ tn.tail,
      all_goals {sorry}}
end

def concat : gen_loop (n+1) x → gen_loop (n+1) x → gen_loop (n+1) x :=
λ p q, from_path (p.to_path.trans q.to_path)

lemma concat2trans (p q : gen_loop (n+1) x) : (p.concat q).to_path = p.to_path.trans q.to_path :=
by { unfold concat, rw from_to}

lemma const_to_refl : (@const _ _ (n+1) x).to_path = path.refl (@const _ _ n x) :=
begin
  ext, unfold const, unfold to_path,
  simp only [continuous_map.const_comp, path.coe_mk, mk_apply, continuous_map.curry_apply,
    continuous_map.const_apply, path.refl_apply, const_eq],
end
end gen_loop

/--
The `n`th homotopy group at `x` defined as the quotient of `gen_loop n x` by the
`homotopic` relation.
-/
@[derive inhabited]
def homotopy_group (n : ℕ) (x : X) : Type _ := quotient (gen_loop.homotopic.setoid n x)
local notation `π` := homotopy_group

namespace homotopy_group
def concat : π (n+1) x → π (n+1) x → π (n+1) x :=
begin
  refine (quotient.map₂' gen_loop.concat _),
  rintros p₀ p₁ Hp q₀ q₁ Hq,
  apply gen_loop.homotopic_iff.2,
  repeat {rw gen_loop.concat2trans},
  apply path.homotopic.hcomp; apply gen_loop.homotopic_iff.1,
  exacts [Hp, Hq],
end
instance has_mul : has_mul (π (n+1) x) := ⟨concat⟩
local infix `⋆`:60 := concat

def concat_assoc (p q r : π (n+1) x) : ((p ⋆ q) ⋆ r) = (p ⋆ (q ⋆ r)) :=
begin
  refine (quotient.induction_on₃ p q r _),
  intros a b c, refine (quotient.sound _),
  apply gen_loop.homotopic_iff.2,
  repeat {rw gen_loop.concat2trans},
  constructor,
  apply path.homotopy.trans_assoc
end

def const : π n x := quotient.mk' gen_loop.const

instance has_one : has_one (π n x) := ⟨const⟩

local notation `𝟙` := const

lemma concat_const (p: π (n+1) x) : p ⋆ 𝟙 = p :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_iff.2,
  repeat {rw gen_loop.concat2trans},
  rw gen_loop.const_to_refl,
  constructor,
  apply path.homotopy.trans_refl,
end

lemma const_concat (p: π (n+1) x) : 𝟙 ⋆ p = p :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_iff.2,
  repeat {rw gen_loop.concat2trans},
  rw gen_loop.const_to_refl,
  constructor,
  apply path.homotopy.refl_trans,
end

def reverse {n':nat} : π (n'+1) x → π (n'+1) x :=
begin
  refine (quotient.map' (λ p, gen_loop.from_path (p.to_path.symm)) _),
  intros p q H,
  apply gen_loop.homotopic_iff.2,
  repeat {rw gen_loop.from_to},
  apply nonempty.map path.homotopy.symm₂,
  exact gen_loop.homotopic_iff.1 H
end
instance has_inv : has_inv (π (n+1) x) := ⟨reverse⟩
local postfix `⁻¹`:65 := has_inv.inv

lemma reverse_concat (p: π (n+1) x) : (p⁻¹) ⋆ p = 𝟙 :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_iff.2,
  repeat {rw gen_loop.concat2trans},
  rw gen_loop.const_to_refl,
  repeat {rw gen_loop.from_to},
  symmetry, constructor,
  apply  path.homotopy.refl_symm_trans
end
lemma concat_reverse (p: π (n+1) x) : p ⋆ (p⁻¹)  = 𝟙 :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_iff.2,
  repeat {rw gen_loop.concat2trans},
  rw gen_loop.const_to_refl,
  repeat {rw gen_loop.from_to},
  symmetry, constructor,
  apply  path.homotopy.refl_trans_symm
end

def is_group : group (π (n+1) x) := {
  mul := concat,
  mul_assoc := concat_assoc,
  one := const,
  one_mul := const_concat,
  mul_one := concat_const,
  npow := npow_rec,
  npow_zero' := λ _, rfl,
  npow_succ' := λ _ _, rfl,
  inv := reverse,
  div := λ a b, a⋆(b⁻¹),
  div_eq_mul_inv := by {intros, refl},
  zpow := zpow_rec,
  zpow_zero' := λ _, rfl,
  zpow_succ' := λ _ _, rfl,
  zpow_neg' := λ _ _, rfl,
  mul_left_inv := reverse_concat
}

def m₂ : π (n+2) x → π (n+2) x → π (n+2) x :=
begin
  refine (quotient.map₂' _ _),
  {rintros H0 H1, refine ⟨_,_⟩; sorry},
  rintros p₀ p₁ Hp q₀ q₁ Hq,
  sorry
end

def unital : @eckmann_hilton.is_unital (π (n+2) x) m₂ const :=
sorry

instance comm_group : comm_group (π (n+2) x) :=
begin
  apply @ eckmann_hilton.comm_group _ _ _ unital is_group,
  intros a b c d,
  sorry
end

end homotopy_group

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
