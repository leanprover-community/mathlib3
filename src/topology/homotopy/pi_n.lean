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
that send the boundary to the base point x, up to homotopic equivalence.

We show that `π 0 x` is equivalent to the path-conected components, and
that `π 1 x` is equivalent to the fundamental grupoid at x

## definitions

* `pre_π n x` is the type of continous fuctions I^n->X that send the boundary to x
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
def cube (n:nat) := fin n -> I
notation `I^` := cube

namespace cube
  instance topology {n} : topological_space (I^n) :=
    Pi.topological_space

  @[continuity] lemma proj_continuous {n} (i:fin n) : continuous (λ(f:I^n), f i)
    := begin
      apply continuous_infi_dom,
      apply continuous_def.2,
      intros s H,
      convert ((@is_open_induced_iff' _ _ _ _ (λ (f : I^n), f i)).2 ⟨s,⟨H,by refl⟩⟩)
    end

  /--
  The points of the nth dimensional cube with a projection set to 0 or 1
  -/
  def boundary (n:nat) : set (I^n)
    := { y | ∃ i:fin n , y i = 0 ∨ y i = 1}

  instance unique_cube0 : unique (I^0)
    := { default := 0, uniq := by {intro a, ext1, exact x.elim0} }

  lemma one_indep (f:I^1) (i j:fin 1) : f i = f j
    := begin rcases i with ⟨⟨_,_⟩,_⟩; rcases j with ⟨⟨_,_⟩,_⟩,
      reflexivity,
      { exfalso, exact (nat.not_lt_zero _ (nat.le_of_succ_le_succ j_property)) },
      all_goals { exfalso, exact (nat.not_lt_zero _ (nat.le_of_succ_le_succ i_property)) },
    end
  lemma one_char (x:I^1) : x=λ _,x 0
    := begin ext1 i, rcases i with ⟨⟨_,_⟩,_⟩, reflexivity,
      exfalso, exact (nat.not_lt_zero _ (nat.le_of_succ_le_succ i_property))
    end

  /--
  The first projection of a non-zero dimensional cube
  -/
  @[simp] def head {n} : I^(n+1) -> I := λc,c 0

  /--
  The last `n` projection of an `n+1` dimensional cube
  -/
  @[simp] def tail {n} : I^(n+1) -> I^n := λc,fin.tail c
end cube

/--
The continous fuctions I^n->X that send the boundary to x
-/
structure pre_π (n : nat) (x : X) extends C(I^n,X) :=
  (boundary : ∀ y ∈ cube.boundary n, to_fun y = x )

namespace pre_π

  instance fun_like : fun_like (pre_π n x) (I^n) (λ _, X) :=
    { coe := λ f, f.1,
      coe_injective' := begin
        intros f g hfg, cases f, cases g,
        congr, ext1, exact congr_fun hfg _,
        end }

  @[ext] lemma ext (f g : pre_π n x) (H : ∀ y, f y = g y) : f = g :=
    fun_like.ext f g H

  @[simp] lemma mk_apply (f : C(I^n, X)) (H y) : (⟨f, H⟩ : pre_π n x)  y = f y :=
      rfl

  /--
  Homotopies are functions I×I^n → X
  -/
  def homotopy (f0 f1 : pre_π n x) :=
    continuous_map.homotopy_rel f0.to_continuous_map f1.to_continuous_map (cube.boundary n)
  infix `~`:50 := homotopy

  namespace homotopy
    section
    variables  {f g h : pre_π n x} (H : f~g)

    instance fun_like : fun_like (f ~ g) (I^(n+1)) (λ _, X) :=
      { coe := λ h c, h.1 (c 0, fin.tail c),
        coe_injective' := begin
          rintros h1 h2 hfg, cases h1, cases h2,
          congr, ext1 ⟨x,y⟩, simpa only [fin.tail_cons] using congr_fun hfg (fin.cons x y),
        end }

    @[continuity] lemma continuous : continuous H :=
      begin  refine H.continuous.comp _, continuity; apply continuous_apply  end

    @[simp] lemma coe_def  (y : I^(n+1))
      : H y = H.1 (y.head, y.tail) := rfl

    @[refl] lemma refl (f : pre_π n x) : f ~ f :=
      continuous_map.homotopy_rel.refl _ _

    @[symm] lemma symm : f ~ g -> g ~ f :=
      continuous_map.homotopy_rel.symm

    @[trans] lemma trans : f ~ g -> g ~ h -> f ~ h :=
      continuous_map.homotopy_rel.trans

    /--
    Eval an homotopy at an intermediate point, yielding a `pre_π`
    -/
    def eval (t:I) : pre_π n x :=
      { to_fun := H.to_homotopy.curry t,
        continuous_to_fun := by {continuity},
        boundary := λ y H, (begin
          simp, rw continuous_map.homotopy_rel.eq_fst,
          apply f.boundary, assumption, assumption,
        end), }

    @[simp] lemma eval0 : H.eval 0 = f :=
      begin ext, unfold eval,
        simp only [mk_apply, continuous_map.homotopy_with.apply_zero,
          continuous_map.coe_mk, continuous_map.homotopy.curry_apply,
          continuous_map.homotopy_with.coe_to_homotopy],
        reflexivity,
      end

    @[simp] lemma eval1 : H.eval 1 = g :=
      begin ext, unfold eval,
        simp only [mk_apply, continuous_map.coe_mk,
          continuous_map.homotopy_with.apply_one, continuous_map.homotopy.curry_apply,
          continuous_map.homotopy_with.coe_to_homotopy],
        reflexivity,
      end

    @[simp] lemma at0 (y : I^n) : H (fin.cons 0 y) = f y :=
      begin convert H.apply_zero y, simp end

    @[simp] lemma at1 (y : I^n) : H (fin.cons 1 y) = g y :=
      begin convert H.apply_one y, simp end

    @[simp] lemma comp0 : H ∘ fin.cons 0 = f :=
      funext (at0 H)

    @[simp] lemma comp1 : H ∘ fin.cons 1 = g :=
      funext (at1 H)

    end
  end homotopy

  /--
  Homotopic relation between `pre_π`s
  -/
  def homotopic (f0 f1 : pre_π n x) : Prop := nonempty (f0 ~ f1)
  namespace homotopic
    @[refl] lemma refl (f : pre_π n x) : homotopic f f :=
      ⟨homotopy.refl f⟩

    @[symm] lemma symm {f g : pre_π n x} (h : homotopic f g) : homotopic g f :=
      h.map homotopy.symm

    @[trans] lemma trans {f g h : pre_π n x} (h0 : homotopic f g) (h1 : homotopic g h)
      : homotopic f h :=
      h0.map2 homotopy.trans h1
    instance setoid (n : nat) (x : X) : setoid (pre_π n x) :=
      ⟨homotopic, ⟨homotopic.refl, λ _ _, homotopic.symm, λ _ _ _, homotopic.trans⟩⟩
  end homotopic

end pre_π

/--
The nth homotopy group at x defined as the quotient of base preserving functions up to homotopic
equivalence
-/
def π (n : nat) (x : X) := quotient (pre_π.homotopic.setoid n x)

variable (X)
/--
The quotient of X up to path components
-/
def path_components := quotient (⟨λ x y, x ∈ path_component y,
    ⟨mem_path_component_self, λ _ _, mem_path_component_of_mem, λ _ _ _, joined.mem_path_component⟩⟩
  : setoid X)
variable {X}

/--
The 0th homotopy "group" is equivalent to the path components of X
-/
def pi0_equiv_path_components : π 0 x ≃ path_components X :=
{ to_fun := begin
    refine quotient.map' (λf,f 0) _,
    rintros f g ⟨h⟩,       constructor, apply path.symm,
    exact ⟨⟨(λt,h (λ_,t)), by continuity⟩,
      by { have h0:h 0=f 0:=h.apply_zero 0,
          have c0:((λ_,0):I^(0+1))=(0:I^(0+1)):=by {ext, simp},
          simp [h0, c0], },
      by { have h1:h 1=g 0:=by convert h.apply_one 1,
          have c1:((λ_,1):I^(0+1))=(1:I^(0+1)):=by {ext, simp},
          simp [h1, c1], }⟩,
    end,
  inv_fun := begin
    refine quotient.map' (λy,⟨continuous_map.const _ y,(λ_ ⟨f0,_⟩,fin.elim0 f0)⟩) _,
    rintros y0 y1 ⟨p⟩, constructor, symmetry,
    exact ⟨⟨⟨(λ tx, p tx.1),by continuity⟩,by simp,by simp⟩, (λ_ _ ⟨f0,_⟩,fin.elim0 f0)⟩,
    end,
  left_inv := begin
    intro f, induction f using quotient.induction_on',
    simp only [quotient.map'_mk', quotient.eq', matrix.zero_empty],
    constructor, convert pre_π.homotopy.refl _, ext1,
    have Hy : y=matrix.vec_empty := subsingleton.elim _ _,
    simp [Hy],
    end,
  right_inv := begin
    intro p, induction p using quotient.induction_on',
    simp only [continuous_map.const_apply, quotient.map'_mk', pre_π.mk_apply],
    end }

/--
The fundamental grupoid "constructor",
-/
def fundamental_groupoid.mk : X -> fundamental_groupoid X := id

/--
The first homotopy group at x is equivalent to the endomorphisms of x in the fundamental grupoid
-/
def pi1_equiv_fundamental_group : π 1 x ≃ category_theory.End (fundamental_groupoid.mk x) :=
{ to_fun := begin
    refine quotient.map' (λ⟨⟨f,Hcont⟩,Hf⟩, path.mk ⟨λt,f (λ_,t), by continuity⟩
        (Hf (λ_,0) ⟨0,by {left, refl}⟩)
        (Hf (λ_,1) ⟨1,by {right, refl}⟩)) _,
    rintros ⟨⟨f,Hfc⟩,Hf⟩ ⟨⟨g,Hgc⟩,Hg⟩ ⟨⟨⟨h,Hhcont⟩,H0,H1⟩,Hh⟩,
    constructor,
    refine
    { to_fun := λx,h ⟨x.fst,λ_,x.snd⟩,
      continuous_to_fun := by continuity,
      map_zero_left' := λx,H0 (λ_,x),
      map_one_left' := λx,H1 (λ_,x),
      prop' := begin
        rintros t x' ⟨_,_⟩,
        { specialize (Hh t (λ_,0) ⟨0,by {left, refl}⟩),
          simp only [continuous_map.coe_mk] at Hh, simp [← Hh] },
        rcases H, specialize (Hh t (λ_,1) ⟨1,by {right, refl}⟩),
        simp only [continuous_map.coe_mk] at Hh, simp [← Hh]
        end },
    end,
  inv_fun := begin
    refine quotient.map' _ _,
    { rintros ⟨⟨f,Hcont⟩,H0,H1⟩,
      refine ⟨⟨(λh,f (h 0)), by continuity⟩, _⟩,
      rintros y ⟨i,H⟩,
      simp only [cube.one_indep y 0 i],
      rcases H,
      { simp only [H], exact H0, },
      simp only [H], exact H1 },
    rintros ⟨⟨f,Hfcont⟩,Hf0,Hf1⟩ ⟨⟨g,Hgcont⟩,Hg0,Hg1⟩ ⟨⟨⟨h,Hhcont⟩,Hh0,Hh1⟩,Hh⟩,
    constructor,
    refine ⟨⟨⟨λx,h ⟨x.fst,x.snd 0⟩,_⟩,(λx,Hh0 (x 0)),(λx,Hh1 (x 0))⟩,_⟩,
    { have h:(λ(x:↥I×I^1), x.snd 0)=(λ(x:I^1), x 0) ∘ prod.snd,
      { ext1, simp },
      continuity, rw h, apply continuous.comp, continuity },
    rintros t x ⟨i,H⟩,
    specialize (Hh t (x 0) (by simp [cube.one_indep x 0 i, H])),
    simp only [subtype.coe_eta] at Hh, exact Hh
    end,
  left_inv := begin
    intro p, induction p using quotient.induction_on',
    rcases p with ⟨⟨p,Hcont⟩,H⟩,
    simp only [quotient.map'_mk', quotient.eq'],
    constructor,
    refine ⟨⟨⟨(λx,p x.snd),by continuity⟩,_,by simp⟩,_⟩,
    { intro y, rw (cube.one_char y), simp },
    rintros t y ⟨i,H⟩,
    rw (cube.one_char y), simp,
    end,
  right_inv := begin
    intro p, induction p using quotient.induction_on',
    rcases p with ⟨⟨p,Hcont⟩,H0,H1⟩,
    constructor
    end }
