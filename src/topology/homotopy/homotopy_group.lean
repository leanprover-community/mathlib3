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

TODO: show that `π_ n x` is abelian when `n > 1`. Path-induced homomorphisms. Show that
`pi1_equiv_fundamental_group` is an isomorphism of groups. Examples with 𝕊^n

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

@[continuity] lemma proj_continuous (i : fin n) : continuous (λ f : I^n, f i) := continuous_apply i

/-- The `i`th projection as a continuous_map -/
@[simps] def proj (i : fin n) : C(I^n,I) := ⟨λ t, t i, proj_continuous i⟩

/-- The points of the `n`-dimensional cube with at least one projection equal to 0 or 1. -/
def boundary (n : ℕ) : set (I^n) := {y | ∃ i, y i = 0 ∨ y i = 1}

/-- The first projection of a positive-dimensional cube. -/
@[simps] def head : C(I^(n+1), I) := proj 0

/-- The projection to the last `n` coordinates from an `n+1` dimensional cube. -/
@[simps] def tail : C(I^(n+1), I^n) := ⟨λ c, fin.tail c,
  (continuous_map.pi (λ i:fin n, ⟨λ f:I^(n+1), f i.succ, continuous_apply i.succ⟩)).2⟩

-- @[simp] lemma tail.coe_to_fun : (tail : I^(n+1) → I^n) = fin.tail :=
--   by {ext, simp only [tail_apply]}

instance unique_cube0 : unique (I^0) := pi.unique_of_is_empty _

lemma one_char (f : I^1) : f = λ _, f 0 := by convert eq_const_of_unique f

/-- Continuous cons map -/
@[simps] def cons : C(I×I^n, I^(n+1)) :=
{ to_fun := λ t, fin.cons t.fst t.snd,
  continuous_to_fun :=
  begin
    refine (continuous_map.pi (λ i:fin (n+1), ⟨λ t:I×I^n, (fin.cons t.fst t.snd : I^(n+1)) i,_⟩)).2,
    revert i, refine (fin.cases _ _); simp only [fin.cons_zero, fin.cons_succ, auto_param_eq],
    exacts [continuous_fst, λ i, (continuous_map.comp (proj i) ⟨_,continuous_snd⟩).2],
  end }

-- @[simp] lemma cons_apply (x₀:I) (xn:I^n): cons ⟨x₀,xn⟩ = fin.cons x₀ xn := rfl

/-- Continuous `head`×`tail` map -/
def uncons : C(I^(n+1), I×I^n) :=
continuous_map.prod_mk ⟨head,head.continuous⟩ ⟨tail,tail.continuous⟩

@[simp] lemma uncons_apply (xn:I^(n+1)): uncons xn = ⟨xn.head,xn.tail⟩ := rfl

section
variable (i : fin (n+1))

/-- Continuos "insert" map, in particular `insert 0 = cons`. -/
def insert (i : fin (n+1)) : C(I×I^n, I^(n+1)):=
begin
  refine ⟨λ t j, _, _⟩,
  { by_cases Hlt : j<i, exact t.snd ⟨j, nat.lt_of_lt_of_le Hlt (nat.lt_succ_iff.mp i.2)⟩,
    by_cases Heq : j=i, exact t.fst,
    refine t.snd (fin.pred j _),
    intro Hj, subst Hj, apply Heq, symmetry,
    exact fin.eq_of_veq (le_zero_iff.mp (fin.coe_fin_le.mpr (not_lt.mp Hlt))) },
  refine (continuous_map.pi (λ j:fin (n+1), ⟨λ t:I×I^n,_,_⟩)).2,
  cases (subtype.decidable_lt j i); simp only [auto_param_eq, dite];
  cases (subtype.decidable_eq j i); try {simp only},
  show continuous prod.fst, exact continuous_fst,
  all_goals {exact (proj_continuous _).comp continuous_snd}
end

@[simp] lemma insert_at_eq (t₀:I) (t) : insert i ⟨t₀, t⟩ i = t₀ :=
by simp only [insert, lt_self_iff_false,not_false_iff,id.def,continuous_map.coe_mk,dif_pos,dif_neg]

lemma insert_at_lt (j : fin n) {t₀ t} : ↑j < i → insert i ⟨t₀, t⟩ ↑j = t j :=
begin
  intro H,
  simp only [insert, not_lt,id.def, fin.coe_eq_cast_succ, continuous_map.coe_mk, fin.coe_cast_succ,
    fin.eta, dite_eq_right_iff, dite],
  cases ((subtype.decidable_lt (fin.cast_succ j) i)); simp only,
  exfalso, apply h, convert H, norm_cast
end

lemma insert_at_lt' (j: fin (n+1)) {t₀ t} (H: ↑j<n) : j<i → insert i ⟨t₀, t⟩ j = t ⟨j,H⟩ :=
begin
  intro H,
  simp only [insert, not_lt,id.def, fin.coe_eq_cast_succ, continuous_map.coe_mk, fin.coe_cast_succ,
    fin.eta, dite_eq_right_iff, dite],
  cases ((subtype.decidable_lt j i)); simp only,
  exfalso, apply h, exact H
end

lemma insert_at_gt (j : fin n) {t₀ t} : i < j.succ → insert i ⟨t₀, t⟩ j.succ = t j :=
begin
  intro H,
  simp only [insert, fin.coe_succ,id.def,continuous_map.coe_mk, fin.cases_succ, dite_eq_ite, dite],
  cases subtype.decidable_lt j.succ i; simp only,
  cases subtype.decidable_eq j.succ i; simp only,
  { simp only [fin.pred_succ] },
  { exfalso, rw h_1 at H, revert H, exact has_lt.lt.false },
  exfalso, exact not_le_of_lt H (le_of_lt h)
end

lemma insert_boundary {t₀:I} {t} : (t₀=0 ∨ t₀=1) ∨ t∈boundary n → insert i ⟨t₀,t⟩ ∈boundary (n+1) :=
begin
  intros H, cases H,
  use i, rwa insert_at_eq,
  rcases H with ⟨j,H⟩,
  by_cases Hlt : ↑j < i, { use j, rwa insert_at_lt, exact Hlt },
  use j.succ, rwa insert_at_gt, simp at Hlt, apply nat.lt_of_le_of_lt Hlt,
  simp only [fin.val_eq_coe, fin.coe_cast_succ, fin.coe_succ, lt_add_iff_pos_right, nat.lt_one_iff]
end

/-- Continuos "extract" map, in particular `extract 0 t = (t.head, t.tail)`. -/
@[simps] def extract (i : fin (n+1)) : C(I^(n+1), I×I^n) :=
begin
  refine ⟨λ t, ⟨t i, λ j, if ↑j<i then t ↑j else t j.succ⟩,_⟩,
  simp only [fin.coe_eq_cast_succ, dite_eq_ite, id.def, auto_param_eq],
  refine (proj_continuous i).prod_mk (continuous_pi (λ (i_1 : fin n), _)),
  unfold ite, cases (subtype.decidable_lt (fin.cast_succ i_1) i); simp only,
  exacts [proj_continuous (fin.succ i_1), proj_continuous (fin.cast_succ i_1)]
end

@[simp] lemma extract_insert (t : I×I^n) : extract i (insert i t) = t :=
begin
  cases t with t₀ t,
  simp only [extract_apply, insert_at_eq, fin.coe_eq_cast_succ, prod.mk.inj_iff, eq_self_iff_true,
    true_and, ite],
  ext1 j, cases subtype.decidable_lt (fin.cast_succ j) i; simp only,
  { apply insert_at_gt, rw fin.lt_def, simp only [fin.val_eq_coe, fin.coe_succ],
    refine nat.lt_succ_iff.mpr _, convert not_lt.mp h },
  convert insert_at_lt i j _, norm_cast, convert h, norm_cast
end

lemma insert_extract (t : I^(n+1)) :  insert i (extract i t) = t :=
begin
  ext1,
  simp only [extract, insert, id.def,fin.coe_eq_cast_succ,continuous_map.coe_mk, fin.cast_succ_mk,
    fin.eta, fin.succ_mk, dite],
  cases subtype.decidable_lt x i; simp only,
  { cases subtype.decidable_eq x i; simp only,
    { simp only [fin.succ_pred, ite_eq_right_iff],
      intro H, exfalso, revert x, refine fin.cases _ (λ j, _); intros,
      { simp only [not_lt] at h,
        have hs : _ := i.pos_iff_ne_zero.mpr (ne.symm h_1),
        revert h hs, rw [fin.le_def, fin.lt_def], exact nat.le_lt_antisymm},
      rw [not_lt, fin.le_def] at h, simp only [fin.val_eq_coe, fin.coe_succ] at h,
      rw fin.lt_def at H, simp only [fin.pred_succ, fin.val_eq_coe, fin.coe_cast_succ] at H,
      cases nat.of_le_succ h, exact nat.lt_le_antisymm H h_2,
      apply h_1, symmetry, apply fin.eq_of_veq, convert h_2,
      cases j, refl},
    rw h_1 },
  simp only [ite]
end

/-- Product with `I` homeomorphism -/
def fold.homeomorph (i : fin n) : I×I^n ≃ₜ I^(n+1) :=
{ to_fun := insert i,
  inv_fun := extract i,
  left_inv := extract_insert i,
  right_inv := insert_extract i,
  continuous_to_fun := (insert i).2,
  continuous_inv_fun := (extract i).2 }

end
end cube

/-- Paths fixed at both ends -/
@[simp] def loop_space (X : Type*) [topological_space X] (x:X) := path x x
local notation `Ω` := loop_space

instance loop_space.inhabitated : inhabited (Ω X x) := ⟨path.refl x⟩

/-- The `n`-dimensional generalized loops; functions `I^n → X` fixed at the boundary. -/
def gen_loop (n : ℕ) (x : X) : set C(I^n, X) := { p | ∀ y ∈ cube.boundary n, p y = x}

namespace gen_loop

lemma boundary (f : gen_loop n x) : ∀ y ∈ cube.boundary n, f y = x := f.2

instance fun_like : fun_like (gen_loop n x) (I^n) (λ _, X) :=
{ coe := λ f, f.1,
  coe_injective' := λ ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ h, by { congr, exact h } }

@[ext] lemma ext (f g : gen_loop n x) (H : ∀ y, f y = g y) : f = g := fun_like.ext f g H

@[simp] lemma mk_apply (f : C(I^n, X)) (H y) : (⟨f, H⟩ : gen_loop n x) y = f y := rfl

lemma congr' (f : gen_loop n x) (s t : I^n) : s = t → f s = f t := λ H, by {rw H}

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

section
variables (i j : fin (n+1))

lemma lt_ltS_lt : j < i → j.val < n :=
  by {rw fin.lt_def, exact gt_of_ge_of_gt (nat.lt_succ_iff.mp i.2)}

lemma neq_nlt_neq : j ≠ i → ¬(j < i) → j ≠ 0 := --sorry
begin
  intros Heq Hlt H0, subst H0, apply Heq, symmetry, apply fin.eq_of_veq, apply le_zero_iff.mp,
  apply not_lt.mp, use Hlt,
end

lemma pred_nlt (Hneq : j≠i) (Hnlt : ¬(j < i)) : ¬(↑(j.pred (neq_nlt_neq _ _ Hneq Hnlt)) < i) :=
begin
  rw fin.lt_def,
  simp only [fin.coe_eq_cast_succ, fin.val_eq_coe, fin.coe_cast_succ, fin.coe_pred, not_lt],
  simp only [not_lt] at Hnlt,
  refine nat.le_pred_of_lt _,
  cases lt_or_eq_of_le Hnlt, use h,
  exfalso, apply Hneq, exact h.symm
end


/-- Path from a generalized loop by `uncons`-ing of `I^(n+1)` -/
def to_path (i : fin (n+1)) : gen_loop (n+1) x → Ω (gen_loop n x) const :=
begin
  rintros ⟨g,gH⟩, refine path.mk ⟨_,_⟩ _ _,
  { intro t, refine ⟨(g.comp (cube.insert i)).curry t,_⟩,
    rintros y ⟨j,jH⟩,
    simp only [continuous_map.curry_apply, continuous_map.comp_apply],
    apply gH, apply cube.insert_boundary, right, exact ⟨j,jH⟩},
  { simp only [auto_param_eq], continuity },
  all_goals {simp only, ext,
    simp only [continuous_map.curry_apply, continuous_map.comp_apply, cube.cons_apply, mk_apply,
      const_eq],
    apply gH, use i },
  left, rw cube.insert_at_eq,
  right, rw cube.insert_at_eq,
end

/-- Generalized loop from a path by `fold`-ing of `I×I^n` -/
def from_path (i : fin (n+1)) : Ω (gen_loop n x) const → gen_loop (n+1) x :=
begin
  rintros ⟨p,H₀,H₁⟩,
  simp only [continuous_map.to_fun_eq_coe] at H₀ H₁,
  refine ⟨(⟨λ t, (p t).1, by continuity⟩ : C(I, C(I^n, X))).uncurry.comp (cube.extract i),_⟩,
  rintros y ⟨j,Hj⟩,
  simp only [subtype.val_eq_coe,continuous_map.comp_apply, cube.extract_apply, fin.coe_eq_cast_succ,
    continuous_map.uncurry_apply, continuous_map.coe_mk, function.uncurry_apply_pair],
  by_cases Heq : j=i, { rw ← Heq, cases Hj; rw Hj; simp only [H₀, H₁]; convert const_eq },
  apply gen_loop.boundary,
  by_cases Hlt : j < i,
  { use j, { exact lt_ltS_lt _ _ Hlt },
    simp only [ite, fin.cast_succ_mk, fin.eta, fin.succ_mk],
    cases subtype.decidable_lt j i; simp only, { exfalso, exact h Hlt },
    exact Hj },
  have Hj0 : j≠0, { exact neq_nlt_neq _ _ Heq Hlt },
  use j.pred Hj0,
  simp only [ite, fin.succ_pred],
  cases (subtype.decidable_lt (fin.cast_succ (j.pred Hj0)) i); simp only,
  exact Hj,
  exfalso, refine pred_nlt _ _ Heq Hlt _,
  convert h, apply fin.eq_of_veq, simp only [fin.coe_eq_cast_succ]
end

lemma from_to (p : gen_loop (n+1) x) : from_path i (to_path i p) = p :=
begin
  rcases p with ⟨⟨p,Hc⟩,Hb⟩,
  ext,
  simp only [to_path, from_path, continuous_map.coe_mk, subtype.coe_mk, continuous_map.comp_apply,
    continuous_map.uncurry_apply, continuous_map.curry_apply],
  cases H : cube.extract i a, simp only [function.uncurry_apply_pair], rw ← H,
  rw cube.insert_extract
end

lemma to_from (p : Ω (gen_loop n x) const) : to_path i (from_path i p) = p :=
begin
  rcases p with ⟨⟨p,Hc⟩,Hs,Ht⟩,
  ext,
  simp only [from_path, to_path, continuous_map.coe_mk, subtype.val_eq_coe, path.coe_mk, mk_apply,
    continuous_map.curry_apply, continuous_map.comp_apply, cube.extract_insert,
    continuous_map.uncurry_apply, function.uncurry_apply_pair],
  refl
end

/-- Loop space equivalence -/
def path_equiv (i : fin n) : gen_loop (n+1) x ≃ Ω (gen_loop n x) const :=
{ to_fun := to_path i,
  inv_fun := from_path i,
  left_inv := from_to i,
  right_inv := to_from i }

lemma insert_to_path {p : gen_loop (n+1) x} {t} {tn} :
  (p.val) (cube.insert i ⟨t, tn⟩) = (@coe_fn _ _ path.has_coe_to_fun (to_path i p)) t tn :=
  by {cases p, simp only [to_path, path.coe_mk, mk_apply, continuous_map.curry_apply,
    continuous_map.comp_apply]}

lemma extract_from_path {p : Ω (gen_loop n x) const} {t : I^(n+1)} :
  (from_path i p : C(I^(n+1),X)) t = p.to_fun (t i) (cube.extract i t).snd :=
begin
  cases p,
  simp only [from_path, subtype.val_eq_coe, subtype.coe_mk, continuous_map.comp_apply,
    cube.extract_apply, fin.coe_eq_cast_succ, continuous_map.uncurry_apply, continuous_map.coe_mk,
    function.uncurry_apply_pair, continuous_map.to_fun_eq_coe],
  refl,
end

lemma uncurry_helper (f : C(I, C(I, C(I^n, X)))) (t y) : f.uncurry t y = f t.fst t.snd y :=
  by {unfold continuous_map.uncurry, unfold function.uncurry, simp only [continuous_map.coe_mk]}

/-- Currying as a continuous map.-/
abbreviation c_currying : C(C(I × I^n, X),C(I, C(I^n, X))) :=
⟨continuous_map.curry,continuous_map.continuous_curry⟩

/-- Uncurrying as a continuous map.-/
abbreviation c_uncurrying : C(C(I, C(I^n, X)),C(I × I^n, X)) :=
⟨continuous_map.uncurry,continuous_map.continuous_uncurry⟩

/-- Composition with insert as a continuous map.-/
abbreviation c_comp_insert (i : fin (n+1)) : C(C(I^(n+1), X), C(I×I^n, X)) :=
⟨λ f, f.comp (cube.insert i), (cube.insert i).continuous_comp_left⟩

lemma homotopic_to {p q : gen_loop (n+1) x} :
  homotopic p q → (to_path i p).homotopic (to_path i q) :=
begin
  apply nonempty.map, rintros H,
  refine
  ⟨⟨  ⟨λ t, ⟨(c_currying.comp ((c_comp_insert i).comp H.to_continuous_map.curry)).uncurry t,_⟩,_⟩,
      _, _⟩, _⟩,
  { rintros y ⟨i,iH⟩,
    simp only [uncurry_helper, continuous_map.comp_apply, continuous_map.coe_mk,
      continuous_map.curry_apply, --cube.insert_apply,
      continuous_map.homotopy_with.coe_to_continuous_map],
    rw H.eq_fst, rw p.property, all_goals {apply cube.insert_boundary, right, exact ⟨i,iH⟩} },
  { simp only [auto_param_eq], continuity },
  show ∀ _ _ _, _,
  { intros t y yH,
    split; ext1;
    simp only [continuous_map.comp_apply, continuous_map.coe_mk, continuous_map.curry_apply,
      continuous_map.homotopy_with.coe_to_continuous_map, continuous_map.uncurry_apply,
      function.uncurry_apply_pair, mk_apply, path.coe_to_continuous_map],
    rw H.eq_fst, refine insert_to_path _, use i, rwa cube.insert_at_eq,
    rw H.eq_snd, refine insert_to_path _, use i, rwa cube.insert_at_eq },
  all_goals
  { intro t, ext1,
    simp only [continuous_map.comp_apply, continuous_map.coe_mk, continuous_map.curry_apply,
      continuous_map.homotopy_with.coe_to_continuous_map, continuous_map.uncurry_apply,
      function.uncurry_apply_pair, mk_apply, continuous_map.homotopy_with.apply_zero,
      continuous_map.homotopy_with.apply_one, subtype.val_eq_coe, path.coe_to_continuous_map],
    exact insert_to_path _}
end

/--Coercion as a continuous map.-/
abbreviation c_coe : C(gen_loop n x, C(I^n,X)) := ⟨λ p, p.val, continuous_induced_dom⟩

lemma homotopic_from {p q : gen_loop (n+1) x} :
  (to_path i p).homotopic (to_path i q) → homotopic p q :=
begin
  apply nonempty.map, rintros H,
  refine ⟨⟨(c_uncurrying.comp (c_coe.comp H.to_continuous_map).curry).uncurry.comp
      ((continuous_map.id I).prod_map (cube.extract i)),_,_⟩,_⟩,
  show ∀ _ _ _, _,
  { rintros t y ⟨j,jH⟩,
    simp only [continuous_map.to_fun_eq_coe, continuous_map.comp_apply,
      continuous_map.prod_map_apply, continuous_map.coe_id, prod.map_mk, id.def, cube.extract_apply,
      fin.coe_eq_cast_succ, continuous_map.uncurry_apply, continuous_map.coe_mk,
      continuous_map.curry_apply, continuous_map.homotopy_with.coe_to_continuous_map,
      subtype.val_eq_coe, function.uncurry_apply_pair],
    have hp : (p : C(I^(n+1),X)) y = x := p.2 _ ⟨j,jH⟩,
    have hq : (q : C(I^(n+1),X)) y = x := q.2 _ ⟨j,jH⟩,
    rw [hp, hq],
    apply (and_self _).mpr,
    by_cases Heq : j = i,
    { rw Heq at jH, cases jH; rw jH;
      simp only [path.homotopy.source, path.homotopy.target]; convert const_eq},
    apply (H (t, y i)).property,
    by_cases Hlt : j < i,
    { use j, { exact lt_ltS_lt _ _ Hlt }, simp only [ite],
      cases (subtype.decidable_lt (fin.cast_succ ⟨↑j, _⟩) i); simp only,
      exfalso, apply h, use Hlt,
      convert jH; apply fin.eq_of_veq; refl},
    have Hj0 : j≠0, { exact neq_nlt_neq _ _ Heq Hlt },
    use j.pred Hj0, simp only [ite, fin.succ_pred],
    cases subtype.decidable_lt (fin.cast_succ (j.pred Hj0)) i; simp only,
    exact jH,
    exfalso, refine pred_nlt _ _ Heq Hlt _,
    convert h, apply fin.eq_of_veq, simp only [fin.coe_eq_cast_succ] },
  all_goals
  { intros y,
    simp only [continuous_map.to_fun_eq_coe, continuous_map.comp_apply,
      continuous_map.prod_map_apply, continuous_map.coe_id, prod.map_mk, id.def, cube.extract_apply,
      fin.coe_eq_cast_succ, continuous_map.uncurry_apply, continuous_map.coe_mk,
      continuous_map.curry_apply, continuous_map.homotopy_with.coe_to_continuous_map,
      subtype.val_eq_coe, function.uncurry_apply_pair, continuous_map.homotopy_with.apply_zero,
      continuous_map.homotopy_with.apply_one, path.coe_to_continuous_map],
    symmetry, convert insert_to_path _,-- rw [← cube.extract__to_fun, cube.insert_uninsert] }
    ext1 j, simp only [cube.insert, continuous_map.coe_mk, fin.cast_succ_mk, fin.eta, fin.succ_mk,
      fin.succ_pred, dite],
    cases subtype.decidable_lt j i; simp only [ite],
    cases subtype.decidable_eq j i; simp only,
    cases subtype.decidable_lt (fin.cast_succ (j.pred _)) i; simp only,
    { exfalso, refine pred_nlt _ _ h_1 h _,
      convert h_2, apply fin.eq_of_veq, simp only [fin.coe_eq_cast_succ] },
    subst h_1 },
end


/-- Concatenation of `gen_loop`s by transitivity as paths -/
def concat_ (i : fin (n+1)) : gen_loop (n+1) x → gen_loop (n+1) x → gen_loop (n+1) x :=
λ p q, from_path i ((to_path i p).trans (to_path i q))

lemma concat_to_trans (p q : gen_loop (n+1) x) :
  to_path i (concat_ i p q) = (to_path i p).trans (to_path i q):=
  by { unfold concat_, rw to_from}

lemma const_to_refl (i: fin (n+1)) : to_path i (@const _ _ (n+1) x) = path.refl (@const _ _ n x) :=
begin
  ext, unfold const, unfold to_path,
  simp only [continuous_map.const_comp, path.coe_mk, mk_apply, continuous_map.curry_apply,
    continuous_map.const_apply, path.refl_apply, const_eq],
end

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

/--Concatenation of equivalence clasess along the _horizontal_ component, i.e. the first.-/
def concat : π_(n+1) X x → π_(n+1) X x → π_(n+1) X x :=
begin
  refine (quotient.map₂' (gen_loop.concat_ 0) _),
  rintros p₀ p₁ Hp q₀ q₁ Hq,
  apply gen_loop.homotopic_from 0,
  repeat {rw gen_loop.concat_to_trans},
  apply path.homotopic.hcomp; apply gen_loop.homotopic_to 0,
  exacts [Hp, Hq],
end
instance has_mul : has_mul (π_(n+1) X x) := ⟨concat⟩

lemma concat_assoc (p q r : π_(n+1) X x) : ((p * q) * r) = (p * (q * r)) :=
begin
  refine (quotient.induction_on₃ p q r _),
  intros a b c, refine (quotient.sound _),
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.concat_to_trans},
  constructor,
  apply path.homotopy.trans_assoc
end

/--Equivalence class of the constant `gen_loop`.-/
def const : π_ n X x := quotient.mk' gen_loop.const

instance has_one : has_one (π_ n X x) := ⟨const⟩

local notation `𝟙` := const

lemma concat_const (p: π_(n+1) X x) : p * 𝟙 = p :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.concat_to_trans},
  rw gen_loop.const_to_refl,
  constructor,
  apply path.homotopy.trans_refl,
end

lemma const_concat (p: π_(n+1) X x) : 𝟙 * p = p :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.concat_to_trans},
  rw gen_loop.const_to_refl,
  constructor,
  apply path.homotopy.refl_trans,
end

/--Reversing an equivalence class of loops-/
def reverse (i : fin (n+1)) : π_(n+1) X x → π_(n+1) X x :=
begin
  refine (quotient.map' (λ p, gen_loop.from_path i ((gen_loop.to_path i p).symm)) _),
  intros p q H,
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.to_from},
  apply nonempty.map path.homotopy.symm₂,
  exact gen_loop.homotopic_to _ H
end
instance has_inv : has_inv (π_(n+1) X x) := ⟨reverse 0⟩
-- local postfix `⁻¹`:65 := has_inv.inv

lemma reverse_concat (p: π_(n+1) X x) : p⁻¹ * p = 𝟙 :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.concat_to_trans},
  rw gen_loop.const_to_refl,
  repeat {rw gen_loop.to_from},
  symmetry, constructor,
  apply  path.homotopy.refl_symm_trans
end
lemma concat_reverse (p: π_(n+1) X x) : p * (p⁻¹)  = 𝟙 :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_from 0,
  rw gen_loop.const_to_refl,
  unfold gen_loop.concat_,
  repeat {rw gen_loop.to_from},
  symmetry, constructor,
  apply path.homotopy.refl_trans_symm,
end

/-- Concatecantion forms a group.-/
def is_group : group (π_(n+1) X x) :=
{ mul := concat,
  mul_assoc := concat_assoc,
  one := const,
  one_mul := const_concat,
  mul_one := concat_const,
  npow := npow_rec,
  npow_zero' := λ _, rfl,
  npow_succ' := λ _ _, rfl,
  inv := reverse 0,
  div := λ a b, a*(b⁻¹),
  div_eq_mul_inv := λ _ _, rfl,
  zpow := zpow_rec,
  zpow_zero' := λ _, rfl,
  zpow_succ' := λ _ _, rfl,
  zpow_neg' := λ _ _, rfl,
  mul_left_inv := reverse_concat }

/--Concatenation of equivalence clasess along the _vertical_ component, i.e. the second.-/
def concat₂ : π_(n+2) X x → π_(n+2) X x → π_(n+2) X x :=
begin
  refine (quotient.map₂' (gen_loop.concat_ 1) _),
  rintros p₀ p₁ Hp  q₀ q₁ Hq,
  apply gen_loop.homotopic_from 1,
  repeat {rw gen_loop.concat_to_trans},
  apply path.homotopic.hcomp; apply gen_loop.homotopic_to 1,
  exacts [Hp, Hq],
end

local infix `*₂`:70 := concat₂

lemma concat₂_const (p: π_(n+2) X x) : p *₂ 𝟙 = p :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.concat_to_trans},
  rw gen_loop.const_to_refl,
  constructor,
  apply path.homotopy.trans_refl,
end

lemma const_concat₂ (p: π_(n+2) X x) : 𝟙 *₂ p = p :=
begin
  induction p using quotient.induction_on,
  refine (quotient.sound _),
  apply gen_loop.homotopic_from,
  repeat {rw gen_loop.concat_to_trans},
  rw gen_loop.const_to_refl,
  constructor,
  apply path.homotopy.refl_trans
end

lemma is_unital : @eckmann_hilton.is_unital (π_(n+2) X x) (*₂) 𝟙 :=⟨⟨const_concat₂⟩,⟨concat₂_const⟩⟩

/-- Conmutativity of horizontal concatenation is shown by
  distributivity with vertical concatenation. -/
@[reducible] def is_comm_group : comm_group (π_(n+2) X x) :=
begin
  apply @eckmann_hilton.comm_group (π_(n+2) X x) (*₂) 𝟙 is_unital is_group,
  intros a b c d,
  induction a using quotient.induction_on, induction b using quotient.induction_on,
  induction c using quotient.induction_on, induction d using quotient.induction_on,
  refine (quotient.sound _),
  constructor,
  suffices Heq : (gen_loop.concat_ 1 (gen_loop.concat_ 0 a b) (gen_loop.concat_ 0 c d)).val =
    (gen_loop.concat_ 0 (gen_loop.concat_ 1 a c) (gen_loop.concat_ 1 b d)).val,
  { rw Heq, apply continuous_map.homotopy_rel.refl},
  ext1 t, simp only [gen_loop.concat_, subtype.val_eq_coe],
  repeat {rw gen_loop.extract_from_path},
  simp only [continuous_map.to_fun_eq_coe, path.coe_to_continuous_map, cube.extract_apply,
    fin.coe_eq_cast_succ, fin.not_lt_zero, if_false],
  repeat {rw path.trans_apply},
  simp only [dite, one_div],
  have H01 : (0:fin (n+2))<1, {rw fin.lt_def, exact zero_lt_one},
  have H1 : ∀ t₀ (t:I^(n+1)), (cube.insert 0) ⟨t₀, t⟩ 1 = t 0,
    { intros, convert cube.insert_at_gt 0 0 _, rw fin.lt_def, exact zero_lt_one },
  have His : ∀ {n} {i : fin n}, fin.cast_succ i.succ = (fin.cast_succ i).succ :=
    by {intros n i, cases i, simp only [fin.succ_mk, fin.cast_succ_mk]},
  cases ((t 0 :ℝ).decidable_le 2⁻¹) with H₀ H₀; cases ((t 1 :ℝ).decidable_le 2⁻¹) with H₁ H₁;
  simp only; repeat {rw ← gen_loop.insert_to_path}; simp only [subtype.val_eq_coe];
  repeat {rw gen_loop.extract_from_path};
  simp only [continuous_map.to_fun_eq_coe, path.coe_to_continuous_map, cube.extract_apply,
  fin.coe_eq_cast_succ, fin.not_lt_zero, if_false, cube.insert_at_gt, fin.succ_pos];
  rw [cube.insert_at_lt' _ _ (by norm_num) H01];
  simp only [fin.coe_zero, fin.mk_zero, fin.cast_succ_zero, fin.succ_zero_eq_one];
  rw [H1, if_pos H01]; repeat {rw path.trans_apply};
  simp only [dite, one_div, fin.succ_zero_eq_one],
  all_goals
  { cases ((t 0 :ℝ).decidable_le 2⁻¹); cases ((t 1 :ℝ).decidable_le 2⁻¹); try {contradiction},
    repeat {rw ← gen_loop.insert_to_path},
    apply gen_loop.congr', ext1 j,
    revert j, refine fin.cases _ (fin.cases _ _),
    rw cube.insert_at_eq, rw [cube.insert_at_lt' _ _ (by norm_num) H01],
    simp only [fin.coe_zero,fin.mk_zero,fin.cast_succ_zero, cube.insert_at_eq,fin.succ_zero_eq_one],
    rw if_pos H01, simp only [fin.succ_zero_eq_one, cube.insert_at_eq],
    rw H1, simp only [fin.succ_zero_eq_one, cube.insert_at_eq],
    intro i,
    repeat {rw [cube.insert_at_gt]}, rw [His, cube.insert_at_gt],
    all_goals {rw fin.lt_def, norm_num } }
end

end homotopy_group
