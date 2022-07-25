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
We give a group instance using path transitivity and show commutativity when `n > 1`.

## definitions

* `gen_loop n x` is the type of continous fuctions `I^n → X` that send the
  boundary to `x`,
* `homotopy_group n x` denoted `π_ n x` is the quotient of `gen_loop n x` by homotopy relative
  to the boundary,
* group instance `group (π_(n+1) x)`,
* commutative group instance `comm_group (π_(n+2) x)`.

TODO: Path-induced homomorphisms. Show that `pi1_equiv_fundamental_group` is a group isomorphism.
  Examples with 𝕊^n (π_n (𝕊^n) = ℤ, π_m (𝕊^n) trivial for m < n).
  Actions of π_1 on π_n.
  Group (up to homotopy) of Ω.
  Lie algebra: ⁅π_(n+1), π_(m+1)⁆ contained in π_(n+m+1).

-/

open_locale unit_interval topological_space

noncomputable theory

universes u
variables {X : Type u} [topological_space X]
variables {n : ℕ} {x : X}

section
variables {i j : fin (n+1)}

lemma neq_nlt_neq : j ≠ i → ¬(j < i) → j ≠ 0 :=
  by {intros Heq Hlt H0, subst H0,
    exact Heq (eq.symm (fin.eq_of_veq (le_zero_iff.mp (not_lt.mp Hlt)))) }

lemma pred_nlt (Hneq : j≠i) (Hnlt : ¬(j < i)) : ¬(↑(j.pred (neq_nlt_neq Hneq Hnlt)) < i) :=
begin
  rw fin.lt_def,
  simp only [fin.coe_eq_cast_succ, fin.val_eq_coe, fin.coe_cast_succ, fin.coe_pred, not_lt],
  simp only [not_lt] at Hnlt,
  refine nat.le_pred_of_lt _,
  cases lt_or_eq_of_le Hnlt, use h,
  exact false.rec (↑i < ↑j) (Hneq (eq.symm h))
end

end

/-- The `n`-dimensional cube. -/
@[derive [has_zero, has_one, topological_space, metric_space]]
def cube (n : ℕ) : Type := fin n → I
local notation `I^` := cube

namespace cube

instance compact_space : compact_space (I^n) :=
@pi.compact_space _ _ _ (λ_,compact_space_Icc (0:ℝ) 1)

instance locally_compact_space : locally_compact_space (I^n) := locally_compact_of_proper

@[continuity] lemma proj_continuous (i : fin n) : continuous (λ f : I^n, f i) := continuous_apply i

/-- The `i`th projection as a continuous_map -/
@[simps] def proj (i : fin n) : C(I^n,I) := ⟨λ t, t i, proj_continuous i⟩

/-- The points of the `n`-dimensional cube with at least one projection equal to 0 or 1. -/
def boundary (n : ℕ) : set (I^n) := {y | ∃ i, y i = 0 ∨ y i = 1}

/-- The first projection of a positive-dimensional cube. -/
@[simps] def head : C(I^(n+1), I) := ⟨λ t, t 0, continuous_apply 0⟩ --proj 0

/-- The projection to the last `n` coordinates from an `n+1` dimensional cube. -/
@[simps] def tail : C(I^(n+1), I^n) := ⟨λ c, fin.tail c,
  (continuous_map.pi (λ i:fin n, ⟨λ f:I^(n+1), f i.succ, continuous_apply i.succ⟩)).2⟩

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

section
variable (i : fin (n+1))

/-- Continuos "insert" map, in particular `insert 0 = cons`. -/
def insert (i : fin (n+1)) : C(I×I^n, I^(n+1)) :=
{ to_fun := λ t j, dite (j<i) (λ H, t.snd ⟨j, nat.lt_of_lt_of_le H (nat.lt_succ_iff.mp i.2)⟩)
    (λ H, dite (j=i) (λ H₀, t.fst) (λ H₀, t.snd (j.pred (neq_nlt_neq H₀ H)))),
  continuous_to_fun :=
  begin
    refine (continuous_map.pi (λ j:fin (n+1), ⟨λ t:I×I^n,_,_⟩)).2,
    cases subtype.decidable_lt j i; simp only [auto_param_eq, dite];
    cases subtype.decidable_eq j i; try {simp only},
    show continuous prod.fst, { exact continuous_fst },
    all_goals {exact (proj_continuous _).comp continuous_snd}
  end }

@[simp] lemma insert_at_eq (t₀:I) (t) : insert i ⟨t₀, t⟩ i = t₀ :=
by simp only [insert, lt_self_iff_false, not_false_iff,id.def,continuous_map.coe_mk,dif_pos,dif_neg]

lemma insert_at_lt (j : fin n) {t₀ t} (H : ↑j < i) : insert i ⟨t₀, t⟩ ↑j = t j :=
begin
  simp only [insert, not_lt, id.def, fin.coe_eq_cast_succ, continuous_map.coe_mk, fin.coe_cast_succ,
    fin.eta, dite_eq_right_iff, dite],
  cases subtype.decidable_lt (fin.cast_succ j) i with H₀; simp only,
  exfalso, apply H₀, convert H, norm_cast
end

lemma insert_at_lt' (j: fin (n+1)) {t₀ t} (H : ↑j<n) (H₀ : j<i) : insert i ⟨t₀, t⟩ j = t ⟨j,H⟩ :=
begin
  simp only [insert, not_lt, id.def, fin.coe_eq_cast_succ, continuous_map.coe_mk,
    fin.coe_cast_succ, fin.eta, dite_eq_right_iff, dite],
  cases subtype.decidable_lt j i with H₁; simp only,
  exfalso, exact H₁ H₀
end

lemma insert_at_gt (j : fin n) {t₀ t} (H : i < j.succ) : insert i ⟨t₀, t⟩ j.succ = t j :=
begin
  simp only [insert, fin.coe_succ,id.def,continuous_map.coe_mk, fin.cases_succ, dite_eq_ite, dite],
  cases subtype.decidable_lt j.succ i with H₀ H₀; simp only,
  cases subtype.decidable_eq j.succ i with H₁ H₁; simp only,
  { simp only [fin.pred_succ] },
  { exfalso, rw H₁ at H, exact has_lt.lt.false H },
  exfalso, exact not_le_of_lt H (le_of_lt H₀)
end

lemma insert_boundary {t₀:I} {t} (H : (t₀=0 ∨ t₀=1) ∨ t∈boundary n) :
  insert i ⟨t₀,t⟩ ∈ boundary (n+1) :=
begin
  cases H, { use i, rwa insert_at_eq },
  rcases H with ⟨j,H⟩,
  by_cases Hlt : ↑j < i, { use j, rwa insert_at_lt, exact Hlt },
  use j.succ, rwa insert_at_gt,
  simp only [fin.coe_eq_cast_succ, not_lt] at Hlt,
  apply nat.lt_of_le_of_lt Hlt,
  simp only [fin.val_eq_coe, fin.coe_cast_succ, fin.coe_succ, lt_add_iff_pos_right, nat.lt_one_iff]
end

/-- Continuos "extract" map, in particular `extract 0 t = (t.head, t.tail)`. -/
@[simps] def extract (i : fin (n+1)) : C(I^(n+1), I×I^n) :=
{ to_fun := λ t, ⟨t i, λ j, if ↑j< i then t ↑j else t j.succ⟩,
  continuous_to_fun :=
  begin
    simp only [fin.coe_eq_cast_succ, dite_eq_ite, id.def, auto_param_eq],
    refine (proj_continuous i).prod_mk (continuous_pi (λ j, _)),
    unfold ite, cases subtype.decidable_lt (fin.cast_succ j) i; simp only,
    exacts [proj_continuous (fin.succ j), proj_continuous (fin.cast_succ j)]
  end }

lemma extract_insert (t : I×I^n) : extract i (insert i t) = t :=
begin
  cases t with t₀ t,
  simp only [extract_apply, insert_at_eq, fin.coe_eq_cast_succ, prod.mk.inj_iff, eq_self_iff_true,
    true_and, ite],
  ext1 j,
  cases subtype.decidable_lt (fin.cast_succ j) i; simp only,
  { apply insert_at_gt, rw fin.lt_def,
    simp only [fin.val_eq_coe, fin.coe_succ],
    refine nat.lt_succ_iff.mpr _,
    convert not_lt.mp h },
  convert insert_at_lt i j _, norm_cast,
  convert h, norm_cast
end

lemma insert_extract (t : I^(n+1)) :  insert i (extract i t) = t :=
begin
  ext1 j,
  simp only [extract, insert, id.def, fin.coe_eq_cast_succ, continuous_map.coe_mk, fin.cast_succ_mk,
    fin.eta, fin.succ_mk, dite],
  cases subtype.decidable_lt j i with Hlt Hlt; simp only,
  show ite _ _ _ = _, { simp only [ite] },
  cases subtype.decidable_eq j i with Heq Heq; simp only,
  show t i = _ , { rw Heq },
  simp only [fin.succ_pred, ite_eq_right_iff],
  intro H, exfalso, revert j, refine fin.cases _ (λ j, _); intros,
  exact nat.le_lt_antisymm (cast (fin.le_def _ _) (not_lt.mp Hlt))
    (cast (fin.lt_def _ _) (i.pos_iff_ne_zero.mpr (ne.symm Heq))),
  rw [not_lt, fin.le_def] at Hlt, simp only [fin.val_eq_coe, fin.coe_succ] at Hlt,
  rw fin.lt_def at H, simp only [fin.pred_succ, fin.val_eq_coe, fin.coe_cast_succ] at H,
  cases nat.of_le_succ Hlt, exact nat.lt_le_antisymm H h,
  apply Heq, symmetry, apply fin.eq_of_veq, convert h,
  cases j, refl,
end

/-- Product with `I` homeomorphism for all components.
 -/
def prod_homeomorph (i : fin n) : I×I^n ≃ₜ I^(n+1) :=
{ to_fun := insert i,
  inv_fun := extract i,
  left_inv := extract_insert i,
  right_inv := insert_extract i,
  continuous_to_fun := (insert i).2,
  continuous_inv_fun := (extract i).2 }

end

end cube

/-- Paths fixed at both ends -/
abbreviation loop_space (X : Type*) [topological_space X] (x:X) := path x x
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

instance inhabited : inhabited (gen_loop n x) := ⟨const⟩

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

/-- Path from a generalized loop by `insert`-ing into `I^(n+1)`. -/
def to_path (i : fin (n+1)) : gen_loop (n+1) x → Ω (gen_loop n x) const := λ p,
{ to_fun := λ t, ⟨ (p.val.comp (cube.insert i)).curry t,
    λ y yH, p.property (cube.insert i (t, y)) (cube.insert_boundary i (or.inr yH))⟩,
  continuous_to_fun := by continuity,
  source' := by {ext t, exact p.property ((cube.insert i) (0, t))
    (Exists.intro i (or.inl (cube.insert_at_eq i 0 t)))},
  target' := by {ext t, exact p.property ((cube.insert i) (1, t))
    (Exists.intro i (or.inr (cube.insert_at_eq i 1 t)))} }

/-- Generalized loop from a path by `extrac`-ing of `I×I^n`. -/
def from_path (i : fin (n+1)) : Ω (gen_loop n x) const → gen_loop (n+1) x :=
λ p, ⟨(⟨λ t, (p t).1, by continuity⟩ : C(I, C(I^n, X))).uncurry.comp (cube.extract i),
begin
  rintros y ⟨j,Hj⟩,
  simp only [subtype.val_eq_coe,continuous_map.comp_apply, cube.extract_apply, fin.coe_eq_cast_succ,
    continuous_map.uncurry_apply, continuous_map.coe_mk, function.uncurry_apply_pair],
  by_cases Heq : j=i,
  { rw ← Heq, cases Hj; rw Hj; simp only [p.source, p.target]; convert const_eq },
  apply gen_loop.boundary,
  by_cases Hlt : j < i,
  { use j, { revert Hlt, rw fin.lt_def, exact gt_of_ge_of_gt (nat.lt_succ_iff.mp i.2) },
    simp only [ite, fin.cast_succ_mk, fin.eta, fin.succ_mk],
    cases subtype.decidable_lt j i; simp only, { exfalso, exact h Hlt },
    exact Hj },
  have Hj0 : j≠0, { exact neq_nlt_neq Heq Hlt },
  use j.pred Hj0,
  simp only [ite, fin.succ_pred],
  cases subtype.decidable_lt (fin.cast_succ (j.pred Hj0)) i; simp only,
  exact Hj,
  exfalso, refine pred_nlt Heq Hlt _,
  convert h, apply fin.eq_of_veq, simp only [fin.coe_eq_cast_succ]
end⟩

lemma from_to (p : gen_loop (n+1) x) : from_path i (to_path i p) = p :=
begin
  rcases p with ⟨⟨p,Hc⟩,Hb⟩,
  ext t,
  simp only [to_path, from_path, path.coe_mk, subtype.coe_mk, continuous_map.comp_apply,
    continuous_map.curry_apply],
  cases H : cube.extract i t,
  simp only [continuous_map.uncurry_apply, continuous_map.coe_mk, continuous_map.curry_apply,
    continuous_map.comp_apply, function.uncurry_apply_pair],
  rw [← H, cube.insert_extract]
end

lemma to_from (p : Ω (gen_loop n x) const) : to_path i (from_path i p) = p :=
  by { ext, rcases p with ⟨⟨p,_⟩,_,_⟩, simpa only [from_path, to_path, continuous_map.coe_mk,
    subtype.val_eq_coe, path.coe_mk,mk_apply, continuous_map.curry_apply, continuous_map.comp_apply,
    cube.extract_insert, continuous_map.uncurry_apply, function.uncurry_apply_pair] }

/-- The (n+1)-dimensional loops are isomorphic to the loop space at `const`.-/
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
  by { cases p, simpa only [from_path, subtype.val_eq_coe,subtype.coe_mk, continuous_map.comp_apply,
    cube.extract_apply, fin.coe_eq_cast_succ, continuous_map.uncurry_apply, continuous_map.coe_mk,
    function.uncurry_apply_pair, continuous_map.to_fun_eq_coe] }

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

/--Coercion as a continuous map.-/
abbreviation c_coe : C(gen_loop n x, C(I^n,X)) := ⟨λ p, p.val, continuous_induced_dom⟩

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
    { use j, { revert Hlt, rw fin.lt_def, exact gt_of_ge_of_gt (nat.lt_succ_iff.mp i.2) },
      simp only [ite],
      cases (subtype.decidable_lt (fin.cast_succ ⟨↑j, _⟩) i); simp only,
      exfalso, apply h, use Hlt,
      convert jH; apply fin.eq_of_veq; refl},
    have Hj0 : j≠0, { exact neq_nlt_neq Heq Hlt },
    use j.pred Hj0, simp only [ite, fin.succ_pred],
    cases subtype.decidable_lt (fin.cast_succ (j.pred Hj0)) i; simp only,
    exact jH,
    exfalso, refine pred_nlt Heq Hlt _,
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
    { exfalso, refine pred_nlt h_1 h _,
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
def homotopy_group (n : ℕ) (x : X) : Type _ :=
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
def pi0_equiv_path_components : π_ 0 x ≃ zeroth_homotopy X :=
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
@[simps] def gen_loop_one_equiv_path_self : gen_loop 1 x ≃ Ω X x :=
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
def pi1_equiv_fundamental_group : π_ 1 x ≃ fundamental_group X x :=
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

/--Equivalence class of the constant `gen_loop`.-/
def const : π_ n x := quotient.mk' gen_loop.const

instance has_one : has_one (π_ n x) := ⟨const⟩
instance has_zero : has_zero (π_ n x) := ⟨const⟩

section
variable (i : fin (n+1))
/--Concatenation of equivalence clasess along the `i`th component.-/
def concat (i: fin (n+1)) : π_(n+1) x → π_(n+1) x → π_(n+1) x :=
quotient.map₂' (gen_loop.concat_ i) (λ _ _ Hp _ _ Hq, gen_loop.homotopic_from i $
  by { repeat {rw gen_loop.concat_to_trans},
    exact (gen_loop.homotopic_to i Hp).hcomp (gen_loop.homotopic_to i Hq) } )

instance has_mul : has_mul (π_(n+1) x) := ⟨concat 0⟩

instance has_add : has_add (π_(n+2) x) := ⟨concat 1⟩

lemma concat_assoc (p q r : π_(n+1) x) : concat i (concat i p q) r = concat i p (concat i q r):=
quotient.induction_on₃ p q r (λ a b c, quotient.sound (gen_loop.homotopic_from i $
  by { repeat {rw gen_loop.concat_to_trans},
       exact nonempty.intro (path.homotopy.trans_assoc
          (gen_loop.to_path _ a) (gen_loop.to_path _ b) (gen_loop.to_path _ c)) } ))


lemma concat_const (p: π_(n+1) x) : concat i p 1 = p :=
quotient.induction_on p (λ p', quotient.sound (gen_loop.homotopic_from i $
begin
  repeat {rw gen_loop.concat_to_trans},
  rw gen_loop.const_to_refl,
  exact nonempty.intro (path.homotopy.trans_refl (gen_loop.to_path i p'))
end))

lemma const_concat (p: π_(n+1) x) : concat i 1 p = p :=
quotient.induction_on p (λ p', quotient.sound (gen_loop.homotopic_from i $
begin
  repeat {rw gen_loop.concat_to_trans},
  rw gen_loop.const_to_refl,
  exact nonempty.intro (path.homotopy.refl_trans (gen_loop.to_path i p')),
end))

/--Reversing an equivalence class of loops-/
def reverse (i : fin (n+1)) : π_(n+1) x → π_(n+1) x :=
quotient.map' (λ p, gen_loop.from_path i (gen_loop.to_path i p).symm)
  (λ _ _ H, gen_loop.homotopic_from _ $
    by { repeat {rw gen_loop.to_from},
         exact nonempty.map path.homotopy.symm₂ (gen_loop.homotopic_to i H) } )

instance has_inv : has_inv (π_(n+1) x) := ⟨reverse 0⟩
instance has_neg : has_neg (π_(n+2) x) := ⟨reverse 1⟩

lemma reverse_concat (p: π_(n+1) x) : concat i (reverse i p) p = 1 :=
quotient.induction_on p
  (λ (p₀ : ↥(gen_loop (n + 1) x)), quotient.sound (gen_loop.homotopic_from i $
begin
  repeat {rw gen_loop.concat_to_trans},
  rw gen_loop.const_to_refl,
  repeat {rw gen_loop.to_from},
  exact path.homotopic.symm (nonempty.intro (path.homotopy.refl_symm_trans (gen_loop.to_path i p₀)))
end))

lemma concat_reverse (p: π_(n+1) x) : concat i p (reverse i p)  = 1 :=
quotient.induction_on p (λ p', quotient.sound (gen_loop.homotopic_from i $
begin
  rw gen_loop.const_to_refl,
  unfold gen_loop.concat_,
  repeat {rw gen_loop.to_from},
  exact path.homotopic.symm (nonempty.intro (path.homotopy.refl_trans_symm (gen_loop.to_path i p')))
end))

end

/-- Concatecantion forms a group.-/
@[reducible] def is_group : group (π_(n+1) x) :=
{ mul := concat 0, mul_assoc := concat_assoc 0,
  one := const, one_mul := const_concat 0, mul_one := concat_const 0,
  inv := reverse 0,
  div := λ a b, a*(b⁻¹), div_eq_mul_inv := λ _ _, rfl,
  mul_left_inv := reverse_concat 0 }

instance : group (π_(n+1) x) := is_group

lemma is_unital : @eckmann_hilton.is_unital (π_(n+2) x) (+) 1 :=
⟨⟨const_concat 1⟩,⟨concat_const 1⟩⟩

/-- Conmutativity of horizontal concatenation is shown by
  distributivity with vertical concatenation, given that it respects the unity. -/
@[reducible] def is_comm_group : comm_group (π_(n+2) x) :=
@eckmann_hilton.comm_group _ _ 1 is_unital is_group $
begin
  intros a b c d,
  refine quotient.induction_on₂ a b (λ a b, quotient.induction_on₂ c d (λ c d, _)),
  refine quotient.sound (nonempty.intro _),
  suffices Heq : (gen_loop.concat_ 1 (gen_loop.concat_ 0 a b) (gen_loop.concat_ 0 c d)).val = _,
  { rw Heq, exact continuous_map.homotopy_rel.refl _ _},
  ext1 t,
  simp only [gen_loop.concat_, subtype.val_eq_coe],
  repeat {rw gen_loop.extract_from_path},
  simp only [continuous_map.to_fun_eq_coe, path.coe_to_continuous_map, cube.extract_apply,
    fin.coe_eq_cast_succ, fin.not_lt_zero, if_false],
  repeat {rw path.trans_apply},
  simp only [dite, one_div],
  have H : (0:fin (n+2))<1, {rw fin.lt_def, exact zero_lt_one},
  have H0 : ∀ t₀ (t:I^(n+1)), (cube.insert 0) ⟨t₀, t⟩ 1 = t 0,
    { intros, convert cube.insert_at_gt 0 0 _, rw fin.lt_def, exact zero_lt_one },
  have H1 : ∀ {n} {i : fin n}, fin.cast_succ i.succ = (fin.cast_succ i).succ :=
    by {intros n i, cases i, simp only [fin.succ_mk, fin.cast_succ_mk]},
  cases ((t 0 :ℝ).decidable_le 2⁻¹) with H₀ H₀; cases ((t 1 :ℝ).decidable_le 2⁻¹) with H₁ H₁;
  simp only; repeat {rw ← gen_loop.insert_to_path}; simp only [subtype.val_eq_coe];
  repeat {rw gen_loop.extract_from_path};
  simp only [continuous_map.to_fun_eq_coe, path.coe_to_continuous_map, cube.extract_apply,
    fin.coe_eq_cast_succ, fin.not_lt_zero, if_false, cube.insert_at_gt, fin.succ_pos];
  rw [cube.insert_at_lt' _ _ (by norm_num) H];
  simp only [fin.coe_zero, fin.mk_zero, fin.cast_succ_zero, fin.succ_zero_eq_one];
  rw [H0, if_pos H]; repeat {rw path.trans_apply};
  simp only [dite, one_div, fin.succ_zero_eq_one],
  all_goals
  { cases ((t 0 :ℝ).decidable_le 2⁻¹); cases ((t 1 :ℝ).decidable_le 2⁻¹); try {contradiction},
    repeat {rw ← gen_loop.insert_to_path},
    apply gen_loop.congr', ext1 j,
    revert j, refine fin.cases _ (fin.cases _ _),
    rw cube.insert_at_eq, rw [cube.insert_at_lt' _ _ (by norm_num) H],
    simp only [fin.coe_zero,fin.mk_zero,fin.cast_succ_zero, cube.insert_at_eq,fin.succ_zero_eq_one],
    rw if_pos H, simp only [fin.succ_zero_eq_one, cube.insert_at_eq],
    rw H0, simp only [fin.succ_zero_eq_one, cube.insert_at_eq],
    intro i,
    repeat {rw [cube.insert_at_gt]}, rw [H1, cube.insert_at_gt],
    all_goals {rw fin.lt_def, norm_num } }
end

instance : comm_group (π_(n+2) x) := is_comm_group

end homotopy_group
