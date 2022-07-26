/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/

import algebraic_topology.fundamental_groupoid.fundamental_group
import group_theory.eckmann_hilton
import logic.equiv.transfer_instance

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
variables {N : Type*} {x : X}

section merge_split

variables (Y : Type*) [topological_space Y]

lemma symm_comp_to_continuous_map (f : X ≃ₜ Y) :
  f.symm.to_continuous_map.comp f.to_continuous_map = continuous_map.id X :=
by { ext, apply f.to_equiv.symm_apply_apply }

@[continuity] lemma proj_continuous (i : N) : continuous (λ f : N → Y, f i) := continuous_apply i

/-- The `i`th projection as a continuous_map -/
@[simps] def proj (i : N) : C(N → Y, Y) := ⟨λ t, t i, proj_continuous Y i⟩

variable [decidable_eq N]

/- Can be defined as
(@equiv.pi_option_equiv_prod _ (λ _, Y)).symm.trans (equiv.arrow_congr
  ((equiv.option_equiv_sum_punit _).trans $
    ((equiv.refl _).sum_congr $ (equiv.set.singleton i).symm).trans $
      (equiv.sum_comm _ _).trans $ equiv.set.sum_compl {i}) (equiv.refl Y))
barring some undiagnosed universe issues,
but the following is simpler and probably better definitionally:
-/
@[simps] def merge_split_equiv (i : N) : Y × ({j // j ≠ i} → Y) ≃ (N → Y) :=
{ to_fun := λ y j, if h : j = i then y.1 else y.2 ⟨j, h⟩,
  inv_fun := λ f, ⟨f i, λ j, f j⟩,
  left_inv := λ y, by { ext; dsimp, { rw dif_pos rfl }, { rw [dif_neg x.prop, subtype.coe_eta] } },
  right_inv := λ y, by { ext j, dsimp, split_ifs, { rw h }, { refl } } }

@[simps] def merge_split (i : N) : Y × ({j // j ≠ i} → Y) ≃ₜ (N → Y) :=
{ to_equiv := merge_split_equiv Y i,
  continuous_to_fun := continuous_pi $ λ j, by { dsimp, split_ifs,
    exacts [continuous_fst, (proj_continuous Y _).comp continuous_snd] },
  continuous_inv_fun := (proj_continuous Y i).prod_mk (continuous_pi $ λ j, proj_continuous Y j) }

@[simp] def merge_split_self (i : N) {t} : merge_split Y i t i = t.1 := by exact dif_pos rfl
-- remove `by exact` -> get strange class synthesized not defeq error

end merge_split

/-- The `n`-dimensional cube. -/
--@[derive [has_zero, has_one, topological_space, metric_space]]
--def cube (n : ℕ) : Type := fin n → I
@[derive [has_zero, has_one, topological_space]]
def cube (N : Type*) := N → I
local notation `I^` n := cube (fin n)

namespace cube

instance compact_space : compact_space (cube N) :=
@pi.compact_space _ _ _ (λ_,compact_space_Icc (0:ℝ) 1)

instance locally_compact_space : locally_compact_space (cube N) := sorry
/- his should hold even if N is infinite, but a different proof is required. -/

/-- The points of the `n`-dimensional cube with at least one projection equal to 0 or 1. -/
def boundary (N) : set (cube N) := {y | ∃ i, y i = 0 ∨ y i = 1}

variable {n : ℕ}
/-- The first projection of a positive-dimensional cube. -/
@[simps] def head : C(I^(n+1), I) := ⟨λ t, t 0, continuous_apply 0⟩ --proj 0

/- The projection to the last `n` coordinates from an `n+1` dimensional cube. -/
@[simps] def tail : C(I^(n+1), I^n) := ⟨λ c, fin.tail c,
  (continuous_map.pi (λ i:fin n, ⟨λ f:I^(n+1), f i.succ, continuous_apply i.succ⟩)).2⟩

instance unique_cube0 : unique (I^0) := pi.unique_of_is_empty _

lemma one_char (f : I^1) : f = λ _, f 0 := eq_const_of_unique f


section
--variable (i : fin (n+1))
variable [decidable_eq N]

lemma insert_boundary (i : N) {t₀ : I} {t} (H : (t₀ = 0 ∨ t₀ = 1) ∨ t ∈ boundary {j // j ≠ i}) :
  merge_split I i ⟨t₀, t⟩ ∈ boundary N :=
begin
  cases H, { use i, rwa [merge_split_apply, dif_pos rfl] },
  cases H with j H,
  { use j, rwa [merge_split_apply, dif_neg j.prop, subtype.coe_eta] },
end

end

end cube

/-- Paths fixed at both ends -/
abbreviation loop_space (X : Type*) [topological_space X] (x : X) := path x x
local notation `Ω` := loop_space

instance loop_space.inhabited : inhabited (Ω X x) := ⟨path.refl x⟩

/-- The `n`-dimensional generalized loops; functions `I^n → X` fixed at the boundary. -/
def gen_loop (N) (x : X) : set C(cube N, X) := {p | ∀ y ∈ cube.boundary N, p y = x}

namespace gen_loop

lemma boundary (f : gen_loop N x) : ∀ y ∈ cube.boundary N, f y = x := f.2

instance fun_like : fun_like (gen_loop N x) (cube N) (λ _, X) :=
{ coe := λ f, f.1,
  coe_injective' := λ ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ h, by { congr, exact h } }

--@[ext] lemma ext (f g : gen_loop N x) (H : ∀ y, f y = g y) : f = g := fun_like.ext f g H
-- just use fun_like.ext ? but it's not labelled @[ext]

@[simp] lemma mk_apply (f : C(cube N, X)) (H y) : (⟨f, H⟩ : gen_loop N x) y = f y := rfl

-- lemma congr' (f : gen_loop N x) (s t : cube N) : s = t → f s = f t := λ H, by rw H
-- just use congr_arg?

/-- The constant `gen_loop` at `x`. -/
def const : gen_loop N x := ⟨continuous_map.const _ x, λ _ _, rfl⟩

@[simp] lemma const_eq {t} : (@const X _ N x) t = x := rfl

instance inhabited : inhabited (gen_loop N x) := ⟨const⟩

/-- The "homotopy relative to boundary" relation between `gen_loop`s. -/
def homotopic (f g : gen_loop N x) : Prop := f.1.homotopic_rel g.1 (cube.boundary N)

namespace homotopic
section
variables {f g h : gen_loop N x}

@[refl] lemma refl (f : gen_loop N x) : homotopic f f := continuous_map.homotopic_rel.refl _

@[symm] lemma symm (H : homotopic f g) : homotopic g f := H.symm

@[trans] lemma trans (H0 : homotopic f g) (H1 : homotopic g h) : homotopic f h := H0.trans H1

lemma equiv : equivalence (@homotopic X _ N x) :=
⟨homotopic.refl, λ _ _, homotopic.symm, λ _ _ _, homotopic.trans⟩

instance setoid (N) (x : X) : setoid (gen_loop N x) := ⟨homotopic, equiv⟩

end
end homotopic

section
--variables (i j : fin (n+1))
variable [decidable_eq N]

/-- Path from a generalized loop by `insert`-ing into `I^(n+1)`. -/
@[simps] def to_path (i : N) : gen_loop N x → Ω (gen_loop {j // j ≠ i} x) const := λ p,
{ to_fun := λ t, ⟨(p.val.comp (merge_split I i).to_continuous_map).curry t,
    λ y yH, p.property (merge_split I i (t, y)) (cube.insert_boundary i $ or.inr yH)⟩,
  continuous_to_fun := by continuity,
  source' := by { ext t, refine p.property (merge_split I i (0, t)) ⟨i, or.inl _⟩, simp },
  target' := by { ext t, refine p.property (merge_split I i (1, t)) ⟨i, or.inr _⟩, simp } }


/-- Generalized loop from a path by `extrac`-ing of `I×I^n`. -/
@[simps] def from_path (i : N) : Ω (gen_loop {j // j ≠ i} x) const → gen_loop N x :=
λ p, ⟨(⟨λ t, (p t).1, by continuity⟩ : C(I, C(cube _, X))).uncurry.comp
  (merge_split I i).symm.to_continuous_map,
begin
  rintros y ⟨j, Hj⟩,
  simp only [subtype.val_eq_coe, continuous_map.comp_apply, homeomorph.to_continuous_map_apply,
    merge_split_symm_apply, continuous_map.uncurry_apply, continuous_map.coe_mk,
    function.uncurry_apply_pair],
  by_cases Heq : j = i,
  { subst Heq, cases Hj; rw Hj; simp only [p.source, p.target]; convert const_eq },
  { exact gen_loop.boundary _ _ ⟨⟨j, Heq⟩, Hj⟩ },
end⟩

lemma from_to (i : N) (p : gen_loop N x) : from_path i (to_path i p) = p :=
by { ext, exact congr_arg p (equiv.apply_symm_apply _ _) }

lemma to_from (i : N) (p : Ω (gen_loop {j // j ≠ i} x) const) : to_path i (from_path i p) = p :=
begin
  ext1, ext1, ext1,
  simp only [subtype.val_eq_coe, to_path_apply_coe, from_path_coe, continuous_map.comp_assoc],
  rw [symm_comp_to_continuous_map, continuous_map.comp_id], ext, refl,
end
/-begin
  ext,
  simp only [subtype.val_eq_coe, to_path_apply_coe, from_path_coe,
    continuous_map.curry_apply, continuous_map.comp_apply, homeomorph.to_continuous_map_apply,
    merge_split_symm_apply, merge_split_apply, dif_pos, subtype.coe_eta, dite_eq_ite,
    continuous_map.uncurry_apply, continuous_map.coe_mk, function.uncurry_apply_pair],
  congr, ext j, rw if_neg j.prop,
end-/

/-- The (n+1)-dimensional loops are isomorphic to the loop space at `const`.-/
def path_equiv (i : N) : gen_loop N x ≃ Ω (gen_loop {j // j ≠ i} x) const :=
{ to_fun := to_path i,
  inv_fun := from_path i,
  left_inv := from_to i,
  right_inv := to_from i }

lemma to_path_apply (i : N) {p : gen_loop N x} {t} {tn} :
  to_path i p t tn = p (merge_split I i ⟨t, tn⟩) := rfl

lemma from_path_apply (i : N) {p : Ω (gen_loop {j // j ≠ i} x) const} {t : cube N} :
  from_path i p t = p (t i) ((merge_split I i).symm t).snd := rfl

end

section

lemma uncurry_helper (f : C(I, C(I, C(cube N, X)))) (t y) : f.uncurry t y = f t.fst t.snd y := rfl

/- ! Generalize to any three spaces and move to topology.compact_open -/
/-- Currying as a continuous map.-/
abbreviation c_currying : C(C(I × cube N, X), C(I, C(cube N, X))) :=
⟨continuous_map.curry, continuous_map.continuous_curry⟩

/-- Uncurrying as a continuous map.-/
abbreviation c_uncurrying : C(C(I, C(cube N, X)), C(I × cube N, X)) :=
⟨continuous_map.uncurry, continuous_map.continuous_uncurry⟩

/--Coercion as a continuous map.-/
abbreviation c_coe : C(gen_loop N x, C(cube N, X)) := ⟨λ p, p.val, continuous_induced_dom⟩

variable [decidable_eq N]

/-- Composition with insert as a continuous map.-/
abbreviation c_comp_insert (i : N) : C(C(cube N, X), C(I × cube {j // j ≠ i}, X)) :=
⟨λ f, f.comp (merge_split I i).to_continuous_map,
  (merge_split I i).to_continuous_map.continuous_comp_left⟩

@[simps] def homotopy_to (i : N) {p q : gen_loop N x} (H : p.1.homotopy_rel q.1 (cube.boundary N)) :
  C(I × I, C(cube {j // j ≠ i}, X)) :=
(c_currying.comp ((c_comp_insert i).comp H.to_continuous_map.curry)).uncurry

lemma homotopic_to (i : N) {p q : gen_loop N x} :
  homotopic p q → (to_path i p).homotopic (to_path i q) :=
begin
  apply nonempty.map, rintros H,
  refine
  ⟨⟨⟨λ t, ⟨homotopy_to i H t, _⟩,_⟩, _, _⟩, _⟩,
  { rintros y ⟨i,iH⟩,
    rw homotopy_to_apply_apply, rw H.eq_fst, rw p.2,
    all_goals { apply cube.insert_boundary, right, exact ⟨i,iH⟩} },
  { continuity },
  show ∀ _ _ _, _,
  { intros t y yH,
    split; ext; erw homotopy_to_apply_apply,
    apply H.eq_fst, work_on_goal 2 { apply H.eq_snd },
    all_goals { use i, rw merge_split_self, exact yH } },
  all_goals { intro, ext, erw [homotopy_to_apply_apply, to_path_apply] },
  exacts [H.apply_zero _, H.apply_one _],
end

@[simps] def homotopy_from (i : N) {p q : gen_loop N x}
  (H : (to_path i p).homotopy (to_path i q)) : C(I × cube N, X) :=
(c_uncurrying.comp (c_coe.comp H.to_continuous_map).curry).uncurry.comp $
  (continuous_map.id I).prod_map (merge_split I i).symm.to_continuous_map

lemma homotopic_from (i : N) {p q : gen_loop N x} :
  (to_path i p).homotopic (to_path i q) → homotopic p q :=
begin
  apply nonempty.map, rintros H,
  refine ⟨⟨homotopy_from i H, _, _⟩, _⟩,
  show ∀ _ _ _, _,
  { rintros t y ⟨j, jH⟩, erw homotopy_from_apply,
    obtain rfl | h := eq_or_ne j i,
    { split,
      { rw H.eq_fst, exacts [congr_arg p (equiv.apply_symm_apply _ _), jH] },
      { rw H.eq_snd, exacts [congr_arg q (equiv.apply_symm_apply _ _), jH] } },
    { rw [p.2 _ ⟨j, jH⟩, q.2 _ ⟨j, jH⟩], split; { apply boundary, exact ⟨⟨j, h⟩, jH⟩ } } },
  all_goals { intro, convert homotopy_from_apply _ _ _,
    rw H.apply_zero <|> rw H.apply_one,
    apply congr_arg p <|> apply congr_arg q,
    exact (equiv.apply_symm_apply _ _).symm },
end


/-- Concatenation of `gen_loop`s by transitivity as paths -/
def concat_ (i : N) (p q : gen_loop N x) : gen_loop N x :=
from_path i ((to_path i p).trans (to_path i q))

lemma concat_to_trans (i : N) (p q : gen_loop N x) :
  to_path i (concat_ i p q) = (to_path i p).trans (to_path i q) :=
by { unfold concat_, rw to_from }

lemma const_to_refl (i : N) : to_path i (@const _ _ N x) = path.refl (@const _ _ _ x) :=
begin
  ext, unfold const to_path,
  simpa only [continuous_map.const_comp, path.coe_mk, mk_apply, continuous_map.curry_apply,
    continuous_map.const_apply, path.refl_apply, const_eq],
end

end

end gen_loop

/-- The `n`th homotopy group at `x` defined as the quotient of `gen_loop n x` by the
  `homotopic` relation. -/
@[derive inhabited]
def homotopy_group (N) (x : X) : Type _ :=
quotient (gen_loop.homotopic.setoid N x)
abbreviation pi (n) (x : X) := homotopy_group (fin n) x
local notation `π_` := pi

variable [decidable_eq N]
open gen_loop
def homotopy_group_equiv_fundamental_group (i : N) :
  homotopy_group N x ≃ fundamental_group (gen_loop {j // j ≠ i} x) gen_loop.const :=
begin
  refine equiv.trans _ (category_theory.groupoid.iso_equiv_hom _ _).symm,
  apply quotient.congr ⟨to_path i, from_path i, from_to i, to_from i⟩,
  exact λ p q, ⟨homotopic_to i, homotopic_from i⟩,
end


namespace homotopy_group

/-- The 0-dimensional generalized loops based at `x` are in 1-1 correspondence with `X`. -/
def gen_loop_zero_equiv : gen_loop (fin 0) x ≃ X :=
{ to_fun := λ f, f 0,
  inv_fun := λ x, ⟨continuous_map.const _ x, λ _ ⟨f0,_⟩, f0.elim0⟩,
  left_inv := λ f, by { ext1, ext1, exact congr_arg f (subsingleton.elim _ _) },
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
@[simps] def gen_loop_one_equiv_path_self : gen_loop (fin 1) x ≃ Ω X x :=
{ to_fun := λ p, path.mk ⟨λ t, p (λ _, t), by continuity⟩
    (gen_loop.boundary p (λ _, 0) ⟨0, or.inl rfl⟩)
    (gen_loop.boundary p (λ _, 1) ⟨1, or.inr rfl⟩),
  inv_fun := λ p,
  begin
    refine ⟨⟨λ (c : I^1), p c.head, by continuity⟩, _⟩,
    rintro y ⟨i, iH|iH⟩; cases unique.eq_default i;
    apply (congr_arg p iH).trans, exacts [p.source, p.target],
  end,
  left_inv := λ p, by { ext, exact congr_arg p a.one_char.symm },
  right_inv := λ p, by { ext, refl } }

/-- The first homotopy group at `x` is equivalent to the fundamental group, i.e. the loops based at
  `x` up to homotopy. -/
-- deduce from homotopy_group_equiv_fundamental_group?
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

section
variables {n : ℕ} (i : fin (n+1))
/--Equivalence class of the constant `gen_loop`.-/
def const : π_ n x := quotient.mk' gen_loop.const

instance is_group : group (π_(n+1) x) :=
(homotopy_group_equiv_fundamental_group 0).group

def aux_group : group (π_(n+2) x) :=
(homotopy_group_equiv_fundamental_group 1).group

lemma ite_ite {α} (a b c : α) (j : fin (n+2)) :
  (if j = 0 then a else if j = 1 then b else c) =
  if j = 1 then b else if j = 0 then a else c :=
by { split_ifs with h₀ h₁, { subst h₀, cases h₁ }, all_goals { refl } }

open unit_interval
lemma path_trans_to_path {p q : gen_loop N x} (i : N) {t tn} :
  (to_path i p).trans (to_path i q) t tn =
  if h : (t : ℝ) ≤ 1/2
  then p (λ j, if hj : j = i then
    ⟨2 * t, (mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩ else tn ⟨j, hj⟩)
  else q (λ j, if hj : j = i then
    ⟨2 * t - 1, two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩ else tn ⟨j, hj⟩) :=
by { rw path.trans_apply, split_ifs; refl }


@[reducible] def is_comm_group : comm_group (π_(n+2) x) :=
@eckmann_hilton.comm_group (π_(n+2) x) aux_group.mul 1
  ⟨⟨λ _, by apply aux_group.one_mul⟩, ⟨λ _, by apply aux_group.mul_one⟩⟩ _ $
begin
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩, apply congr_arg quotient.mk,
  ext, erw [path_trans_to_path, path_trans_to_path],
  simp only [homeomorph.to_continuous_map_apply,
    merge_split_symm_apply, equiv.coe_fn_mk, equiv.coe_fn_symm_mk],
  split_ifs with h₁ h₀ h₀;
  { simp only [from_path_apply, path_trans_to_path,
      dif_neg fin.zero_ne_one, dif_neg fin.zero_ne_one.symm],
  erw dif_neg h₁ <|> erw dif_pos h₁, erw dif_neg h₀ <|> erw dif_pos h₀,
  congr' 1, ext1 j, simp_rw [merge_split_symm_apply, subtype.coe_mk, dite_eq_ite], apply ite_ite },
end

instance has_one : has_one (π_ n x) := ⟨const⟩
instance has_zero : has_zero (π_ n x) := ⟨const⟩

/--Concatenation of equivalence clasess along the `i`th component.-/
def concat (i : fin (n+1)) : π_(n+1) x → π_(n+1) x → π_(n+1) x :=
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

/-- Concatenation forms a group.-/
@[reducible] def is_group : group (π_(n+1) x) :=
{ mul := concat 0, mul_assoc := concat_assoc 0,
  one := const, one_mul := const_concat 0, mul_one := concat_const 0,
  inv := reverse 0,
  div := λ a b, a*(b⁻¹), div_eq_mul_inv := λ _ _, rfl,
  mul_left_inv := reverse_concat 0 }

instance : group (π_(n+1) x) := is_group

lemma is_unital : @eckmann_hilton.is_unital (π_(n+2) x) (+) 1 :=
⟨⟨const_concat 1⟩,⟨concat_const 1⟩⟩

/-- Commutativity of horizontal concatenation is shown by
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
