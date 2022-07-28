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

-- TODO : move to topology.subset_properties near is_compact_univ_pi
instance {ι : Type*} {π : ι → Type*} [Π i, topological_space (π i)] [∀ i, compact_space (π i)]
  [∀ i, locally_compact_space (π i)] : locally_compact_space (Π i, π i) :=
⟨λ t n hn, begin
  rw [nhds_pi, filter.mem_pi] at hn,
  obtain ⟨s, hs, n', hn', hsub⟩ := hn,
  choose n'' hn'' hsub' hc using λ i, locally_compact_space.local_compact_nhds (t i) (n' i) (hn' i),
  use s.pi n'', rw set_pi_mem_nhds_iff hs,
  refine ⟨λ i _, hn'' i, subset_trans (λ _, _) hsub, _⟩,
  { refine forall₂_imp (λ i _, _), apply hsub' },
  { classical, rw ← set.univ_pi_ite, apply is_compact_univ_pi,
    intro i, by_cases i ∈ s, { rw if_pos h, apply hc },
    { rw if_neg h, exact compact_space.compact_univ } },
end⟩

section merge_split

variables (Y : Type*) [topological_space Y]

lemma symm_comp_to_continuous_map (f : X ≃ₜ Y) :
  f.symm.to_continuous_map.comp f.to_continuous_map = continuous_map.id X :=
by { ext, apply f.to_equiv.symm_apply_apply }
-- TODO: move to the end of topology.continuous_function.basic and add the swapped version.

variable [decidable_eq N]

@[simps] def merge_split_equiv (i : N) : Y × ({j // j ≠ i} → Y) ≃ (N → Y) :=
-- maybe use (n : N) everywhere? use (n : ℕ) only in the final section?
{ to_fun := λ y j, if h : j = i then y.1 else y.2 ⟨j, h⟩,
  inv_fun := λ f, ⟨f i, λ j, f j⟩,
  left_inv := λ y, by { ext; dsimp only, { rw dif_pos rfl }, { rw [dif_neg x.prop,
    subtype.coe_eta] } },
  right_inv := λ y, by { ext j, dsimp only, split_ifs, { rw h }, { refl } } }
-- TODO: move to logic.equiv.basic around equiv.pi_option_equiv_prod
-- should it be generalized to a type family like equiv.pi_option_equiv_prod?
-- (may cause some unification issue when applied to a const family, but usually tolerable)
-- squeeze dsimp ..
-- What's a more descriptive name? Maybe equiv.prod_pi_erase_equiv_pi?

@[simps] def merge_split (i : N) : Y × ({j // j ≠ i} → Y) ≃ₜ (N → Y) :=
{ to_equiv := merge_split_equiv Y i,
  continuous_to_fun := continuous_pi $ λ j, by { dsimp, split_ifs,
    exacts [continuous_fst, (continuous_apply _).comp continuous_snd] },
  continuous_inv_fun := (continuous_apply i).prod_mk (continuous_pi $ λ j, continuous_apply j) }
-- TODO: move to topology.homeomorph, maybe below homeomorph.fin_two_arrow
-- homeomorph.prod_pi_erase_equiv_pi? generalize to family of spaces like homeomorph.pi_fin_two?

@[simp] def merge_split_self (i : N) {t} : merge_split Y i t i = t.1 := by exact dif_pos rfl
-- remove `by exact` -> get strange class synthesized not defeq error

end merge_split

/-- The `n`-dimensional cube. -/
@[derive [has_zero, has_one, topological_space]]
def cube (N : Type*) := N → I
local notation `I^` n := cube (fin n)

namespace cube

instance compact_space : compact_space (cube N) :=
by { convert pi.compact_space, intro, apply_instance }
/- The problem is that Lean can't synthesize `N → compact_space I` even if it knows the instance
  `compact_space I`. Can Lean 3 be made automatically infer these? What about Lean 4? -/
instance locally_compact_space : locally_compact_space (cube N) :=
by convert pi.locally_compact_space; intro; apply_instance

/-- The points of the `n`-dimensional cube with at least one projection equal to 0 or 1. -/
def boundary (N) : set (cube N) := {y | ∃ i, y i = 0 ∨ y i = 1}

variable {n : ℕ}
/-- The first projection of a positive-dimensional cube. -/
@[simps] def head : C(I^(n+1), I) := ⟨λ t, t 0, continuous_apply 0⟩ --proj 0

instance unique_cube0 : unique (I^0) := pi.unique_of_is_empty _

lemma one_char (f : I^1) : f = λ _, f 0 := eq_const_of_unique f


section
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

@[ext] lemma ext (f g : gen_loop N x) (H : ∀ y, f y = g y) : f = g := fun_like.ext f g H
-- using fun_like.ext is cumbersome as it's not labelled @[ext]

@[simp] lemma mk_apply (f : C(cube N, X)) (H y) : (⟨f, H⟩ : gen_loop N x) y = f y := rfl

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

lemma to_from (i : N) (p : Ω (gen_loop {j // j ≠ i} x) const) : to_path i (from_path i p) = p :=
begin
  simp_rw [to_path, from_path, continuous_map.comp_assoc,
    symm_comp_to_continuous_map, continuous_map.comp_id], ext, refl,
end

/-- The (n+1)-dimensional loops are isomorphic to the loop space at `const`.-/
@[simps] def path_equiv (i : N) : gen_loop N x ≃ Ω (gen_loop {j // j ≠ i} x) const :=
{ to_fun := to_path i,
  inv_fun := from_path i,
  left_inv := λ p, by { ext, exact congr_arg p (equiv.apply_symm_apply _ _) },
  right_inv := to_from i }

lemma to_path_apply (i : N) {p : gen_loop N x} {t} {tn} :
  to_path i p t tn = p (merge_split I i ⟨t, tn⟩) := rfl

lemma from_path_apply (i : N) {p : Ω (gen_loop {j // j ≠ i} x) const} {t : cube N} :
  from_path i p t = p (t i) ((merge_split I i).symm t).snd := rfl

end

section

/--Coercion as a continuous map.-/
abbreviation c_coe : C(gen_loop N x, C(cube N, X)) := ⟨λ p, p.val, continuous_induced_dom⟩

variable [decidable_eq N]

/-- Composition with insert as a continuous map.-/
abbreviation c_comp_insert (i : N) : C(C(cube N, X), C(I × cube {j // j ≠ i}, X)) :=
⟨λ f, f.comp (merge_split I i).to_continuous_map,
  (merge_split I i).to_continuous_map.continuous_comp_left⟩

@[simps] def homotopy_to (i : N) {p q : gen_loop N x} (H : p.1.homotopy_rel q.1 (cube.boundary N)) :
  C(I × I, C(cube {j // j ≠ i}, X)) :=
((⟨_, continuous_map.continuous_curry⟩: C(_,_)).comp $
  (c_comp_insert i).comp H.to_continuous_map.curry).uncurry

lemma homotopic_to (i : N) {p q : gen_loop N x} :
  homotopic p q → (to_path i p).homotopic (to_path i q) :=
begin
  refine nonempty.map (λ H, ⟨⟨⟨λ t, ⟨homotopy_to i H t, _⟩, _⟩, _, _⟩, _⟩),
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
((⟨_,continuous_map.continuous_uncurry⟩ : C(_,_)).comp
  (c_coe.comp H.to_continuous_map).curry).uncurry.comp $
    (continuous_map.id I).prod_map (merge_split I i).symm.to_continuous_map

lemma homotopic_from (i : N) {p q : gen_loop N x} :
  (to_path i p).homotopic (to_path i q) → homotopic p q :=
begin
  refine nonempty.map (λ H, ⟨⟨homotopy_from i H, _, _⟩, _⟩),
  show ∀ _ _ _, _,
  { rintros t y ⟨j, jH⟩, erw homotopy_from_apply,
    obtain rfl | h := eq_or_ne j i,
    { split,
      { rw H.eq_fst, exacts [congr_arg p (equiv.apply_symm_apply _ _), jH] },
      { rw H.eq_snd, exacts [congr_arg q (equiv.apply_symm_apply _ _), jH] } },
    { rw [p.2 _ ⟨j, jH⟩, q.2 _ ⟨j, jH⟩], split; { apply boundary, exact ⟨⟨j, h⟩, jH⟩ } } },
  all_goals { intro,
    convert homotopy_from_apply _ _ _,
    rw H.apply_zero <|> rw H.apply_one,
    apply congr_arg p <|> apply congr_arg q,
    exact (equiv.apply_symm_apply _ _).symm },
end
-- above proofs: still room for golfing?

end

end gen_loop

/-- The `n`th homotopy group at `x` defined as the quotient of `gen_loop n x` by the
  `homotopic` relation. -/
@[derive inhabited]
def homotopy_group (N) (X : Type*) [topological_space X] (x : X) : Type _ :=
quotient (gen_loop.homotopic.setoid N x)
abbreviation pi (n) (X : Type*) [topological_space X] (x : X) := homotopy_group (fin n) _ x
-- TODO: Maybe switch these two names
local notation `π_` := pi

variable [decidable_eq N]
open gen_loop
def homotopy_group_equiv_fundamental_group (i : N) :
  homotopy_group N X x ≃ fundamental_group (gen_loop {j // j ≠ i} x) gen_loop.const :=
begin
  refine equiv.trans _ (category_theory.groupoid.iso_equiv_hom _ _).symm,
  apply quotient.congr (path_equiv i),
  exact λ p q, ⟨homotopic_to i, homotopic_from i⟩,
end

namespace homotopy_group

/-- The 0-dimensional generalized loops based at `x` are in 1-1 correspondence with `X`. -/
def gen_loop_zero_equiv : gen_loop (fin 0) x ≃ X :=
{ to_fun := λ f, f 0,
  inv_fun := λ x, ⟨continuous_map.const _ x, λ _ ⟨f0,_⟩, f0.elim0⟩,
  left_inv := λ f, by { ext, exact congr_arg f (subsingleton.elim _ _) },
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
  left_inv := λ p, by { ext, exact congr_arg p y.one_char.symm },
  right_inv := λ p, by { ext, refl } }

/-- The first homotopy group at `x` is equivalent to the fundamental group, i.e. the loops based at
  `x` up to homotopy. -/
-- TODO: deduce from homotopy_group_equiv_fundamental_group?
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
      prop' := λ t y iH, H.prop' _ _ ⟨0, iH⟩ }⟩,
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

instance is_group : group (π_(n+1) X x) :=
(homotopy_group_equiv_fundamental_group 0).group

def aux_group : group (π_(n+2) X x) :=
(homotopy_group_equiv_fundamental_group 1).group

instance add_group : add_group (additive $ π_(n+2) X x) := additive.add_group

lemma ite_ite {α} (a b c : α) (j : fin (n+2)) :
  (if j = 0 then a else if j = 1 then b else c) =
  if j = 1 then b else if j = 0 then a else c :=
by { split_ifs with h₀ h₁, { subst h₀, cases h₁ }, all_goals { refl } }

lemma from_path_trans_to_path {p q : gen_loop N x} (i : N) {t} :
  (path_equiv i).symm ((path_equiv i p).trans $ path_equiv i q) t = if (t i : ℝ) ≤ 1/2
    then p (λ j, if j = i then set.proj_Icc 0 1 zero_le_one (2 * t i) else t j)
    else q (λ j, if j = i then set.proj_Icc 0 1 zero_le_one (2 * t i - 1) else t j) :=
by { dsimp [path.trans, from_path], split_ifs; refl }

/-- Characterization for the multiplication on gen_loop;
  do the same for const/base point (easy) and reverse/path.symm? -/
lemma mul_spec {p q : gen_loop (fin (n+1)) x} :
  ∃ r, (⟦p⟧ * ⟦q⟧ : π_(n+1) X x) = ⟦r⟧ ∧ ∀ t, r t = if (t 0 : ℝ) ≤ 1/2
    then q (λ j, if j = 0 then set.proj_Icc 0 1 zero_le_one (2 * t 0) else t j)
    else p (λ j, if j = 0 then set.proj_Icc 0 1 zero_le_one (2 * t 0 - 1) else t j) :=
⟨_, rfl, λ _, from_path_trans_to_path 0⟩

@[reducible] def is_comm_group : comm_group (π_(n+2) x) :=
@eckmann_hilton.comm_group (π_(n+2) X x) aux_group.mul 1
  ⟨⟨λ _, by apply aux_group.one_mul⟩, ⟨λ _, by apply aux_group.mul_one⟩⟩ _
begin
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩, apply congr_arg quotient.mk,
  simp only [equiv.coe_fn_mk, equiv.coe_fn_symm_mk],
  ext, iterate 6 { rw from_path_trans_to_path },
  simp_rw [if_neg fin.zero_ne_one, if_neg fin.zero_ne_one.symm],
  split_ifs; { congr, ext1, apply ite_ite },
end

/- sorry warining -/
instance comm_group : comm_group (π_(n+2) X x) := is_comm_group

instance add_comm_group : add_comm_group (additive $ π_(n+2) X x) := additive.add_comm_group

end

end homotopy_group
