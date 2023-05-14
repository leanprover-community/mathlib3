/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/

import algebraic_topology.fundamental_groupoid.fundamental_group
import group_theory.eckmann_hilton
import logic.equiv.transfer_instance
import algebra.group.ext

/-!
# `n`th homotopy group

We define the `n`th homotopy group at `x`, `π_n x`, as the equivalence classes
of functions from the nth dimensional cube to the topological space `X`
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are generalized loops `gen_loop n x`, in particular
`gen_loop 1 x ≃ path x x`

We show that `π_0 x` is equivalent to the path-conected components, and
that `π_1 x` is equivalent to the fundamental group at `x`.
We give a group instance using path composition and show commutativity when `n > 1`.

## definitions

* `gen_loop n x` is the type of continous fuctions `I^n → X` that send the boundary to `x`,
* `homotopy_group n x` denoted `π_ n x` is the quotient of `gen_loop n x` by homotopy relative
  to the boundary,
* group instance `group (π_(n+1) x)`,
* commutative group instance `comm_group (π_(n+2) x)`.

TODO:
* Path-induced homomorphisms. Show that `pi1_equiv_fundamental_group` is a group isomorphism.
* Examples with `𝕊^n (π_n (𝕊^n) = ℤ`, `π_m (𝕊^n)` trivial for `m < n`.
* Actions of π_1 on π_n.
* Group (up to homotopy) of Ω.
* Lie algebra: `⁅π_(n+1), π_(m+1)⁆` contained in `π_(n+m+1)`.

-/

open_locale unit_interval topology
open homeomorph

noncomputable theory

universes u
variables {X : Type u} [topological_space X]
variables {N : Type*} {x : X}

/-- We allow an arbitrary indexing type `N`, not just `fin n`, in the definition of `cube`, so as to
  be able to identify facets of a cube to cubes indexed by subtypes of `N`, which is more
  convenient than using `fin (n-1)`. -/
@[derive [has_zero, has_one, topological_space]]
def cube (N : Type*) := N → I
local notation `I^` n := cube (fin n)

namespace cube

instance compact_space : compact_space (cube N) :=
by { convert pi.compact_space, intro, apply_instance }

instance locally_compact_space : locally_compact_space (cube N) :=
by convert locally_compact_space.pi; intro; apply_instance

/-- The points in a cube with at least one projection equal to 0 or 1. -/
def boundary (N) : set (cube N) := {y | ∃ i, y i = 0 ∨ y i = 1}

variable {n : ℕ}
/-- The first projection of a positive-dimensional cube. -/
@[simps] def head : C(I^(n+1), I) := ⟨λ t, t 0, continuous_apply 0⟩

instance unique_cube0 : unique (I^0) := pi.unique_of_is_empty _

lemma one_char (f : I^1) : f = λ _, f 0 := eq_const_of_unique f

section
variable [decidable_eq N]

/-- The forward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$. -/
@[reducible] def split_at (i : N) : cube N ≃ₜ I × cube {j // j ≠ i} := fun_split_at I i

/-- The backward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$. -/
@[reducible] def insert_at (i : N) : I × cube {j // j ≠ i} ≃ₜ cube N := (fun_split_at I i).symm

lemma insert_at_boundary (i : N) {t₀ : I} {t} (H : (t₀ = 0 ∨ t₀ = 1) ∨ t ∈ boundary {j // j ≠ i}) :
  insert_at i ⟨t₀, t⟩ ∈ boundary N :=
begin
  obtain H | ⟨j, H⟩ := H,
  { use i, rwa [fun_split_at_symm_apply, dif_pos rfl] },
  { use j, rwa [fun_split_at_symm_apply, dif_neg j.prop, subtype.coe_eta] },
end

end

end cube

/-- The space of paths with both endpoints equal to a specified point `x : X`. -/
@[reducible] def loop_space (X : Type*) [topological_space X] (x : X) := path x x
local notation `Ω` := loop_space

/-- The `n`-dimensional generalized loops based at `x` in a space `X` are
  continuous functions `I^n → X` that sends the boundary to `x`.
  We allow an arbitrary indexing type `N` in place of `fin n` here. -/
def gen_loop (N) (x : X) : set C(cube N, X) := {p | ∀ y ∈ cube.boundary N, p y = x}

namespace gen_loop

/-- Copy of a `gen_loop` with a new map from the unit cube equal to the old one.
  Useful to fix definitional equalities. -/
def copy (f : gen_loop N x) (g : cube N → X) (h : g = f) : gen_loop N x :=
⟨⟨g, h.symm ▸ f.1.2⟩, by { convert f.2, ext1, simp_rw h, refl }⟩

lemma coe_copy (f : gen_loop N x) {g : cube N → X} (h : g = f) : ⇑(copy f g h) = g := rfl

lemma copy_eq (f : gen_loop N x) {g : cube N → X} (h : g = f) : copy f g h = f :=
by { ext x, exact congr_fun h x }

lemma boundary (f : gen_loop N x) : ∀ y ∈ cube.boundary N, f y = x := f.2

instance fun_like : fun_like (gen_loop N x) (cube N) (λ _, X) :=
{ coe := λ f, f.1,
  coe_injective' := λ ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ h, by { congr, exact h } }

@[ext] lemma ext (f g : gen_loop N x) (H : ∀ y, f y = g y) : f = g :=
fun_like.coe_injective' (funext H)

@[simp] lemma mk_apply (f : C(cube N, X)) (H y) : (⟨f, H⟩ : gen_loop N x) y = f y := rfl

/-- The constant `gen_loop` at `x`. -/
def const : gen_loop N x := ⟨continuous_map.const _ x, λ _ _, rfl⟩

@[simp] lemma const_apply {t} : (@const X _ N x) t = x := rfl

instance inhabited : inhabited (gen_loop N x) := ⟨const⟩

/-- The "homotopic relative to boundary" relation between `gen_loop`s. -/
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

/-- Loop from a generalized loop by currying $I^N → X$ into $I → (I^{N\setminus\{j\}} → X)$. -/
@[simps] def to_loop (i : N) : gen_loop N x → Ω (gen_loop {j // j ≠ i} x) const := λ p,
{ to_fun := λ t, ⟨(p.val.comp (cube.insert_at i).to_continuous_map).curry t,
    λ y yH, p.property (cube.insert_at i (t, y)) (cube.insert_at_boundary i $ or.inr yH)⟩,
  source' := by { ext t, refine p.property (cube.insert_at i (0, t)) ⟨i, or.inl _⟩, simp },
  target' := by { ext t, refine p.property (cube.insert_at i (1, t)) ⟨i, or.inr _⟩, simp } }

/-- Generalized loop from a loop by uncurrying $I → (I^{N\setminus\{j\}} → X)$ into $I^N → X$. -/
@[simps] def from_loop (i : N) (p : Ω (gen_loop {j // j ≠ i} x) const) : gen_loop N x :=
⟨(⟨λ t, (p t).1, by continuity⟩ : C(I, C(cube _, X))).uncurry.comp
  (cube.split_at i).to_continuous_map,
begin
  rintros y ⟨j, Hj⟩,
  simp only [subtype.val_eq_coe, continuous_map.comp_apply, to_continuous_map_apply,
    fun_split_at_apply, continuous_map.uncurry_apply, continuous_map.coe_mk,
    function.uncurry_apply_pair],
  obtain rfl | Hne := eq_or_ne j i,
  { cases Hj; rw Hj; simp only [p.source, p.target]; convert const_apply },
  { exact gen_loop.boundary _ _ ⟨⟨j, Hne⟩, Hj⟩ },
end⟩

lemma to_from (i : N) (p : Ω (gen_loop {j // j ≠ i} x) const) : to_loop i (from_loop i p) = p :=
begin
  simp_rw [to_loop, from_loop, continuous_map.comp_assoc, to_continuous_map_as_coe,
    to_continuous_map_comp_symm, continuous_map.comp_id], ext, refl,
end

/-- The `n+1`-dimensional loops are in bijection with the loops in the space of
  `n`-dimensional loops with base point `const`.
  We allow an arbitrary indexing type `N` in place of `fin n` here. -/
@[simps] def loop_equiv (i : N) : gen_loop N x ≃ Ω (gen_loop {j // j ≠ i} x) const :=
{ to_fun := to_loop i,
  inv_fun := from_loop i,
  left_inv := λ p, by { ext, exact congr_arg p (equiv.apply_symm_apply _ _) },
  right_inv := to_from i }

lemma to_loop_apply (i : N) {p : gen_loop N x} {t} {tn} :
  to_loop i p t tn = p (cube.insert_at i ⟨t, tn⟩) := rfl

lemma from_loop_apply (i : N) {p : Ω (gen_loop {j // j ≠ i} x) const} {t : cube N} :
  from_loop i p t = p (t i) (cube.split_at i t).snd := rfl

end

section

/-- The inclusion from the space of generalized loops to the space of all continuous functions
  (not necessarily constant on the boundary), as a continuous map. -/
@[reducible] def c_coe : C(gen_loop N x, C(cube N, X)) := ⟨λ p, p.val, continuous_induced_dom⟩

variable [decidable_eq N]

/-- Composition with `cube.insert_at` as a continuous map. -/
@[reducible] def c_comp_insert (i : N) : C(C(cube N, X), C(I × cube {j // j ≠ i}, X)) :=
⟨λ f, f.comp (cube.insert_at i).to_continuous_map,
  (cube.insert_at i).to_continuous_map.continuous_comp_left⟩

/-- A homotopy between `n+1`-dimensional loops `p` and `q` constant on the boundary
  seen as a homotopy between two paths in the space of `n`-dimensional paths. -/
@[simps] def homotopy_to (i : N) {p q : gen_loop N x} (H : p.1.homotopy_rel q.1 (cube.boundary N)) :
  C(I × I, C(cube {j // j ≠ i}, X)) :=
((⟨_, continuous_map.continuous_curry⟩: C(_,_)).comp $
  (c_comp_insert i).comp H.to_continuous_map.curry).uncurry

lemma homotopic_to (i : N) {p q : gen_loop N x} :
  homotopic p q → (to_loop i p).homotopic (to_loop i q) :=
begin
  refine nonempty.map (λ H, ⟨⟨⟨λ t, ⟨homotopy_to i H t, _⟩, _⟩, _, _⟩, _⟩),
  { rintros y ⟨i, iH⟩,
    rw homotopy_to_apply_apply, rw H.eq_fst, rw p.2,
    all_goals { apply cube.insert_at_boundary, right, exact ⟨i, iH⟩} },
  { continuity },
  show ∀ _ _ _, _,
  { intros t y yH,
    split; ext; erw homotopy_to_apply_apply,
    apply H.eq_fst, work_on_goal 2 { apply H.eq_snd },
    all_goals { use i, rw [fun_split_at_symm_apply, dif_pos rfl], exact yH } },
  all_goals { intro, ext, erw [homotopy_to_apply_apply, to_loop_apply] },
  exacts [H.apply_zero _, H.apply_one _],
end

/-- The converse to `gen_loop.homotopy_to`: a homotopy between two loops in the space of
  `n`-dimensional loops can be seen as a homotopy between two `n+1`-dimensional paths. -/
@[simps] def homotopy_from (i : N) {p q : gen_loop N x}
  (H : (to_loop i p).homotopy (to_loop i q)) : C(I × cube N, X) :=
((⟨_, continuous_map.continuous_uncurry⟩ : C(_,_)).comp
  (c_coe.comp H.to_continuous_map).curry).uncurry.comp $
    (continuous_map.id I).prod_map (cube.split_at i).to_continuous_map

lemma homotopic_from (i : N) {p q : gen_loop N x} :
  (to_loop i p).homotopic (to_loop i q) → homotopic p q :=
begin
  refine nonempty.map (λ H, ⟨⟨homotopy_from i H, _, _⟩, _⟩),
  show ∀ _ _ _, _,
  { rintros t y ⟨j, jH⟩, erw homotopy_from_apply,
    obtain rfl | h := eq_or_ne j i,
    { split,
      { rw H.eq_fst, exacts [congr_arg p (equiv.right_inv _ _), jH] },
      { rw H.eq_snd, exacts [congr_arg q (equiv.right_inv _ _), jH] } },
    { rw [p.2 _ ⟨j, jH⟩, q.2 _ ⟨j, jH⟩], split; { apply boundary, exact ⟨⟨j, h⟩, jH⟩ } } },
  all_goals { intro,
    convert homotopy_from_apply _ _ _,
    rw H.apply_zero <|> rw H.apply_one,
    apply congr_arg p <|> apply congr_arg q,
    exact (equiv.right_inv _ _).symm },
end

end

end gen_loop

/-- The `n`th homotopy group at `x` defined as the quotient of `gen_loop n x` by the
  `gen_loop.homotopic` relation. -/
@[derive inhabited]
def homotopy_group (N) (X : Type*) [topological_space X] (x : X) : Type _ :=
quotient (gen_loop.homotopic.setoid N x)
/-- Homotopy group of finite index. -/
@[reducible] def pi (n) (X : Type*) [topological_space X] (x : X) := homotopy_group (fin n) _ x
local notation `π_` := pi

variable [decidable_eq N]
open gen_loop
/-- Equivalence between the homotopy group of X and the fundamental group of
  `gen_loop {j // j ≠ i} x`. -/
def homotopy_group_equiv_fundamental_group (i : N) :
  homotopy_group N X x ≃ fundamental_group (gen_loop {j // j ≠ i} x) const :=
begin
  refine equiv.trans _ (category_theory.groupoid.iso_equiv_hom _ _).symm,
  apply quotient.congr (loop_equiv i),
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

/-- The 1-dimensional generalized loops based at `x` are in 1-1 correspondence with loops at `x`. -/
@[simps] def gen_loop_one_equiv_loop : gen_loop (fin 1) x ≃ Ω X x :=
{ to_fun := λ p, path.mk ⟨λ t, p (λ _, t), by continuity⟩
    (gen_loop.boundary _ (λ _, 0) ⟨0, or.inl rfl⟩)
    (gen_loop.boundary _ (λ _, 1) ⟨1, or.inr rfl⟩),
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
  refine quotient.congr gen_loop_one_equiv_loop _,
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
variables {n : ℕ} (i : N)

/-- Group structure on `π_(n+1)`. -/
instance group : group (π_(n+1) X x) :=
(homotopy_group_equiv_fundamental_group 0).group

/-- Group structure on `homotopy_group` obtained by pulling back path composition along the
  `i`th direction. The group structures for two different `i j : N` distribute over each
  other, and therefore are equal by the Eckmann-Hilton argument. When `N = fin (n+1)`,
  the group structure with `i = 0` is taken to be default and registered as an instance above. -/
@[reducible] def aux_group (i : N) : group (homotopy_group N X x) :=
(homotopy_group_equiv_fundamental_group i).group

lemma is_unital_aux_group (i : N) :
  eckmann_hilton.is_unital (aux_group i).mul (⟦const⟧ : homotopy_group N X x) :=
⟨⟨(aux_group i).one_mul⟩, ⟨(aux_group i).mul_one⟩⟩

/-- Concatenation of two `gen_loop`s along the `i`th coordinate. -/
def trans_at (i : N) (f g : gen_loop N x) : gen_loop N x :=
copy ((loop_equiv i).symm ((loop_equiv i f).trans $ loop_equiv i g))
  (λ t, if (t i : ℝ) ≤ 1/2
    then f (function.update t i $ set.proj_Icc 0 1 zero_le_one (2 * t i))
    else g (function.update t i $ set.proj_Icc 0 1 zero_le_one (2 * t i - 1)))
begin
  ext1, symmetry,
  dsimp only [path.trans, from_loop, path.coe_mk, function.comp_app, loop_equiv_symm_apply,
    mk_apply, continuous_map.comp_apply, to_continuous_map_apply, fun_split_at_apply,
    continuous_map.uncurry_apply, continuous_map.coe_mk, function.uncurry_apply_pair],
  split_ifs, change f _ = _, swap, change g _ = _,
  all_goals { congr' 1 }
end

/-- Reversal of a `gen_loop` along the `i`th coordinate. -/
def symm_at (i : N) (f : gen_loop N x) : gen_loop N x :=
copy ((loop_equiv i).symm (loop_equiv i f).symm)
  (λ t, f $ λ j, if j = i then σ (t i) else t j) $
  by { ext1, change _ = f _, congr, ext1, simp }

lemma trans_at_distrib {i j : N} (h : i ≠ j) (a b c d : gen_loop N x) :
  trans_at i (trans_at j a b) (trans_at j c d) = trans_at j (trans_at i a c) (trans_at i b d) :=
begin
  ext, simp_rw [trans_at, coe_copy, function.update_apply, if_neg h, if_neg h.symm],
  split_ifs; { congr' 1, ext1, simp only [function.update, eq_rec_constant, dite_eq_ite],
    apply ite_ite_comm, rintro rfl, exact h.symm },
end

lemma from_loop_trans_to_loop {p q : gen_loop N x} :
  (loop_equiv i).symm ((loop_equiv i p).trans $ loop_equiv i q) = trans_at i p q :=
(copy_eq _ _).symm

lemma from_loop_symm_to_loop {p : gen_loop N x} :
  (loop_equiv i).symm (loop_equiv i p).symm = symm_at i p := (copy_eq _ _).symm

lemma aux_group_indep (i j : N) : (aux_group i : group (homotopy_group N X x)) = aux_group j :=
begin
  by_cases h : i = j, { rw h },
  refine group.ext (eckmann_hilton.mul (is_unital_aux_group i) (is_unital_aux_group j) _),
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩,
  apply congr_arg quotient.mk,
  simp_rw [from_loop_trans_to_loop, trans_at_distrib h],
end

lemma trans_at_indep {i} (j) (f g : gen_loop N x) : ⟦trans_at i f g⟧ = ⟦trans_at j f g⟧ :=
begin
  simp_rw ← from_loop_trans_to_loop,
  have := congr_arg (@group.mul _) (aux_group_indep i j),
  exact congr_fun₂ this ⟦g⟧ ⟦f⟧,
end

lemma symm_at_indep {i} (j) (f : gen_loop N x) : ⟦symm_at i f⟧ = ⟦symm_at j f⟧ :=
begin
  simp_rw ← from_loop_symm_to_loop,
  have := congr_arg (@group.inv _) (aux_group_indep i j),
  exact congr_fun this ⟦f⟧,
end

/-- Characterization of multiplicative identity -/
lemma const_spec : (1 : π_(n+1) X x) = ⟦const⟧ := rfl

/-- Characterization of multiplication -/
lemma mul_spec {i} {p q : gen_loop (fin (n+1)) x} : (⟦p⟧ * ⟦q⟧ : π_(n+1) X x) = ⟦trans_at i q p⟧ :=
by { rw [trans_at_indep 0 q, ← from_loop_trans_to_loop], apply quotient.sound, refl }

/-- Characterization of multiplicative inverse -/
lemma inv_spec {i} {p : gen_loop (fin (n+1)) x} : (⟦p⟧⁻¹ : π_(n+1) X x) = ⟦symm_at i p⟧ :=
by { rw [symm_at_indep 0 p, ← from_loop_symm_to_loop], apply quotient.sound, refl }

/-- Multiplication on `π_(n+2)` is commutative. -/
instance comm_group : comm_group (π_(n+2) X x) :=
@eckmann_hilton.comm_group (π_(n+2) X x) _ 1 (is_unital_aux_group 1) _
begin
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩,
  apply congr_arg quotient.mk,
  simp_rw [from_loop_trans_to_loop, trans_at_distrib fin.zero_ne_one],
end

end

end homotopy_group
