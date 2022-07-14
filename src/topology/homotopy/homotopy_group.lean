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


@[simp] lemma uncurry_apply  {α : Type*} {β : Type*} {γ : Type*}
[topological_space α] [topological_space β] [topological_space γ] [locally_compact_space β]
(f : C(α, C(β, γ))) (a : α) (b : β) : f.uncurry ⟨a, b⟩ = f a b := rfl

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
@[simps] def proj (i : fin n) : C(I^n,I) := ⟨λ t, t i, proj_continuous i⟩

/-- The points of the `n`-dimensional cube with at least one projection equal to 0 or 1. -/
def boundary (n : ℕ) : set (I^n) := {y | ∃ i, y i = 0 ∨ y i = 1}

/-- The first projection of a positive-dimensional cube. -/
@[simps] def head : C(I^(n+1), I) := proj 0

-- @[continuity] lemma head.continuous : continuous (@head n) := proj_continuous 0

/-- The projection to the last `n` coordinates from an `n+1` dimensional cube. -/
@[simps] def tail : C(I^(n+1), I^n) := ⟨λ c, fin.tail c,
  (continuous_map.pi (λ i:fin n, ⟨λ f:I^(n+1), f i.succ, continuous_apply i.succ⟩)).2⟩

@[simp] lemma tail.coe_to_fun : (tail : I^(n+1) → I^n) = fin.tail :=
  by {ext, simp only [tail_to_fun]}

instance unique_cube0 : unique (I^0) := pi.unique_of_is_empty _

lemma one_char (f : I^1) : f = λ _, f 0 := by convert eq_const_of_unique f

/-- Continuous cons map -/
def cons : C(I×I^n, I^(n+1)) :=
{ to_fun := λ t, fin.cons t.fst t.snd,
  continuous_to_fun :=
  begin
    refine (continuous_map.pi (λ i:fin (n+1), ⟨λ t:I×I^n, (fin.cons t.fst t.snd : I^(n+1)) i,_⟩)).2,
    revert i, refine (fin.cases _ _); simp only [fin.cons_zero, fin.cons_succ, auto_param_eq],
    exacts [continuous_fst, λ i, (continuous_map.comp (proj i) ⟨_,continuous_snd⟩).2],
  end }

@[simp] lemma cons_apply (x₀:I) (xn:I^n): cons ⟨x₀,xn⟩ = fin.cons x₀ xn := rfl

/-- Continuous `head`×`tail` map -/
def uncons : C(I^(n+1), I×I^n) :=
continuous_map.prod_mk ⟨head,head.continuous⟩ ⟨tail,tail.continuous⟩

@[simp] lemma uncons_apply (xn:I^(n+1)): uncons xn = ⟨xn.head,xn.tail⟩ := rfl

-- @[simp] lemma unfold_fold (t : I×I^n) : unfold (fold t) = t :=
-- by { rcases t with ⟨t,tn⟩, simp only [fold, unfold, tail, continuous_map.coe_mk,
--   continuous_map.prod_eval, head_to_fun, fin.cons_zero, fin.tail_cons] }

-- @[simp] lemma cons_unfold (t : I^(n+1)) : cons (unfold t) = t :=
-- by simp only [unfold, cons, tail.coe_to_fun, continuous_map.prod_eval, continuous_map.coe_mk,
--   head_to_fun, fin.cons_self_tail]

section
variable (i : fin (n+1))

/-- Continuos "insert" map, in particular `cons_ 0 = cons`. -/
def cons_ (i : fin (n+1)) : C(I×I^n, I^(n+1)):=
begin
  rcases i with ⟨i,iH⟩, revert n iH,
  induction i; intros n iH,
  exact cons,
  cases n, refine ⟨λ t,(λ _, t.fst), by continuity⟩,
  refine (continuous_map.comp _ (i_ih (nat.succ_lt_succ_iff.mp iH)).curry).uncurry,
  refine continuous_map.curry ⟨λ ft, fin.cons ft.snd.head (ft.fst ft.snd.tail), _⟩,
  simp, continuity,
  sorry
end

@[simp] lemma cons_0 : @cons_ n 0 = cons := rfl

@[simp] lemma cons_S {i : ℕ} (H: i.succ < n+2) {H₁: i < n.succ} (t₀) (t : I^(n+1)) :
  cons_ (⟨_,H⟩ : fin _) ⟨t₀,t⟩ = fin.cons t.head (cons_ ⟨_,H₁⟩  ⟨t₀,t.tail⟩) :=
by simp [cons_]

@[simp] lemma cons_S₀ {i : ℕ} {H: i < 1} {H₁: i < n.succ} (t₀) {t : I^0} :
  cons_ (⟨_,H⟩ : fin _) ⟨t₀,t⟩ = λ _, t₀ :=
begin
  cases i, simp [cons_0], ext, revert x, refine (fin.cases _ fin.elim0 ), rw fin.cons_zero,
  exfalso, exact not_lt_zero' (nat.succ_lt_succ_iff.mp H),
end

@[simp] lemma cons_at_eq (t₀:I) (t) : cons_ i ⟨t₀, t⟩ i = t₀ :=
begin
  rcases i with ⟨i,iH⟩, revert n iH,
  induction i; intros n iH t,
  { change (⟨_,iH⟩: fin (n+1)) with (0 : fin (n+1)), rw [cons_0, cons_apply, fin.cons_zero] },
  cases n, exfalso, revert iH, norm_num,
  apply i_ih,
end

@[simp] lemma cons_at_lt (j : fin n) (t₀ t) : ↑j < i → cons_ i ⟨t₀, t⟩ j = t j :=
begin
  intro H,
  rcases i with ⟨i,iH⟩, revert n iH,
  induction i; intros n iH j t H,
  { exfalso, revert H, norm_num },
  cases n, { exfalso, revert iH, norm_num },
  -- revert t₁, refine (fin.cases _ _); intros,
  rw cons_S, show _<_, exact nat.succ_lt_succ_iff.mp iH,
  revert j, refine (fin.cases _ _); intros,
  { have hr : ↑(0 : fin n.succ) = (0 : fin (n+2)) := rfl, rw hr,
    simp only [head_to_fun, fin.cons_zero]},
  -- have hr : ↑(i.succ) = fin.succ (↑i), {apply fin.eq_of_veq,
  -- simp only [fin.val_eq_coe, fin.coe_succ]},
  -- change ↑0 with (0:fin (n+1)),

  -- have h : _ := cons_S ⟨i_n,_⟩ t₀ t,
  -- simp at h,
  -- have hr : (⟨i_n.succ, iH⟩ : fin n+2) = (fin.succ ⟨i_n,_⟩ : fin (n+1)),
  -- { apply fin.eq_of_veq, simp only [fin.succ_mk, fin.val_eq_coe], norm_cast, sorry },
  -- rw [hr, cons_S],
  -- apply i_ih,
  all_goals {sorry}
end

@[simp] lemma cons_at_gt (j : fin n) (t₀ t) : i < j.succ → cons_ i ⟨t₀, t⟩ j.succ = t j :=
begin
  intro H,
  rcases i with ⟨i,iH⟩, revert n iH,
  induction i; intros n iH t₁ t H,
  { simp },
  cases n,
  { exact t₁.elim0 },
  -- have hr : (⟨i_n.succ, iH⟩ : fin (n+2)) = fin.succ ⟨i_n,_⟩ := rfl, rw  hr, rw cons_S,
  -- simp,
  -- cases n, { exfalso, revert iH, norm_num },
  -- have h : _ := cons_S ⟨i_n,_⟩ t₀ t,
  -- simp at h,
  -- have hr : (⟨i_n.succ, iH⟩ : fin n+2) = (fin.succ ⟨i_n,_⟩ : fin (n+1)),
  -- { apply fin.eq_of_veq, simp only [fin.succ_mk, fin.val_eq_coe], norm_cast, sorry },
  -- rw [hr, cons_S],
  -- apply i_ih,
  all_goals {sorry}
end
lemma cons_boundary (t₀:I) (t) : (t₀=0 ∨ t₀=1) ∨ t∈boundary n → cons_ i ⟨t₀, t⟩ ∈ boundary (n+1) :=
begin
  intros H, cases H,
  use i, rwa cons_at_eq,
  rcases H with ⟨j,H⟩,
  by_cases (↑j < i),
  { use j, rwa cons_at_lt, finish },
  use j.succ, rwa cons_at_gt,
  sorry
end

def uncons_ (i : fin (n+1)) : C(I^(n+1), I×I^n) :=
begin
  rcases i with ⟨i,iH⟩, revert n iH,
  induction i; intros n iH,
  exact uncons,
  cases n, refine ⟨λ t, ⟨t.head, fin.elim0⟩, by continuity⟩,
  refine ⟨λ t, _,_⟩,
  let IH := (i_ih (nat.succ_lt_succ_iff.mp iH)) t.tail,
  exact ⟨IH.fst, fin.cons t.head IH.snd⟩,
  simp, continuity,
  all_goals {sorry}
end

@[simp] lemma uncons_0 : @uncons_ n 0 = uncons := rfl

@[simp] lemma uncons_S {i : ℕ} {t} (H : i.succ<n+2) {H₁ : i < n+1} : uncons_ (⟨_,H⟩ : fin _) t =
  ⟨(uncons_⟨_,H₁⟩ t.tail).fst, fin.cons t.head (uncons_⟨_,H₁⟩ t.tail).snd⟩ :=
by simp [uncons_]

lemma uncons_apply' (t) : uncons_ i t = ⟨t i, (uncons_ i t).snd⟩ :=
begin
  rcases i with ⟨i,iH⟩, revert n,
  induction i; intros,
  simp only [fin.mk_zero, uncons_0, uncons_apply, head_to_fun],
  cases n, {exfalso, revert iH, norm_num },
  rw uncons_S,
  simp only [tail.coe_to_fun, prod.mk.inj_iff, eq_self_iff_true, and_true],
  rw i_ih,
  simp only [fin.tail, fin.succ_mk],
  exact nat.succ_lt_succ_iff.mp iH
end

@[simp] lemma uncons_cons (t : I×I^n) : uncons_ i (cons_ i t) = t :=
begin
  rcases i with ⟨i,iH⟩, revert n iH,
  induction i; rintros n iH ⟨t₀,t⟩, simp,
  cases n, exfalso, revert iH, norm_num,
  rw [cons_S, uncons_S],
  simp only [head_to_fun, tail.coe_to_fun, fin.tail_cons, fin.cons_zero, prod.mk.inj_iff],
  rw i_ih,
  simp only [eq_self_iff_true, fin.cons_self_tail, and_self],
  exact nat.succ_lt_succ_iff.mp iH
end

@[simp] lemma cons_uncons (t : I^(n+1)) : cons_ i (uncons_ i t) = t :=
begin
  rcases i with ⟨i,iH⟩, revert n iH,
  induction i; rintros n iH t, simp,
  cases n, exfalso, revert iH, norm_num,
  rw [uncons_S,cons_S],
  simp only [head_to_fun, tail.coe_to_fun, fin.cons_zero, fin.tail_cons, prod.mk.eta],
  rw i_ih,
  simp only [fin.cons_self_tail],
  exact nat.succ_lt_succ_iff.mp iH
end

/-- Product with `I` homeomorphism -/
def fold.homeomorph (i : fin n) : I×I^n ≃ₜ I^(n+1) :=
{ to_fun := cons_ i,
  inv_fun := uncons_ i,
  left_inv := uncons_cons i,
  right_inv := cons_uncons i,
  continuous_to_fun := (cons_ i).2,
  continuous_inv_fun := (uncons_ i).2 }

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
variables (i : fin (n+1))

/-- Path from a generalized loop by `uncons`-ing of `I^(n+1)` -/
def to_path (i : fin (n+1)) : gen_loop (n+1) x → Ω (gen_loop n x) const :=
begin
  rintros ⟨g,gH⟩, refine path.mk ⟨_,_⟩ _ _,
  { intro t, refine ⟨(g.comp (cube.cons_ i)).curry t,_⟩,
    rintros y ⟨j,jH⟩,
    simp only [continuous_map.curry_apply, continuous_map.comp_apply], --cube.fold_apply],
    apply gH, apply cube.cons_boundary, right, exact ⟨j,jH⟩},
  { simp only [auto_param_eq], continuity },
  all_goals {simp only, ext,
    simp only [continuous_map.curry_apply, continuous_map.comp_apply, cube.cons_apply, mk_apply,
      const_eq],
    apply gH, use i },
  left, rw cube.cons_at_eq,
  right, rw cube.cons_at_eq,
end

/-- Generalized loop from a path by `fold`-ing of `I×I^n` -/
def from_path (i : fin (n+1)) : Ω (gen_loop n x) const → gen_loop (n+1) x :=
begin
  rintros ⟨p,H₀,H₁⟩,
  simp only [continuous_map.to_fun_eq_coe] at H₀ H₁,
  refine ⟨(⟨λ t, (p t).1, by continuity⟩ : C(I, C(I^n, X))).uncurry.comp (cube.uncons_ i),_⟩,
  rintros y ⟨j,Hj⟩,
  simp only [subtype.val_eq_coe, continuous_map.comp_apply, cube.uncons_apply, uncurry_apply],
  rcases h : (cube.uncons_ ↑i y) with ⟨t₀, t⟩,
  rw cube.uncons_apply',
  simp only [uncurry_apply, continuous_map.coe_mk],
  by_cases (j=i),
  rw ← h, cases Hj; rw Hj, rw H₀, simp [const], rw H₁, simp [const],
  -- let a := , rw ← a, -- with ⟨⟨t₀, t⟩, H⟩,
  -- simp only [coe_coe, fin.coe_coe_eq_self, set.set_of_eq_eq_singleton', set.mem_singleton_iff] at H, rw ← H,
  -- revert j Hj, refine (fin.cases _ _); intros,
  -- {
  --   simp only [fin.coe_eq_cast_succ],
  --   cases iH; rw iH, rw H₀, exact (@const_eq _ _ n x y.tail),
  --   rw H₁, exact (@const_eq _ _ n x y.tail) },
  apply gen_loop.boundary, --exact ⟨i,iH⟩
  by_cases (j<i),
  use j, sorry,--let i2 :=i.2, norm_num,
  all_goals {sorry}
end

lemma from_to (p : gen_loop (n+1) x) : from_path i (to_path i p) = p :=
begin
  rcases p with ⟨⟨p,Hc⟩,Hb⟩,
  ext,
  unfold to_path, unfold from_path, unfold continuous_map.comp, unfold function.comp,
  unfold continuous_map.curry, unfold continuous_map.uncurry, unfold function.uncurry,
  simp only [continuous_map.coe_mk, subtype.coe_mk],
  unfold continuous_map.curry', unfold function.curry,
  simp only [continuous_map.coe_mk, prod.mk.eta],
  rw cube.cons_uncons
end

lemma to_from (p : Ω (gen_loop n x) const) : to_path i (from_path i p) = p :=
begin
  rcases p with ⟨⟨p,Hc⟩,Hs,Ht⟩,
  ext,
  unfold from_path, unfold to_path, unfold continuous_map.comp, unfold function.comp,
  unfold continuous_map.curry, unfold continuous_map.uncurry, unfold function.uncurry,
  simp only [continuous_map.coe_mk, subtype.val_eq_coe, fin.coe_eq_cast_succ, cube.uncons_cons,
    path.coe_mk, mk_apply],
  unfold continuous_map.curry', unfold function.curry,
  simpa only [continuous_map.coe_mk]
end

/-- Loop space equivalence -/
def path_equiv (i : fin n) : gen_loop (n+1) x ≃ Ω (gen_loop n x) const :=
{ to_fun := to_path i,
  inv_fun := from_path i,
  left_inv := from_to i,
  right_inv := to_from i }

lemma curry_to_path {p : gen_loop (n+1) x} {t} {tn} :
  (p.val) (cube.cons_ i ⟨t, tn⟩) = (to_path i p).to_fun t tn :=
  sorry
--   by {rcases p with ⟨p,pH⟩, unfold to_path, simp only [mk_apply, continuous_map.curry_apply, continuous_map.comp_apply], sorry}

lemma uncurry_helper (f : C(I, C(I, C(I^n, X)))) (t y) : f.uncurry t y = f t.fst t.snd y :=
  by {unfold continuous_map.uncurry, unfold function.uncurry, simp only [continuous_map.coe_mk]}

/-- Currying as a continuous map.-/
abbreviation c_currying : C(C(I × I^n, X),C(I, C(I^n, X))) :=
⟨continuous_map.curry,continuous_map.continuous_curry⟩

/-- Uncurrying as a continuous map.-/
abbreviation c_uncurrying : C(C(I, C(I^n, X)),C(I × I^n, X)) :=
⟨continuous_map.uncurry,continuous_map.continuous_uncurry⟩

/-- Composition with cons as a continuous map.-/
abbreviation c_comp_fold (i : fin (n+1)) : C(C(I^(n+1), X), C(I×I^n, X)) :=
⟨λ f, f.comp (cube.cons_ i), (cube.cons_ i).continuous_comp_left⟩

lemma homotopic_to {p q : gen_loop (n+1) x} :
  homotopic p q → (to_path i p).homotopic (to_path i q) :=
begin
  apply nonempty.map, rintros H,
  refine
  ⟨⟨⟨λ t, ⟨(c_currying.comp ((c_comp_fold i).comp H.to_continuous_map.curry)).uncurry t,_⟩,_⟩,_,_⟩,_⟩,
  { rintros y ⟨i,iH⟩,
    simp only [uncurry_helper, continuous_map.comp_apply, continuous_map.coe_mk,
      continuous_map.curry_apply, cube.cons_apply,
      continuous_map.homotopy_with.coe_to_continuous_map],
    rw H.eq_fst, rw p.property, all_goals {apply cube.cons_boundary, right, exact ⟨i,iH⟩} },
  { simp only [auto_param_eq], continuity },
  show ∀ _ _ _, _,
  { intros t y yH,
    split; ext1; simp only [uncurry_apply, continuous_map.comp_apply, continuous_map.coe_mk,
      continuous_map.curry_apply, cube.cons_apply,
      continuous_map.homotopy_with.coe_to_continuous_map, mk_apply, path.coe_to_continuous_map],
    rw H.eq_fst, refine curry_to_path _, use i, rwa cube.cons_at_eq,
    rw H.eq_snd, refine curry_to_path _, use i, rwa cube.cons_at_eq },
  all_goals {intro t, ext1,
    simp only [uncurry_apply, continuous_map.comp_apply, continuous_map.coe_mk,
      continuous_map.curry_apply, cube.cons_apply,
      continuous_map.homotopy_with.coe_to_continuous_map, mk_apply,
      continuous_map.homotopy_with.apply_zero, continuous_map.homotopy_with.apply_one,
      subtype.val_eq_coe, path.coe_to_continuous_map],
    exact curry_to_path _}
end

@[simp] lemma prod_map_eval {α₁ α₂ β₁ β₂ : Type*} [topological_space α₁] [topological_space β₁]
[topological_space α₂] [topological_space β₂] (f : C(α₁, α₂)) (g : C(β₁, β₂)) (x:α₁) (y:β₁) :
f.prod_map g ⟨x,y⟩ = ⟨f x, g y⟩ := rfl

/--Coercion as a continuous map.-/
abbreviation c_coe : C(gen_loop n x, C(I^n,X)) := ⟨λ p, p.val, continuous_induced_dom⟩

lemma homotopic_from {p q : gen_loop (n+1) x} :
  (to_path i p).homotopic (to_path i q) → homotopic p q :=
begin
  apply nonempty.map, rintros H,
  refine ⟨⟨(c_uncurrying.comp (c_coe.comp H.to_continuous_map).curry).uncurry.comp
      ((continuous_map.id I).prod_map (cube.uncons_ i)),_,_⟩,_⟩,
  show ∀ _ _ _, _,
  { rintros t y ⟨i,iH⟩,
    simp only [continuous_map.to_fun_eq_coe, continuous_map.comp_apply, prod_map_eval,
      continuous_map.id_apply, uncurry_apply, continuous_map.coe_mk, subtype.val_eq_coe],
    rw cube.uncons_apply',
    simp only [uncurry_apply, continuous_map.curry_apply, continuous_map.comp_apply,
      continuous_map.homotopy_with.coe_to_continuous_map, continuous_map.coe_mk,subtype.val_eq_coe],
    -- cases iH; rw iH,
    sorry },
  all_goals
  { intros y,
    simp only [continuous_map.to_fun_eq_coe, continuous_map.comp_apply, prod_map_eval,
      continuous_map.id_apply, uncurry_apply, continuous_map.coe_mk, subtype.val_eq_coe],
    rw cube.uncons_apply',
    simp only [uncurry_apply, continuous_map.curry_apply, continuous_map.comp_apply,
      continuous_map.homotopy_with.coe_to_continuous_map, continuous_map.homotopy_with.apply_zero,
      continuous_map.homotopy_with.apply_one, path.coe_to_continuous_map, continuous_map.coe_mk,
      subtype.val_eq_coe],
    symmetry, convert curry_to_path _, rw [← cube.uncons_apply', cube.cons_uncons] }
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

/--Concatenation of equivalence clasess.-/
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

def concat₂ : π_(n+2) X x → π_(n+2) X x → π_(n+2) X x :=
begin
  refine (quotient.map₂' (gen_loop.concat_ 1) _),
  rintros p₀ p₁ Hp  q₀ q₁ Hq,
  apply gen_loop.homotopic_from 1,
  repeat {rw gen_loop.concat_to_trans},
  apply path.homotopic.hcomp; apply gen_loop.homotopic_to 1,
  exacts [Hp, Hq],
end

-- instance has_add : has_add (π_(n+2) X x) := ⟨concat₂⟩
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

instance comm_group : comm_group (π_(n+2) X x) :=
begin
  apply @eckmann_hilton.comm_group (π_(n+2) X x) (*₂) 𝟙 ⟨⟨const_concat₂⟩,⟨concat₂_const⟩⟩ is_group,
  intros a b c d,
  induction a using quotient.induction_on, induction b using quotient.induction_on,
  induction c using quotient.induction_on, induction d using quotient.induction_on,
  refine (quotient.sound _),
  constructor,
  simp [gen_loop.concat_],
  repeat {rw gen_loop.to_from},
  -- refine @gen_loop.ext X _ (n+2) x (gen_loop.concat_ 1 (gen_loop.concat_ 0 a b) (gen_loop.concat_ 0 c d)) (gen_loop.concat_ 0 (gen_loop.concat_ 1 a c) (gen_loop.concat_ 1 b d)) _, refl,
  sorry
end

end homotopy_group
