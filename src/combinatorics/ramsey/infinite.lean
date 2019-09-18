/-
Copyright (c) 2019 Jared Corduan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jared Corduan.
-/

import logic.basic

/-!
# The Infinite Ramsey Theorem

The main theorem, `infinite_ramsey_pairs_two_colors`, states that given
a function from the unordered pairs of natural numbers to a set
with two elements (often named `red` and `blue`), there exists an
infinite set of natural numbers whose unordered pairs are all given
the same color.

The proof given here follows a very standard proof, such as the one
given in chapter 1, theorem 5, of Graham, et al.

The proof roughly goes as follows:

Given a function `f` of unordered pairs into the colors `red` and `blue`,
define a sequence `(Sᵢ, xᵢ)` so that:

* (S₀, x₀) = (ℕ, 0)
* Sᵢ₊₁ ⊆ Sᵢ
* xᵢ₊₁ ∈ Sᵢ
* xᵢ < xᵢ₊₁
* f {xᵢ₊₁, y} = f {xᵢ₊₁, z} for all xᵢ₊₁ < y < z in Sₓ, x = xᵢ

Then the set {xᵢ | i ∈ ℕ} has the property that
f {xᵢ, xⱼ} = f {xᵢ, xₖ} for all i < j < k.
If we color singletons in this set by f' xᵢ = f {xᵢ, xᵢ₊₁},
then by the pigeon hole principle there is an infinite subset
of the xᵢ's whose unordered pairs are all colored the same.

## Notation

This file uses `[S]²` to denote the set of unordered pairs of
the given set `S`.

## Implementation notes

The set of two colors is defined as an emumeration.
This definition is easy to work with, and easy to read,
but comes at the cost of not generalizing.

Unordered pairs are implemented as ordered pairs with the condition
that the second element is strictly greater than the first.
This definition is also easy to work with but does not generalize.

## References

*  [Graham, R.L. and Rothschild, B.L. and Spencer, J.H., *Ramsey Theory*][graham1990]
-/

open set
open classical
open nat

section infinite_ramsey_pairs

/--
A set of natural numbers H is infinite if for any natural
number there is a larger number in H.
-/
def infinite (H : set ℕ) := ∀ x : ℕ, ∃ y : ℕ, x < y ∧ y ∈ H

/--
There are two colors, red and blue.
-/
inductive color
| red : color
| blue : color

/--
An infinite set of natural numbers.
-/
structure Inf :=
(s : set ℕ)
(pf : infinite s)

instance : has_coe Inf (set ℕ) := ⟨Inf.s⟩
instance : has_mem ℕ Inf := ⟨λ n H, n ∈ H.s⟩
instance : has_subset Inf := ⟨λ H₁ H₂, H₁.s ⊆ H₂.s⟩

open color

/--
Given a function from natural numbers to colors,
this property describes the numbers which are mapped to red.
-/
def reds (f : ℕ → color) (H : set ℕ) := {n : ℕ | f n = red ∧ n ∈ H}

/--
Given a function from natural numbers to colors,
this property describes the numbers which are mapped to blues.
-/
def blues (f : ℕ → color) (H : set ℕ) := (λ n : ℕ, f n = blue ∧ H n)

lemma lt_succ_sum : forall x y : ℕ, x < x + y + 1 :=
λ x y : ℕ, lt_add_of_pos_right x (succ_pos y)

/--
Unordered pairs are defined as ordered pairs with the condition
that the second element is strictly greater than the first.
-/
def unordered_pairs (S : set ℕ) :=
  {p : ℕ × ℕ // p.fst < p.snd ∧ S p.fst ∧ S p.snd}

notation `[ℕ]²` := unordered_pairs univ
notation `[` S `]²` := unordered_pairs S

/--
Given a number m and a coloring f, the projection of a coloring
of unordered_pairs to a coloring of numbers is given by fixing
the first element as m. Note that red is arbitrarily chosen
as the color assigned to any number below m.
-/
def project (f : [ℕ]² → color) (m : ℕ) : ℕ → color :=
  λ n : ℕ,
    dite (m < n)
      (λ h : m < n, f (subtype.mk (m, n) ⟨h, trivial, trivial⟩))
      (λ _, red)

/--
The coloring of an unordered pair {a, b}, where a < b,
agrees with the projection of a applied to b.
-/
lemma project_eq (f : [ℕ]² → color) (p : [ℕ]²):
  f p = project f p.val.fst p.val.snd :=
begin
  unfold project,
  simp [p.property.left]
end

/--
Given coloring of natural numbers, a homogeneous set is
one which is always mapped to the same color.
-/
def homogeneous (f : ℕ → color) (H : Inf) :=
  ∃ c : color, ∀ n, n ∈ H → f n = c

/--
Given a coloring f, a homogeneous projection is a set of natural numbers
together with a single natural number.
The intended use is a set which is homogeneous when projected
with the given number and coloring.
-/
structure homogeneous_proj (f : [ℕ]² → color) extends Inf := (pt : ℕ)

instance (f : [ℕ]² → color) : has_coe (homogeneous_proj f) Inf := ⟨λ c, c.to_Inf⟩

/--
A homogeneous projection p is refined by another homogeneous projection q if:
the number given by q is greater than the number given by p,
the number given by q is an elment of the set given by p,
the set given by q is contained in the set given by p,
and the projection using the number given by q is homogeneous
on the set given by q.
-/
def refines {f : [ℕ]² → color} (p q: homogeneous_proj f) :=
p.pt < q.pt ∧ q.pt ∈ p.s ∧ q.s ⊆ p.s ∧ homogeneous (project f q.pt) q

infix `<<`:50 := refines

local attribute [instance] prop_decidable

/--
A version of the infinite pigeon hole principle, tailored to our use case.
-/
lemma pigeon_hole_principle (f : ℕ → color) (H : Inf):
  infinite (reds f H) ∨ infinite (blues f H) :=
begin
  rw or_iff_not_imp_left,
  intros redFin,
  simp [infinite, not_forall, not_exists] at redFin,
  cases redFin with w Hw,
  intros x,
  have x_lt_a : x < x + w + 1, exact lt_succ_sum x w,
  have w_lt_a : w < x + w + 1,
    { simp, exact lt_succ_sum w x },
  let a : ℕ := x + w + 1,
    cases (H.pf a) with b Hb,
  have w_lt_b : w < b, exact lt_trans w_lt_a Hb.left,
  have hrb : f b = red ∨ f b = blue,
    { cases f b, simp, simp },
  apply exists.intro b,
  constructor,
  { exact lt_trans x_lt_a Hb.left },
  {
    cases hrb with hRed hBlue,
    { exact absurd (and.intro hRed Hb.right) (Hw b w_lt_b) },
    { exact ⟨hBlue, Hb.right⟩ }
  }
end

/--
This is the key lemma, reducing the Ramsey Theorem for pairs
to the pigeon hole principle. It shows how to refine one homogeneous
projection to get another homogeneous projection.
-/
lemma refine_homo_proj (f : [ℕ]² → color) :
  ∀ (p : homogeneous_proj f), ∃ q : homogeneous_proj f, p << q :=
begin
  intros p,
  cases p.pf p.pt with x Hx,
  have Hinf :
    infinite (reds (project f x) p.s) ∨ infinite (blues (project f x) p.s),
    apply pigeon_hole_principle,
  cases Hinf,
  any_goals { -- Red Case
    apply exists.intro (homogeneous_proj.mk f ⟨reds (project f x) p.s, Hinf⟩ x),
  },
  any_goals { -- Blue Case
    apply exists.intro (homogeneous_proj.mk f ⟨blues (project f x) p.s, Hinf⟩ x)
  },
  all_goals
  {
    constructor,
    { exact Hx.left },
    constructor,
    { exact Hx.right },
    constructor,
    { intros n Hn, exact Hn.right },
    { apply exists.intro, intros n Hn, exact Hn.left },
  }
end

/--
The natural numbers, as an infinite set.
-/
def NatInf : Inf := Inf.mk univ
begin
  intro x, apply exists.intro (x+1),
  constructor, exact lt_succ_sum x 0, trivial,
end

/--
The initial set and number used to define
all the homogeneous projections.
-/
def init (f : [ℕ]² → color) := (⟨f, NatInf, 0⟩ : homogeneous_proj f)

/--
Iterate the procedure of refining a homogeneous projection.
TODO is is possible to remove this definition?
-/
def iterate_refinement (f : [ℕ]² → color)
    (cf : Π (x : homogeneous_proj f), (λ (x : homogeneous_proj f), homogeneous_proj f) x) :
  ℕ → homogeneous_proj f
| 0 := cf (init f)
| (n+1) := let p := iterate_refinement n in cf ⟨f, p, p.pt⟩

/--
There exists an infinite sequence of homogeneous projections,
each a refinement of the previous one.
-/
lemma exists_homo_proj_seq (f : [ℕ]² → color) :
∃ (g : ℕ → homogeneous_proj f), init f << g 0 ∧ ∀ n, g n << g (n+1) :=
begin
  have ac : ∃ (cf : Π (x : homogeneous_proj f), (λ (x : homogeneous_proj f), homogeneous_proj f) x),
    ∀ (p : homogeneous_proj f), (λ (p q : homogeneous_proj f), p<<q) p (cf p),
    exact axiom_of_choice (refine_homo_proj f),
  cases ac with cf Hcf,
  let g := λ m : ℕ, (iterate_refinement f cf m),
  apply exists.intro g,
  constructor,
  {
    exact Hcf (init f)
  },
  {
    intro n,
    have h1 : (g n) << cf (g n),
      exact Hcf (g n),
    have h2 : ∀ p : homogeneous_proj f, p = ⟨f, ↑p, p.pt⟩,
      intro p, cases p with H n, cases H with s pf, refl,
    have h3 : cf (g n) = iterate_refinement f cf (n+1),
      unfold iterate_refinement, simp, rw ← (h2 (g n)),
    simp * at *
  }
end

/--
The sets in a sequence of refined homogeneous projections are
closed upward under inclusion.
-/
lemma homo_proj_seq_mono_sets
  (f : [ℕ]² → color)
  (g : ℕ → homogeneous_proj f)
  (h : ∀ n, g n << g (n+1))
  (x y : ℕ) :
  (g (x+y)).s ⊆ (g x).s :=
begin
  induction y with y ih,
  {
    intros y hy, exact hy,
  },
  {
    intros a ha,
    exact ih ((h (x+y)).right.right.left ha),
  }
end

/--
The points in a sequence of refined homogeneous projections are
contained in the previous sets.
-/
lemma homo_proj_seq_mono_pts
  (f : [ℕ]² → color)
  (g : ℕ → homogeneous_proj f)
  (h : ∀ n, g n << g (n+1))
  (x y : ℕ) :
  (g (x+y+1)).pt ∈ (g x).s :=
by exact (homo_proj_seq_mono_sets f g h x y) ((h (x+y)).right.left)

/--
The points in a sequence of refined homogeneous projections have
the property that f {xᵢ, y} = f {xᵢ, z} for all xᵢ < y < z in Sₓ.
-/
lemma homo_proj_seq_stable_colors
  (f : [ℕ]² → color)
  (g : ℕ → homogeneous_proj f)
  (h0 : (init f) << g 0)
  (hn : ∀ n, g n << g (n+1))
  (x y : ℕ) :
  (project f (g x).pt) (g (x+1)).pt = (project f (g x).pt) (g (x+y+1)).pt :=
begin
  cases x,
  {
    have h : homogeneous (project f (g 0).pt) (g 0),
      exact h0.right.right.right,
    cases h with c hm,
    simp,
    rw hm ((g 1).pt) (homo_proj_seq_mono_pts f g hn 0 0),
    have hzy : y + 1 = 0 + y + 1, simp,
    rw hzy,
    rw hm ((g (0+y+1)).pt) (homo_proj_seq_mono_pts f g hn 0 y),
  },
  {
    have hgx : g x << g (x+1), exact (hn x),
    have hm : homogeneous (project f (g (x+1)).pt) (g (x+1)),
      exact hgx.right.right.right,
    cases hm with c Hm',
    rw Hm' ((g (x + 1 + 1)).pt) (homo_proj_seq_mono_pts f g hn (x+1) 0),
    rw Hm' ((g (x + 1 + y + 1)).pt) (homo_proj_seq_mono_pts f g hn (x+1) y),
  }
end

section increasing_functions

--TODO are the results of this section proved elsewhere in mathlib?

def increasing (f : ℕ → ℕ) := ∀ x y : ℕ, x < y → f x < f y

lemma increasing_by_step (f : ℕ → ℕ) :
  (∀ n : ℕ, f n < f (n+1)) → increasing f :=
λ (hf : ∀ n : ℕ, f n < f (n+1)) (x y : ℕ), nat.rec_on y
(λ (contr : x < 0), absurd contr (not_succ_le_zero x))
(λ (z : ℕ) (ih : x < z → f x < f z) (h : x < succ z),
or.cases_on (nat.eq_or_lt_of_le (le_of_lt_succ h))
(λ hxz : x = z, hxz ▸ (hf x))
(λ (hxz : x < z), lt_trans (ih hxz) (hf z)))

lemma x_le_fx_incr (f : ℕ → ℕ) (x : ℕ): increasing f → x ≤ f x :=
λ (incr : increasing f),
  nat.rec_on x (zero_le (f 0))
  (λ (n : ℕ) (ih : n ≤ f n),
  le_trans (succ_le_succ ih) (incr n (succ n) (lt_succ_self n)))

lemma incr_range_inf (H : Inf) (g : ℕ → ℕ) (hg : increasing g) :
  infinite (image g H) :=
begin
  intros x,
  have h : ∃ h, x < h ∧ h ∈ H, exact H.pf x,
  cases h with h Hh,
  apply exists.intro (g h),
  constructor,
  exact (lt_of_lt_of_le Hh.left (x_le_fx_incr g h hg)),
  unfold image,
  apply exists.intro h, constructor, exact Hh.right, refl,
end

lemma incr_dom (g : ℕ → ℕ) (hg : increasing g) (x y : ℕ) (h : g x < g y):
  x < y :=
begin
  cases (lt_trichotomy x y) with hlt hlte,
    exact hlt,
    cases hlte with hlt he, rw hlt at h,
    exact absurd h (lt_irrefl (g y)),
    exact absurd (lt_trans (hg y x he) h) (lt_irrefl (g y)),
end

end increasing_functions

/--
Trivial lemma needed below.
-/
lemma domain_dist_rw (x y : ℕ) (h : x < y): y = x + (y - (x+1)) + 1 :=
by rw [ add_assoc x (y - (x+1)) 1
      , add_comm (y - (x+1)) 1
      , ←add_assoc x 1 (y - (x+1))
      , add_sub_of_le (succ_le_of_lt h)]

/--
The points in a sequence of refined homogeneous projections
are increasing.
-/
lemma homo_proj_seq_incr
(f : [ℕ]² → color)
(g : ℕ → homogeneous_proj f)
(h : ∀ n, g n << g (n+1)) :
increasing (λ n : ℕ, (g n).pt) :=
begin
have h : ∀ n : ℕ, (g n).pt < (g (n+1)).pt,
intro, exact (h n).left,
exact increasing_by_step (λ n : ℕ, (g n).pt) h,
end

/--
Restrict a coloring of unordered pairs of all natural numbers
to unordered pairs of a given infinite set H.
-/
def restrict (f : [ℕ]² → color) (H : set ℕ) : [H]² → color :=
  λ h, f (⟨h.val, ⟨h.property.left, ⟨true.intro, true.intro⟩⟩⟩)

/--
The main theorem, stating that given a function from the unordered pairs of
natural numbers to a set with two elements, there exists an infinite set of
natural numbers whose unordered pairs are all given the same color.
-/
theorem infinite_ramsey_pairs_two_colors (f : [ℕ]² → color) :
  ∃ H : Inf, ∃ c : color,
  ∀ h : [H]²,
  (restrict f H) h = c :=
begin
  have hseq : ∃ (g : ℕ → homogeneous_proj f), init f << g 0 ∧ ∀ n, g n << g (n+1),
    exact exists_homo_proj_seq f,
  cases hseq with g Hg,
  cases Hg with HgInit HgSeq,
  let g' := (λ n, (g n).pt),
  let f' := (λ n, project f (g' n) (g' (n+1))),
  have HgIncr : increasing g', exact homo_proj_seq_incr f g HgSeq,
  let preH := (⟨image g' NatInf, incr_range_inf NatInf g' HgIncr⟩ : Inf),
  cases (pigeon_hole_principle f' preH) with Hred Hblue,

  any_goals { -- Red Case
    let H := (⟨reds f' preH, Hred⟩ : Inf),
    apply exists.intro (⟨image g' H, incr_range_inf H g' HgIncr⟩ : Inf),
    apply exists.intro red,
    intros p,
  },
  any_goals { -- Blue Case
    let H := (⟨blues f' preH, Hblue⟩ : Inf),
    apply exists.intro (⟨image g' H, incr_range_inf H g' HgIncr⟩ : Inf),
    apply exists.intro blue,
    intros p,
  },
  all_goals {
    have hp1 : p.val.fst ∈ image g' H, exact p.property.right.left,
    cases hp1 with h₁ Hh₁,
    have hfh₁ : f' h₁ = _, exact Hh₁.left.left,
    have hfgh₁ : project f (g' h₁) (g' (h₁+1)) = _, rw ←hfh₁,
    have hp2 : p.val.snd ∈ image g' H, exact p.property.right.right,
    cases hp2 with h₂ Hgh₂,
    have hg : p.val.fst < p.val.snd, exact p.property.left,
    rw [←Hh₁.right, ←Hgh₂.right] at hg,
    let d := h₂ - (h₁ + 1),
    have hd : h₂ = h₁ + d + 1,
      exact domain_dist_rw h₁ h₂ (incr_dom g' HgIncr h₁ h₂ hg),
    have stable :
      (project f (g' h₁)) (g' (h₁+1)) = (project f (g' h₁)) (g' (h₁+d+1)),
      exact homo_proj_seq_stable_colors f g HgInit HgSeq h₁ d,
    rw [hfgh₁, ←hd, Hh₁.right, Hgh₂.right] at stable,
    have hproj : f ⟨p.val, _⟩ = project f p.val.fst p.val.snd,
      exact project_eq f ⟨p.val, ⟨p.property.left, trivial, trivial⟩⟩,
    rw [←stable, hproj] at hproj,
    rw ←hproj, refl,
  }
end

end infinite_ramsey_pairs
