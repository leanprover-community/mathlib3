/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.fintype.basic
import data.list.sublists
import group_theory.subgroup.basic

/-!
# Free groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines free groups over a type. Furthermore, it is shown that the free group construction
is an instance of a monad. For the result that `free_group` is the left adjoint to the forgetful
functor from groups to types, see `algebra/category/Group/adjunctions`.

## Main definitions

* `free_group`/`free_add_group`: the free group (resp. free additive group) associated to a type
  `α` defined as the words over `a : α × bool` modulo the relation `a * x * x⁻¹ * b = a * b`.
* `free_group.mk`/`free_add_group.mk`: the canonical quotient map `list (α × bool) → free_group α`.
* `free_group.of`/`free_add_group.of`: the canonical injection `α → free_group α`.
* `free_group.lift f`/`free_add_group.lift`: the canonical group homomorphism `free_group α →* G`
  given a group `G` and a function `f : α → G`.

## Main statements

* `free_group.church_rosser`/`free_add_group.church_rosser`: The Church-Rosser theorem for word
  reduction (also known as Newman's diamond lemma).
* `free_group.free_group_unit_equiv_int`: The free group over the one-point type
  is isomorphic to the integers.
* The free group construction is an instance of a monad.

## Implementation details

First we introduce the one step reduction relation `free_group.red.step`:
`w * x * x⁻¹ * v   ~>   w * v`, its reflexive transitive closure `free_group.red.trans`
and prove that its join is an equivalence relation. Then we introduce `free_group α` as a quotient
over `free_group.red.step`.

For the additive version we introduce the same relation under a different name so that we can
distinguish the quotient types more easily.


## Tags

free group, Newman's diamond lemma, Church-Rosser theorem
-/

open relation

universes u v w

variables {α : Type u}

local attribute [simp] list.append_eq_has_append

run_cmd to_additive.map_namespace `free_group `free_add_group

/-- Reduction step for the additive free group relation: `w + x + (-x) + v ~> w + v` -/
inductive free_add_group.red.step : list (α × bool) → list (α × bool) → Prop
| bnot {L₁ L₂ x b} : free_add_group.red.step (L₁ ++ (x, b) :: (x, bnot b) :: L₂) (L₁ ++ L₂)
attribute [simp] free_add_group.red.step.bnot

/-- Reduction step for the multiplicative free group relation: `w * x * x⁻¹ * v ~> w * v` -/
@[to_additive]
inductive free_group.red.step : list (α × bool) → list (α × bool) → Prop
| bnot {L₁ L₂ x b} : free_group.red.step (L₁ ++ (x, b) :: (x, bnot b) :: L₂) (L₁ ++ L₂)
attribute [simp] free_group.red.step.bnot

namespace free_group

variables {L L₁ L₂ L₃ L₄ : list (α × bool)}

/-- Reflexive-transitive closure of red.step -/
@[to_additive "Reflexive-transitive closure of red.step"]
def red : list (α × bool) → list (α × bool) → Prop := refl_trans_gen red.step

@[refl, to_additive] lemma red.refl : red L L := refl_trans_gen.refl
@[trans, to_additive] lemma red.trans : red L₁ L₂ → red L₂ L₃ → red L₁ L₃ := refl_trans_gen.trans

namespace red

/-- Predicate asserting that the word `w₁` can be reduced to `w₂` in one step, i.e. there are words
`w₃ w₄` and letter `x` such that `w₁ = w₃xx⁻¹w₄` and `w₂ = w₃w₄`  -/
@[to_additive
"Predicate asserting that the word `w₁` can be reduced to `w₂` in one step, i.e. there are words
`w₃ w₄` and letter `x` such that `w₁ = w₃ + x + (-x) + w₄` and `w₂ = w₃w₄`"]
theorem step.length : ∀ {L₁ L₂ : list (α × bool)}, step L₁ L₂ → L₂.length + 2 = L₁.length
| _ _ (@red.step.bnot _ L1 L2 x b) := by rw [list.length_append, list.length_append]; refl

@[simp, to_additive]
lemma step.bnot_rev {x b} : step (L₁ ++ (x, bnot b) :: (x, b) :: L₂) (L₁ ++ L₂) :=
by cases b; from step.bnot

@[simp, to_additive] lemma step.cons_bnot {x b} : red.step ((x, b) :: (x, bnot b) :: L) L :=
@step.bnot _ [] _ _ _

@[simp, to_additive] lemma step.cons_bnot_rev {x b} : red.step ((x, bnot b) :: (x, b) :: L) L :=
@red.step.bnot_rev _ [] _ _ _

@[to_additive]
theorem step.append_left : ∀ {L₁ L₂ L₃ : list (α × bool)}, step L₂ L₃ → step (L₁ ++ L₂) (L₁ ++ L₃)
| _ _ _ red.step.bnot := by rw [← list.append_assoc, ← list.append_assoc]; constructor

@[to_additive]
theorem step.cons {x} (H : red.step L₁ L₂) : red.step (x :: L₁) (x :: L₂) :=
@step.append_left _ [x] _ _ H

@[to_additive]
theorem step.append_right : ∀ {L₁ L₂ L₃ : list (α × bool)}, step L₁ L₂ → step (L₁ ++ L₃) (L₂ ++ L₃)
| _ _ _ red.step.bnot := by simp

@[to_additive]
lemma not_step_nil : ¬ step [] L :=
begin
  generalize h' : [] = L',
  assume h,
  cases h with L₁ L₂,
  simp [list.nil_eq_append_iff] at h',
  contradiction
end

@[to_additive]
lemma step.cons_left_iff {a : α} {b : bool} :
  step ((a, b) :: L₁) L₂ ↔ (∃L, step L₁ L ∧ L₂ = (a, b) :: L) ∨ (L₁ = (a, bnot b)::L₂) :=
begin
  split,
  { generalize hL : ((a, b) :: L₁ : list _) = L,
    rintro @⟨_ | ⟨p, s'⟩, e, a', b'⟩,
    { simp at hL, simp [*] },
    { simp at hL,
      rcases hL with ⟨rfl, rfl⟩,
      refine or.inl ⟨s' ++ e, step.bnot, _⟩,
      simp } },
  { rintro (⟨L, h, rfl⟩ | rfl),
    { exact step.cons h },
    { exact step.cons_bnot } }
end

@[to_additive]
lemma not_step_singleton : ∀ {p : α × bool}, ¬ step [p] L
| (a, b) := by simp [step.cons_left_iff, not_step_nil]

@[to_additive]
lemma step.cons_cons_iff : ∀{p : α × bool}, step (p :: L₁) (p :: L₂) ↔ step L₁ L₂ :=
by simp [step.cons_left_iff, iff_def, or_imp_distrib] {contextual := tt}

@[to_additive]
lemma step.append_left_iff : ∀L, step (L ++ L₁) (L ++ L₂) ↔ step L₁ L₂
| [] := by simp
| (p :: l) := by simp [step.append_left_iff l, step.cons_cons_iff]

@[to_additive]
theorem step.diamond_aux : ∀ {L₁ L₂ L₃ L₄ : list (α × bool)} {x1 b1 x2 b2},
  L₁ ++ (x1, b1) :: (x1, bnot b1) :: L₂ = L₃ ++ (x2, b2) :: (x2, bnot b2) :: L₄ →
  L₁ ++ L₂ = L₃ ++ L₄ ∨ ∃ L₅, red.step (L₁ ++ L₂) L₅ ∧ red.step (L₃ ++ L₄) L₅
| []        _ []        _ _ _ _ _ H := by injections; subst_vars; simp
| []        _ [(x3,b3)] _ _ _ _ _ H := by injections; subst_vars; simp
| [(x3,b3)] _ []        _ _ _ _ _ H := by injections; subst_vars; simp
| []                     _ ((x3,b3)::(x4,b4)::tl) _ _ _ _ _ H :=
  by injections; subst_vars; simp; right; exact ⟨_, red.step.bnot, red.step.cons_bnot⟩
| ((x3,b3)::(x4,b4)::tl) _ []                     _ _ _ _ _ H :=
  by injections; subst_vars; simp; right; exact ⟨_, red.step.cons_bnot, red.step.bnot⟩
| ((x3,b3)::tl) _ ((x4,b4)::tl2) _ _ _ _ _ H :=
  let ⟨H1, H2⟩ := list.cons.inj H in
  match step.diamond_aux H2 with
    | or.inl H3 := or.inl $ by simp [H1, H3]
    | or.inr ⟨L₅, H3, H4⟩ := or.inr
      ⟨_, step.cons H3, by simpa [H1] using step.cons H4⟩
  end

@[to_additive]
theorem step.diamond : ∀ {L₁ L₂ L₃ L₄ : list (α × bool)},
  red.step L₁ L₃ → red.step L₂ L₄ → L₁ = L₂ →
  L₃ = L₄ ∨ ∃ L₅, red.step L₃ L₅ ∧ red.step L₄ L₅
| _ _ _ _ red.step.bnot red.step.bnot H := step.diamond_aux H

@[to_additive]
lemma step.to_red : step L₁ L₂ → red L₁ L₂ :=
refl_trans_gen.single

/-- **Church-Rosser theorem** for word reduction: If `w1 w2 w3` are words such that `w1` reduces
to `w2` and `w3` respectively, then there is a word `w4` such that `w2` and `w3` reduce to `w4`
respectively. This is also known as Newman's diamond lemma. -/
@[to_additive
"**Church-Rosser theorem** for word reduction: If `w1 w2 w3` are words such that `w1` reduces
to `w2` and `w3` respectively, then there is a word `w4` such that `w2` and `w3` reduce to `w4`
respectively. This is also known as Newman's diamond lemma."]
theorem church_rosser : red L₁ L₂ → red L₁ L₃ → join red L₂ L₃ :=
relation.church_rosser (assume a b c hab hac,
match b, c, red.step.diamond hab hac rfl with
| b, _, or.inl rfl           := ⟨b, by refl, by refl⟩
| b, c, or.inr ⟨d, hbd, hcd⟩ := ⟨d, refl_gen.single hbd, hcd.to_red⟩
end)

@[to_additive]
lemma cons_cons {p} : red L₁ L₂ → red (p :: L₁) (p :: L₂) :=
refl_trans_gen.lift (list.cons p) (assume a b, step.cons)

@[to_additive]
lemma cons_cons_iff (p) : red (p :: L₁) (p :: L₂) ↔ red L₁ L₂ :=
iff.intro
  begin
    generalize eq₁ : (p :: L₁ : list _) = LL₁,
    generalize eq₂ : (p :: L₂ : list _) = LL₂,
    assume h,
    induction h using relation.refl_trans_gen.head_induction_on
      with L₁ L₂ h₁₂ h ih
      generalizing L₁ L₂,
    { subst_vars, cases eq₂, constructor },
    { subst_vars,
      cases p with a b,
      rw [step.cons_left_iff] at h₁₂,
      rcases h₁₂ with ⟨L, h₁₂, rfl⟩ | rfl,
      { exact (ih rfl rfl).head h₁₂ },
      { exact (cons_cons h).tail step.cons_bnot_rev } }
  end
  cons_cons

@[to_additive]
lemma append_append_left_iff : ∀L, red (L ++ L₁) (L ++ L₂) ↔ red L₁ L₂
| []       := iff.rfl
| (p :: L) := by simp [append_append_left_iff L, cons_cons_iff]

@[to_additive]
lemma append_append (h₁ : red L₁ L₃) (h₂ : red L₂ L₄) : red (L₁ ++ L₂) (L₃ ++ L₄) :=
(h₁.lift (λL, L ++ L₂) (assume a b, step.append_right)).trans ((append_append_left_iff _).2 h₂)

@[to_additive]
lemma to_append_iff : red L (L₁ ++ L₂) ↔ (∃L₃ L₄, L = L₃ ++ L₄ ∧ red L₃ L₁ ∧ red L₄ L₂) :=
iff.intro
  begin
    generalize eq : L₁ ++ L₂ = L₁₂,
    assume h,
    induction h with L' L₁₂ hLL' h ih generalizing L₁ L₂,
    { exact ⟨_, _, eq.symm, by refl, by refl⟩ },
    { cases h with s e a b,
      rcases list.append_eq_append_iff.1 eq with ⟨s', rfl, rfl⟩ | ⟨e', rfl, rfl⟩,
      { have : L₁ ++ (s' ++ ((a, b) :: (a, bnot b) :: e)) =
                 (L₁ ++ s') ++ ((a, b) :: (a, bnot b) :: e),
        { simp },
        rcases ih this with ⟨w₁, w₂, rfl, h₁, h₂⟩,
        exact ⟨w₁, w₂, rfl, h₁, h₂.tail step.bnot⟩ },
      { have : (s ++ ((a, b) :: (a, bnot b) :: e')) ++ L₂ =
                 s ++ ((a, b) :: (a, bnot b) :: (e' ++ L₂)),
        { simp },
        rcases ih this with ⟨w₁, w₂, rfl, h₁, h₂⟩,
        exact ⟨w₁, w₂, rfl, h₁.tail step.bnot, h₂⟩ }, }
  end
  (assume ⟨L₃, L₄, eq, h₃, h₄⟩, eq.symm ▸ append_append h₃ h₄)

/-- The empty word `[]` only reduces to itself. -/
@[to_additive "The empty word `[]` only reduces to itself."]
theorem nil_iff : red [] L ↔ L = [] :=
refl_trans_gen_iff_eq (assume l, red.not_step_nil)

/-- A letter only reduces to itself. -/
@[to_additive "A letter only reduces to itself."]
theorem singleton_iff {x} : red [x] L₁ ↔ L₁ = [x] :=
refl_trans_gen_iff_eq (assume l, not_step_singleton)

/-- If `x` is a letter and `w` is a word such that `xw` reduces to the empty word, then `w` reduces
to `x⁻¹` -/
@[to_additive "If `x` is a letter and `w` is a word such that `x + w` reduces to the empty word,
then `w` reduces to `-x`."]
theorem cons_nil_iff_singleton {x b} : red ((x, b) :: L) [] ↔ red L [(x, bnot b)] :=
iff.intro
  (assume h,
    have h₁ : red ((x, bnot b) :: (x, b) :: L) [(x, bnot b)], from cons_cons h,
    have h₂ : red ((x, bnot b) :: (x, b) :: L) L, from refl_trans_gen.single step.cons_bnot_rev,
    let ⟨L', h₁, h₂⟩ := church_rosser h₁ h₂ in
    by rw [singleton_iff] at h₁; subst L'; assumption)
  (assume h, (cons_cons h).tail step.cons_bnot)

@[to_additive]
theorem red_iff_irreducible {x1 b1 x2 b2} (h : (x1, b1) ≠ (x2, b2)) :
  red [(x1, bnot b1), (x2, b2)] L ↔ L = [(x1, bnot b1), (x2, b2)] :=
begin
  apply refl_trans_gen_iff_eq,
  generalize eq : [(x1, bnot b1), (x2, b2)] = L',
  assume L h',
  cases h',
  simp [list.cons_eq_append_iff, list.nil_eq_append_iff] at eq,
  rcases eq with ⟨rfl, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩, subst_vars,
  simp at h,
  contradiction
end

/-- If `x` and `y` are distinct letters and `w₁ w₂` are words such that `xw₁` reduces to `yw₂`, then
`w₁` reduces to `x⁻¹yw₂`. -/
@[to_additive
"If `x` and `y` are distinct letters and `w₁ w₂` are words such that `x + w₁` reduces to `y + w₂`,
then `w₁` reduces to `-x + y + w₂`."]
theorem inv_of_red_of_ne {x1 b1 x2 b2}
  (H1 : (x1, b1) ≠ (x2, b2))
  (H2 : red ((x1, b1) :: L₁) ((x2, b2) :: L₂)) :
  red L₁ ((x1, bnot b1) :: (x2, b2) :: L₂) :=
begin
  have : red ((x1, b1) :: L₁) ([(x2, b2)] ++ L₂), from H2,
  rcases to_append_iff.1 this with ⟨_ | ⟨p, L₃⟩, L₄, eq, h₁, h₂⟩,
  { simp [nil_iff] at h₁, contradiction },
  { cases eq,
    show red (L₃ ++ L₄) ([(x1, bnot b1), (x2, b2)] ++ L₂),
    apply append_append _ h₂,
    have h₁ : red ((x1, bnot b1) :: (x1, b1) :: L₃) [(x1, bnot b1), (x2, b2)],
    { exact cons_cons h₁ },
    have h₂ : red ((x1, bnot b1) :: (x1, b1) :: L₃) L₃,
    { exact step.cons_bnot_rev.to_red },
    rcases church_rosser h₁ h₂ with ⟨L', h₁, h₂⟩,
    rw [red_iff_irreducible H1] at h₁,
    rwa [h₁] at h₂ }
end

@[to_additive]
theorem step.sublist (H : red.step L₁ L₂) : L₂ <+ L₁ :=
by cases H; simp; constructor; constructor; refl

/-- If `w₁ w₂` are words such that `w₁` reduces to `w₂`, then `w₂` is a sublist of `w₁`. -/
@[to_additive "If `w₁ w₂` are words such that `w₁` reduces to `w₂`,
then `w₂` is a sublist of `w₁`."]
protected theorem sublist : red L₁ L₂ → L₂ <+ L₁ :=
refl_trans_gen_of_transitive_reflexive
  (λl, list.sublist.refl l) (λa b c hab hbc, list.sublist.trans hbc hab) (λa b, red.step.sublist)

@[to_additive]
theorem length_le (h : red L₁ L₂) : L₂.length ≤ L₁.length := h.sublist.length_le

@[to_additive]
theorem sizeof_of_step : ∀ {L₁ L₂ : list (α × bool)}, step L₁ L₂ → L₂.sizeof < L₁.sizeof
| _ _ (@step.bnot _ L1 L2 x b) :=
  begin
    induction L1 with hd tl ih,
    case list.nil
    { dsimp [list.sizeof],
      have H : 1 + sizeof (x, b) + (1 + sizeof (x, bnot b) + list.sizeof L2)
        = (list.sizeof L2 + 1) + (sizeof (x, b) + sizeof (x, bnot b) + 1),
      { ac_refl },
      rw H,
      exact nat.le_add_right _ _ },
    case list.cons
    { dsimp [list.sizeof],
      exact nat.add_lt_add_left ih _ }
  end

@[to_additive]
theorem length (h : red L₁ L₂) : ∃ n, L₁.length = L₂.length + 2 * n :=
begin
  induction h with L₂ L₃ h₁₂ h₂₃ ih,
  { exact ⟨0, rfl⟩ },
  { rcases ih with ⟨n, eq⟩,
    existsi (1 + n),
    simp [mul_add, eq, (step.length h₂₃).symm, add_assoc] }
end

@[to_additive]
theorem antisymm (h₁₂ : red L₁ L₂) (h₂₁ : red L₂ L₁) : L₁ = L₂ :=
h₂₁.sublist.antisymm h₁₂.sublist

end red

@[to_additive]
theorem equivalence_join_red : equivalence (join (@red α)) :=
equivalence_join_refl_trans_gen $ assume a b c hab hac,
(match b, c, red.step.diamond hab hac rfl with
| b, _, or.inl rfl           := ⟨b, by refl, by refl⟩
| b, c, or.inr ⟨d, hbd, hcd⟩ := ⟨d, refl_gen.single hbd, refl_trans_gen.single hcd⟩
end)

@[to_additive]
theorem join_red_of_step (h : red.step L₁ L₂) : join red L₁ L₂ :=
join_of_single reflexive_refl_trans_gen h.to_red

@[to_additive]
theorem eqv_gen_step_iff_join_red : eqv_gen red.step L₁ L₂ ↔ join red L₁ L₂ :=
iff.intro
  (assume h,
    have eqv_gen (join red) L₁ L₂ := h.mono (assume a b, join_red_of_step),
    equivalence_join_red.eqv_gen_iff.1 this)
  (join_of_equivalence (eqv_gen.is_equivalence _) $ assume a b,
    refl_trans_gen_of_equivalence (eqv_gen.is_equivalence _) eqv_gen.rel)

end free_group

/-- The free group over a type, i.e. the words formed by the elements of the type and their formal
inverses, quotient by one step reduction. -/
@[to_additive "The free additive group over a type, i.e. the words formed by the elements of the
type and their formal inverses, quotient by one step reduction."]
def free_group (α : Type u) : Type u :=
quot $ @free_group.red.step α

namespace free_group

variables {α} {L L₁ L₂ L₃ L₄ : list (α × bool)}

/-- The canonical map from `list (α × bool)` to the free group on `α`. -/
@[to_additive "The canonical map from `list (α × bool)` to the free additive group on `α`."]
def mk (L) : free_group α := quot.mk red.step L

@[simp, to_additive] lemma quot_mk_eq_mk : quot.mk red.step L = mk L := rfl

@[simp, to_additive] lemma quot_lift_mk (β : Type v) (f : list (α × bool) → β)
  (H : ∀ L₁ L₂, red.step L₁ L₂ → f L₁ = f L₂) :
quot.lift f H (mk L) = f L := rfl

@[simp, to_additive] lemma quot_lift_on_mk (β : Type v) (f : list (α × bool) → β)
  (H : ∀ L₁ L₂, red.step L₁ L₂ → f L₁ = f L₂) :
quot.lift_on (mk L) f H = f L := rfl

@[simp, to_additive] lemma quot_map_mk (β : Type v) (f : list (α × bool) → list (β × bool))
  (H : (red.step ⇒ red.step) f f) :
quot.map f H (mk L) = mk (f L) := rfl

@[to_additive]
instance : has_one (free_group α) := ⟨mk []⟩
@[to_additive]
lemma one_eq_mk : (1 : free_group α) = mk [] := rfl

@[to_additive]
instance : inhabited (free_group α) := ⟨1⟩

@[to_additive]
instance : has_mul (free_group α) :=
⟨λ x y, quot.lift_on x
    (λ L₁, quot.lift_on y (λ L₂, mk $ L₁ ++ L₂) (λ L₂ L₃ H, quot.sound $ red.step.append_left H))
    (λ L₁ L₂ H, quot.induction_on y $ λ L₃, quot.sound $ red.step.append_right H)⟩
@[simp, to_additive] lemma mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂) := rfl

/-- Transform a word representing a free group element into a word representing its inverse. -/
@[to_additive "Transform a word representing a free group element into a word representing its
negative."]
def inv_rev (w : list (α × bool)) : list (α × bool) :=
(list.map (λ (g : α × bool), (g.1, bnot g.2)) w).reverse

@[simp, to_additive] lemma inv_rev_length : (inv_rev L₁).length = L₁.length := by simp [inv_rev]
@[simp, to_additive] lemma inv_rev_inv_rev : (inv_rev (inv_rev L₁) = L₁) := by simp [inv_rev, (∘)]
@[simp, to_additive] lemma inv_rev_empty : inv_rev ([] : list (α × bool)) = [] := rfl

@[to_additive]
lemma inv_rev_involutive : function.involutive (@inv_rev α) := λ _, inv_rev_inv_rev
@[to_additive]
lemma inv_rev_injective : function.injective (@inv_rev α) := inv_rev_involutive.injective
@[to_additive]
lemma inv_rev_surjective : function.surjective (@inv_rev α) := inv_rev_involutive.surjective
@[to_additive]
lemma inv_rev_bijective : function.bijective (@inv_rev α) := inv_rev_involutive.bijective

@[to_additive]
instance : has_inv (free_group α) :=
⟨quot.map inv_rev (by { intros a b h, cases h, simp [inv_rev], })⟩

@[simp, to_additive] lemma inv_mk : (mk L)⁻¹ = mk (inv_rev L) := rfl

@[to_additive]
lemma red.step.inv_rev {L₁ L₂ : list (α × bool)} (h : red.step L₁ L₂) :
  red.step (inv_rev L₁) (inv_rev L₂) :=
begin
  cases h with a b x y,
  simp [inv_rev],
end

@[to_additive]
lemma red.inv_rev {L₁ L₂ : list (α × bool)} (h : red L₁ L₂) :
  red (inv_rev L₁) (inv_rev L₂) :=
relation.refl_trans_gen.lift _ (λ a b, red.step.inv_rev) h

@[simp, to_additive]
lemma red.step_inv_rev_iff : red.step (inv_rev L₁) (inv_rev L₂) ↔ red.step L₁ L₂ :=
⟨λ h, by simpa only [inv_rev_inv_rev] using h.inv_rev, λ h, h.inv_rev⟩

@[simp, to_additive] lemma red_inv_rev_iff : red (inv_rev L₁) (inv_rev L₂) ↔ red L₁ L₂ :=
⟨λ h, by simpa only [inv_rev_inv_rev] using h.inv_rev, λ h, h.inv_rev⟩

@[to_additive]
instance : group (free_group α) :=
{ mul := (*),
  one := 1,
  inv := has_inv.inv,
  mul_assoc := by rintros ⟨L₁⟩ ⟨L₂⟩ ⟨L₃⟩; simp,
  one_mul := by rintros ⟨L⟩; refl,
  mul_one := by rintros ⟨L⟩; simp [one_eq_mk],
  mul_left_inv := by rintros ⟨L⟩; exact (list.rec_on L rfl $
    λ ⟨x, b⟩ tl ih, eq.trans (quot.sound $ by simp [inv_rev, one_eq_mk]) ih) }

/-- `of` is the canonical injection from the type to the free group over that type by sending each
element to the equivalence class of the letter that is the element. -/
@[to_additive "`of` is the canonical injection from the type to the free group over that type
by sending each element to the equivalence class of the letter that is the element."]
def of (x : α) : free_group α :=
mk [(x, tt)]

@[to_additive]
theorem red.exact : mk L₁ = mk L₂ ↔ join red L₁ L₂ :=
calc (mk L₁ = mk L₂) ↔ eqv_gen red.step L₁ L₂ : iff.intro (quot.exact _) quot.eqv_gen_sound
  ... ↔ join red L₁ L₂ : eqv_gen_step_iff_join_red

/-- The canonical map from the type to the free group is an injection. -/
@[to_additive "The canonical map from the type to the additive free group is an injection."]
theorem of_injective : function.injective (@of α) :=
λ _ _ H, let ⟨L₁, hx, hy⟩ := red.exact.1 H in
  by simp [red.singleton_iff] at hx hy; cc

section lift

variables {β : Type v} [group β] (f : α → β) {x y : free_group α}

/-- Given `f : α → β` with `β` a group, the canonical map `list (α × bool) → β` -/
@[to_additive "Given `f : α → β` with `β` an additive group, the canonical map
`list (α × bool) → β`"]
def lift.aux : list (α × bool) → β :=
λ L, list.prod $ L.map $ λ x, cond x.2 (f x.1) (f x.1)⁻¹

@[to_additive]
theorem red.step.lift {f : α → β} (H : red.step L₁ L₂) :
  lift.aux f L₁ = lift.aux f L₂ :=
by cases H with _ _ _ b; cases b; simp [lift.aux]


/-- If `β` is a group, then any function from `α` to `β`
extends uniquely to a group homomorphism from
the free group over `α` to `β` -/
@[to_additive "If `β` is an additive group, then any function from `α` to `β`
extends uniquely to an additive group homomorphism from
the free additive group over `α` to `β`", simps symm_apply]
def lift : (α → β) ≃ (free_group α →* β) :=
{ to_fun := λ f,
    monoid_hom.mk' (quot.lift (lift.aux f) $ λ L₁ L₂, red.step.lift) $ begin
      rintros ⟨L₁⟩ ⟨L₂⟩, simp [lift.aux],
    end,
  inv_fun := λ g, g ∘ of,
  left_inv := λ f, one_mul _,
  right_inv := λ g, monoid_hom.ext $ begin
    rintros ⟨L⟩,
    apply list.rec_on L,
    { exact g.map_one.symm, },
    { rintros ⟨x, _ | _⟩ t (ih : _ = g (mk t)),
      { show _ = g ((of x)⁻¹ * mk t),
        simpa [lift.aux] using ih },
      { show _ = g (of x * mk t),
        simpa [lift.aux] using ih }, },
  end }
variable {f}

@[simp, to_additive] lemma lift.mk : lift f (mk L) =
  list.prod (L.map $ λ x, cond x.2 (f x.1) (f x.1)⁻¹) :=
rfl

@[simp, to_additive] lemma lift.of {x} : lift f (of x) = f x :=
one_mul _

@[to_additive]
theorem lift.unique (g : free_group α →* β)
  (hg : ∀ x, g (of x) = f x) : ∀{x}, g x = lift f x :=
monoid_hom.congr_fun $ (lift.symm_apply_eq).mp (funext hg : g ∘ of = f)

/-- Two homomorphisms out of a free group are equal if they are equal on generators.

See note [partially-applied ext lemmas]. -/
@[ext, to_additive
"Two homomorphisms out of a free additive group are equal if they are equal on generators.

See note [partially-applied ext lemmas]."]
lemma ext_hom {G : Type*} [group G] (f g : free_group α →* G) (h : ∀ a, f (of a) = g (of a)) :
  f = g :=
lift.symm.injective $ funext h

@[to_additive]
theorem lift.of_eq (x : free_group α) : lift of x = x :=
monoid_hom.congr_fun (lift.apply_symm_apply (monoid_hom.id _)) x

@[to_additive]
theorem lift.range_le {s : subgroup β} (H : set.range f ⊆ s) :
  (lift f).range ≤ s :=
by rintros _ ⟨⟨L⟩, rfl⟩; exact list.rec_on L s.one_mem
(λ ⟨x, b⟩ tl ih, bool.rec_on b
    (by simp at ih ⊢; from s.mul_mem
      (s.inv_mem $ H ⟨x, rfl⟩) ih)
    (by simp at ih ⊢; from s.mul_mem (H ⟨x, rfl⟩) ih))

@[to_additive]
theorem lift.range_eq_closure :
  (lift f).range = subgroup.closure (set.range f) :=
begin
  apply le_antisymm (lift.range_le subgroup.subset_closure),
  rw subgroup.closure_le,
  rintros _ ⟨a, rfl⟩,
  exact ⟨of a, by simp only [lift.of]⟩,
end

end lift

section map

variables {β : Type v} (f : α → β) {x y : free_group α}

/-- Any function from `α` to `β` extends uniquely
to a group homomorphism from the free group
over `α` to the free group over `β`. -/
@[to_additive "Any function from `α` to `β` extends uniquely to an additive group homomorphism
from the additive free group over `α` to the additive free group over `β`."]
def map : free_group α →* free_group β :=
monoid_hom.mk'
  (quot.map (list.map $ λ x, (f x.1, x.2)) $ λ L₁ L₂ H, by cases H; simp)
  (by { rintros ⟨L₁⟩ ⟨L₂⟩, simp })

variable {f}

@[simp, to_additive] lemma map.mk : map f (mk L) = mk (L.map (λ x, (f x.1, x.2))) :=
rfl

@[simp, to_additive] lemma map.id (x : free_group α) : map id x = x :=
by rcases x with ⟨L⟩; simp [list.map_id']

@[simp, to_additive] lemma map.id' (x : free_group α) : map (λ z, z) x = x := map.id x

@[to_additive]
theorem map.comp {γ : Type w} (f : α → β) (g : β → γ) (x) :
  map g (map f x) = map (g ∘ f) x :=
by rcases x with ⟨L⟩; simp

@[simp, to_additive] lemma map.of {x} : map f (of x) = of (f x) := rfl

@[to_additive]
theorem map.unique (g : free_group α →* free_group β)
  (hg : ∀ x, g (of x) = of (f x)) : ∀{x}, g x = map f x :=
by rintros ⟨L⟩; exact list.rec_on L g.map_one
(λ ⟨x, b⟩ t (ih : g (mk t) = map f (mk t)), bool.rec_on b
  (show g ((of x)⁻¹ * mk t) = map f ((of x)⁻¹ * mk t),
     by simp [g.map_mul, g.map_inv, hg, ih])
  (show g (of x * mk t) = map f (of x * mk t),
     by simp [g.map_mul, hg, ih]))

@[to_additive]
theorem map_eq_lift : map f x = lift (of ∘ f) x :=
eq.symm $ map.unique _ $ λ x, by simp

/-- Equivalent types give rise to multiplicatively equivalent free groups.

The converse can be found in `group_theory.free_abelian_group_finsupp`,
as `equiv.of_free_group_equiv`
 -/
@[to_additive "Equivalent types give rise to additively equivalent additive free groups.",
simps apply]
def free_group_congr {α β} (e : α ≃ β) : free_group α ≃* free_group β :=
{ to_fun := map e, inv_fun := map e.symm,
  left_inv := λ x, by simp [function.comp, map.comp],
  right_inv := λ x, by simp [function.comp, map.comp],
  map_mul' := monoid_hom.map_mul _ }

@[simp, to_additive]
lemma free_group_congr_refl : free_group_congr (equiv.refl α) = mul_equiv.refl _ :=
mul_equiv.ext map.id

@[simp, to_additive] lemma free_group_congr_symm {α β} (e : α ≃ β) :
  (free_group_congr e).symm = free_group_congr e.symm :=
rfl

@[to_additive]
lemma free_group_congr_trans {α β γ} (e : α ≃ β) (f : β ≃ γ) :
  (free_group_congr e).trans (free_group_congr f) = free_group_congr (e.trans f) :=
mul_equiv.ext $ map.comp _ _

end map

section prod

variables [group α] (x y : free_group α)

/-- If `α` is a group, then any function from `α` to `α`
extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the multiplicative
version of `free_group.sum`. -/
@[to_additive
"If `α` is an additive group, then any function from `α` to `α`
extends uniquely to an additive homomorphism from the
additive free group over `α` to `α`."]
def prod : free_group α →* α := lift id

variables {x y}

@[simp, to_additive] lemma prod_mk :
  prod (mk L) = list.prod (L.map $ λ x, cond x.2 x.1 x.1⁻¹) :=
rfl

@[simp, to_additive] lemma prod.of {x : α} : prod (of x) = x :=
lift.of

@[to_additive]
lemma prod.unique (g : free_group α →* α)
  (hg : ∀ x, g (of x) = x) {x} :
  g x = prod x :=
lift.unique g hg

end prod

@[to_additive]
theorem lift_eq_prod_map {β : Type v} [group β] {f : α → β} {x} :
  lift f x = prod (map f x) :=
begin
  rw ←lift.unique (prod.comp (map f)),
  { refl },
  { simp }
end

section sum

variables [add_group α] (x y : free_group α)

/-- If `α` is a group, then any function from `α` to `α`
extends uniquely to a homomorphism from the
free group over `α` to `α`. This is the additive
version of `prod`. -/
def sum : α :=
@prod (multiplicative _) _ x

variables {x y}

@[simp] lemma sum_mk :
  sum (mk L) = list.sum (L.map $ λ x, cond x.2 x.1 (-x.1)) :=
rfl

@[simp] lemma sum.of {x : α} : sum (of x) = x :=
prod.of

-- note: there are no bundled homs with different notation in the domain and codomain, so we copy
-- these manually
@[simp] lemma sum.map_mul : sum (x * y) = sum x + sum y :=
(@prod (multiplicative _) _).map_mul _ _

@[simp] lemma sum.map_one : sum (1:free_group α) = 0 :=
(@prod (multiplicative _) _).map_one

@[simp] lemma sum.map_inv : sum x⁻¹ = -sum x :=
(prod : free_group (multiplicative α) →* multiplicative α).map_inv _

end sum

/-- The bijection between the free group on the empty type, and a type with one element. -/
@[to_additive
"The bijection between the additive free group on the empty type, and a type with one element."]
def free_group_empty_equiv_unit : free_group empty ≃ unit :=
{ to_fun    := λ _, (),
  inv_fun   := λ _, 1,
  left_inv  := by rintros ⟨_ | ⟨⟨⟨⟩, _⟩, _⟩⟩; refl,
  right_inv := λ ⟨⟩, rfl }

/-- The bijection between the free group on a singleton, and the integers. -/
def free_group_unit_equiv_int : free_group unit ≃ ℤ :=
{ to_fun    := λ x,
   sum begin revert x, apply monoid_hom.to_fun,
    apply map (λ _, (1 : ℤ)),
  end,
  inv_fun   := λ x, of () ^ x,
  left_inv  :=
  begin
    rintros ⟨L⟩,
    refine list.rec_on L rfl _,
    exact (λ ⟨⟨⟩, b⟩ tl ih, by cases b; simp [zpow_add] at ih ⊢; rw ih; refl),
  end,
  right_inv :=
    λ x, int.induction_on x (by simp)
    (λ i ih, by simp at ih; simp [zpow_add, ih])
    (λ i ih, by simp at ih; simp [zpow_add, ih, sub_eq_add_neg, -int.add_neg_one]) }

section category

variables {β : Type u}

@[to_additive]
instance : monad free_group.{u} :=
{ pure := λ α, of,
  map := λ α β f, (map f),
  bind := λ α β x f, lift f x }

@[elab_as_eliminator, to_additive]
protected theorem induction_on
  {C : free_group α → Prop}
  (z : free_group α)
  (C1 : C 1)
  (Cp : ∀ x, C $ pure x)
  (Ci : ∀ x, C (pure x) → C (pure x)⁻¹)
  (Cm : ∀ x y, C x → C y → C (x * y)) : C z :=
quot.induction_on z $ λ L, list.rec_on L C1 $ λ ⟨x, b⟩ tl ih,
bool.rec_on b (Cm _ _ (Ci _ $ Cp x) ih) (Cm _ _ (Cp x) ih)

@[simp, to_additive]
lemma map_pure (f : α → β) (x : α) : f <$> (pure x : free_group α) = pure (f x) := map.of

@[simp, to_additive] lemma map_one (f : α → β) : f <$> (1 : free_group α) = 1 :=
(map f).map_one

@[simp, to_additive]
lemma map_mul (f : α → β) (x y : free_group α) : f <$> (x * y) = f <$> x * f <$> y :=
(map f).map_mul x y

@[simp, to_additive] lemma map_inv (f : α → β) (x : free_group α) : f <$> (x⁻¹) = (f <$> x)⁻¹ :=
(map f).map_inv x

@[simp, to_additive] lemma pure_bind (f : α → free_group β) (x) : pure x >>= f = f x :=
lift.of

@[simp, to_additive] lemma one_bind (f : α → free_group β) : 1 >>= f = 1 :=
(lift f).map_one

@[simp, to_additive] lemma mul_bind (f : α → free_group β) (x y : free_group α) :
  x * y >>= f = (x >>= f) * (y >>= f) :=
(lift f).map_mul _ _

@[simp, to_additive]
lemma inv_bind (f : α → free_group β) (x : free_group α) : x⁻¹ >>= f = (x >>= f)⁻¹ :=
(lift f).map_inv _

@[to_additive]
instance : is_lawful_monad free_group.{u} :=
{ id_map := λ α x, free_group.induction_on x (map_one id) (λ x, map_pure id x)
    (λ x ih, by rw [map_inv, ih]) (λ x y ihx ihy, by rw [map_mul, ihx, ihy]),
  pure_bind := λ α β x f, pure_bind f x,
  bind_assoc := λ α β γ x f g, free_group.induction_on x
    (by iterate 3 { rw one_bind }) (λ x, by iterate 2 { rw pure_bind })
    (λ x ih, by iterate 3 { rw inv_bind }; rw ih)
    (λ x y ihx ihy, by iterate 3 { rw mul_bind }; rw [ihx, ihy]),
  bind_pure_comp_eq_map := λ α β f x, free_group.induction_on x
    (by rw [one_bind, map_one]) (λ x, by rw [pure_bind, map_pure])
    (λ x ih, by rw [inv_bind, map_inv, ih]) (λ x y ihx ihy, by rw [mul_bind, map_mul, ihx, ihy]) }

end category

section reduce

variable [decidable_eq α]

/-- The maximal reduction of a word. It is computable
iff `α` has decidable equality. -/
@[to_additive "The maximal reduction of a word. It is computable
iff `α` has decidable equality."]
def reduce (L : list (α × bool)) : list (α × bool) :=
list.rec_on L [] $ λ hd1 tl1 ih,
list.cases_on ih [hd1] $ λ hd2 tl2,
if hd1.1 = hd2.1 ∧ hd1.2 = bnot hd2.2 then tl2
else hd1 :: hd2 :: tl2

@[simp, to_additive] lemma reduce.cons (x) : reduce (x :: L) =
  list.cases_on (reduce L) [x] (λ hd tl,
  if x.1 = hd.1 ∧ x.2 = bnot hd.2 then tl
  else x :: hd :: tl) := rfl

/-- The first theorem that characterises the function
`reduce`: a word reduces to its maximal reduction. -/
@[to_additive
"The first theorem that characterises the function
`reduce`: a word reduces to its maximal reduction."]
theorem reduce.red : red L (reduce L) :=
begin
  induction L with hd1 tl1 ih,
  case list.nil
  { constructor },
  case list.cons
  { dsimp,
    revert ih,
    generalize htl : reduce tl1 = TL,
    intro ih,
    cases TL with hd2 tl2,
    case list.nil
    { exact red.cons_cons ih },
    case list.cons
    { dsimp only,
      split_ifs with h,
      { transitivity,
        { exact red.cons_cons ih },
        { cases hd1, cases hd2, cases h,
          dsimp at *, subst_vars,
          exact red.step.cons_bnot_rev.to_red } },
      { exact red.cons_cons ih } } }
end

@[to_additive]
theorem reduce.not {p : Prop} :
  ∀ {L₁ L₂ L₃ : list (α × bool)} {x b}, reduce L₁ = L₂ ++ (x, b) :: (x, bnot b) :: L₃ → p
| [] L2 L3 _ _ := λ h, by cases L2; injections
| ((x,b)::L1) L2 L3 x' b' := begin
  dsimp,
  cases r : reduce L1,
  { dsimp, intro h,
    have := congr_arg list.length h,
    simp [-add_comm] at this,
    exact absurd this dec_trivial },
  cases hd with y c,
  dsimp only,
  split_ifs with h; intro H,
  { rw H at r,
    exact @reduce.not L1 ((y,c)::L2) L3 x' b' r },
  rcases L2 with _|⟨a, L2⟩,
  { injections, subst_vars,
    simp at h, cc },
  { refine @reduce.not L1 L2 L3 x' b' _,
    injection H with _ H,
    rw [r, H], refl }
end

/-- The second theorem that characterises the
function `reduce`: the maximal reduction of a word
only reduces to itself. -/
@[to_additive "The second theorem that characterises the
function `reduce`: the maximal reduction of a word
only reduces to itself."]
theorem reduce.min (H : red (reduce L₁) L₂) : reduce L₁ = L₂ :=
begin
  induction H with L1 L' L2 H1 H2 ih,
  { refl },
  { cases H1 with L4 L5 x b,
    exact reduce.not H2 }
end

/-- `reduce` is idempotent, i.e. the maximal reduction
of the maximal reduction of a word is the maximal
reduction of the word. -/
@[simp, to_additive "`reduce` is idempotent, i.e. the maximal reduction
of the maximal reduction of a word is the maximal
reduction of the word."] theorem reduce.idem : reduce (reduce L) = reduce L :=
eq.symm $ reduce.min reduce.red

@[to_additive]
theorem reduce.step.eq (H : red.step L₁ L₂) : reduce L₁ = reduce L₂ :=
let ⟨L₃, HR13, HR23⟩ := red.church_rosser reduce.red (reduce.red.head H) in
(reduce.min HR13).trans (reduce.min HR23).symm

/-- If a word reduces to another word, then they have
a common maximal reduction. -/
@[to_additive "If a word reduces to another word, then they have
a common maximal reduction."]
theorem reduce.eq_of_red (H : red L₁ L₂) : reduce L₁ = reduce L₂ :=
let ⟨L₃, HR13, HR23⟩ := red.church_rosser reduce.red (red.trans H reduce.red) in
(reduce.min HR13).trans (reduce.min HR23).symm

alias reduce.eq_of_red ← red.reduce_eq
alias free_add_group.reduce.eq_of_red ← free_add_group.red.reduce_eq

@[to_additive]
lemma red.reduce_right (h : red L₁ L₂) : red L₁ (reduce L₂) :=
reduce.eq_of_red h ▸ reduce.red

@[to_additive]
lemma red.reduce_left (h : red L₁ L₂) : red L₂ (reduce L₁) :=
(reduce.eq_of_red h).symm ▸ reduce.red

/-- If two words correspond to the same element in
the free group, then they have a common maximal
reduction. This is the proof that the function that
sends an element of the free group to its maximal
reduction is well-defined. -/
@[to_additive
"If two words correspond to the same element in
the additive free group, then they have a common maximal
reduction. This is the proof that the function that
sends an element of the free group to its maximal
reduction is well-defined."]
theorem reduce.sound (H : mk L₁ = mk L₂) : reduce L₁ = reduce L₂ :=
let ⟨L₃, H13, H23⟩ := red.exact.1 H in
(reduce.eq_of_red H13).trans (reduce.eq_of_red H23).symm

/-- If two words have a common maximal reduction,
then they correspond to the same element in the free group. -/
@[to_additive "If two words have a common maximal reduction,
then they correspond to the same element in the additive free group."]
theorem reduce.exact (H : reduce L₁ = reduce L₂) : mk L₁ = mk L₂ :=
red.exact.2 ⟨reduce L₂, H ▸ reduce.red, reduce.red⟩

/-- A word and its maximal reduction correspond to
the same element of the free group. -/
@[to_additive "A word and its maximal reduction correspond to
the same element of the additive free group."]
theorem reduce.self : mk (reduce L) = mk L :=
reduce.exact reduce.idem

/-- If words `w₁ w₂` are such that `w₁` reduces to `w₂`,
then `w₂` reduces to the maximal reduction of `w₁`. -/
@[to_additive "If words `w₁ w₂` are such that `w₁` reduces to `w₂`,
then `w₂` reduces to the maximal reduction of `w₁`."]
theorem reduce.rev (H : red L₁ L₂) : red L₂ (reduce L₁) :=
(reduce.eq_of_red H).symm ▸ reduce.red

/-- The function that sends an element of the free
group to its maximal reduction. -/
@[to_additive "The function that sends an element of the additive free
group to its maximal reduction."]
def to_word : free_group α → list (α × bool) :=
quot.lift reduce $ λ L₁ L₂ H, reduce.step.eq H

@[to_additive]
lemma mk_to_word : ∀{x : free_group α}, mk (to_word x) = x :=
by rintros ⟨L⟩; exact reduce.self

@[to_additive]
lemma to_word_injective : function.injective (to_word : free_group α → list (α × bool)) :=
by rintros ⟨L₁⟩ ⟨L₂⟩; exact reduce.exact

@[simp, to_additive] lemma to_word_inj {x y : free_group α} : to_word x = to_word y ↔ x = y :=
to_word_injective.eq_iff

@[simp, to_additive] lemma to_word_mk : (mk L₁).to_word = reduce L₁ := rfl

@[simp, to_additive] lemma reduce_to_word : ∀ (x : free_group α), reduce (to_word x) = to_word x :=
by { rintro ⟨L⟩, exact reduce.idem }

@[simp, to_additive] lemma to_word_one : (1 : free_group α).to_word = [] := rfl

@[simp, to_additive] lemma to_word_eq_nil_iff {x : free_group α} : (x.to_word = []) ↔ (x = 1) :=
to_word_injective.eq_iff' to_word_one

@[to_additive]
lemma reduce_inv_rev {w : list (α × bool)} : reduce (inv_rev w) = inv_rev (reduce w) :=
begin
  apply reduce.min,
  rw [← red_inv_rev_iff, inv_rev_inv_rev],
  apply red.reduce_left,
  have : red (inv_rev (inv_rev w)) (inv_rev (reduce (inv_rev w))) := reduce.red.inv_rev,
  rwa inv_rev_inv_rev at this
end

@[to_additive]
lemma to_word_inv {x : free_group α} : (x⁻¹).to_word = inv_rev x.to_word :=
begin
  rcases x with ⟨L⟩,
  rw [quot_mk_eq_mk, inv_mk, to_word_mk, to_word_mk, reduce_inv_rev]
end

/-- Constructive Church-Rosser theorem (compare `church_rosser`). -/
@[to_additive "Constructive Church-Rosser theorem (compare `church_rosser`)."]
def reduce.church_rosser (H12 : red L₁ L₂) (H13 : red L₁ L₃) :
  { L₄ // red L₂ L₄ ∧ red L₃ L₄ } :=
⟨reduce L₁, reduce.rev H12, reduce.rev H13⟩

@[to_additive]
instance : decidable_eq (free_group α) :=
to_word_injective.decidable_eq

-- TODO @[to_additive] doesn't succeed, possibly due to a bug
instance red.decidable_rel : decidable_rel (@red α)
| [] []          := is_true red.refl
| [] (hd2::tl2)  := is_false $ λ H, list.no_confusion (red.nil_iff.1 H)
| ((x,b)::tl) [] := match red.decidable_rel tl [(x, bnot b)] with
  | is_true H  := is_true $ red.trans (red.cons_cons H) $
    (@red.step.bnot _ [] [] _ _).to_red
  | is_false H := is_false $ λ H2, H $ red.cons_nil_iff_singleton.1 H2
  end
| ((x1,b1)::tl1) ((x2,b2)::tl2) := if h : (x1, b1) = (x2, b2)
  then match red.decidable_rel tl1 tl2 with
    | is_true H  := is_true $ h ▸ red.cons_cons H
    | is_false H := is_false $ λ H2, H $ h ▸ (red.cons_cons_iff _).1 $ H2
    end
  else match red.decidable_rel tl1 ((x1,bnot b1)::(x2,b2)::tl2) with
    | is_true H  := is_true $ (red.cons_cons H).tail red.step.cons_bnot
    | is_false H := is_false $ λ H2, H $ red.inv_of_red_of_ne h H2
    end

/-- A list containing every word that `w₁` reduces to. -/
def red.enum (L₁ : list (α × bool)) : list (list (α × bool)) :=
list.filter (λ L₂, red L₁ L₂) (list.sublists L₁)

theorem red.enum.sound (H : L₂ ∈ red.enum L₁) : red L₁ L₂ :=
list.of_mem_filter H

theorem red.enum.complete (H : red L₁ L₂) : L₂ ∈ red.enum L₁ :=
list.mem_filter_of_mem (list.mem_sublists.2 $ red.sublist H) H

instance : fintype { L₂ // red L₁ L₂ } :=
fintype.subtype (list.to_finset $ red.enum L₁) $
λ L₂, ⟨λ H, red.enum.sound $ list.mem_to_finset.1 H,
  λ H, list.mem_to_finset.2 $ red.enum.complete H⟩

end reduce

section metric

variable [decidable_eq α]

/-- The length of reduced words provides a norm on a free group. -/
@[to_additive "The length of reduced words provides a norm on an additive free group."]
def norm (x : free_group α) : ℕ := x.to_word.length

@[simp, to_additive] lemma norm_inv_eq {x : free_group α} : norm x⁻¹ = norm x :=
by simp only [norm, to_word_inv, inv_rev_length]

@[simp, to_additive] lemma norm_eq_zero {x : free_group α} : norm x = 0 ↔ x = 1 :=
by simp only [norm, list.length_eq_zero, to_word_eq_nil_iff]

@[simp, to_additive] lemma norm_one : norm (1 : free_group α) = 0 := rfl

@[to_additive]
theorem norm_mk_le : norm (mk L₁) ≤ L₁.length := reduce.red.length_le

@[to_additive]
lemma norm_mul_le (x y : free_group α) : norm (x * y) ≤ norm x + norm y :=
calc norm (x * y) = norm (mk (x.to_word ++ y.to_word)) : by rw [← mul_mk, mk_to_word, mk_to_word]
              ... ≤ (x.to_word ++ y.to_word).length    : norm_mk_le
              ... = norm x + norm y                    : list.length_append _ _

end metric

end free_group
