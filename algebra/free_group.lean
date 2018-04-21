/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.group algebra.group_power
import data.equiv data.fintype data.list.basic data.quot
import group_theory.subgroup

universes u v w

variables {α : Type u}

lemma list.append_eq_has_append {L₁ L₂ : list α} : list.append L₁ L₂ = L₁ ++ L₂ := rfl

lemma list.infix_cons {L₁ L₂ : list α} {x : α} : L₁ <:+: L₂ → L₁ <:+: x :: L₂ :=
λ ⟨LP, LS, H⟩, ⟨x :: LP, LS, eq.rec_on H rfl⟩

local attribute [simp] list.append_eq_has_append

namespace free_group

inductive red.step : list (α × bool) → list (α × bool) → Prop
| bnot {L₁ L₂ x b} : red.step (L₁ ++ (x, b) :: (x, bnot b) :: L₂) (L₁ ++ L₂)

inductive red : list (α × bool) → list (α × bool) → Prop
| refl {L} : red L L
| step_trans {L₁ L₂ L₃} (H : free_group.red.step L₁ L₂) :
    red L₂ L₃ → red L₁ L₃

attribute [simp] red.step.bnot
attribute [refl] red.refl

variables {L L₁ L₂ L₃ L₄ : list (α × bool)}

theorem red.trans.aux (H12 : red L₁ L₂) : ∀ {L₃}, red L₂ L₃ → red L₁ L₃ :=
red.rec_on H12 (λ _ _, id) $ λ _ _ _ H1 H2 ih L₃ H23,
red.step_trans H1 $ ih H23

@[trans] theorem red.trans (H12 : red L₁ L₂) (H23 : red L₂ L₃) : red L₁ L₃ :=
red.trans.aux H12 H23

@[simp] lemma red.step.bnot_rev {x b} : red.step (L₁ ++ (x, bnot b) :: (x, b) :: L₂) (L₁ ++ L₂) :=
by cases b; from step.bnot

theorem red.step.length : ∀ {L₁ L₂ : list (α × bool)}, red.step L₁ L₂ → L₂.length + 2 = L₁.length
| _ _ (@red.step.bnot _ L1 L2 x b) := by rw [list.length_append, list.length_append]; refl

theorem red.sizeof : ∀ {L₁ L₂ : list (α × bool)}, red.step L₁ L₂ → L₂.sizeof < L₁.sizeof
| _ _ (@red.step.bnot _ L1 L2 x b) :=
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

theorem red.of_step (H : red.step L₁ L₂) : red L₁ L₂ :=
red.step_trans H red.refl

@[simp] lemma red.bnot {x b} : red (L₁ ++ (x, b) :: (x, bnot b) :: L₂) (L₁ ++ L₂) :=
red.step_trans red.step.bnot red.refl

@[simp] lemma red.step.cons_bnot {x b} : red.step ((x, b) :: (x, bnot b) :: L) L :=
@red.step.bnot _ [] _ _ _

@[simp] lemma red.cons_bnot {x b} : red ((x, b) :: (x, bnot b) :: L) L :=
@red.bnot _ [] _ _ _

@[simp] lemma red.cons_bnot_rev {x b} : red ((x, bnot b) :: (x, b) :: L) L :=
red.of_step $ @red.step.bnot_rev _ [] _ _ _

theorem red.step.append_left : ∀ {L₁ L₂ L₃ : list (α × bool)},
  red.step L₂ L₃ → red.step (L₁ ++ L₂) (L₁ ++ L₃)
| _ _ _ red.step.bnot := by rw [← list.append_assoc, ← list.append_assoc]; constructor

theorem red.step.append_right : ∀ {L₁ L₂ L₃ : list (α × bool)},
  red.step L₁ L₂ → red.step (L₁ ++ L₃) (L₂ ++ L₃)
| _ _ _ red.step.bnot := by simp

theorem red.step.cons {x} (H : red.step L₁ L₂) : red.step (x :: L₁) (x :: L₂) :=
@red.step.append_left _ [x] _ _ H

theorem red.append : ∀ {L₁ L₂ L₃ L₄ : list (α × bool)},
  red L₁ L₃ → red L₂ L₄ → red (L₁ ++ L₂) (L₃ ++ L₄)
| _ _ _ _ red.refl red.refl := red.refl
| _ _ _ _ red.refl (red.step_trans H3 H4) :=
  have _ := red.sizeof H3,
  red.step_trans (red.step.append_left H3) (red.append red.refl H4)
| _ _ _ _ (red.step_trans H1 H2) H3 :=
  have _ := red.sizeof H1,
  red.step_trans (red.step.append_right H1) (red.append H2 H3)

theorem red.cons {x} (H : red L₁ L₂) : red (x :: L₁) (x :: L₂) :=
@red.append _ [x] _ _ _ red.refl H

theorem red.of_cons {x} : red (x :: L₁) (x :: L₂) → red L₁ L₂ :=
begin
  generalize H1 : (x :: L₁ : list _) = L1,
  generalize H2 : (x :: L₂ : list _) = L2,
  intro H,
  induction H with L3 L3 L4 L5 H3 H4 ih generalizing x L₁ L₂,
  case red.refl
  { subst H1; injections; subst_vars },
  case red.step_trans
  { cases H3 with L6 L7 x1 b1,
    subst_vars,
    cases L6 with hd tl,
    case list.nil
    { injection H1 with H5 H6,
      substs H5 H6,
      clear H1 H3,
      transitivity,
      { exact red.cons H4 },
      { simp } },
    case list.cons
    { injection H1 with H5 H6,
      substs H5 H6,
      exact red.trans red.bnot (ih rfl rfl) } }
end

@[simp] lemma red.cons_iff {x} : red (x :: L₁) (x :: L₂) ↔ red L₁ L₂ :=
⟨red.of_cons, red.cons⟩

theorem red.length (H : red L₁ L₂) : ∃ n, L₁.length = L₂.length + 2 * n :=
red.rec_on H (λ _, ⟨0, rfl⟩) $ λ _ _ _ H1 H2 ⟨n, ih⟩,
⟨nat.succ n, red.step.length H1 ▸ ih.symm ▸ rfl⟩

theorem red.antisymm (H : red L₁ L₂) : red L₂ L₁ → L₁ = L₂ :=
red.rec_on H (λ _ _, rfl) $ λ L1 L2 L3 H1 H2 ih H21,
let ⟨n, hn⟩ := red.length (red.trans H2 H21) in
have H3 : list.length L2 = list.length L2 + 2 + 2 * n,
  from (red.step.length H1).symm ▸ hn,
have H4 : list.length L2 + 0 = list.length L2 + (2 * n + 2),
  by simpa using H3,
nat.no_confusion $ nat.add_left_cancel H4

theorem red.step.church_rosser.aux2 : ∀ {L₁ L₂ L₃ L₄ : list (α × bool)} {x1 b1 x2 b2},
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
  match red.step.church_rosser.aux2 H2 with
    | or.inl H3 := or.inl $ by simp [H1, H3]
    | or.inr ⟨L₅, H3, H4⟩ := or.inr
      ⟨_, red.step.cons H3, by simpa [H1] using red.step.cons H4⟩
  end

theorem red.step.church_rosser.aux : ∀ {L₁ L₂ L₃ L₄ : list (α × bool)},
  red.step L₁ L₃ → red.step L₂ L₄ → L₁ = L₂ →
  L₃ = L₄ ∨ ∃ L₅, red.step L₃ L₅ ∧ red.step L₄ L₅
| _ _ _ _ red.step.bnot red.step.bnot H := red.step.church_rosser.aux2 H

theorem red.step.church_rosser (H12 : red.step L₁ L₂) (H13 : red.step L₁ L₃) :
  L₂ = L₃ ∨ ∃ L₄, red.step L₂ L₄ ∧ red.step L₃ L₄ :=
red.step.church_rosser.aux H12 H13 rfl

theorem church_rosser_1 : ∀ {L₁ L₂ L₃ : list (α × bool)},
  red.step L₁ L₂ → red L₁ L₃ →
  red L₂ L₃ ∨ ∃ L₄, red L₂ L₄ ∧ step L₃ L₄
| _ _ _ H12 red.refl := or.inr ⟨_, red.refl, H12⟩
| _ _ _ H12 (red.step_trans H1 H2) :=
  have _ := red.sizeof H1,
  match red.step.church_rosser H12 H1 with
    | or.inl H3 := or.inl $ H3.symm ▸ H2
    | or.inr ⟨L1, H3, H4⟩ := match church_rosser_1 H4 H2 with
      | or.inl H5 := or.inl $ red.step_trans H3 H5
      | or.inr ⟨L2, H5, H6⟩ := or.inr $ ⟨L2, red.step_trans H3 H5, H6⟩
      end
  end

theorem church_rosser : ∀ {L₁ L₂ L₃ : list (α × bool)},
  red L₁ L₂ → red L₁ L₃ → ∃ L₄, red L₂ L₄ ∧ red L₃ L₄
| _ _ _ red.refl H23 := ⟨_, H23, red.refl⟩
| _ _ _ (red.step_trans H1 H2) H23 :=
  have _ := red.sizeof H1,
  match church_rosser_1 H1 H23 with
    | or.inl H3 := church_rosser H2 H3
    | or.inr ⟨L7, H3, H4⟩ :=
        let ⟨L8, H5, H6⟩ := church_rosser H2 H3 in
        ⟨L8, H5, red.step_trans H4 H6⟩
  end

end free_group

variable α

def free_group : Type u :=
quot $ @free_group.red.step α

namespace free_group

variables {α} {L L₁ L₂ L₃ L₄ : list (α × bool)}

def mk (L) : free_group α := quot.mk red.step L

@[simp] lemma quot_mk_eq_mk : quot.mk red.step L = mk L := rfl

@[simp] lemma quot_lift_mk (β : Type*) (f : list (α × bool) → β)
  (H : ∀ L₁ L₂, red.step L₁ L₂ → f L₁ = f L₂) :
quot.lift f H (mk L) = f L := rfl

@[simp] lemma quot_lift_on_mk (β : Type*) (f : list (α × bool) → β)
  (H : ∀ L₁ L₂, red.step L₁ L₂ → f L₁ = f L₂) :
quot.lift_on (mk L) f H = f L := rfl

def inv : list (α × bool) → list (α × bool) :=
λ L, (L.map $ λ x : α × bool, (x.1, bnot x.2)).reverse

theorem red.step.inv (H : red.step L₁ L₂) : red.step (inv L₁) (inv L₂) :=
by cases H; simp [inv]

instance : group (free_group α) :=
{ mul := λ x y, quot.lift_on x
    (λ L₁, quot.lift_on y
       (λ L₂, mk $ L₁ ++ L₂)
       (λ L₂ L₃ H, quot.sound $ red.step.append_left H))
    (λ L₁ L₂ H, quot.induction_on y $
       λ L₃, quot.sound $ red.step.append_right H),
  mul_assoc := λ x y z, quot.induction_on x $ λ L₁,
    quot.induction_on y $ λ L₂, quot.induction_on z $ λ L₃, by simp,
  one := mk [],
  one_mul := λ x, quot.induction_on x $ λ L, rfl,
  mul_one := λ x, quot.induction_on x $ λ L, by simp [(*)],
  inv := λ x, quot.lift_on x
    (λ L, mk $ inv L)
    (λ L₁ L₂ H, quot.sound $ red.step.inv H),
  mul_left_inv := λ x, quot.induction_on x $ λ L,
    list.rec_on L rfl $ λ ⟨x, b⟩ tl ih, eq.trans
      (quot.sound $ by simp [inv]) ih }

@[simp] lemma mul_mk : mk L₁ * mk L₂ = mk (L₁ ++ L₂) := rfl

def of (x : α) : free_group α :=
mk [(x, tt)]

theorem red.step.eqv_gen_of_red (H : red L₁ L₂) : eqv_gen red.step L₁ L₂ :=
red.rec_on H (λ _, eqv_gen.refl _) $ λ _ _ _ H1 _ ih,
eqv_gen.trans _ _ _ (eqv_gen.rel _ _ H1) ih

theorem red.step.exact (H : mk L₁ = mk L₂) :
  ∃ L₃, red L₁ L₃ ∧ red L₂ L₃ :=
eqv_gen.rec_on (quot.exact red.step H)
  (λ L1 L2 H12, ⟨L2, red.of_step H12, red.refl⟩)
  (λ L, ⟨L, red.refl, red.refl⟩)
  (λ L1 L2 H12 ⟨L3, H13, H23⟩, ⟨L3, H23, H13⟩)
  (λ L1 L2 L3 H12 H13 ⟨L4, H14, H24⟩ ⟨L5, H25, H35⟩,
     let ⟨L6, H46, H56⟩ := church_rosser H24 H25 in
     ⟨L6, red.trans H14 H46, red.trans H35 H56⟩)

theorem red.step.sound (L₃) (H13 : red L₁ L₃) (H23 : red L₂ L₃) :
  mk L₁ = mk L₂ :=
quot.eqv_gen_sound $ eqv_gen.trans _ _ _
  (red.step.eqv_gen_of_red H13)
  (eqv_gen.symm _ _ $ red.step.eqv_gen_of_red H23)

theorem red.nil.aux : ∀ {L₁ L₂ : list (α × bool)},
  red L₁ L₂ → L₁ = [] → [] = L₂
| _ _ red.refl                                        H := H.symm
| _ _ (red.step_trans (@red.step.bnot _ [] _ _ _) H2) H := list.no_confusion H

theorem red.nil (H : red [] L) : [] = L :=
red.nil.aux H rfl

theorem red.singleton.aux : ∀ {L₁ L₂ : list (α × bool)} {x},
  red L₁ L₂ → L₁ = [x] → [x] = L₂
| _ _ _ red.refl                                         H := H.symm
| _ _ _ (red.step_trans (@red.step.bnot _ [] _ _ _) H2)  H :=
  list.no_confusion (list.cons.inj H).2
| _ _ _ (red.step_trans (@red.step.bnot _ [x] _ _ _) H2) H :=
  list.no_confusion (list.cons.inj H).2

theorem red.singleton {x} (H : red [x] L₁) : [x] = L₁ :=
red.singleton.aux H rfl

theorem of.inj {x y : α} (H : of x = of y) : x = y :=
let ⟨L₁, hx, hy⟩ := red.step.exact H in
have H1 : _ := (red.singleton hx).trans (red.singleton hy).symm,
by injections

theorem red.step.sublist (H : red.step L₁ L₂) : L₂ <+ L₁ :=
by cases H; simp; constructor; constructor; refl

theorem red.sublist (H : red L₁ L₂) : L₂ <+ L₁ :=
red.rec_on H list.sublist.refl $ λ _ _ _ H1 H2 ih,
list.sublist.trans ih $ red.step.sublist H1

theorem red.inv_of_red_nil.aux {x b} (H : red L₁ L₂) :
  ∀ {L}, L₁ = ((x, b) :: L) → L₂ = [] → red L [(x, bnot b)] :=
red.rec_on H (by cc) $ λ L3 L4 L5 H34,
red.step.cases_on H34 $ λ L6 L7 x1 b1,
list.cases_on L6
  (λ H45 ih L H7 H5, by injections; subst_vars; simpa)
  (λ ⟨x2, b2⟩ tl H45 ih L H7 H5, by injections; subst_vars;
     from red.step_trans red.step.bnot (ih rfl H5))

theorem red.inv_of_red_nil {x b} (H : red ((x, b) :: L) []) :
  red L [(x, bnot b)] :=
red.inv_of_red_nil.aux H rfl rfl

theorem red.inv_of_red_of_ne.aux {x1 b1 x2 b2} 
  (H1 : (x1, b1) ≠ (x2, b2)) (H2 : red L₁ L₂) :
  ∀ {L₃}, L₁ = (x1, b1) :: L₃ → L₂ = (x2, b2) :: L₄ →
  red L₃ ((x1, bnot b1) :: L₂) :=
red.rec_on H2 (by cc) $ λ L5 L6 L7 H56,
red.step.cases_on H56 $ λ L8 L9 x b,
list.cases_on L8
  (λ H67 ih L₃ H6 H7, by injections; subst_vars; simpa)
  (λ ⟨x, b⟩ tl H67 ih L₃ H6 H7, by injections; subst_vars;
    from red.step_trans red.step.bnot (ih rfl H7))

theorem red.inv_of_red_of_ne {x1 b1 x2 b2}
  (H1 : (x1, b1) ≠ (x2, b2))
  (H2 : red ((x1, b1) :: L₁) ((x2, b2) :: L₂)) :
  red L₁ ((x1, bnot b1) :: (x2, b2) :: L₂) :=
red.inv_of_red_of_ne.aux H1 H2 rfl rfl

section to_group

variables {β : Type v} [group β] (f : α → β) {x y : free_group α}

def to_group.aux : list (α × bool) → β :=
λ L, list.prod $ L.map $ λ x, cond x.2 (f x.1) (f x.1)⁻¹

theorem red.step.to_group {f : α → β} (H : red.step L₁ L₂) :
  to_group.aux f L₁ = to_group.aux f L₂ :=
by cases H with _ _ _ b; cases b; simp [to_group.aux]

theorem red.to_group {f : α → β} (H : red L₁ L₂) :
  to_group.aux f L₁ = to_group.aux f L₂ :=
red.rec_on H (λ _, rfl) $ λ _ _ _ H1 H2 ih,
eq.trans (by cases H1 with _ _ _ b; cases b; simp [to_group.aux]) ih

def to_group : free_group α → β :=
quot.lift (to_group.aux f) $ λ L₁ L₂ H, red.step.to_group H

variable {f}

@[simp] lemma to_group.mk : to_group f (mk L) =
  list.prod (L.map $ λ x, cond x.2 (f x.1) (f x.1)⁻¹) :=
rfl

@[simp] lemma to_group.of {x} : to_group f (of x) = f x :=
one_mul _

instance to_group.is_group_hom : is_group_hom (to_group f) :=
⟨λ x y, quot.induction_on x $ λ L₁, quot.induction_on y $ λ L₂, by simp⟩

@[simp] lemma to_group.mul : to_group f (x * y) = to_group f x * to_group f y :=
is_group_hom.mul _ _ _

@[simp] lemma to_group.one : to_group f 1 = 1 :=
is_group_hom.one _

@[simp] lemma to_group.inv : to_group f x⁻¹ = (to_group f x)⁻¹ :=
is_group_hom.inv _ _

theorem to_group.unique (g : free_group α → β) [is_group_hom g]
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = to_group f x :=
quot.induction_on x $ λ L, list.rec_on L (is_group_hom.one g) $
λ ⟨x, b⟩ t (ih : g (mk t) = _), bool.rec_on b
  (show g ((of x)⁻¹ * mk t) = to_group f (mk ((x, ff) :: t)),
     by simp [is_group_hom.mul g, is_group_hom.inv g, hg, ih, to_group, to_group.aux])
  (show g (of x * mk t) = to_group f (mk ((x, tt) :: t)),
     by simp [is_group_hom.mul g, is_group_hom.inv g, hg, ih, to_group, to_group.aux])

theorem to_group.of_eq (x : free_group α) : to_group of x = x :=
eq.symm $ to_group.unique id (λ x, rfl)

theorem to_group.range_subset {s : set β} [is_subgroup s] (H : set.range f ⊆ s) :
  set.range (to_group f) ⊆ s :=
λ y ⟨x, H1⟩, H1 ▸ (quot.induction_on x $ λ L,
list.rec_on L (is_submonoid.one_mem s) $ λ ⟨x, b⟩ tl ih,
bool.rec_on b
  (by simp at ih ⊢; from is_submonoid.mul_mem
    (is_subgroup.inv_mem $ H ⟨x, rfl⟩) ih)
  (by simp at ih ⊢; from is_submonoid.mul_mem (H ⟨x, rfl⟩) ih))

theorem to_group.range_eq_closure :
  set.range (to_group f) = group.closure (set.range f) :=
set.subset.antisymm
  (to_group.range_subset group.subset_closure)
  (group.closure_subset $ λ y ⟨x, hx⟩, ⟨of x, by simpa⟩)

end to_group

section map

variables {β : Type v} (f : α → β) {x y : free_group α}

def map.aux (L : list (α × bool)) : list (β × bool) :=
L.map $ λ x, (f x.1, x.2)

theorem red.map (H : red L₁ L₂) : red (map.aux f L₁) (map.aux f L₂) :=
red.rec_on H (λ _, red.refl) $ λ _ _ _ H1 H2 ih,
red.step_trans (by cases H1; simp [map.aux]) ih

def map (x : free_group α) : free_group β :=
x.lift_on (λ L, mk $ map.aux f L) $
λ L₁ L₂ H, quot.sound $ by cases H; simp [map.aux]

instance map.is_group_hom : is_group_hom (map f) :=
⟨λ x y, quot.induction_on x $ λ L₁, quot.induction_on y $ λ L₂,
by simp [map, map.aux]⟩

variable {f}

@[simp] lemma map.mk : map f (mk L) = mk (L.map (λ x, (f x.1, x.2))) :=
rfl

@[simp] lemma map.id : map id x = x :=
have H1 : (λ (x : α × bool), x) = id := rfl,
quot.induction_on x $ λ L, by simp [H1]

@[simp] lemma map.id' : map (λ z, z) x = x := map.id

theorem map.comp {γ : Type w} {f : α → β} {g : β → γ} {x} :
  map g (map f x) = map (g ∘ f) x :=
quot.induction_on x $ λ L, by simp

@[simp] lemma map.of {x} : map f (of x) = of (f x) := rfl

@[simp] lemma map.mul : map f (x * y) = map f x * map f y :=
is_group_hom.mul _ x y

@[simp] lemma map.one : map f 1 = 1 :=
is_group_hom.one _

@[simp] lemma map.inv : map f x⁻¹ = (map f x)⁻¹ :=
is_group_hom.inv _ x

theorem map.unique (g : free_group α → free_group β) [is_group_hom g]
  (hg : ∀ x, g (of x) = of (f x)) {x} :
  g x = map f x :=
quot.induction_on x $ λ L, list.rec_on L (is_group_hom.one g) $
λ ⟨x, b⟩ t (ih : g (mk t) = map f (mk t)), bool.rec_on b
  (show g ((of x)⁻¹ * mk t) = map f ((of x)⁻¹ * mk t),
     by simp [is_group_hom.mul g, is_group_hom.inv g, hg, ih])
  (show g (of x * mk t) = map f (of x * mk t),
     by simp [is_group_hom.mul g, hg, ih])

def free_group_congr {α β} (e : α ≃ β) : free_group α ≃ free_group β :=
⟨map e, map e.symm,
 λ x, by simp [function.comp, map.comp],
 λ x, by simp [function.comp, map.comp]⟩

theorem map_eq_to_group : map f x = to_group (of ∘ f) x :=
eq.symm $ map.unique _ $ λ x, by simp

end map

section prod

variables [group α] (x y : free_group α)

def prod : α :=
to_group id x

variables {x y}

@[simp] lemma prod_mk :
  prod (mk L) = list.prod (L.map $ λ x, cond x.2 x.1 x.1⁻¹) :=
rfl

@[simp] lemma prod.of {x : α} : prod (of x) = x :=
to_group.of

instance prod.is_group_hom : is_group_hom (@prod α _) :=
to_group.is_group_hom

@[simp] lemma prod.mul : prod (x * y) = prod x * prod y :=
to_group.mul

@[simp] lemma prod.one : prod (1:free_group α) = 1 :=
to_group.one

@[simp] lemma prod.inv : prod x⁻¹ = (prod x)⁻¹ :=
to_group.inv

end prod

theorem to_group_eq_prod_map {β : Type v} [group β] {f : α → β} {x} :
  to_group f x = prod (map f x) :=
eq.symm $ to_group.unique (prod ∘ map f) $ λ _, by simp

section sum

variables [add_group α] (x y : free_group α)

def sum : α :=
@prod (multiplicative _) _ x

variables {x y}

@[simp] lemma sum_mk :
  sum (mk L) = list.sum (L.map $ λ x, cond x.2 x.1 (-x.1)) :=
rfl

@[simp] lemma sum.of {x : α} : sum (of x) = x :=
prod.of

instance sum.is_group_hom : is_group_hom (@sum α _) :=
prod.is_group_hom

@[simp] lemma sum.sum : sum (x * y) = sum x + sum y :=
prod.mul

@[simp] lemma sum.one : sum (1:free_group α) = 0 :=
prod.one

@[simp] lemma sum.inv : sum x⁻¹ = -sum x :=
prod.inv

end sum

def free_group_empty_equiv_unit : free_group empty ≃ unit :=
{ to_fun    := λ _, (),
  inv_fun   := λ _, 1,
  left_inv  := λ x, quot.induction_on x $ λ L,
    match L with [] := rfl end,
  right_inv := λ ⟨⟩, rfl }

def free_group_unit_equiv_int : free_group unit ≃ int :=
{ to_fun    := λ x, sum $ map (λ _, 1) x,
  inv_fun   := λ x, of () ^ x,
  left_inv  := λ x, quot.induction_on x $ λ L, list.rec_on L rfl $
    λ ⟨⟨⟩, b⟩ tl ih, by cases b; simp [gpow_add] at ih ⊢; rw ih; refl,
  right_inv := λ x, int.induction_on x (by simp)
    (λ i ih, by simp at ih; simp [gpow_add, ih])
    (λ i ih, by simp at ih; simp [gpow_add, ih]) }

section reduce

variable [decidable_eq α]

def reduce (L : list (α × bool)) : list (α × bool) :=
list.rec_on L [] $ λ hd1 tl1 ih,
list.cases_on ih [hd1] $ λ hd2 tl2,
if hd1.1 = hd2.1 ∧ hd1.2 = bnot hd2.2 then tl2
else hd1 :: hd2 :: tl2

@[simp] lemma reduce.cons (x) : reduce (x :: L) =
  list.cases_on (reduce L) [x] (λ hd tl,
  if x.1 = hd.1 ∧ x.2 = bnot hd.2 then tl
  else x :: hd :: tl) := rfl

theorem reduce.red : red L (reduce L) :=
begin
  induction L with hd1 tl1 ih,
  case list.nil
  { refl },
  case list.cons
  { dsimp,
    revert ih,
    generalize htl : reduce tl1 = TL,
    intro ih,
    cases TL with hd2 tl2,
    case list.nil
    { exact red.cons ih },
    case list.cons
    { dsimp,
      by_cases h : hd1.fst = hd2.fst ∧ hd1.snd = bnot (hd2.snd),
      { rw [if_pos h],
        transitivity,
        { exact red.cons ih },
        { cases hd1, cases hd2, cases h,
          dsimp at *, subst_vars,
          simp } },
      { rw [if_neg h],
        exact red.cons ih } } }
end

theorem reduce.not {p : Prop} : ∀ {L₁ L₂ L₃ : list (α × bool)} {x b}, reduce L₁ =L₂ ++ (x, b) :: (x, bnot b) :: L₃ → p
| [] L2 L3 _ _ := λ h, by cases L2; injections
| ((x,b)::L1) L2 L3 x' b' := begin
  dsimp,
  cases r : reduce L1,
  { dsimp, intro h,
    have := congr_arg list.length h,
    simp [-add_comm] at this,
    exact absurd this dec_trivial },
  cases hd with y c,
  by_cases x = y ∧ b = bnot c; simp [h]; intro H,
  { rw H at r,
    exact @reduce.not L1 ((y,c)::L2) L3 x' b' r },
  rcases L2 with _|⟨a, L2⟩,
  { injections, subst_vars,
    simp at h, cc },
  { refine @reduce.not L1 L2 L3 x' b' _,
    injection H with _ H,
    rw [r, H], refl }
end

theorem reduce.min (H : red (reduce L₁) L₂) : reduce L₁ = L₂ :=
begin
  revert H,
  generalize h1 : reduce L₁ = L,
  intro H,
  induction H with L1 L1 L2 L3 H1 H2 ih,
  case red.refl
  { refl },
  case red.step_trans
  { cases H1 with L4 L5 x b,
    exact reduce.not h1 }
end

theorem reduce.idem : reduce (reduce L) = reduce L :=
eq.symm $ reduce.min reduce.red

theorem reduce.step.eq (H : red.step L₁ L₂) : reduce L₁ = reduce L₂ :=
let ⟨L₃, HR13, HR23⟩ := church_rosser reduce.red (red.step_trans H reduce.red) in
(reduce.min HR13).trans (reduce.min HR23).symm

theorem reduce.eq_of_red (H : red L₁ L₂) : reduce L₁ = reduce L₂ :=
let ⟨L₃, HR13, HR23⟩ := church_rosser reduce.red (red.trans H reduce.red) in
(reduce.min HR13).trans (reduce.min HR23).symm

theorem reduce.sound (H : mk L₁ = mk L₂) : reduce L₁ = reduce L₂ :=
let ⟨L₃, H13, H23⟩ := red.step.exact H in
(reduce.eq_of_red H13).trans (reduce.eq_of_red H23).symm

theorem reduce.exact (H : reduce L₁ = reduce L₂) : mk L₁ = mk L₂ :=
red.step.sound (reduce L₂) (H ▸ reduce.red) (reduce.red)

theorem reduce.self : mk (reduce L) = mk L :=
reduce.exact reduce.idem

theorem reduce.rev (H : red L₁ L₂) : red L₂ (reduce L₁) :=
(reduce.eq_of_red H).symm ▸ reduce.red

def to_word : free_group α → list (α × bool) :=
quot.lift reduce $ λ L₁ L₂ H, reduce.step.eq H

def to_word.mk {x : free_group α} : mk (to_word x) = x :=
quot.induction_on x $ λ L₁, reduce.self

def to_word.inj (x y : free_group α) : to_word x = to_word y → x = y :=
quot.induction_on x $ λ L₁, quot.induction_on y $ λ L₂, reduce.exact

def reduce.church_rosser (H12 : red L₁ L₂) (H13 : red L₁ L₃) :
  { L₄ // red L₂ L₄ ∧ red L₃ L₄ } :=
⟨reduce L₁, reduce.rev H12, reduce.rev H13⟩

instance : decidable_eq (free_group α) :=
function.injective.decidable_eq to_word.inj

instance red.decidable_rel : decidable_rel (@red α)
| [] [] := is_true red.refl
| [] (hd2::tl2) := is_false $ λ H,
  list.no_confusion $ red.nil H
| ((x,b)::tl) [] := match red.decidable_rel tl [(x, bnot b)] with
  | is_true H  := is_true $ red.trans (red.cons H) $
    red.of_step $ @red.step.bnot _ [] [] _ _
  | is_false H := is_false $ λ H2,
    have H3 : reduce ((x, bnot b) :: (x, b) :: tl) = [(x, bnot b)],
      from reduce.eq_of_red (red.cons H2),
    H $ H3 ▸ reduce.rev (red.cons_bnot_rev)
  end
| ((x1,b1)::tl1) ((x2,b2)::tl2) := if h : (x1, b1) = (x2, b2)
  then match red.decidable_rel tl1 tl2 with
    | is_true H  := is_true $ h ▸ red.cons H
    | is_false H := is_false $ λ H2, H $ h ▸ red.of_cons $ H2
    end
  else match red.decidable_rel tl1 ((x1,bnot b1)::(x2,b2)::tl2) with
    | is_true H  := is_true $ red.trans (red.cons H) $ red.cons_bnot
    | is_false H := is_false $ λ H2, H $ red.inv_of_red_of_ne h H2
    end

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

end free_group
