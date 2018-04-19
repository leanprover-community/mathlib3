/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.group algebra.group_power
import data.equiv data.list.basic data.quot
import group_theory.subgroup

universes u v w

variables {α : Type u}

lemma list.append_eq_has_append {L₁ L₂ : list α} : list.append L₁ L₂ = L₁ ++ L₂ := rfl

local attribute [simp] list.append_eq_has_append

namespace free_group

inductive red.step : list (α × bool) → list (α × bool) → Prop
| bnot {L₁ L₂ x b} : red.step (L₁ ++ (x, b) :: (x, bnot b) :: L₂) (L₁ ++ L₂)

inductive red : list (α × bool) → list (α × bool) → Prop
| refl {L} : red L L
| step_trans {L₁ L₂ L₃} (H : free_group.red.step L₁ L₂) :
    red L₂ L₃ → red L₁ L₃

attribute [refl] red.refl

variables {L L₁ L₂ L₃ L₄ : list (α × bool)}

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

theorem red.bnot {x b} : red (L₁ ++ (x, b) :: (x, bnot b) :: L₂) (L₁ ++ L₂) :=
red.step_trans red.step.bnot red.refl

theorem red.step.cons_bnot {x b} : red.step ((x, b) :: (x, bnot b) :: L) L :=
@red.step.bnot _ [] _ _ _

theorem red.cons_bnot {x b} : red ((x, b) :: (x, bnot b) :: L) L :=
@red.bnot _ [] _ _ _

theorem red.step.append_left : ∀ {L₁ L₂ L₃ : list (α × bool)},
  red.step L₂ L₃ → red.step (L₁ ++ L₂) (L₁ ++ L₃)
| _ _ _ red.step.bnot := by rw [← list.append_assoc, ← list.append_assoc]; constructor

theorem red.step.append_right : ∀ {L₁ L₂ L₃ : list (α × bool)},
  red.step L₁ L₂ → red.step (L₁ ++ L₃) (L₂ ++ L₃)
| _ _ _ red.step.bnot := by rw [list.append_assoc, list.append_assoc]; constructor

theorem red.step.cons {x} (H : red.step L₁ L₂) : red.step (x :: L₁) (x :: L₂) :=
@red.step.append_left _ [x] _ _ H

theorem red.trans.aux (H12 : red L₁ L₂) : ∀ {L₃}, red L₂ L₃ → red L₁ L₃ :=
red.rec_on H12 (λ _ _, id) $ λ _ _ _ H1 H2 ih L₃ H23,
red.step_trans H1 $ ih H23

@[trans] theorem red.trans (H12 : red L₁ L₂) (H23 : red L₂ L₃) : red L₁ L₃ :=
red.trans.aux H12 H23

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

variable α

instance : setoid (list (α × bool)) :=
⟨λ L₁ L₂, ∃ L₃, red L₁ L₃ ∧ red L₂ L₃,
 λ L, ⟨L, red.refl, red.refl⟩,
 λ L₁ L₂ ⟨L₃, H13, H23⟩, ⟨L₃, H23, H13⟩,
 λ L₁ L₂ L₃ ⟨L₄, H14, H24⟩ ⟨L₅, H25, H35⟩,
   let ⟨L₆, H46, H56⟩ := church_rosser H24 H25 in
   ⟨L₆, red.trans H14 H46, red.trans H35 H56⟩⟩

end free_group

variable α

def free_group : Type u :=
quotient (free_group.setoid α)

namespace free_group

variables {α} {L L₁ L₂ L₃ L₄ : list (α × bool)}

theorem red.append : ∀ {L₁ L₂ L₃ L₄ : list (α × bool)},
  red L₁ L₃ → red L₂ L₄ → red (L₁ ++ L₂) (L₃ ++ L₄)
| _ _ _ _ red.refl red.refl := red.refl
| _ _ _ _ red.refl (red.step_trans H3 H4) :=
  have _ := red.sizeof H3,
  red.step_trans (red.step.append_left H3) (red.append red.refl H4)
| _ _ _ _ (red.step_trans H1 H2) H3 :=
  have _ := red.sizeof H1,
  red.step_trans (red.step.append_right H1) (red.append H2 H3)

theorem red.cons (H : red L₁ L₂) {x} : red (x :: L₁) (x :: L₂) :=
red.append (@red.refl _ [x]) H

theorem rel.append : L₁ ≈ L₃ → L₂ ≈ L₄ → (L₁ ++ L₂) ≈ (L₃ ++ L₄) :=
λ ⟨L₅, H15, H35⟩ ⟨L₆, H26, H46⟩,
⟨L₅ ++ L₆, red.append H15 H26, red.append H35 H46⟩

def inv : list (α × bool) → list (α × bool) :=
λ L, (L.map $ λ x : α × bool, (x.1, bnot x.2)).reverse

theorem red.inv (H : red L₁ L₂) : red (inv L₁) (inv L₂) :=
red.rec_on H (λ _, red.refl) $ λ _ _ _ H1 H2 ih,
red.step_trans (by cases H1; simp [inv]; constructor) ih

theorem rel.inv : L₁ ≈ L₂ → inv L₁ ≈ inv L₂ :=
λ ⟨L₃, H13, H23⟩, ⟨inv L₃, red.inv H13, red.inv H23⟩

theorem red.inv_append : ∀ {L : list (α × bool)}, red (inv L ++ L) []
| []     := red.refl
| ((x,b)::t) :=
  have H1 : inv t ++ (x, bnot b) :: (x, bnot (bnot b)) :: t
    = inv ((x, b) :: t) ++ (x, b) :: t, by simp [inv],
  H1 ▸ red.trans (red.bnot) red.inv_append

instance : group (free_group α) :=
{ mul := quotient.lift₂ (λ L₁ L₂, ⟦L₁ ++ L₂⟧) $
    λ _ _ _ _ H1 H2, quotient.sound $ rel.append H1 H2,
  mul_assoc := λ x y z, quotient.induction_on₃ x y z $
    λ _ _ _, quotient.sound $ by simp,
  one := ⟦[]⟧,
  one_mul := λ x, quotient.induction_on x $
    λ _, quotient.sound $ setoid.refl _,
  mul_one := λ x, quotient.induction_on x $
    λ _, quotient.sound $ by simp,
  inv := quotient.lift (λ L, ⟦inv L⟧) $
    λ _ _ H, quotient.sound $ rel.inv H,
  mul_left_inv := λ x, quotient.induction_on x $
    λ _, quotient.sound $ ⟨[], red.inv_append, red.refl⟩ }

@[simp] lemma mul_mk : (⟦L₁⟧ * ⟦L₂⟧ : free_group α) = ⟦L₁ ++ L₂⟧ := rfl

def of (x : α) : free_group α :=
⟦[(x, tt)]⟧

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
let ⟨L₁, hx, hy⟩ := quotient.exact H in
have H1 : _ := (red.singleton hx).trans (red.singleton hy).symm,
by injections

section to_group

variables {β : Type v} [group β] (f : α → β) {x y : free_group α}

def to_group.aux : list (α × bool) → β :=
λ L, list.prod $ L.map $ λ x, cond x.2 (f x.1) (f x.1)⁻¹

def red.to_group {f : α → β} (H : red L₁ L₂) :
  to_group.aux f L₁ = to_group.aux f L₂ :=
red.rec_on H (λ _, rfl) $ λ _ _ _ H1 H2 ih,
eq.trans (by cases H1 with _ _ _ b; cases b; simp [to_group.aux]) ih

def to_group : free_group α → β :=
quotient.lift (to_group.aux f) $ λ L₁ L₂ ⟨L₃, H13, H23⟩,
(red.to_group H13).trans (red.to_group H23).symm

variable {f}

@[simp] lemma to_group.mk : to_group f ⟦L⟧ =
  list.prod (L.map $ λ x, cond x.2 (f x.1) (f x.1)⁻¹) :=
rfl

@[simp] lemma to_group.of {x} : to_group f (of x) = f x :=
one_mul _

instance to_group.is_group_hom : is_group_hom (to_group f) :=
⟨λ x y, quotient.induction_on₂ x y $ λ _ _,
by simp [to_group, to_group.aux]⟩

@[simp] lemma to_group.mul : to_group f (x * y) = to_group f x * to_group f y :=
is_group_hom.mul _ _ _

@[simp] lemma to_group.one : to_group f 1 = 1 :=
is_group_hom.one _

@[simp] lemma to_group.inv : to_group f x⁻¹ = (to_group f x)⁻¹ :=
is_group_hom.inv _ _

theorem to_group.unique (g : free_group α → β) [is_group_hom g]
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = to_group f x :=
quotient.induction_on x $ λ L, list.rec_on L (is_group_hom.one g) $
λ ⟨x, b⟩ t ih, bool.rec_on b
  (show g ((of x)⁻¹ * ⟦t⟧) = to_group f ⟦(x, ff) :: t⟧,
     by simp [is_group_hom.mul g, is_group_hom.inv g, hg, ih, to_group, to_group.aux])
  (show g (of x * ⟦t⟧) = to_group f ⟦(x, tt) :: t⟧,
     by simp [is_group_hom.mul g, hg, ih, to_group, to_group.aux])

theorem to_group.of_eq (x : free_group α) : to_group of x = x :=
eq.symm $ to_group.unique id (λ x, rfl)

theorem to_group.range_subset {s : set β} [is_subgroup s] (H : set.range f ⊆ s) :
  set.range (to_group f) ⊆ s :=
λ y ⟨x, H1⟩, H1 ▸ (quotient.induction_on x $ λ L,
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
red.step_trans (by cases H1; simp [map.aux]; constructor) ih

theorem rel.map {f : α → β} : L₁ ≈ L₂ → map.aux f L₁ ≈ map.aux f L₂ :=
λ ⟨L₃, H13, H23⟩, ⟨map.aux f L₃, red.map f H13, red.map f H23⟩

def map (x : free_group α) : free_group β :=
x.lift_on (λ L, ⟦map.aux f L⟧) $
λ L₁ L₂ H, quotient.sound $ rel.map H

instance map.is_group_hom : is_group_hom (map f) :=
⟨λ x y, quotient.induction_on₂ x y $ λ L₁ L₂,
quotient.sound $ by simp [map.aux]⟩

variable {f}

@[simp] lemma map.mk : map f ⟦L⟧ = ⟦L.map (λ x, (f x.1, x.2))⟧ :=
rfl

@[simp] lemma map.id : map id x = x :=
have H1 : (λ (x : α × bool), x) = id := rfl,
quotient.induction_on x $ λ L, quotient.sound $ by simp [map.aux, H1]

@[simp] lemma map.id' : map (λ z, z) x = x := map.id

theorem map.comp {γ : Type w} {f : α → β} {g : β → γ} {x} :
  map g (map f x) = map (g ∘ f) x :=
quotient.induction_on x $ λ L, quotient.sound $ by simp [map.aux]

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
quotient.induction_on x $ λ L, list.rec_on L (is_group_hom.one g) $
λ ⟨x, b⟩ t ih, bool.rec_on b
  (show g ((of x)⁻¹ * ⟦t⟧) = map f ((of x)⁻¹ * ⟦t⟧),
     by simp [is_group_hom.mul g, is_group_hom.inv g, hg, ih])
  (show g (of x * ⟦t⟧) = map f (of x * ⟦t⟧),
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

@[simp] protected lemma prod.quotient.mk :
  prod ⟦L⟧ = list.prod (L.map $ λ x, cond x.2 x.1 x.1⁻¹) :=
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

@[simp] protected lemma sum.quotient.mk :
  sum ⟦L⟧ = list.sum (L.map $ λ x, cond x.2 x.1 (-x.1)) :=
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
  left_inv  := λ x, quotient.induction_on x $ λ L,
    match L with [] := rfl end,
  right_inv := λ ⟨⟩, rfl }

def free_group_unit_equiv_int : free_group unit ≃ int :=
{ to_fun    := λ x, sum $ map (λ _, 1) x,
  inv_fun   := λ x, of () ^ x,
  left_inv  := λ x, quotient.induction_on x $ λ L, list.rec_on L rfl $
    λ ⟨⟨⟩, b⟩ tl ih, by cases b; simp [function.comp, gpow_add] at ih ⊢; rw ih; refl,
  right_inv := λ x, int.induction_on x (by simp)
    (λ i ih, by simp at ih; simp [gpow_add, ih])
    (λ i ih, by simp at ih; simp [gpow_add, ih]) }

section reduce

variable [decidable_eq α]

def reduce.step : list (α × bool) → (α × bool) → list (α × bool)
| (hd::tl) x := if hd.1 = x.1 ∧ hd.2 = bnot x.2 then tl else x::hd::tl
| [] x := [x]

def reduce.core : list (α × bool) → list (α × bool) → list (α × bool)
| L []       := L
| L (hd::tl) := reduce.core (reduce.step L hd) tl

def reduce (L : list (α × bool)) : list (α × bool) :=
reduce.core [] L.reverse

theorem reduce.step.red : ∀ {L : list (α × bool)} {x},
  red (x::L) (reduce.step L x)
| []            _       := red.refl
| ((x1,b1)::tl) (x2,b2) := if H : x1 = x2 ∧ b1 = bnot b2
  then by simp [reduce.step, H]; from red.cons_bnot
  else by simp [reduce.step, H]

theorem reduce.core.red : ∀ {L₁}, red (L₂.reverse ++ L₁) (reduce.core L₁ L₂) :=
list.rec_on L₂ (λ _, red.refl) $ λ hd tl ih L₁, by simp [reduce.core];
from red.trans (red.append red.refl reduce.step.red) ih

theorem reduce.red : red L (reduce L) :=
by simpa using @reduce.core.red _ L.reverse _ []

theorem reduce.step.not : ∀ {L₂ : list (α × bool)} {x1 b1 x2 b2},
  (x2, b2) :: (x2, bnot b2) :: L₁ <:+ reduce.step L₂ (x1, b1) →
  (x2, b2) :: (x2, bnot b2) :: L₁ <:+ L₂
| []            _  _  _ _ ⟨L, H⟩ :=
  by cases L with _ tl; injections; cases tl; injections
| ((x3,b3)::tl) x1 b1 _ _ ⟨L, H⟩ := if h : x3 = x1 ∧ b3 = bnot b1
  then by simp [reduce.step, h] at H; subst H;
    rw ← list.cons_append; from list.suffix_append _ _
  else begin
    simp [reduce.step, h] at H,
    cases L; injections, {cc},
    rw ← h_2,
    exact list.suffix_append _ _
  end

theorem reduce.core.not {x b} : ∀ {L₁},
  (x, b) :: (x, bnot b) :: L <:+ reduce.core L₁ L₂ →
  (x, b) :: (x, bnot b) :: L <:+ L₁ :=
list.rec_on L₂ (λ _, id) $
λ ⟨x, b⟩ tl ih L₁ H, reduce.step.not (ih H)

theorem reduce.min.aux (H : red L₁ L₃) : L₁ = reduce L₂ → reduce L₂ = L₃ :=
red.rec_on H (λ _, eq.symm) $ λ _ _ _ H1 H2 ih H3,
by cases H1 with _ L x b; subst_vars;
  cases reduce.core.not ⟨_, H3⟩ with L1;
  cases L1; injections

theorem reduce.min (H : red (reduce L₁) L₂) : reduce L₁ = L₂ :=
reduce.min.aux H rfl

theorem reduce.idem : reduce (reduce L) = reduce L :=
eq.symm $ reduce.min reduce.red

theorem reduce.eq_of_red (H : red L₁ L₂) : reduce L₁ = reduce L₂ :=
let ⟨L₃, HR13, HR23⟩ := church_rosser reduce.red (red.trans H reduce.red) in
(reduce.min HR13).trans (reduce.min HR23).symm

theorem reduce.rel : L₁ ≈ L₂ → reduce L₁ = reduce L₂ :=
λ ⟨L₃, H13, H23⟩, (reduce.eq_of_red H13).trans
(reduce.eq_of_red H23).symm

theorem reduce.sound (H : ⟦L₁⟧ = ⟦L₂⟧) : reduce L₁ = reduce L₂ :=
reduce.rel $ quotient.exact H

theorem reduce.exact (H : reduce L₁ = reduce L₂) : ⟦L₁⟧ = ⟦L₂⟧ :=
quotient.sound $ ⟨reduce L₂, H ▸ reduce.red, reduce.red⟩

theorem reduce.self : ⟦reduce L⟧ = ⟦L⟧ :=
reduce.exact reduce.idem

def to_word : free_group α → list (α × bool) :=
quotient.lift reduce $ λ L₁ L₂, reduce.rel

def to_word.mk {x : free_group α} : ⟦to_word x⟧ = x :=
quotient.induction_on x $ λ L₁, reduce.self

def to_word.inj (x y : free_group α) : to_word x = to_word y → x = y :=
quotient.induction_on₂ x y $ λ L₁ L₂, reduce.exact

instance : decidable_eq (free_group α) :=
function.injective.decidable_eq to_word.inj

end reduce

end free_group
