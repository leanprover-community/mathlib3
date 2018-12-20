/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

Natural numbers with infinity, represented as roption ℕ.
-/
import data.pfun algebra.ordered_group

open roption lattice

def enat : Type := roption ℕ

namespace enat

instance : has_zero enat := ⟨some 0⟩
instance : has_one enat := ⟨some 1⟩
instance : has_add enat := ⟨λ x y, ⟨x.dom ∧ y.dom, λ h, get x h.1 + get y h.2⟩⟩
instance : has_coe ℕ enat := ⟨some⟩

@[simp] lemma coe_inj {x y : ℕ} : (x : enat) = y ↔ x = y := roption.some_inj

instance : add_comm_monoid enat :=
{ add       := (+),
  zero      := (0),
  add_comm  := λ x y, roption.ext' and.comm (λ _ _, add_comm _ _),
  zero_add  := λ x, roption.ext' (true_and _) (λ _ _, zero_add _),
  add_zero  := λ x, roption.ext' (and_true _) (λ _ _, add_zero _),
  add_assoc := λ x y z, roption.ext' and.assoc (λ _ _, add_assoc _ _ _) }

instance : has_le enat := ⟨λ x y, ∃ h : y.dom → x.dom, ∀ hy : y.dom, x.get (h hy) ≤ y.get hy⟩
instance : has_top enat := ⟨none⟩
instance : has_bot enat := ⟨0⟩
instance : has_sup enat := ⟨λ x y, ⟨x.dom ∧ y.dom, λ h, x.get h.1 ⊔ y.get h.2⟩⟩

@[elab_as_eliminator] protected lemma cases_on {P : enat → Prop} : ∀ a : enat,
  P ⊤ →  (∀ n : ℕ, P n) → P a :=
roption.induction_on

@[simp] lemma top_add (x : enat) : ⊤ + x = ⊤ :=
roption.ext' (false_and _) (λ h, h.left.elim)

@[simp] lemma add_top (x : enat) : x + ⊤ = ⊤ :=
by rw [add_comm, top_add]

@[simp] lemma coe_zero : ((0 : ℕ) : enat) = 0 := rfl

@[simp] lemma coe_one : ((1 : ℕ) : enat) = 1 := rfl

@[simp] lemma coe_add (x y : ℕ) : ((x + y : ℕ) : enat) = x + y :=
roption.ext' (and_true _).symm (λ _ _, rfl)

@[simp] lemma coe_add_get {x : ℕ} {y : enat} (h : ((x : enat) + y).dom) :
  get ((x : enat) + y) h = x + get y h.2 := rfl

@[simp] lemma get_add {x y : enat} (h : (x + y).dom) :
  get (x + y) h = x.get h.1 + y.get h.2 := rfl

@[simp] lemma coe_get {x : enat} (h : x.dom) : (x.get h : enat) = x :=
roption.ext' (iff_of_true trivial h) (λ _ _, rfl)

@[simp] lemma get_zero (h : (0 : enat).dom) : (0 : enat).get h = 0 := rfl

@[simp] lemma get_one (h : (1 : enat).dom) : (1 : enat).get h = 1 := rfl

lemma dom_of_le_some {x : enat} {y : ℕ} : x ≤ y → x.dom :=
λ ⟨h, _⟩, h trivial

instance : partial_order enat :=
{ le          := (≤),
  le_refl     := λ x, ⟨id, λ _, le_refl _⟩,
  le_trans    := λ x y z ⟨hxy₁, hxy₂⟩ ⟨hyz₁, hyz₂⟩,
    ⟨hxy₁ ∘ hyz₁, λ _, le_trans (hxy₂ _) (hyz₂ _)⟩,
  le_antisymm := λ x y ⟨hxy₁, hxy₂⟩ ⟨hyx₁, hyx₂⟩, roption.ext' ⟨hyx₁, hxy₁⟩
    (λ _ _, le_antisymm (hxy₂ _) (hyx₂ _)) }

@[simp] lemma coe_le_coe {x y : ℕ} : (x : enat) ≤ y ↔ x ≤ y :=
⟨λ ⟨_, h⟩, h trivial, λ h, ⟨λ _, trivial, λ _, h⟩⟩

@[simp] lemma coe_lt_coe {x y : ℕ} : (x : enat) < y ↔ x < y :=
by rw [lt_iff_le_not_le, lt_iff_le_not_le, coe_le_coe, coe_le_coe]

lemma get_le_get {x y : enat} {hx : x.dom} {hy : y.dom} :
  x.get hx ≤ y.get hy ↔ x ≤ y :=
by conv { to_lhs, rw [← coe_le_coe, coe_get, coe_get]}

instance semilattice_sup_bot : semilattice_sup_bot enat :=
{ sup := (⊔),
  bot := (⊥),
  bot_le := λ _, ⟨λ _, trivial, λ _, nat.zero_le _⟩,
  le_sup_left := λ _ _, ⟨and.left, λ _, le_sup_left⟩,
  le_sup_right := λ _ _, ⟨and.right, λ _, le_sup_right⟩,
  sup_le := λ x y z ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩, ⟨λ hz, ⟨hx₁ hz, hy₁ hz⟩,
    λ _, sup_le (hx₂ _) (hy₂ _)⟩,
  ..enat.partial_order }

instance order_top : order_top enat :=
{ top := (⊤),
  le_top := λ x, ⟨λ h, false.elim h, λ hy, false.elim hy⟩,
  ..enat.semilattice_sup_bot }

lemma coe_lt_top (x : ℕ) : (x : enat) < ⊤ :=
lt_of_le_of_ne le_top (λ h, absurd (congr_arg dom h) true_ne_false)

lemma pos_iff_one_le {x : enat} : 0 < x ↔ 1 ≤ x :=
enat.cases_on x ⟨λ _, le_top, λ _, coe_lt_top _⟩
  (λ n, ⟨λ h, enat.coe_le_coe.2 (enat.coe_lt_coe.1 h),
    λ h, enat.coe_lt_coe.2 (enat.coe_le_coe.1 h)⟩)

noncomputable instance : decidable_linear_order enat :=
{ le_total := λ x y, enat.cases_on x
    (or.inr le_top) (enat.cases_on y (λ _, or.inl le_top)
      (λ x y, (le_total x y).elim (or.inr ∘ coe_le_coe.2)
        (or.inl ∘ coe_le_coe.2))),
  decidable_le := classical.dec_rel _,
  ..enat.partial_order }

noncomputable instance : bounded_lattice enat :=
{ inf := min,
  inf_le_left := min_le_left,
  inf_le_right := min_le_right,
  le_inf := λ _ _ _, le_min,
  ..enat.order_top,
  ..enat.semilattice_sup_bot }

lemma sup_eq_max {a b : enat} : a ⊔ b = max a b :=
le_antisymm (sup_le (le_max_left _ _) (le_max_right _ _))
  (max_le le_sup_left le_sup_right)

lemma inf_eq_min {a b : enat} : a ⊓ b = min a b := rfl

instance : ordered_comm_monoid enat :=
{ add_le_add_left := λ a b ⟨h₁, h₂⟩ c,
    enat.cases_on c (by simp)
      (λ c, ⟨λ h, and.intro trivial (h₁ h.2),
        λ _, add_le_add_left (h₂ _) c⟩),
  lt_of_add_lt_add_left := λ a b c, enat.cases_on a
    (λ h, by simpa [lt_irrefl] using h)
    (λ a, enat.cases_on b
      (λ h, absurd h (not_lt_of_ge (by rw add_top; exact le_top)))
      (λ b, enat.cases_on c
        (λ _, coe_lt_top _)
        (λ c h,  coe_lt_coe.2 (by rw [← coe_add, ← coe_add, coe_lt_coe] at h;
            exact lt_of_add_lt_add_left h)))),
  ..enat.decidable_linear_order,
  ..enat.add_comm_monoid }

instance : canonically_ordered_monoid enat :=
{ le_iff_exists_add := λ a b, enat.cases_on b
    (iff_of_true le_top ⟨⊤, (add_top _).symm⟩)
    (λ b, enat.cases_on a
      (iff_of_false (not_le_of_gt (coe_lt_top _))
        (not_exists.2 (λ x, ne_of_lt (by rw [top_add]; exact coe_lt_top _))))
      (λ a, ⟨λ h, ⟨(b - a : ℕ),
          by rw [← coe_add, coe_inj, add_comm, nat.sub_add_cancel (coe_le_coe.1 h)]⟩,
        (λ ⟨c, hc⟩, enat.cases_on c
          (λ hc, hc.symm ▸ show (a : enat) ≤ a + ⊤, by rw [add_top]; exact le_top)
          (λ c (hc : (b : enat) = a + c),
            coe_le_coe.2 (by rw [← coe_add, coe_inj] at hc;
              rw hc; exact nat.le_add_right _ _)) hc)⟩))
  ..enat.ordered_comm_monoid }

end enat
 
