/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

Natural numbers with infinity, represented as roption ℕ.
-/
import data.pfun data.nat.cast algebra.ordered_group
import tactic.norm_cast

open roption lattice

def enat : Type := roption ℕ

namespace enat

instance : has_zero enat := ⟨some 0⟩
instance : has_one enat := ⟨some 1⟩
instance : has_add enat := ⟨λ x y, ⟨x.dom ∧ y.dom, λ h, get x h.1 + get y h.2⟩⟩
instance : has_le enat := ⟨λ x y, ∃ h : y.dom → x.dom, ∀ hy : y.dom, x.get (h hy) ≤ y.get hy⟩
instance : has_top enat := ⟨none⟩
instance : has_bot enat := ⟨0⟩
instance : has_sup enat := ⟨λ x y, ⟨x.dom ∧ y.dom, λ h, x.get h.1 ⊔ y.get h.2⟩⟩

@[simp] lemma some_eq_coe (n : ℕ) :
  (some n : enat) = (↑n : enat) :=
  -- (@coe nat enat (@coe_to_lift nat enat (@coe_base nat enat nat.cast_coe)) n) = n :=
begin
 induction n with n IH, {refl},
 simp only [nat.succ_eq_add_one, nat.cast_succ, IH.symm],
 apply roption.ext', { show true ↔ (true ∧ true), simp },
 intros h₁ h₂, refl
end

@[reducible] def finite (x : enat) : Prop := x.dom

@[simp] lemma not_finite_top : ¬ finite ⊤ := id

@[simp] lemma finite_coe (n : ℕ) : finite (n : enat) :=
by { rw ← some_eq_coe, exact trivial }

@[simp] lemma finite_zero : finite 0 := trivial

@[simp] lemma finite_one : finite 1 := trivial

@[simp] lemma finite_add {x y : enat} (hx : finite x) (hy : finite y) :
  finite (x + y) := ⟨hx, hy⟩

lemma finite_of_le_coe {x : enat} {y : ℕ} : x ≤ y → x.finite :=
λ ⟨h, _⟩, h $ finite_coe y

instance decidable_finite_top : decidable (⊤ : enat).finite := is_false not_finite_top

instance decidable_finite_coe (n : ℕ) : decidable (n : enat).finite :=
is_true $ finite_coe n

instance decidable_finite_zero : decidable (0 : enat).finite := is_true finite_zero

instance decidable_finite_one : decidable (1 : enat).finite := is_true finite_one

instance decidable_finite_add (x y : enat) [decidable x.finite] [decidable y.finite] :
  decidable (x + y).finite :=
@and.decidable _ _ ‹_› ‹_›

instance : add_comm_monoid enat :=
{ add       := (+),
  zero      := (0),
  add_comm  := λ x y, roption.ext' and.comm (λ _ _, add_comm _ _),
  zero_add  := λ x, roption.ext' (true_and _) (λ _ _, zero_add _),
  add_zero  := λ x, roption.ext' (and_true _) (λ _ _, add_zero _),
  add_assoc := λ x y z, roption.ext' and.assoc (λ _ _, add_assoc _ _ _) }

@[simp] lemma coe_inj {x y : ℕ} : (x : enat) = y ↔ x = y :=
by rw [← some_eq_coe, ← some_eq_coe]; exact roption.some_inj

lemma coe_injective : function.injective (coe : ℕ → enat) :=
λ x y, coe_inj.mp

@[elab_as_eliminator] protected lemma cases_on {P : enat → Prop} : ∀ a : enat,
  P ⊤ →  (∀ n : ℕ, P n) → P a :=
λ x h ih, roption.induction_on x h $ (by simpa using ih)

@[simp] lemma top_add (x : enat) : ⊤ + x = ⊤ :=
roption.ext' (false_and _) (λ h, h.left.elim)

@[simp] lemma add_top (x : enat) : x + ⊤ = ⊤ :=
by rw [add_comm, top_add]

@[simp, squash_cast] lemma coe_zero : ((0 : ℕ) : enat) = 0 := rfl

@[simp, squash_cast] lemma coe_one : ((1 : ℕ) : enat) = 1 := (some_eq_coe 1).symm

@[simp, move_cast] lemma coe_add (x y : ℕ) : ((x + y : ℕ) : enat) = x + y :=
nat.cast_add _ _

@[simp] lemma get_add {x y : enat} (h : (x + y).finite) :
  get (x + y) h = x.get h.1 + y.get h.2 := rfl

@[simp] lemma get_coe (n : ℕ) :
  ∀ h, (n : enat).get h = n :=
by { rw ← some_eq_coe, intro h, refl }

@[simp, squash_cast] lemma coe_get {x : enat} (h : x.finite) : (x.get h : enat) = x :=
by { rw ← some_eq_coe, exact roption.ext' (iff_of_true trivial h) (λ _ _, rfl) }

@[simp] lemma get_zero (h : (0 : enat).finite) : (0 : enat).get h = 0 := rfl

@[simp] lemma get_one (h : (1 : enat).finite) : (1 : enat).get h = 1 := rfl

instance : partial_order enat :=
{ le          := (≤),
  le_refl     := λ x, ⟨id, λ _, le_refl _⟩,
  le_trans    := λ x y z ⟨hxy₁, hxy₂⟩ ⟨hyz₁, hyz₂⟩,
    ⟨hxy₁ ∘ hyz₁, λ _, le_trans (hxy₂ _) (hyz₂ _)⟩,
  le_antisymm := λ x y ⟨hxy₁, hxy₂⟩ ⟨hyx₁, hyx₂⟩, roption.ext' ⟨hyx₁, hxy₁⟩
    (λ _ _, le_antisymm (hxy₂ _) (hyx₂ _)) }

@[simp, elim_cast] lemma coe_le_coe {x y : ℕ} : (x : enat) ≤ y ↔ x ≤ y :=
⟨λ ⟨_, h⟩, by simpa using h (finite_coe y),
 λ h, ⟨λ _, (finite_coe x), λ _, by simpa using h⟩⟩

@[simp, elim_cast] lemma coe_lt_coe {x y : ℕ} : (x : enat) < y ↔ x < y :=
by rw [lt_iff_le_not_le, lt_iff_le_not_le, coe_le_coe, coe_le_coe]

lemma get_le_get {x y : enat} {hx : x.finite} {hy : y.finite} :
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
lt_of_le_of_ne le_top (λ h, absurd (congr_arg finite h) $
  by rw ← some_eq_coe; exact true_ne_false)

@[simp] lemma coe_ne_top (x : ℕ) : (x : enat) ≠ ⊤ := ne_of_lt (coe_lt_top x)

lemma pos_iff_one_le {x : enat} : 0 < x ↔ 1 ≤ x :=
enat.cases_on x ⟨λ _, le_top, λ _, by simpa using (coe_lt_top 0)⟩
  (λ n, ⟨λ h, by { rw [← nat.cast_one, coe_le_coe], rwa [← nat.cast_zero, coe_lt_coe] at h },
      λ h, by { rw [← nat.cast_one, coe_le_coe] at h, rwa [← nat.cast_zero, coe_lt_coe] }⟩)

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
      (λ c, ⟨λ h, and.intro (finite_coe c) (h₁ h.2),
        λ _, add_le_add_left (h₂ _) _⟩),
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
              rw hc; exact nat.le_add_right _ _)) hc)⟩)),
  ..enat.semilattice_sup_bot,
  ..enat.ordered_comm_monoid }

section with_top

def to_with_top (x : enat) [h : decidable x.finite] : with_top ℕ := @roption.to_option ℕ x h

lemma to_with_top_top : to_with_top ⊤ = ⊤ := rfl
@[simp] lemma to_with_top_top' [decidable (⊤ : enat).finite] : to_with_top ⊤ = ⊤ :=
by convert to_with_top_top

lemma to_with_top_zero : to_with_top 0 = 0 := rfl
@[simp] lemma to_with_top_zero' [decidable (0 : enat).finite] : to_with_top 0 = 0 :=
by convert to_with_top_zero

lemma to_with_top_add (m n : ℕ) : to_with_top (m + n) = m + n :=
begin
  delta to_with_top to_option,
  rw (dif_pos $ finite_add (finite_coe m) (finite_coe n)),
  { simp [with_top.some_eq_coe] }
end
@[simp] lemma to_with_top_add' (m n : ℕ) [decidable (finite m)] [decidable (finite n)] :
  to_with_top (m + n) = m + n :=
by convert to_with_top_add m n

lemma to_with_top_coe (n : ℕ) : to_with_top n = n :=
begin
  delta to_with_top to_option,
  rw (dif_pos $ finite_coe n),
  { simp [with_top.some_eq_coe] }
end
@[simp] lemma to_with_top_coe' (n : ℕ) [decidable (finite n)] : to_with_top n = n :=
by convert to_with_top_coe n

@[simp] lemma to_with_top_le {x y : enat} :
  Π [decidable x.finite] [decidable y.finite], by exactI to_with_top x ≤ to_with_top y ↔ x ≤ y :=
enat.cases_on y (by simp) (enat.cases_on x (by simp) (by intros; simp))

@[simp] lemma to_with_top_lt {x y : enat} [decidable x.finite] [decidable y.finite] :
  to_with_top x < to_with_top y ↔ x < y :=
by simp only [lt_iff_le_not_le, to_with_top_le]

end with_top

lemma lt_wf : well_founded ((<) : enat → enat → Prop) :=
show well_founded (λ a b : enat, a < b),
by haveI := classical.dec; simp only [to_with_top_lt.symm] {eta := ff};
    exact inv_image.wf _ (with_top.well_founded_lt nat.lt_wf)

instance : has_well_founded enat := ⟨(<), lt_wf⟩

end enat
