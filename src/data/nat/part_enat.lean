/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.hom.equiv.basic
import data.part
import data.enat.lattice
import tactic.norm_num

/-!
# Natural numbers with infinity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The natural numbers and an extra `top` element `⊤`. This implementation uses `part ℕ` as an
implementation. Use `ℕ∞` instead unless you care about computability.

## Main definitions

The following instances are defined:

* `ordered_add_comm_monoid part_enat`
* `canonically_ordered_add_monoid part_enat`
* `complete_linear_order part_enat`

There is no additive analogue of `monoid_with_zero`; if there were then `part_enat` could
be an `add_monoid_with_top`.

* `to_with_top` : the map from `part_enat` to `ℕ∞`, with theorems that it plays well
with `+` and `≤`.

* `with_top_add_equiv : part_enat ≃+ ℕ∞`
* `with_top_order_iso : part_enat ≃o ℕ∞`

## Implementation details

`part_enat` is defined to be `part ℕ`.

`+` and `≤` are defined on `part_enat`, but there is an issue with `*` because it's not
clear what `0 * ⊤` should be. `mul` is hence left undefined. Similarly `⊤ - ⊤` is ambiguous
so there is no `-` defined on `part_enat`.

Before the `open_locale classical` line, various proofs are made with decidability assumptions.
This can cause issues -- see for example the non-simp lemma `to_with_top_zero` proved by `rfl`,
followed by `@[simp] lemma to_with_top_zero'` whose proof uses `convert`.


## Tags

part_enat, ℕ∞
-/
open part (hiding some)

/-- Type of natural numbers with infinity (`⊤`) -/
def part_enat : Type := part ℕ

namespace part_enat

/-- The computable embedding `ℕ → part_enat`.

This coincides with the coercion `coe : ℕ → part_enat`, see `part_enat.some_eq_coe`.
However, `coe` is noncomputable so `some` is preferable when computability is a concern. -/
def some : ℕ → part_enat := part.some

instance : has_zero part_enat := ⟨some 0⟩
instance : inhabited part_enat := ⟨0⟩
instance : has_one part_enat := ⟨some 1⟩
instance : has_add part_enat := ⟨λ x y, ⟨x.dom ∧ y.dom, λ h, get x h.1 + get y h.2⟩⟩

instance (n : ℕ) : decidable (some n).dom := is_true trivial

@[simp] lemma dom_some (x : ℕ) : (some x).dom := trivial

instance : add_comm_monoid part_enat :=
{ add       := (+),
  zero      := (0),
  add_comm  := λ x y, part.ext' and.comm (λ _ _, add_comm _ _),
  zero_add  := λ x, part.ext' (true_and _) (λ _ _, zero_add _),
  add_zero  := λ x, part.ext' (and_true _) (λ _ _, add_zero _),
  add_assoc := λ x y z, part.ext' and.assoc (λ _ _, add_assoc _ _ _) }

instance : add_comm_monoid_with_one part_enat :=
{ one := 1,
  nat_cast := some,
  nat_cast_zero := rfl,
  nat_cast_succ := λ _, part.ext' (true_and _).symm (λ _ _, rfl),
  .. part_enat.add_comm_monoid }

lemma some_eq_coe (n : ℕ) : some n = n := rfl

@[simp, norm_cast] lemma coe_inj {x y : ℕ} : (x : part_enat) = y ↔ x = y := part.some_inj

@[simp] lemma dom_coe (x : ℕ) : (x : part_enat).dom := trivial

instance : can_lift part_enat ℕ coe dom := ⟨λ n hn, ⟨n.get hn, part.some_get _⟩⟩

instance : has_le part_enat := ⟨λ x y, ∃ h : y.dom → x.dom, ∀ hy : y.dom, x.get (h hy) ≤ y.get hy⟩
instance : has_top part_enat := ⟨none⟩
instance : has_bot part_enat := ⟨0⟩
instance : has_sup part_enat := ⟨λ x y, ⟨x.dom ∧ y.dom, λ h, x.get h.1 ⊔ y.get h.2⟩⟩

lemma le_def (x y : part_enat) :
  x ≤ y ↔ ∃ h : y.dom → x.dom, ∀ hy : y.dom, x.get (h hy) ≤ y.get hy :=
iff.rfl

@[elab_as_eliminator] protected lemma cases_on' {P : part_enat → Prop} :
  ∀ a : part_enat, P ⊤ → (∀ n : ℕ, P (some n)) → P a :=
part.induction_on

@[elab_as_eliminator] protected lemma cases_on {P : part_enat → Prop} :
  ∀ a : part_enat, P ⊤ → (∀ n : ℕ, P n) → P a :=
by { simp only [← some_eq_coe], exact part_enat.cases_on' }

@[simp] lemma top_add (x : part_enat) : ⊤ + x = ⊤ :=
part.ext' (false_and _) (λ h, h.left.elim)

@[simp] lemma add_top (x : part_enat) : x + ⊤ = ⊤ :=
by rw [add_comm, top_add]

@[simp] lemma coe_get {x : part_enat} (h : x.dom) : (x.get h : part_enat) = x :=
by { rw [← some_eq_coe], exact part.ext' (iff_of_true trivial h) (λ _ _, rfl) }

@[simp, norm_cast] lemma get_coe' (x : ℕ) (h : (x : part_enat).dom) : get (x : part_enat) h = x :=
by rw [← coe_inj, coe_get]

lemma get_coe {x : ℕ} : get (x : part_enat) (dom_coe x) = x := get_coe' _ _

lemma coe_add_get {x : ℕ} {y : part_enat} (h : ((x : part_enat) + y).dom) :
  get ((x : part_enat) + y) h = x + get y h.2 :=
by { simp only [← some_eq_coe] at h ⊢, refl }

@[simp] lemma get_add {x y : part_enat} (h : (x + y).dom) :
  get (x + y) h = x.get h.1 + y.get h.2 := rfl

@[simp] lemma get_zero (h : (0 : part_enat).dom) : (0 : part_enat).get h = 0 := rfl

@[simp] lemma get_one (h : (1 : part_enat).dom) : (1 : part_enat).get h = 1 := rfl

lemma get_eq_iff_eq_some {a : part_enat} {ha : a.dom} {b : ℕ} :
  a.get ha = b ↔ a = some b := get_eq_iff_eq_some

lemma get_eq_iff_eq_coe {a : part_enat} {ha : a.dom} {b : ℕ} :
  a.get ha = b ↔ a = b := by rw [get_eq_iff_eq_some, some_eq_coe]

lemma dom_of_le_of_dom {x y : part_enat} : x ≤ y → y.dom → x.dom := λ ⟨h, _⟩, h

lemma dom_of_le_some {x : part_enat} {y : ℕ} (h : x ≤ some y) : x.dom := dom_of_le_of_dom h trivial

lemma dom_of_le_coe {x : part_enat} {y : ℕ} (h : x ≤ y) : x.dom :=
by { rw [← some_eq_coe] at h, exact dom_of_le_some h }

instance decidable_le (x y : part_enat) [decidable x.dom] [decidable y.dom] : decidable (x ≤ y) :=
if hx : x.dom
then decidable_of_decidable_of_iff
  (show decidable (∀ (hy : (y : part_enat).dom), x.get hx ≤ (y : part_enat).get hy),
    from forall_prop_decidable _) $
  by { dsimp [(≤)], simp only [hx, exists_prop_of_true, forall_true_iff] }
else if hy : y.dom
then is_false $ λ h, hx $ dom_of_le_of_dom h hy
else is_true ⟨λ h, (hy h).elim, λ h, (hy h).elim⟩

/-- The coercion `ℕ → part_enat` preserves `0` and addition. -/
def coe_hom : ℕ →+ part_enat := ⟨coe, nat.cast_zero, nat.cast_add⟩

@[simp] lemma coe_coe_hom : ⇑coe_hom = coe := rfl

instance : partial_order part_enat :=
{ le          := (≤),
  le_refl     := λ x, ⟨id, λ _, le_rfl⟩,
  le_trans    := λ x y z ⟨hxy₁, hxy₂⟩ ⟨hyz₁, hyz₂⟩,
    ⟨hxy₁ ∘ hyz₁, λ _, le_trans (hxy₂ _) (hyz₂ _)⟩,
  le_antisymm := λ x y ⟨hxy₁, hxy₂⟩ ⟨hyx₁, hyx₂⟩, part.ext' ⟨hyx₁, hxy₁⟩
    (λ _ _, le_antisymm (hxy₂ _) (hyx₂ _)) }

lemma lt_def (x y : part_enat) : x < y ↔ ∃ (hx : x.dom), ∀ (hy : y.dom), x.get hx < y.get hy :=
begin
  rw [lt_iff_le_not_le, le_def, le_def, not_exists],
  split,
  { rintro ⟨⟨hyx, H⟩, h⟩,
    by_cases hx : x.dom,
    { use hx, intro hy,
      specialize H hy, specialize h (λ _, hy),
      rw not_forall at h, cases h with hx' h,
      rw not_le at h, exact h },
    { specialize h (λ hx', (hx hx').elim),
      rw not_forall at h, cases h with hx' h,
      exact (hx hx').elim } },
  { rintro ⟨hx, H⟩, exact ⟨⟨λ _, hx, λ hy, (H hy).le⟩, λ hxy h, not_lt_of_le (h _) (H _)⟩ }
end

@[simp, norm_cast] lemma coe_le_coe {x y : ℕ} : (x : part_enat) ≤ y ↔ x ≤ y :=
by { rw [← some_eq_coe, ← some_eq_coe], exact ⟨λ ⟨_, h⟩, h trivial, λ h, ⟨λ _, trivial, λ _, h⟩⟩ }

@[simp, norm_cast] lemma coe_lt_coe {x y : ℕ} : (x : part_enat) < y ↔ x < y :=
by rw [lt_iff_le_not_le, lt_iff_le_not_le, coe_le_coe, coe_le_coe]

@[simp] lemma get_le_get {x y : part_enat} {hx : x.dom} {hy : y.dom} :
  x.get hx ≤ y.get hy ↔ x ≤ y :=
by conv { to_lhs, rw [← coe_le_coe, coe_get, coe_get]}

lemma le_coe_iff (x : part_enat) (n : ℕ) : x ≤ n ↔ ∃ h : x.dom, x.get h ≤ n :=
begin
  rw [← some_eq_coe],
  show (∃ (h : true → x.dom), _) ↔ ∃ h : x.dom, x.get h ≤ n,
  simp only [forall_prop_of_true, some_eq_coe, dom_coe, get_coe']
end

lemma lt_coe_iff (x : part_enat) (n : ℕ) : x < n ↔ ∃ h : x.dom, x.get h < n :=
by simp only [lt_def, forall_prop_of_true, get_coe', dom_coe]

lemma coe_le_iff (n : ℕ) (x : part_enat) : (n : part_enat) ≤ x ↔ ∀ h : x.dom, n ≤ x.get h :=
begin
  rw [← some_eq_coe],
  simp only [le_def, exists_prop_of_true, dom_some, forall_true_iff],
  refl,
end

lemma coe_lt_iff (n : ℕ) (x : part_enat) : (n : part_enat) < x ↔ ∀ h : x.dom, n < x.get h :=
begin
  rw [← some_eq_coe],
  simp only [lt_def, exists_prop_of_true, dom_some, forall_true_iff],
  refl,
end

instance ne_zero.one : ne_zero (1 : part_enat) := ⟨coe_inj.not.mpr dec_trivial⟩

instance semilattice_sup : semilattice_sup part_enat :=
{ sup := (⊔),
  le_sup_left := λ _ _, ⟨and.left, λ _, le_sup_left⟩,
  le_sup_right := λ _ _, ⟨and.right, λ _, le_sup_right⟩,
  sup_le := λ x y z ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩, ⟨λ hz, ⟨hx₁ hz, hy₁ hz⟩,
    λ _, sup_le (hx₂ _) (hy₂ _)⟩,
  ..part_enat.partial_order }

instance order_bot : order_bot part_enat :=
{ bot := (⊥),
  bot_le := λ _, ⟨λ _, trivial, λ _, nat.zero_le _⟩ }

instance order_top : order_top part_enat :=
{ top := (⊤),
  le_top := λ x, ⟨λ h, false.elim h, λ hy, false.elim hy⟩ }

lemma eq_zero_iff {x : part_enat} : x = 0 ↔ x ≤ 0 := eq_bot_iff
lemma ne_zero_iff {x : part_enat} : x ≠ 0 ↔ ⊥ < x := bot_lt_iff_ne_bot.symm

lemma dom_of_lt {x y : part_enat} : x < y → x.dom :=
part_enat.cases_on x not_top_lt $ λ _ _, dom_coe _

lemma top_eq_none : (⊤ : part_enat) = none := rfl

@[simp] lemma coe_lt_top (x : ℕ) : (x : part_enat) < ⊤ :=
ne.lt_top (λ h, absurd (congr_arg dom h) $ by simpa only [dom_coe] using true_ne_false)

@[simp] lemma coe_ne_top (x : ℕ) : (x : part_enat) ≠ ⊤ := ne_of_lt (coe_lt_top x)

lemma not_is_max_coe (x : ℕ) : ¬ is_max (x : part_enat) :=
not_is_max_of_lt (coe_lt_top x)

lemma ne_top_iff {x : part_enat} : x ≠ ⊤ ↔ ∃ (n : ℕ), x = n :=
by simpa only [← some_eq_coe] using part.ne_none_iff

lemma ne_top_iff_dom {x : part_enat} : x ≠ ⊤ ↔ x.dom :=
by classical; exact not_iff_comm.1 part.eq_none_iff'.symm

lemma not_dom_iff_eq_top {x : part_enat} : ¬ x.dom ↔ x = ⊤ :=
iff.not_left ne_top_iff_dom.symm

lemma ne_top_of_lt {x y : part_enat} (h : x < y) : x ≠ ⊤ :=
ne_of_lt $ lt_of_lt_of_le h le_top

lemma eq_top_iff_forall_lt (x : part_enat) : x = ⊤ ↔ ∀ n : ℕ, (n : part_enat) < x :=
begin
  split,
  { rintro rfl n, exact coe_lt_top _ },
  { contrapose!, rw ne_top_iff, rintro ⟨n, rfl⟩, exact ⟨n, irrefl _⟩ }
end

lemma eq_top_iff_forall_le (x : part_enat) : x = ⊤ ↔ ∀ n : ℕ, (n : part_enat) ≤ x :=
(eq_top_iff_forall_lt x).trans
⟨λ h n, (h n).le, λ h n, lt_of_lt_of_le (coe_lt_coe.mpr n.lt_succ_self) (h (n + 1))⟩

lemma pos_iff_one_le {x : part_enat} : 0 < x ↔ 1 ≤ x :=
part_enat.cases_on x (by simp only [iff_true, le_top, coe_lt_top, ← @nat.cast_zero part_enat]) $
  λ n, by { rw [← nat.cast_zero, ← nat.cast_one, part_enat.coe_lt_coe, part_enat.coe_le_coe], refl }

instance : is_total part_enat (≤) :=
{ total := λ x y, part_enat.cases_on x
    (or.inr le_top) (part_enat.cases_on y (λ _, or.inl le_top)
      (λ x y, (le_total x y).elim (or.inr ∘ coe_le_coe.2)
        (or.inl ∘ coe_le_coe.2))) }

noncomputable instance : linear_order part_enat :=
{ le_total := is_total.total,
  decidable_le := classical.dec_rel _,
  max := (⊔),
  max_def := @sup_eq_max_default _ _ (id _) _,
  ..part_enat.partial_order }

instance : bounded_order part_enat :=
{ ..part_enat.order_top,
  ..part_enat.order_bot }

noncomputable instance : lattice part_enat :=
{ inf := min,
  inf_le_left := min_le_left,
  inf_le_right := min_le_right,
  le_inf := λ _ _ _, le_min,
  ..part_enat.semilattice_sup }

instance : ordered_add_comm_monoid part_enat :=
{ add_le_add_left := λ a b ⟨h₁, h₂⟩ c,
    part_enat.cases_on c (by simp)
      (λ c, ⟨λ h, and.intro (dom_coe _) (h₁ h.2),
        λ h, by simpa only [coe_add_get] using add_le_add_left (h₂ _) c⟩),
  ..part_enat.linear_order,
  ..part_enat.add_comm_monoid }

instance : canonically_ordered_add_monoid part_enat :=
{ le_self_add := λ a b, part_enat.cases_on b (le_top.trans_eq (add_top _).symm) $
    λ b, part_enat.cases_on a (top_add _).ge $
      λ a, (coe_le_coe.2 le_self_add).trans_eq (nat.cast_add _ _),
  exists_add_of_le := λ a b, part_enat.cases_on b (λ _, ⟨⊤, (add_top _).symm⟩) $
    λ b, part_enat.cases_on a (λ h, ((coe_lt_top _).not_le h).elim) $ λ a h, ⟨(b - a : ℕ),
        by rw [←nat.cast_add, coe_inj, add_comm, tsub_add_cancel_of_le (coe_le_coe.1 h)]⟩,
  ..part_enat.semilattice_sup,
  ..part_enat.order_bot,
  ..part_enat.ordered_add_comm_monoid }

lemma eq_coe_sub_of_add_eq_coe {x y : part_enat} {n : ℕ} (h : x + y = n) :
  x = ↑(n - y.get (dom_of_le_coe ((le_add_left le_rfl).trans_eq h))) :=
begin
  lift x to ℕ using dom_of_le_coe ((le_add_right le_rfl).trans_eq h),
  lift y to ℕ using dom_of_le_coe ((le_add_left le_rfl).trans_eq h),
  rw [← nat.cast_add, coe_inj] at h,
  rw [get_coe, coe_inj, eq_tsub_of_add_eq h]
end

protected lemma add_lt_add_right {x y z : part_enat} (h : x < y) (hz : z ≠ ⊤) : x + z < y + z :=
begin
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩,
  rcases ne_top_iff.mp hz with ⟨k, rfl⟩,
  induction y using part_enat.cases_on with n,
  { rw [top_add], apply_mod_cast coe_lt_top },
  norm_cast at h, apply_mod_cast add_lt_add_right h
end

protected lemma add_lt_add_iff_right {x y z : part_enat} (hz : z ≠ ⊤) : x + z < y + z ↔ x < y :=
⟨lt_of_add_lt_add_right, λ h, part_enat.add_lt_add_right h hz⟩

protected lemma add_lt_add_iff_left {x y z : part_enat} (hz : z ≠ ⊤) : z + x < z + y ↔ x < y :=
by rw [add_comm z, add_comm z, part_enat.add_lt_add_iff_right hz]

protected lemma lt_add_iff_pos_right {x y : part_enat} (hx : x ≠ ⊤) : x < x + y ↔ 0 < y :=
by { conv_rhs { rw [← part_enat.add_lt_add_iff_left hx] }, rw [add_zero] }

lemma lt_add_one {x : part_enat} (hx : x ≠ ⊤) : x < x + 1 :=
by { rw [part_enat.lt_add_iff_pos_right hx], norm_cast, norm_num }

lemma le_of_lt_add_one {x y : part_enat} (h : x < y + 1) : x ≤ y :=
begin
  induction y using part_enat.cases_on with n, apply le_top,
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩,
  apply_mod_cast nat.le_of_lt_succ, apply_mod_cast h
end

lemma add_one_le_of_lt {x y : part_enat} (h : x < y) : x + 1 ≤ y :=
begin
  induction y using part_enat.cases_on with n, apply le_top,
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩,
  apply_mod_cast nat.succ_le_of_lt, apply_mod_cast h
end

lemma add_one_le_iff_lt {x y : part_enat} (hx : x ≠ ⊤) : x + 1 ≤ y ↔ x < y :=
begin
  split, swap, exact add_one_le_of_lt,
  intro h, rcases ne_top_iff.mp hx with ⟨m, rfl⟩,
  induction y using part_enat.cases_on with n, apply coe_lt_top,
  apply_mod_cast nat.lt_of_succ_le, apply_mod_cast h
end

lemma lt_add_one_iff_lt {x y : part_enat} (hx : x ≠ ⊤) : x < y + 1 ↔ x ≤ y :=
begin
  split, exact le_of_lt_add_one,
  intro h, rcases ne_top_iff.mp hx with ⟨m, rfl⟩,
  induction y using part_enat.cases_on with n, { rw [top_add], apply coe_lt_top },
  apply_mod_cast nat.lt_succ_of_le, apply_mod_cast h
end

lemma add_eq_top_iff {a b : part_enat} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
by apply part_enat.cases_on a; apply part_enat.cases_on b;
  simp; simp only [(nat.cast_add _ _).symm, part_enat.coe_ne_top]; simp

protected lemma add_right_cancel_iff {a b c : part_enat} (hc : c ≠ ⊤) : a + c = b + c ↔ a = b :=
begin
  rcases ne_top_iff.1 hc with ⟨c, rfl⟩,
  apply part_enat.cases_on a; apply part_enat.cases_on b;
  simp [add_eq_top_iff, coe_ne_top, @eq_comm _ (⊤ : part_enat)];
  simp only [(nat.cast_add _ _).symm, add_left_cancel_iff, part_enat.coe_inj, add_comm];
  tauto
end

protected lemma add_left_cancel_iff {a b c : part_enat} (ha : a ≠ ⊤) : a + b = a + c ↔ b = c :=
by rw [add_comm a, add_comm a, part_enat.add_right_cancel_iff ha]

section with_top

/-- Computably converts an `part_enat` to a `ℕ∞`. -/
def to_with_top (x : part_enat) [decidable x.dom] : ℕ∞ := x.to_option

lemma to_with_top_top : to_with_top ⊤ = ⊤ := rfl

@[simp] lemma to_with_top_top' {h : decidable (⊤ : part_enat).dom} : to_with_top ⊤ = ⊤ :=
by convert to_with_top_top

lemma to_with_top_zero : to_with_top 0 = 0 := rfl

@[simp] lemma to_with_top_zero' {h : decidable (0 : part_enat).dom} : to_with_top 0 = 0 :=
by convert to_with_top_zero

lemma to_with_top_some (n : ℕ) : to_with_top (some n) = n := rfl

lemma to_with_top_coe (n : ℕ) {_ : decidable (n : part_enat).dom} : to_with_top n = n :=
by simp only [← some_eq_coe, ← to_with_top_some]

@[simp] lemma to_with_top_coe' (n : ℕ) {h : decidable (n : part_enat).dom} :
  to_with_top (n : part_enat) = n :=
by convert to_with_top_coe n

@[simp] lemma to_with_top_le {x y : part_enat} : Π [decidable x.dom]
  [decidable y.dom], by exactI to_with_top x ≤ to_with_top y ↔ x ≤ y :=
part_enat.cases_on y (by simp) (part_enat.cases_on x (by simp) (by intros; simp))

@[simp] lemma to_with_top_lt {x y : part_enat} [decidable x.dom] [decidable y.dom] :
  to_with_top x < to_with_top y ↔ x < y :=
lt_iff_lt_of_le_iff_le to_with_top_le

end with_top

section with_top_equiv

open_locale classical

@[simp] lemma to_with_top_add {x y : part_enat} :
  to_with_top (x + y) = to_with_top x + to_with_top y :=
by apply part_enat.cases_on y; apply part_enat.cases_on x; simp [← nat.cast_add, ← enat.coe_add]

/-- `equiv` between `part_enat` and `ℕ∞` (for the order isomorphism see
`with_top_order_iso`). -/
noncomputable def with_top_equiv : part_enat ≃ ℕ∞ :=
{ to_fun := λ x, to_with_top x,
  inv_fun := λ x, match x with (option.some n) := coe n | none := ⊤ end,
  left_inv := λ x, by apply part_enat.cases_on x; intros; simp; refl,
  right_inv := λ x, by cases x; simp [with_top_equiv._match_1]; refl }

@[simp] lemma with_top_equiv_top : with_top_equiv ⊤ = ⊤ :=
to_with_top_top'

@[simp] lemma with_top_equiv_coe (n : nat) : with_top_equiv n = n :=
to_with_top_coe' _

@[simp] lemma with_top_equiv_zero : with_top_equiv 0 = 0 :=
by simpa only [nat.cast_zero] using with_top_equiv_coe 0

@[simp] lemma with_top_equiv_le {x y : part_enat} : with_top_equiv x ≤ with_top_equiv y ↔ x ≤ y :=
to_with_top_le

@[simp] lemma with_top_equiv_lt {x y : part_enat} : with_top_equiv x < with_top_equiv y ↔ x < y :=
to_with_top_lt

/-- `to_with_top` induces an order isomorphism between `part_enat` and `ℕ∞`. -/
noncomputable def with_top_order_iso : part_enat ≃o ℕ∞ :=
{ map_rel_iff' := λ _ _, with_top_equiv_le,
  .. with_top_equiv}

@[simp] lemma with_top_equiv_symm_top : with_top_equiv.symm ⊤ = ⊤ :=
rfl

@[simp] lemma with_top_equiv_symm_coe (n : nat) : with_top_equiv.symm n = n :=
rfl

@[simp] lemma with_top_equiv_symm_zero : with_top_equiv.symm 0 = 0 :=
rfl

@[simp] lemma with_top_equiv_symm_le {x y : ℕ∞} :
  with_top_equiv.symm x ≤ with_top_equiv.symm y ↔ x ≤ y :=
by rw ← with_top_equiv_le; simp

@[simp] lemma with_top_equiv_symm_lt {x y : ℕ∞} :
  with_top_equiv.symm x < with_top_equiv.symm y ↔ x < y :=
by rw ← with_top_equiv_lt; simp

/-- `to_with_top` induces an additive monoid isomorphism between `part_enat` and `ℕ∞`. -/
noncomputable def with_top_add_equiv : part_enat ≃+ ℕ∞ :=
{ map_add' := λ x y, by simp only [with_top_equiv]; convert to_with_top_add,
  ..with_top_equiv}

end with_top_equiv

lemma lt_wf : @well_founded part_enat (<) :=
begin
  classical,
  change well_founded (λ a b : part_enat, a < b),
  simp_rw ←to_with_top_lt,
  exact inv_image.wf _ (with_top.well_founded_lt nat.lt_wf)
end

instance : well_founded_lt part_enat := ⟨lt_wf⟩
instance : is_well_order part_enat (<) := { }
instance : has_well_founded part_enat := ⟨(<), lt_wf⟩

section find

variables (P : ℕ → Prop) [decidable_pred P]

/-- The smallest `part_enat` satisfying a (decidable) predicate `P : ℕ → Prop` -/
def find : part_enat := ⟨∃ n, P n, nat.find⟩

@[simp] lemma find_get (h : (find P).dom) : (find P).get h = nat.find h := rfl

lemma find_dom (h : ∃ n, P n) : (find P).dom := h

lemma lt_find (n : ℕ) (h : ∀ m ≤ n, ¬P m) : (n : part_enat) < find P :=
begin
  rw coe_lt_iff, intro h', rw find_get,
  have := @nat.find_spec P _ h',
  contrapose! this,
  exact h _ this
end

lemma lt_find_iff (n : ℕ) : (n : part_enat) < find P ↔ (∀ m ≤ n, ¬P m) :=
begin
  refine ⟨_, lt_find P n⟩,
  intros h m hm,
  by_cases H : (find P).dom,
  { apply nat.find_min H, rw coe_lt_iff at h, specialize h H, exact lt_of_le_of_lt hm h },
  { exact not_exists.mp H m }
end

lemma find_le (n : ℕ) (h : P n) : find P ≤ n :=
by { rw le_coe_iff, refine ⟨⟨_, h⟩, @nat.find_min' P _ _ _ h⟩ }

lemma find_eq_top_iff : find P = ⊤ ↔ ∀ n, ¬P n :=
(eq_top_iff_forall_lt _).trans
⟨λ h n, (lt_find_iff P n).mp (h n) _ le_rfl, λ h n, lt_find P n $ λ _ _, h _⟩

end find

noncomputable instance : linear_ordered_add_comm_monoid_with_top part_enat :=
{ top_add' := top_add,
  .. part_enat.linear_order,
  .. part_enat.ordered_add_comm_monoid,
  .. part_enat.order_top }

noncomputable instance : complete_linear_order part_enat :=
{ inf := (⊓),
  sup := (⊔),
  top := ⊤,
  bot := ⊥,
  le := (≤),
  lt := (<),
  .. part_enat.lattice,
  .. with_top_order_iso.symm.to_galois_insertion.lift_complete_lattice,
  .. part_enat.linear_order, }

end part_enat
