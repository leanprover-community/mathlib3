/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Mario Carneiro

Cardinal arithmetic.

Cardinals are represented as quotient over equinumerable types.

Future work:
* define ordinal numbers and relate them to cardinals
* proof `κ + κ = κ` and `κ * κ = κ` for all infinite cardinal `κ`
-/

import data.set.finite data.quot logic.schroeder_bernstein logic.function
noncomputable theory

open function lattice set classical
local attribute [instance] prop_decidable

universes u v w x

instance cardinal.is_equivalent : setoid (Type u) :=
{ r := λα β, nonempty (α ≃ β),
  iseqv := ⟨λα,
    ⟨equiv.refl α⟩,
    λα β ⟨e⟩, ⟨e.symm⟩,
    λα β γ ⟨e₁⟩ ⟨e₂⟩, ⟨e₁.trans e₂⟩⟩ }

def cardinal : Type (u + 1) := quotient cardinal.is_equivalent

namespace cardinal

def mk : Type u → cardinal := quotient.mk

@[simp] theorem mk_def (α : Type u) : @eq cardinal ⟦α⟧ (mk α) := rfl

instance : has_le cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, nonempty $ α ↪ β) $
  assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
    propext ⟨assume ⟨e⟩, ⟨e.congr e₁ e₂⟩, assume ⟨e⟩, ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

theorem le_mk_iff_exists_set {c : cardinal} {α : Type u} :
  c ≤ mk α ↔ ∃ p : set α, mk p = c :=
⟨quotient.induction_on c $ λ β ⟨⟨f, hf⟩⟩,
  ⟨set.range f, eq.symm $ quot.sound ⟨equiv.set.range f hf⟩⟩,
λ ⟨p, e⟩, e ▸ ⟨⟨subtype.val, λ a b, subtype.eq⟩⟩⟩

instance : linear_order cardinal.{u} :=
{ le          := (≤),
  le_refl     := assume a, quot.induction_on a $ λ α, ⟨embedding.refl _⟩,
  le_trans    := assume a b c, quotient.induction_on₃ a b c $ assume α β γ ⟨e₁⟩ ⟨e₂⟩, ⟨e₁.trans e₂⟩,
  le_antisymm := assume a b, quotient.induction_on₂ a b $ assume α β ⟨e₁⟩ ⟨e₂⟩,
    quotient.sound (e₁.antisymm e₂),
  le_total    := assume a b, quotient.induction_on₂ a b $ assume α β, embedding.total }

instance : decidable_linear_order cardinal.{u} :=
{ decidable_le := by apply_instance, ..cardinal.linear_order }

instance : distrib_lattice cardinal.{u} := by apply_instance

instance : has_zero cardinal.{u} := ⟨⟦ulift empty⟧⟩

instance : inhabited cardinal.{u} := ⟨0⟩

theorem ne_zero_iff_nonempty {α : Type u} : mk α ≠ 0 ↔ nonempty α :=
not_iff_comm.1
  ⟨λ h, quotient.sound ⟨(equiv.empty_of_not_nonempty h).trans equiv.ulift.symm⟩,
   λ e, let ⟨h⟩ := quotient.exact e in λ ⟨a⟩, (h a).down.elim⟩

instance : has_one cardinal.{u} := ⟨⟦ulift unit⟧⟩

instance : zero_ne_one_class cardinal.{u} :=
{ zero := 0, one := 1, zero_ne_one :=
  ne.symm $ ne_zero_iff_nonempty.2 ⟨⟨()⟩⟩ }

theorem le_one_iff_subsingleton {α : Type u} : mk α ≤ 1 ↔ subsingleton α :=
⟨λ ⟨f⟩, ⟨λ a b, f.inj (subsingleton.elim _ _)⟩,
 λ ⟨h⟩, ⟨⟨λ a, ⟨()⟩, λ a b _, h _ _⟩⟩⟩

instance : has_add cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, mk (α ⊕ β)) $ assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.sum_congr e₁ e₂⟩⟩

instance : has_mul cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, mk (α × β)) $ assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.prod_congr e₁ e₂⟩⟩

private theorem add_comm (a b : cardinal.{u}) : a + b = b + a :=
quotient.induction_on₂ a b $ assume α β, quotient.sound ⟨equiv.sum_comm α β⟩

private theorem mul_comm (a b : cardinal.{u}) : a * b = b * a :=
quotient.induction_on₂ a b $ assume α β, quotient.sound ⟨equiv.prod_comm α β⟩

private theorem zero_add (a : cardinal.{u}) : 0 + a = a :=
quotient.induction_on a $ assume α, quotient.sound
  ⟨equiv.trans (equiv.sum_congr equiv.ulift (equiv.refl α)) (equiv.empty_sum α)⟩

private theorem zero_mul (a : cardinal.{u}) : 0 * a = 0 :=
quotient.induction_on a $ assume α, quotient.sound
  ⟨equiv.trans (equiv.prod_congr equiv.ulift (equiv.refl α)) $
    equiv.trans (equiv.empty_prod α) equiv.ulift.symm⟩

private theorem one_mul (a : cardinal.{u}) : 1 * a = a :=
quotient.induction_on a $ assume α, quotient.sound
  ⟨equiv.trans (equiv.prod_congr equiv.ulift (equiv.refl α)) (equiv.unit_prod α)⟩

private theorem left_distrib (a b c : cardinal.{u}) : a * (b + c) = a * b + a * c :=
quotient.induction_on₃ a b c $ assume α β γ, quotient.sound ⟨equiv.prod_sum_distrib α β γ⟩

instance : comm_semiring cardinal.{u} :=
{ zero          := 0,
  one           := 1,
  add           := (+),
  mul           := (*),
  zero_add      := zero_add,
  add_zero      := assume a, by rw [add_comm a 0, zero_add a],
  add_assoc     := λa b c, quotient.induction_on₃ a b c $ assume α β γ,
    quotient.sound ⟨equiv.sum_assoc α β γ⟩,
  add_comm      := add_comm,
  zero_mul      := zero_mul,
  mul_zero      := assume a, by rw [mul_comm a 0, zero_mul a],
  one_mul       := one_mul,
  mul_one       := assume a, by rw [mul_comm a 1, one_mul a],
  mul_assoc     := λa b c, quotient.induction_on₃ a b c $ assume α β γ,
    quotient.sound ⟨equiv.prod_assoc α β γ⟩,
  mul_comm      := mul_comm,
  left_distrib  := left_distrib,
  right_distrib := assume a b c,
    by rw [mul_comm (a + b) c, left_distrib c a b, mul_comm c a, mul_comm c b] }

protected def power (a b : cardinal.{u}) : cardinal.{u} :=
quotient.lift_on₂ a b (λα β, mk (β → α)) $ assume α₁ α₂ β₁ β₂ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.arrow_congr e₂ e₁⟩

local notation a ^ b := cardinal.power a b

@[simp] theorem power_zero {a : cardinal} : a ^ 0 = 1 :=
quotient.induction_on a $ assume α, quotient.sound ⟨
  equiv.trans (equiv.arrow_congr equiv.ulift (equiv.refl α)) $
  equiv.trans equiv.arrow_empty_unit $
  equiv.ulift.symm⟩

@[simp] theorem one_power {a : cardinal} : 1 ^ a = 1 :=
quotient.induction_on a $ assume α, quotient.sound ⟨
  equiv.trans (equiv.arrow_congr (equiv.refl α) equiv.ulift) $
  equiv.trans (equiv.arrow_unit_equiv_unit α) $
  equiv.ulift.symm⟩

@[simp] theorem prop_eq_two : mk (ulift Prop) = 2 :=
quot.sound ⟨equiv.ulift.trans $ equiv.Prop_equiv_bool.trans $
  equiv.bool_equiv_unit_sum_unit.trans
  (equiv.sum_congr equiv.ulift equiv.ulift).symm⟩

@[simp] theorem zero_power {a : cardinal} : a ≠ 0 → 0 ^ a = 0 :=
quotient.induction_on a $ assume α heq,
  have nonempty α, from ne_zero_iff_nonempty.1 heq,
  let a := choice this in
  have (α → empty) ≃ empty,
    from ⟨λf, f a, λe a, e, assume f, (f a).rec_on (λ_, (λa', f a) = f), assume e, rfl⟩,
  quotient.sound
    ⟨equiv.trans (equiv.arrow_congr (equiv.refl α) equiv.ulift) $ equiv.trans this equiv.ulift.symm⟩

theorem mul_power {a b c : cardinal} : (a * b) ^ c = a ^ c * b ^ c :=
quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.arrow_prod_equiv_prod_arrow α β γ⟩

theorem power_sum {a b c : cardinal} : a ^ (b + c) = a ^ b * a ^ c :=
quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.sum_arrow_equiv_prod_arrow β γ α⟩

theorem power_mul {a b c : cardinal} : (a ^ b) ^ c = a ^ (b * c) :=
by rw [_root_.mul_comm b c];
from (quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.arrow_arrow_equiv_prod_arrow γ β α⟩)

section order_properties
open sum

theorem zero_le (a : cardinal.{u}) : 0 ≤ a :=
quot.induction_on a $ λ α, ⟨embedding.of_not_nonempty $ λ ⟨⟨a⟩⟩, a.elim⟩

theorem le_zero (a : cardinal.{u}) : a ≤ 0 ↔ a = 0 :=
by simp [le_antisymm_iff, zero_le]

theorem zero_lt_one : (0 : cardinal) < 1 :=
lt_of_le_of_ne (zero_le _) zero_ne_one

theorem add_mono {a b c d : cardinal.{u}} : a ≤ b → c ≤ d → a + c ≤ b + d :=
quotient.induction_on₂ a b $ assume α β, quotient.induction_on₂ c d $ assume γ δ ⟨e₁⟩ ⟨e₂⟩,
  ⟨embedding.sum_congr e₁ e₂⟩

theorem mul_mono {a b c d : cardinal.{u}} : a ≤ b → c ≤ d → a * c ≤ b * d :=
quotient.induction_on₂ a b $ assume α β, quotient.induction_on₂ c d $ assume γ δ ⟨e₁⟩ ⟨e₂⟩,
  ⟨embedding.prod_congr e₁ e₂⟩

theorem power_mono_left {a b c : cardinal.{u}} : a ≤ b → a ^ c ≤ b ^ c :=
quotient.induction_on₃ a b c $ assume α β γ ⟨e⟩, ⟨embedding.arrow_congr_left e⟩

theorem power_mono_right {a b c : cardinal.{u}} : a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c :=
quotient.induction_on₃ a b c $ assume α β γ hα ⟨e⟩,
  have nonempty α, from classical.by_contradiction $ assume hnα,
    hα $ quotient.sound ⟨equiv.trans (equiv.empty_of_not_nonempty hnα) equiv.ulift.symm⟩,
  let ⟨a⟩ := this in
  ⟨@embedding.arrow_congr_right _ _ _ ⟨a⟩ e⟩

theorem le_iff_exists_add {a b : cardinal.{u}} : a ≤ b ↔ ∃ c, b = a + c :=
⟨quotient.induction_on₂ a b $ λ α β ⟨⟨f, hf⟩⟩,
  have (α ⊕ ↥-range f) ≃ β, from
    (equiv.sum_congr (equiv.set.range f hf) (equiv.refl _)).trans $
    (equiv.set.sum_compl (range f)),
  ⟨⟦(-range f : set β)⟧, quotient.sound ⟨this.symm⟩⟩,
 λ ⟨c, e⟩, add_zero a ▸ e.symm ▸ add_mono (le_refl _) (zero_le _)⟩

end order_properties

instance : canonically_ordered_monoid cardinal.{u} :=
{ add_le_add_left       := λ a b h c, add_mono (le_refl _) h,
  lt_of_add_lt_add_left := λ a b c, le_imp_le_iff_lt_imp_lt.1 (add_mono (le_refl _)),
  le_iff_exists_add     := @le_iff_exists_add,
  ..cardinal.comm_semiring, ..cardinal.linear_order }

instance : order_bot cardinal.{u} :=
{ bot := 0, bot_le := zero_le, ..cardinal.linear_order }

theorem cantor (a : cardinal.{u}) : a < 2 ^ a :=
by rw ← prop_eq_two; exact
quot.induction_on a (λ α, ⟨⟨⟨λ a b, ⟨a = b⟩,
  λ a b h, cast (ulift.up.inj (congr_fun h b)).symm rfl⟩⟩,
λ ⟨⟨f, hf⟩⟩, cantor_injective (λ s, f (λ a, ⟨s a⟩)) $
  λ s t h, by funext a; injection congr_fun (hf h) a⟩)

instance : no_top_order cardinal.{u} :=
{ no_top := λ a, ⟨_, cantor a⟩, ..cardinal.linear_order }

def min {ι} (I : nonempty ι) (f : ι → cardinal) : cardinal :=
f $ classical.some $
@embedding.injective_min _ (λ i, (f i).out) I

theorem min_eq {ι} (I) (f : ι → cardinal) : ∃ i, min I f = f i :=
⟨_, rfl⟩

theorem min_le {ι I} (f : ι → cardinal) (i) : min I f ≤ f i :=
by rw [← quotient.out_eq (min I f), ← quotient.out_eq (f i)]; exact
let ⟨g⟩ := classical.some_spec
  (@embedding.injective_min _ (λ i, (f i).out) I) in
⟨g i⟩

theorem le_min {ι I} {f : ι → cardinal} {a} : a ≤ min I f ↔ ∀ i, a ≤ f i :=
⟨λ h i, le_trans h (min_le _ _),
 λ h, let ⟨i, e⟩ := min_eq I f in e.symm ▸ h i⟩

protected theorem wf : @well_founded cardinal.{u} (<) :=
⟨λ a, classical.by_contradiction $ λ h,
  let ι := {c :cardinal // ¬ acc (<) c},
      f : ι → cardinal := subtype.val,
      ⟨⟨c, hc⟩, hi⟩ := @min_eq ι ⟨⟨_, h⟩⟩ f in
    hc (acc.intro _ (λ j ⟨_, h'⟩,
      classical.by_contradiction $ λ hj, h' $
      by have := min_le f ⟨j, hj⟩; rwa hi at this))⟩

instance has_wf : @has_well_founded cardinal.{u} := ⟨(<), cardinal.wf⟩

def succ (c : cardinal) : cardinal :=
@min {c' // c < c'} ⟨⟨_, cantor _⟩⟩ subtype.val 

theorem lt_succ_self (c : cardinal) : c < succ c :=
by cases min_eq _ _ with s e; rw [succ, e]; exact s.2

theorem succ_le {a b : cardinal} : succ a ≤ b ↔ a < b :=
⟨lt_of_lt_of_le (lt_succ_self _), λ h,
  by exact min_le _ (subtype.mk b h)⟩

theorem add_one_le_succ (c : cardinal) : c + 1 ≤ succ c :=
begin
  refine quot.induction_on c (λ α, _) (lt_succ_self c),
  refine quot.induction_on (succ (quot.mk setoid.r α)) (λ β h, _),
  cases h.left with f,
  have : ¬ surjective f := λ hn,
    ne_of_lt h (quotient.sound ⟨equiv.of_bijective ⟨f.inj, hn⟩⟩),
  cases classical.not_forall.1 this with b nex,
  refine ⟨⟨sum.rec (by exact f) _, _⟩⟩,
  { exact λ _, b },
  { intros a b h, rcases a with a|⟨⟨⟨⟩⟩⟩; rcases b with b|⟨⟨⟨⟩⟩⟩,
    { rw f.inj h },
    { exact nex.elim ⟨_, h⟩ },
    { exact nex.elim ⟨_, h.symm⟩ },
    { refl } }
end

def sum {ι} (f : ι → cardinal) : cardinal := ⟦Σ i, (f i).out⟧

theorem le_sum {ι} (f : ι → cardinal) (i) : f i ≤ sum f :=
by rw ← quotient.out_eq (f i); exact
⟨⟨λ a, ⟨i, a⟩, λ a b h, eq_of_heq $ by injection h⟩⟩

def sup {ι} (f : ι → cardinal) : cardinal :=
@min {c // ∀ i, f i ≤ c} ⟨⟨sum f, le_sum f⟩⟩ (λ a, a.1)

theorem le_sup {ι} (f : ι → cardinal) (i) : f i ≤ sup f :=
by dsimp [sup]; cases min_eq _ _ with c hc; rw hc; exact c.2 i

theorem sup_le {ι} (f : ι → cardinal) (a) : sup f ≤ a ↔ ∀ i, f i ≤ a :=
⟨λ h i, le_trans (le_sup _ _) h,
 λ h, by dsimp [sup]; change a with (⟨a, h⟩:subtype _).1; apply min_le⟩

def lift (c : cardinal.{u}) : cardinal.{max u v} :=
quotient.lift_on c (λ α, ⟦ulift α⟧) $ λ α β ⟨e⟩,
quotient.sound ⟨equiv.ulift.trans $ e.trans equiv.ulift.symm⟩

theorem lift_mk (α) : lift.{u v} (mk α) = mk (ulift.{v u} α) := rfl

theorem lift_umax : lift.{u (max u v)} = lift.{u v} :=
funext $ λ a, quot.induction_on a $ λ α,
quotient.sound ⟨equiv.ulift.trans equiv.ulift.symm⟩

@[simp] theorem lift_id (a : cardinal) : lift a = a :=
quot.induction_on a $ λ α, quot.sound ⟨equiv.ulift⟩

@[simp] theorem lift_lift (a : cardinal) : lift.{(max u v) w} (lift.{u v} a) = lift.{u (max v w)} a :=
quot.induction_on a $ λ α,
quotient.sound ⟨equiv.ulift.trans $ equiv.ulift.trans equiv.ulift.symm⟩

theorem lift_mk_le {α : Type u} {β : Type v} :
  lift.{u (max v w)} (mk α) ≤ lift.{v (max u w)} (mk β) ↔ nonempty (α ↪ β) :=
⟨λ ⟨f⟩, ⟨embedding.congr equiv.ulift equiv.ulift f⟩,
 λ ⟨f⟩, ⟨embedding.congr equiv.ulift.symm equiv.ulift.symm f⟩⟩

theorem lift_mk_eq {α : Type u} {β : Type v} :
  lift.{u (max v w)} (mk α) = lift.{v (max u w)} (mk β) ↔ nonempty (α ≃ β) :=
quotient.eq.trans
⟨λ ⟨f⟩, ⟨equiv.ulift.symm.trans $ f.trans equiv.ulift⟩,
 λ ⟨f⟩, ⟨equiv.ulift.trans $ f.trans equiv.ulift.symm⟩⟩

@[simp] theorem lift_le {a b : cardinal} : lift a ≤ lift b ↔ a ≤ b :=
quotient.induction_on₂ a b $ λ α β, 
by rw ← lift_umax; exact lift_mk_le

@[simp] theorem lift_inj {a b : cardinal} : lift a = lift b ↔ a = b :=
by simp [le_antisymm_iff]

@[simp] theorem lift_lt {a b : cardinal} : lift a < lift b ↔ a < b :=
by simp [lt_iff_le_not_le, -not_le]

@[simp] theorem lift_zero : lift 0 = 0 :=
quotient.sound ⟨equiv.ulift.trans $ equiv.ulift.trans equiv.ulift.symm⟩

@[simp] theorem lift_one : lift 1 = 1 :=
quotient.sound ⟨equiv.ulift.trans $ equiv.ulift.trans equiv.ulift.symm⟩

@[simp] theorem lift_add (a b) : lift (a + b) = lift a + lift b :=
quotient.induction_on₂ a b $ λ α β, 
quotient.sound ⟨equiv.ulift.trans (equiv.sum_congr equiv.ulift equiv.ulift).symm⟩

@[simp] theorem lift_mul (a b) : lift (a * b) = lift a * lift b :=
quotient.induction_on₂ a b $ λ α β, 
quotient.sound ⟨equiv.ulift.trans (equiv.prod_congr equiv.ulift equiv.ulift).symm⟩

@[simp] theorem lift_power (a b) : lift (a ^ b) = lift a ^ lift b :=
quotient.induction_on₂ a b $ λ α β, 
quotient.sound ⟨equiv.ulift.trans (equiv.arrow_congr equiv.ulift equiv.ulift).symm⟩

@[simp] theorem lift_min {ι I} (f : ι → cardinal) : lift (min I f) = min I (lift ∘ f) :=
le_antisymm (le_min.2 $ λ a, lift_le.2 $ min_le _ a) $
let ⟨i, e⟩ := min_eq I (lift ∘ f) in
by rw e; exact lift_le.2 (le_min.2 $ λ j, lift_le.1 $
by have := min_le (lift ∘ f) j; rwa e at this)

theorem lift_down {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b ≤ lift a → ∃ a', lift a' = b :=
quotient.induction_on₂ a b $ λ α β,
by dsimp; rw [← lift_id (mk β), ← lift_umax, ← lift_umax.{u v}, lift_mk_le]; exact
λ ⟨f⟩, ⟨mk (set.range f), eq.symm $ lift_mk_eq.2
  ⟨embedding.equiv_of_surjective
    (embedding.cod_restrict _ f set.mem_range_self)
    $ λ ⟨a, ⟨b, e⟩⟩, ⟨b, subtype.eq e⟩⟩⟩

theorem le_lift_iff {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
⟨λ h, let ⟨a', e⟩ := lift_down h in ⟨a', e, lift_le.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_le.2 h⟩

theorem lt_lift_iff {a : cardinal.{u}} {b : cardinal.{max u v}} :
  b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
⟨λ h, let ⟨a', e⟩ := lift_down (le_of_lt h) in
      ⟨a', e, lift_lt.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_lt.2 h⟩

def omega : cardinal.{u} := lift (mk ℕ)

theorem omega_ne_zero : omega ≠ 0 :=
ne_zero_iff_nonempty.2 ⟨⟨0⟩⟩

@[simp] theorem lift_omega : lift omega = omega := lift_lift _

@[simp] theorem mk_fin : ∀ (n : ℕ), mk (fin n) = n
| 0     := quotient.sound ⟨(equiv.empty_of_not_nonempty $
  by exact λ ⟨h⟩, h.elim0).trans equiv.ulift.symm⟩
| (n+1) := by rw [nat.cast_succ, ← mk_fin]; exact
  quotient.sound (fintype.card_eq.1 $ by simp)

@[simp] theorem lift_nat_cast (n : ℕ) : lift n = n :=
by induction n; simp *

theorem lift_mk_fin (n : ℕ) : lift (mk (fin n)) = n := by simp

theorem fintype_card (α : Type u) [fintype α] : mk α = fintype.card α :=
by rw [← lift_mk_fin.{u}, ← lift_id.{u u} (mk α), lift_mk_eq.{u 0 u}];
   exact fintype.card_eq.1 (by simp)

@[simp] theorem nat_cast_le {m n : ℕ} : (m : cardinal) ≤ n ↔ m ≤ n :=
by rw [← lift_mk_fin, ← lift_mk_fin, lift_le]; exact
⟨λ ⟨⟨f, hf⟩⟩, begin
  have : _ = fintype.card _ := finset.card_image_of_injective finset.univ hf,
  simp at this,
  rw [← fintype.card_fin n, ← this],
  exact finset.card_le_of_subset (finset.subset_univ _)
end,
λ h, ⟨⟨λ i, ⟨i.1, lt_of_lt_of_le i.2 h⟩, λ a b h,
  have _, from fin.veq_of_eq h, fin.eq_of_veq this⟩⟩⟩

@[simp] theorem nat_cast_lt {m n : ℕ} : (m : cardinal) < n ↔ m < n :=
by simp [lt_iff_le_not_le, -not_le]

@[simp] theorem nat_cast_inj {m n : ℕ} : (m : cardinal) = n ↔ m = n :=
by simp [le_antisymm_iff]

@[simp] theorem nat_succ (n : ℕ) : succ n = n.succ :=
le_antisymm (succ_le.2 $ nat_cast_lt.2 $ nat.lt_succ_self _) (add_one_le_succ _)

@[simp] theorem succ_zero : succ 0 = 1 :=
by simpa using nat_succ 0

theorem nat_lt_omega (n : ℕ) : (n : cardinal.{u}) < omega :=
succ_le.1 $ by rw [nat_succ, ← lift_mk_fin, omega, lift_mk_le.{0 0 u}]; exact
⟨⟨fin.val, λ a b, fin.eq_of_veq⟩⟩

theorem lt_omega {c : cardinal.{u}} : c < omega ↔ ∃ n : ℕ, c = n :=
⟨λ h, begin
  rcases lt_lift_iff.1 h with ⟨c, rfl, h'⟩,
  rcases le_mk_iff_exists_set.1 h'.1 with ⟨S, rfl⟩,
  suffices : finite S,
  { cases this,
    existsi fintype.card S,
    rw [← lift_nat_cast.{0 u}, lift_inj, fintype_card S] },
  by_contra nf,
  have P : ∀ (n : ℕ) (IH : ∀ i<n, S), ∃ a : S, ¬ ∃ y h, IH y h = a :=
    λ n IH,
    let g : {i | i < n} → S := λ ⟨i, h⟩, IH i h in
    classical.not_forall.1 (λ h, nf
      ⟨fintype.of_surjective g (λ a, subtype.exists.2 (h a))⟩),
  let F : ℕ → S := nat.lt_wf.fix (λ n IH, some (P n IH)),
  refine not_le_of_lt h' ⟨⟨F, _⟩⟩,
  suffices : ∀ (n : ℕ) (m < n), F m ≠ F n,
  { refine λ m n, not_imp_not.1 (λ ne, _),
    rcases lt_trichotomy m n with h|h|h,
    { exact this n m h },
    { contradiction },
    { exact (this m n h).symm } },
  intros n m h,
  have := some_spec (P n (λ y _, F y)),
  rw [← show F n = some (P n (λ y _, F y)),
      from nat.lt_wf.fix_eq (λ n IH, some (P n IH)) n] at this,
  exact λ e, this ⟨m, h, e⟩,
end, λ ⟨n, e⟩, e.symm ▸ nat_lt_omega _⟩

theorem lt_omega_iff_fintype {α : Type u} : mk α < omega ↔ nonempty (fintype α) :=
lt_omega.trans ⟨λ ⟨n, e⟩, begin
  rw [← lift_mk_fin n] at e,
  cases quotient.exact e with f,
  exact ⟨fintype.of_equiv _ f.symm⟩
end, λ ⟨_⟩, by exact ⟨_, fintype_card _⟩⟩

theorem lt_omega_iff_finite {α} {S : set α} : mk S < omega ↔ finite S :=
lt_omega_iff_fintype

end cardinal
