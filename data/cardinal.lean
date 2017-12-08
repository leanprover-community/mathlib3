/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Cardinal arithmetic.

Cardinals are represented as quotient over equinumerable types.

Future work:
* define ordinal numbers and relate them to cardinals
* proof well-ordering of the cardinal numbers
* proof `κ + κ = κ` and `κ * κ = κ` for all infinite cardinal `κ`
-/

import data.set data.quot data.equiv order.fixed_points logic.function order.zorn
noncomputable theory

open function lattice set classical
local attribute [instance] prop_decidable

universes u v w x

lemma equiv.of_bijective {α : Type u} {β : Type v} {f : α → β} (hf : bijective f) :
  nonempty (α ≃ β) :=
by_cases
  (assume : nonempty α,
    let ⟨a⟩ := this in
    let hi : inhabited α := ⟨a⟩ in
    ⟨⟨f, @inv_fun _ _ ⟨a⟩ f,
      @left_inverse_inv_fun _ _ f hi hf.1,
      @right_inverse_inv_fun _ _ f hi hf.2⟩⟩)
  (assume hα : ¬ nonempty α,
    have hβ : ¬ nonempty β,
      from assume ⟨b⟩, let ⟨a, ha⟩ := hf.2 b in hα ⟨a⟩,
    ⟨⟨λa, (hα ⟨a⟩).elim, λb, (hβ ⟨b⟩).elim,
      λa, (hα ⟨a⟩).elim, λb, (hβ ⟨b⟩).elim⟩⟩)

structure embedding (α : Sort*) (β : Sort*) :=
(to_fun : α → β)
(inj    : injective to_fun)

namespace embedding

protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}
  (e₁ : α ≃ β) (e₂ : γ ≃ δ) : embedding α γ → embedding β δ
| ⟨f, hf⟩ := ⟨e₂.to_fun ∘ f ∘ e₁.inv_fun, assume x y h,
  begin
    apply (e₁.symm.apply_eq_iff_eq x y).mp,
    cases e₁,
    apply @hf _ _ ((e₂.apply_eq_iff_eq _ _).mp h)
  end⟩

protected def of_surjective {α : Type u} {β : Type v} {f : β → α} (hf : surjective f) :
  embedding α β :=
⟨surj_inv hf, injective_surj_inv _⟩

protected def of_not_nonempty {α : Type u} {β : Type v} (hα : ¬ nonempty α) : embedding α β :=
⟨λa, (hα ⟨a⟩).elim, assume a, (hα ⟨a⟩).elim⟩

section antisymm
variables {α : Type u} {β : Type v}

lemma schroeder_bernstein {f : α → β} {g : β → α}
  (hf : injective f) (hg : injective g) : ∃h:α→β, bijective h :=
let s : set α := lfp $ λs, - (g '' - (f '' s)) in
have hs : s = - (g '' - (f '' s)),
  from lfp_eq $ assume s t h,
    compl_subset_compl_iff_subset.mpr $ image_subset _ $
    compl_subset_compl_iff_subset.mpr $ image_subset _ h,

have hns : - s = g '' - (f '' s),
  from lattice.neg_eq_neg_of_eq $ by simp [hs.symm],

let g' := λa, @inv_fun β α ⟨f a⟩ g a in
have g'g : g' ∘ g = id,
  from funext $ assume b, @left_inverse_inv_fun _ _ _ ⟨f (g b)⟩ hg b,
have hg'ns : g' '' (-s) = - (f '' s),
  by rw [hns, ←image_comp, g'g, image_id],

let h := λa, if a ∈ s then f a else g' a in

have h '' univ = univ,
  from calc h '' univ = h '' s ∪ h '' (- s) : by rw [←image_union, union_compl_self]
    ... = f '' s ∪ g' '' (-s) :
      congr (congr_arg (∪)
        (image_congr $ by simp [h, if_pos] {contextual := tt}))
        (image_congr $ by simp [h, if_neg] {contextual := tt})
    ... = univ : by rw [hg'ns, union_compl_self],
have surjective h,
  from assume b,
  have b ∈ h '' univ, by rw [this]; trivial,
  let ⟨a, _, eq⟩ := this in
  ⟨a, eq⟩,

have split : ∀x∈s, ∀y∉s, h x = h y → false,
  from assume x hx y hy eq,
  have y ∈ g '' - (f '' s), by rwa [←hns],
  let ⟨y', hy', eq_y'⟩ := this in
  have f x = y',
    from calc f x = g' y : by simp [h, hx, hy, if_pos, if_neg] at eq; assumption
      ... = (g' ∘ g) y' : by simp [(∘), eq_y']
      ... = _ : by simp [g'g],
  have y' ∈ f '' s, from this ▸ mem_image_of_mem _ hx,
  hy' this,
have injective h,
  from assume x y eq,
  by_cases
    (assume hx : x ∈ s, by_cases
      (assume hy : y ∈ s, by simp [h, hx, hy, if_pos, if_neg] at eq; exact hf eq)
      (assume hy : y ∉ s, (split x hx y hy eq).elim))
    (assume hx : x ∉ s, by_cases
      (assume hy : y ∈ s, (split y hy x hx eq.symm).elim)
      (assume hy : y ∉ s,
        have x ∈ g '' - (f '' s), by rwa [←hns],
        let ⟨x', hx', eqx⟩ := this in
        have y ∈ g '' - (f '' s), by rwa [←hns],
        let ⟨y', hy', eqy⟩ := this in
        have g' x = g' y, by simp [h, hx, hy, if_pos, if_neg] at eq; assumption,
        have (g' ∘ g) x' = (g' ∘ g) y', by simp [(∘), eqx, eqy, this],
        have x' = y', by rwa [g'g] at this,
        calc x = g x' : eqx.symm
          ... = g y' : by rw [this]
          ... = y : eqy)),

⟨h, ‹injective h›, ‹surjective h›⟩

lemma antisymm : embedding α β → embedding β α → nonempty (equiv α β)
| ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ :=
  let ⟨f, hf⟩ := schroeder_bernstein h₁ h₂ in
  equiv.of_bijective hf

end antisymm

section wo
parameters {ι : Type u} {β : ι → Type v}

private def sets := {s : set (∀ i, β i) //
  ∀ (x ∈ s) (y ∈ s) i, (x : ∀ i, β i) i = y i → x = y}

private def sets.partial_order : partial_order sets :=
{ le          := λ s t, s.1 ⊆ t.1,
  le_refl     := λ s, subset.refl _,
  le_trans    := λ s t u, subset.trans,
  le_antisymm := λ s t h₁ h₂, subtype.eq (subset.antisymm h₁ h₂) }

local attribute [instance] sets.partial_order

theorem injective_min (I : nonempty ι) : ∃ i, ∀ j, ∃ f : β i → β j, injective f :=
let ⟨⟨s, hs⟩, ms⟩ := show ∃s:sets, ∀a, s ≤ a → a = s, from
  zorn.zorn_partial_order $ λ c hc,
    ⟨⟨⋃₀ (subtype.val '' c),
    λ x ⟨_, ⟨⟨s, hs⟩, sc, rfl⟩, xs⟩ y ⟨_, ⟨⟨t, ht⟩, tc, rfl⟩, yt⟩,
      (hc.total sc tc).elim (λ h, ht _ (h xs) _ yt) (λ h, hs _ xs _ (h yt))⟩,
    λ ⟨s, hs⟩ sc x h, ⟨s, ⟨⟨s, hs⟩, sc, rfl⟩, h⟩⟩ in
let ⟨i, e⟩ := show ∃ i, ∀ y, ∃ x ∈ s, (x : ∀ i, β i) i = y, from
  classical.by_contradiction $ λ h,
  have h : ∀ i, ∃ y, ∀ x ∈ s, (x : ∀ i, β i) i ≠ y,
    by simpa [classical.not_forall] using h,
  let ⟨f, hf⟩ := axiom_of_choice h in
  have f ∈ (⟨s, hs⟩:sets).1, from
    let s' : sets := ⟨insert f s, λ x hx y hy, begin
      cases hx; cases hy, {simp [hx, hy]},
      { subst x, exact λ i e, (hf i y hy e.symm).elim },
      { subst y, exact λ i e, (hf i x hx e).elim },
      { exact hs x hx y hy }
    end⟩ in ms s' (subset_insert f s) ▸ mem_insert _ _,
  let ⟨i⟩ := I in hf i f this rfl in
let ⟨f, hf⟩ := axiom_of_choice e in
⟨i, λ j, ⟨λ a, f a j, λ a b e',
  let ⟨sa, ea⟩ := hf a, ⟨sb, eb⟩ := hf b in
  by rw [← ea, ← eb, hs _ sa _ sb _ e']⟩⟩

end wo

private lemma total.aux {α : Type u} {β : Type v} (f : ulift α → ulift β) (hf : injective f) : nonempty (embedding α β) :=
⟨⟨λ x, (f ⟨x⟩).down, λ x y h, begin
  have := congr_arg ulift.up h,
  rw [ulift.up_down, ulift.up_down] at this,
  injection hf this
end⟩⟩

lemma total {α : Type u} {β : Type v} : nonempty (embedding α β) ∨ nonempty (embedding β α) :=
match @injective_min bool (λ b, cond b (ulift α) (ulift.{(max u v) v} β)) ⟨tt⟩ with
| ⟨tt, h⟩ := let ⟨f, hf⟩ := h ff in or.inl (total.aux f hf)
| ⟨ff, h⟩ := let ⟨f, hf⟩ := h tt in or.inr (total.aux f hf)
end

def prod_congr {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  (e₁ : embedding α β) (e₂ : embedding γ δ) : embedding (α × γ) (β × δ) :=
⟨assume ⟨a, b⟩, (e₁.to_fun a, e₂.to_fun b),
  assume ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h,
  have a₁ = a₂ ∧ b₁ = b₂, from (prod.mk.inj h).imp (assume h, e₁.inj h) (assume h, e₂.inj h),
  this.left ▸ this.right ▸ rfl⟩

section sum
open sum

def sum_congr {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  (e₁ : embedding α β) (e₂ : embedding γ δ) : embedding (α ⊕ γ) (β ⊕ δ) :=
⟨assume s, match s with inl a := inl (e₁.to_fun a) | inr b := inr (e₂.to_fun b) end,
    assume s₁ s₂ h, match s₁, s₂, h with
    | inl a₁, inl a₂, h := congr_arg inl $ e₁.inj $ inl.inj h
    | inr b₁, inr b₂, h := congr_arg inr $ e₂.inj $ inr.inj h
    end⟩

end sum

def arrow_congr_left {α : Type u} {β : Type v} {γ : Type w}
  (e : embedding α β) : embedding (γ → α) (γ → β) :=
⟨λf d, e.to_fun $ f $ d, assume f₁ f₂ h, funext $ assume d, e.inj $ @congr_fun _ _ _ _ h d⟩

def arrow_congr_right {α : Type u} {β : Type v} {γ : Type w} [inhabited γ]
  (e : embedding α β) : embedding (α → γ) (β → γ) :=
let f' : (α → γ) → (β → γ) := λf b, if h : ∃c, e.to_fun c = b then f (some h) else default γ in
⟨f', assume f₁ f₂ h, funext $ assume c,
  have ∃c', e.to_fun c' = e.to_fun c, from ⟨c, rfl⟩,
  have eq' : f' f₁ (e.to_fun c) = f' f₂ (e.to_fun c), from congr_fun h _,
  have eq_b : some this = c, from e.inj $ some_spec this,
  by simp [f', this, if_pos, eq_b] at eq'; assumption⟩

end embedding

instance cardinal.is_equivalent : setoid (Type u) :=
{ r := λα β, nonempty (α ≃ β),
  iseqv := ⟨λα,
    ⟨equiv.refl α⟩,
    λα β ⟨e⟩, ⟨e.symm⟩,
    λα β γ ⟨e₁⟩ ⟨e₂⟩, ⟨e₁.trans e₂⟩⟩ }

def cardinal : Type (u + 1) := quotient cardinal.is_equivalent

namespace cardinal

instance : has_le cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, nonempty $ embedding α β) $
  assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
    propext ⟨assume ⟨e⟩, ⟨e.congr e₁ e₂⟩, assume ⟨e⟩, ⟨e.congr e₁.symm e₂.symm⟩⟩⟩

instance : linear_order cardinal.{u} :=
{ le          := (≤),
  le_refl     := assume a, quotient.induction_on a $
    assume α, ⟨⟨id, injective_id⟩⟩,
  le_trans    := assume a b c, quotient.induction_on₃ a b c $ assume α β γ ⟨e₁⟩ ⟨e₂⟩,
    ⟨⟨e₂.to_fun ∘ e₁.to_fun, injective_comp e₂.inj e₁.inj⟩⟩,
  le_antisymm := assume a b, quotient.induction_on₂ a b $ assume α β ⟨e₁⟩ ⟨e₂⟩,
    quotient.sound (embedding.antisymm e₁ e₂),
  le_total    := assume a b, quotient.induction_on₂ a b $ assume α β, embedding.total }

instance : decidable_linear_order cardinal.{u} :=
{ decidable_le := by apply_instance, ..cardinal.linear_order }

instance : distrib_lattice cardinal.{u} := by apply_instance

instance : has_zero cardinal.{u} := ⟨⟦ulift empty⟧⟩

theorem ne_zero_iff_nonempty {α : Type u} : @ne cardinal ⟦α⟧ 0 ↔ nonempty α :=
not_iff_comm.1
  ⟨λ h, quotient.sound ⟨(equiv.empty_of_not_nonempty h).trans equiv.ulift.symm⟩,
   λ e, let ⟨h⟩ := quotient.exact e in λ ⟨a⟩, (h a).down.elim⟩

instance : has_one cardinal.{u} := ⟨⟦ulift unit⟧⟩

instance : has_add cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, ⟦ α ⊕ β ⟧) $ assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.sum_congr e₁ e₂⟩⟩

instance : has_mul cardinal.{u} :=
⟨λq₁ q₂, quotient.lift_on₂ q₁ q₂ (λα β, ⟦ α × β ⟧) $ assume α β γ δ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.prod_congr e₁ e₂⟩⟩

private lemma add_comm (a b : cardinal.{u}) : a + b = b + a :=
quotient.induction_on₂ a b $ assume α β, quotient.sound ⟨equiv.sum_comm α β⟩

private lemma mul_comm (a b : cardinal.{u}) : a * b = b * a :=
quotient.induction_on₂ a b $ assume α β, quotient.sound ⟨equiv.prod_comm α β⟩

private lemma zero_add (a : cardinal.{u}) : 0 + a = a :=
quotient.induction_on a $ assume α, quotient.sound
  ⟨equiv.trans (equiv.sum_congr equiv.ulift (equiv.refl α)) (equiv.sum_empty_left α)⟩

private lemma zero_mul (a : cardinal.{u}) : 0 * a = 0 :=
quotient.induction_on a $ assume α, quotient.sound
  ⟨equiv.trans (equiv.prod_congr equiv.ulift (equiv.refl α)) $
    equiv.trans (equiv.prod_empty_left α) equiv.ulift.symm⟩

private lemma one_mul (a : cardinal.{u}) : 1 * a = a :=
quotient.induction_on a $ assume α, quotient.sound
  ⟨equiv.trans (equiv.prod_congr equiv.ulift (equiv.refl α)) (equiv.prod_unit_left α)⟩

private lemma left_distrib (a b c : cardinal.{u}) : a * (b + c) = a * b + a * c :=
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

def ω : cardinal.{u} := ⟦ulift ℕ⟧

protected def power (a b : cardinal.{u}) : cardinal.{u} :=
quotient.lift_on₂ a b (λα β, ⟦β → α⟧) $ assume α₁ α₂ β₁ β₂ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.arrow_congr e₂ e₁⟩

local notation a ^ b := cardinal.power a b

@[simp] lemma power_zero {a : cardinal} : a ^ 0 = 1 :=
quotient.induction_on a $ assume α, quotient.sound ⟨
  equiv.trans (equiv.arrow_congr equiv.ulift (equiv.refl α)) $
  equiv.trans equiv.arrow_empty_unit $
  equiv.ulift.symm⟩

@[simp] lemma one_power {a : cardinal} : 1 ^ a = 1 :=
quotient.induction_on a $ assume α, quotient.sound ⟨
  equiv.trans (equiv.arrow_congr (equiv.refl α) equiv.ulift) $
  equiv.trans (equiv.arrow_unit_equiv_unit α) $
  equiv.ulift.symm⟩

@[simp] lemma prop_eq_two : @eq cardinal.{u} ⟦ulift Prop⟧ 2 :=
quot.sound ⟨equiv.ulift.trans $ equiv.Prop_equiv_bool.trans $
  equiv.bool_equiv_unit_sum_unit.trans
  (equiv.sum_congr equiv.ulift equiv.ulift).symm⟩

@[simp] lemma zero_power {a : cardinal} : a ≠ 0 → 0 ^ a = 0 :=
quotient.induction_on a $ assume α heq,
  have nonempty α, from ne_zero_iff_nonempty.1 heq,
  let a := choice this in
  have (α → empty) ≃ empty,
    from ⟨λf, f a, λe a, e, assume f, (f a).rec_on (λ_, (λa', f a) = f), assume e, rfl⟩,
  quotient.sound
    ⟨equiv.trans (equiv.arrow_congr (equiv.refl α) equiv.ulift) $ equiv.trans this equiv.ulift.symm⟩

lemma mul_power {a b c : cardinal} : (a * b) ^ c = a ^ c * b ^ c :=
quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.arrow_prod_equiv_prod_arrow α β γ⟩

lemma power_sum {a b c : cardinal} : a ^ (b + c) = a ^ b * a ^ c :=
quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.sum_arrow_equiv_prod_arrow β γ α⟩

lemma power_mul {a b c : cardinal} : (a ^ b) ^ c = a ^ (b * c) :=
by rw [_root_.mul_comm b c];
from (quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.arrow_arrow_equiv_prod_arrow γ β α⟩)

section order_properties
open sum

lemma zero_le (a : cardinal.{u}) : 0 ≤ a :=
quot.induction_on a $ λ α, ⟨embedding.of_not_nonempty $ λ ⟨⟨a⟩⟩, a.elim⟩

lemma add_mono {a b c d : cardinal.{u}} : a ≤ b → c ≤ d → a + c ≤ b + d :=
quotient.induction_on₂ a b $ assume α β, quotient.induction_on₂ c d $ assume γ δ ⟨e₁⟩ ⟨e₂⟩,
  ⟨embedding.sum_congr e₁ e₂⟩

lemma mul_mono {a b c d : cardinal.{u}} : a ≤ b → c ≤ d → a * c ≤ b * d :=
quotient.induction_on₂ a b $ assume α β, quotient.induction_on₂ c d $ assume γ δ ⟨e₁⟩ ⟨e₂⟩,
  ⟨embedding.prod_congr e₁ e₂⟩

lemma power_mono_left {a b c : cardinal.{u}} : a ≤ b → a ^ c ≤ b ^ c :=
quotient.induction_on₃ a b c $ assume α β γ ⟨e⟩, ⟨embedding.arrow_congr_left e⟩

lemma power_mono_right {a b c : cardinal.{u}} : a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c :=
quotient.induction_on₃ a b c $ assume α β γ hα ⟨e⟩,
  have nonempty α, from classical.by_contradiction $ assume hnα,
    hα $ quotient.sound ⟨equiv.trans (equiv.empty_of_not_nonempty hnα) equiv.ulift.symm⟩,
  let ⟨a⟩ := this in
  ⟨@embedding.arrow_congr_right _ _ _ ⟨a⟩ e⟩

lemma le_iff_exists_add {a b : cardinal.{u}} : a ≤ b ↔ ∃ c, b = a + c :=
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

def min {ι} [inhabited ι] (f : ι → cardinal) : cardinal :=
f $ classical.some $
@embedding.injective_min _ (λ i, (f i).out) nonempty_of_inhabited

theorem min_eq {ι} [inhabited ι] (f : ι → cardinal) : ∃ i, min f = f i :=
⟨_, rfl⟩

theorem min_le {ι} [inhabited ι] (f : ι → cardinal) (i) : min f ≤ f i :=
by rw [← quotient.out_eq (min f), ← quotient.out_eq (f i)]; exact
let ⟨g, hg⟩ := classical.some_spec
  (@embedding.injective_min _ (λ i, (f i).out) nonempty_of_inhabited) i in
⟨⟨g, hg⟩⟩

theorem le_min {ι} [inhabited ι] {f : ι → cardinal} {a} : a ≤ min f ↔ ∀ i, a ≤ f i :=
⟨λ h i, le_trans h (min_le _ _),
 λ h, let ⟨i, e⟩ := min_eq f in e.symm ▸ h i⟩

protected theorem wf : @well_founded cardinal.{u} (<) :=
⟨λ a, classical.by_contradiction $ λ h,
  let ι := {c :cardinal // ¬ acc (<) c},
      f : ι → cardinal := subtype.val in
  by have : inhabited ι := ⟨⟨_, h⟩⟩; exact
  let ⟨⟨c, hc⟩, hi⟩ := min_eq f in
    hc (acc.intro _ (λ j ⟨_, h'⟩,
      classical.by_contradiction $ λ hj, h' $
      by have := min_le f ⟨j, hj⟩; rwa hi at this))⟩

instance has_wf : @has_well_founded cardinal.{u} := ⟨(<), cardinal.wf⟩

def sum {ι} (f : ι → cardinal) : cardinal := ⟦Σ i, (f i).out⟧

theorem le_sum {ι} (f : ι → cardinal) (i) : f i ≤ sum f :=
by rw ← quotient.out_eq (f i); exact
⟨⟨λ a, ⟨i, a⟩, λ a b h, eq_of_heq $ by injection h⟩⟩

def sup {ι} (f : ι → cardinal) : cardinal :=
@min {c // ∀ i, f i ≤ c} ⟨⟨sum f, le_sum f⟩⟩ (λ a, a.1)

theorem le_sup {ι} (f : ι → cardinal) (i) : f i ≤ sup f :=
by dsimp [sup]; cases min_eq _ with c hc; rw hc; exact c.2 i

theorem sup_le {ι} (f : ι → cardinal) (a) : sup f ≤ a ↔ ∀ i, f i ≤ a :=
⟨λ h i, le_trans (le_sup _ _) h,
 λ h, by dsimp [sup]; change a with (⟨a, h⟩:subtype _).1; apply min_le⟩

end cardinal
