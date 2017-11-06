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
local attribute [instance] decidable_inhabited prop_decidable

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

section total

section option_le
open option
variable {α : Type u}

inductive option.le : option α → option α → Prop
| none : ∀x:option α, option.le none x
| some_some : ∀a:α, option.le (some a) (some a)

def option.strict_partial_order : partial_order (option α) :=
{ partial_order .
  le       := option.le,
  le_refl     := assume a, match a with
    | none := option.le.none none
    | some a := option.le.some_some a
    end,
  le_trans    := assume a b c h₁ h₂,
    match a, b, c, h₁, h₂ with
    | _, _, c, option.le.none a, h₂ := option.le.none c
    | _, _, _, option.le.some_some _, option.le.some_some b := option.le.some_some b
    end,
  le_antisymm := assume a b h₁ h₂,
    match a, b, h₁, h₂ with
    | _, b, option.le.none a, option.le.none _ := rfl
    | _, _, option.le.some_some _, option.le.some_some b := rfl
    end }

local attribute [instance] option.strict_partial_order

lemma option.eq_of_le_some {a : α} : ∀{b : option α} (h : some a ≤ b), b = some a
| _ (option.le.some_some _) := rfl

def option.Sup (s : set (option α)) : option α :=
if h : ∃a:α, some a ∈ s then some (classical.some h) else none

lemma option.le_Sup {s : set (option α)} {a : option α}
  (hs : @zorn.chain (option α) (≤) s) (ha : a ∈ s) : a ≤ option.Sup s :=
begin
  by_cases ∃a:α, some a ∈ s with h,
  { have : some (some h) ∈ s, from classical.some_spec h,
    have : some (some h) ≤ a ∨ a ≤ some (some h),
      from if heq : some (some h) = a then or.inl $ le_of_eq heq else hs _ this _ ha heq,
    have : a ≤ some (some h),
      from match a, this with
      | _, or.inl (option.le.some_some _) := le_refl _
      | _, or.inr h := h
      end,
    simp [option.Sup, h, if_pos, this] },
  { have ha_eq : a = none,
      from match a, ha with
      | none,   ha := rfl
      | some a, ha := (h ⟨a, ha⟩).elim
      end,
    rw [ha_eq],
    exact option.le.none _ }
end

lemma option.Sup_le {s : set (option α)} {a : option α}
  (hs : @zorn.chain (option α) (≤) s) (ha : ∀b∈s, b ≤ a) : option.Sup s ≤ a :=
begin
  by_cases ∃a:α, some a ∈ s with h,
  { have : some (some h) ≤ a,
      from ha _ (classical.some_spec h),
    simp [option.Sup, if_pos, h, this] },
  { simp [option.Sup, if_neg, h],
    exact option.le.none a }
end

lemma option.mem_of_Sup_eq_some {s : set (option α)} {a : α}
  (hs : @zorn.chain (option α) (≤) s) (h : option.Sup s = some a) : some a ∈ s :=
have ∃a:α, some a ∈ s,
  from classical.by_contradiction $ assume hn, by simp [hn, option.Sup] at h; assumption,
let ⟨a', ha'⟩ := this in
have some a' ≤ some a,
  from h ▸ option.le_Sup hs ha',
have a = a',
  from match a', this with _, option.le.some_some a := rfl end,
this.symm ▸ ha'

end option_le

parameters {α : Type u} {β : Type v}
local attribute [instance] option.strict_partial_order

def pfun := {f : α → option β // ∀a₁ a₂ b, f a₁ = option.some b → f a₂ = option.some b → a₁ = a₂}

def pfun.partial_order : partial_order pfun :=
{ partial_order .
  le          := λf g, ∀a, option.le (f.val a) (g.val a),
  le_refl     := assume f a, le_refl (f.val a),
  le_trans    := assume a b c h₁ h₂ x, @le_trans (option β) _ _ _ _ (h₁ x) (h₂ x),
  le_antisymm := assume a b h₁ h₂, subtype.eq $ funext $ assume x,
      @le_antisymm (option β) _ _ _ (h₁ x) (h₂ x) }

local attribute [instance] pfun.partial_order

lemma exists_injective_or_surjective [inhabited β] : ∃f : α → β, injective f ∨ surjective f :=
have ∃m:pfun, ∀a, m ≤ a → a = m,
  from zorn.zorn_partial_order $ assume c hc,
  let f : α → option β := λa:α, option.Sup ((λf:pfun, f.val a) '' c) in
  have hc' : ∀a, @zorn.chain (option β) (≤) ((λf:pfun, f.val a) '' c),
    from assume a b₁ ⟨f₁, hf₁, eq₁⟩ b₂ ⟨f₂, hf₂, eq₂⟩ h,
    have f₁ ≠ f₂, from assume eq, h $ eq₁ ▸ eq₂ ▸ eq ▸ rfl,
    have f₁ ≤ f₂ ∨ f₂ ≤ f₁, from hc _ hf₁ _ hf₂ this,
    eq₁ ▸ eq₂ ▸ this.imp (assume h, h a) (assume h, h a),
  have ∀a₁ a₂ b, f a₁ = option.some b → f a₂ = option.some b → a₁ = a₂,
    from assume a₁ a₂ b h₁ h₂,
    have some b ∈ ((λf:pfun, f.val a₁) '' c), from option.mem_of_Sup_eq_some (hc' a₁) h₁,
    let ⟨f₁, hf₁, eq₁⟩ := this in
    have some b ∈ ((λf:pfun, f.val a₂) '' c), from option.mem_of_Sup_eq_some (hc' a₂) h₂,
    let ⟨f₂, hf₂, eq₂⟩ := this in
    have f₁ ≤ f₂ ∨ f₂ ≤ f₁,
      from if heq : f₁ = f₂ then or.inl $ le_of_eq heq else hc _ hf₁ _ hf₂ heq,
    match this with
    | or.inl h := f₂.property _ _ b (option.eq_of_le_some $ eq₁ ▸ h a₁) eq₂
    | or.inr h := f₁.property _ _ b eq₁ (option.eq_of_le_some $ eq₂ ▸ h a₂)
    end,
  ⟨⟨f, this⟩, assume ⟨g, hg⟩ hgc a, option.le_Sup (hc' a) (mem_image_of_mem _ hgc)⟩,
let ⟨m, hm⟩ := this in
let f : α → β := λa, option.get_or_else (m.val a) (default β) in
have injective f ∨ surjective f,
  from if h : ∀a:α, ∃b:β, m.val a = some b
  then or.inl $ assume a₁ a₂ eq,
    let ⟨b₁, hb₁⟩ := h a₁, ⟨b₂, hb₂⟩ := h a₂ in
    have eq₁ : f a₁ = b₁, begin simp [f], rw [hb₁], simp [option.get_or_else] end,
    have eq₂ : f a₂ = b₂, begin simp [f], rw [hb₂], simp [option.get_or_else] end,
    have b₁ = b₂, from eq₁ ▸ eq₂ ▸ eq,
    m.property _ _ b₁ hb₁ (this.symm ▸ hb₂)
  else or.inr $ assume b,
    have ∃a:α, ∀b:β, m.val a ≠ some b, by simp [classical.not_forall] at h; assumption,
    let ⟨a, ha'⟩ := this in
    have ma_eq : m.val a = none,
      from match m.val a, ha' with some b, h := (h b rfl).elim | none, h := rfl end,
    if h : ∃a, m.val a = some b
    then let ⟨a, ha⟩ := h in ⟨a, begin simp [f], rw [ha], simp [option.get_or_else] end⟩
    else
      let f' : α → option β := λa', if a' = a then some b else m.val a' in
      have eq_b : ∀{b':β}, f' a = some b' → b' = b,
        by simp [f', if_pos] {contextual := tt},
      have eq_a : ∀{a':α}, f' a' = some b → a' = a,
        from assume a' ha', classical.by_contradiction $ assume neq,
        begin
          simp [f', neq, if_neg, ma_eq] at ha',
          exact h ⟨a', ha'⟩
        end,
      have ∀a₁ a₂ b, f' a₁ = option.some b → f' a₂ = option.some b → a₁ = a₂,
        from assume a₁ a₂ b' h₁ h₂,
        if h : a₁ = a ∨ a₂ = a
        then h.elim
          (assume a₁_eq,
            begin
              rw [a₁_eq],
              apply (eq_a _).symm,
              rw [h₂, @eq_b b' (a₁_eq ▸ h₁)]
            end)
          (assume a₂_eq,
            begin
              rw [a₂_eq],
              apply eq_a _,
              rw [h₁, @eq_b b' (a₂_eq ▸ h₂)]
            end)
        else
          have a₁ ≠ a, from assume ne, h $ or.inl ne,
          have h₁ : m.val a₁ = some b', by simp [f', this, if_neg] at h₁; assumption,
          have a₂ ≠ a, from assume ne, h $ or.inr ne,
          have h₂ : m.val a₂ = some b', by simp [f', this, if_neg] at h₂; assumption,
          m.property _ _ b' h₁ h₂,
      let m' : pfun := ⟨f', this⟩ in
      have m ≤ m', from assume a', if eq : a' = a
        then by simp [m', f', eq, if_pos, ma_eq]; exact option.le.none _
        else by simp [m', f', eq, if_neg]; exact le_refl (m.val a'),
      have m'.val a = m.val a, by rw [hm _ this],
      by simp [m', f', if_pos, ma_eq] at this; contradiction,
⟨f, this⟩

lemma total : nonempty (embedding α β) ∨ nonempty (embedding β α) :=
by_cases
  (assume : nonempty β,
    let ⟨b⟩ := this in
    match @exists_injective_or_surjective ⟨b⟩ with
    | ⟨f, or.inl hf⟩ := or.inl ⟨⟨f, hf⟩⟩
    | ⟨f, or.inr hf⟩ := or.inr ⟨embedding.of_surjective hf⟩
    end)
  (assume : ¬ nonempty β,
    or.inr ⟨embedding.of_not_nonempty this⟩)

end total

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
{ setoid .
  r := λα β, nonempty (α ≃ β),
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
{ linear_order .
  le          := (≤),
  le_refl     := assume a, quotient.induction_on a $
    assume α, ⟨⟨id, injective_id⟩⟩,
  le_trans    := assume a b c, quotient.induction_on₃ a b c $ assume α β γ ⟨e₁⟩ ⟨e₂⟩,
    ⟨⟨e₂.to_fun ∘ e₁.to_fun, injective_comp e₂.inj e₁.inj⟩⟩,
  le_antisymm := assume a b, quotient.induction_on₂ a b $ assume α β ⟨e₁⟩ ⟨e₂⟩,
    quotient.sound (embedding.antisymm e₁ e₂),
  le_total    := assume a b, quotient.induction_on₂ a b $ assume α β, embedding.total }

instance : has_zero cardinal.{u} := ⟨⟦ulift empty⟧⟩

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
{ comm_semiring .
  zero          := 0,
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

section power

protected def power (a b : cardinal.{u}) : cardinal.{u} :=
quotient.lift_on₂ a b (λα β, ⟦β → α⟧) $ assume α₁ α₂ β₁ β₂ ⟨e₁⟩ ⟨e₂⟩,
  quotient.sound ⟨equiv.arrow_congr e₂ e₁⟩

@[simp] lemma power_zero {a : cardinal} : a.power 0 = 1 :=
quotient.induction_on a $ assume α, quotient.sound ⟨
  equiv.trans (equiv.arrow_congr equiv.ulift (equiv.refl α)) $
  equiv.trans equiv.arrow_empty_unit $
  equiv.ulift.symm⟩

@[simp] lemma one_power {a : cardinal} : (1 : cardinal).power a = 1 :=
quotient.induction_on a $ assume α, quotient.sound ⟨
  equiv.trans (equiv.arrow_congr (equiv.refl α) equiv.ulift) $
  equiv.trans (equiv.arrow_unit_equiv_unit α) $
  equiv.ulift.symm⟩

@[simp] lemma zero_power {a : cardinal} : a ≠ 0 → (0 : cardinal).power a = 0 :=
quotient.induction_on a $ assume α heq,
  have nonempty α, from classical.by_contradiction $ assume hα,
    heq $ quotient.sound ⟨equiv.trans (equiv.empty_of_not_nonempty hα) equiv.ulift.symm⟩,
  let a := choice this in
  have (α → empty) ≃ empty,
    from ⟨λf, f a, λe a, e, assume f, (f a).rec_on (λ_, (λa', f a) = f), assume e, rfl⟩,
  quotient.sound
    ⟨equiv.trans (equiv.arrow_congr (equiv.refl α) equiv.ulift) $ equiv.trans this equiv.ulift.symm⟩

lemma mul_power {a b c : cardinal} : (a * b).power c = a.power c * b.power c :=
quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.arrow_prod_equiv_prod_arrow α β γ⟩

lemma power_sum {a b c : cardinal} : a.power (b + c) = a.power b * a.power c :=
quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.sum_arrow_equiv_prod_arrow β γ α⟩

lemma power_mul {a b c : cardinal} : (a.power b).power c = a.power (b * c) :=
by rw [_root_.mul_comm b c];
from (quotient.induction_on₃ a b c $ assume α β γ,
  quotient.sound ⟨equiv.arrow_arrow_equiv_prod_arrow γ β α⟩)

end power

section order_properties
open sum

lemma add_mono {a b c d : cardinal.{u}} : a ≤ b → c ≤ d → a + c ≤ b + d :=
quotient.induction_on₂ a b $ assume α β, quotient.induction_on₂ c d $ assume γ δ ⟨e₁⟩ ⟨e₂⟩,
  ⟨embedding.sum_congr e₁ e₂⟩

lemma mul_mono {a b c d : cardinal.{u}} : a ≤ b → c ≤ d → a * c ≤ b * d :=
quotient.induction_on₂ a b $ assume α β, quotient.induction_on₂ c d $ assume γ δ ⟨e₁⟩ ⟨e₂⟩,
  ⟨embedding.prod_congr e₁ e₂⟩

lemma power_mono_left {a b c : cardinal.{u}} : a ≤ b → a.power c ≤ b.power c :=
quotient.induction_on₃ a b c $ assume α β γ ⟨e⟩, ⟨embedding.arrow_congr_left e⟩

lemma power_mono_right {a b c : cardinal.{u}} : a ≠ 0 → b ≤ c → a.power b ≤ a.power c :=
quotient.induction_on₃ a b c $ assume α β γ hα ⟨e⟩,
  have nonempty α, from classical.by_contradiction $ assume hnα,
    hα $ quotient.sound ⟨equiv.trans (equiv.empty_of_not_nonempty hnα) equiv.ulift.symm⟩,
  let ⟨a⟩ := this in
  ⟨@embedding.arrow_congr_right _ _ _ ⟨a⟩ e⟩

end order_properties

end cardinal
