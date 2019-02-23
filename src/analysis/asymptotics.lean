/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

We introduce these relations:

  `is_bigo f g l`    : "f is big O of g along l"
  `is_littleo f g l` : "f is little o of g along l"

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed that there is a norm associated with
these types, and it is the norm that is compared asymptotically.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `is_bigo f g l ↔ is_bigo (λ x, ∥f x∥) (λ x, ∥g x∥) l`,

and similarly for `is_littleo`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `is_littleo f g l ↔ tendsto (λ x, f x / (g x)) (nhds 0) l`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)
-/
import analysis.normed_space.basic
open filter

namespace asymptotics

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section
variables [has_norm β] [has_norm γ] [has_norm δ]

def is_bigo (f : α → β) (g : α → γ) (l : filter α) : Prop :=
∃ c > 0, { x | ∥ f x ∥ ≤ c * ∥ g x ∥ } ∈ l.sets

def is_littleo (f : α → β) (g : α → γ) (l : filter α) : Prop :=
∀ c > 0, { x | ∥ f x ∥ ≤  c * ∥ g x ∥ } ∈ l.sets

theorem is_bigo_refl (f : α → β) (l : filter α) :
  is_bigo f f l :=
⟨1, zero_lt_one, by { filter_upwards [univ_mem_sets], intros x _, simp }⟩

theorem is_bigo.comp {f : α → β} {g : α → γ} {l : filter α} (hfg : is_bigo f g l)
    {δ : Type*} (k : δ → α) :
  is_bigo (f ∘ k) (g ∘ k) (l.comap k) :=
let ⟨c, cpos, hfgc⟩ := hfg in
⟨c, cpos, mem_comap_sets.mpr ⟨_, hfgc, set.subset.refl _⟩⟩

theorem is_littleo.comp {f : α → β} {g : α → γ} {l : filter α} (hfg : is_littleo f g l)
    {δ : Type*} (k : δ → α) :
  is_littleo (f ∘ k) (g ∘ k) (l.comap k) :=
λ c cpos, mem_comap_sets.mpr ⟨_, hfg c cpos, set.subset.refl _⟩

theorem is_bigo.mono {f : α → β} {g : α → γ} {l₁ l₂ : filter α} (h : l₁ ≤ l₂)
  (h' : is_bigo f g l₂) : is_bigo f g l₁ :=
let ⟨c, cpos, h'c⟩ := h' in ⟨c, cpos, h (h'c)⟩

theorem is_littleo.mono {f : α → β} {g : α → γ} {l₁ l₂ : filter α} (h : l₁ ≤ l₂)
  (h' : is_littleo f g l₂) : is_littleo f g l₁ :=
λ c cpos, h (h' c cpos)

theorem is_littleo.to_is_bigo {f : α → β} {g : α → γ} {l : filter α} (hgf : is_littleo f g l) :
  is_bigo f g l :=
⟨1, zero_lt_one, hgf 1 zero_lt_one⟩

theorem is_bigo.trans {f : α → β} {g : α → γ} {k : α → δ} {l : filter α}
    (h₁ : is_bigo f g l)
    (h₂ : is_bigo g k l) :
  is_bigo f k l :=
let ⟨c,  cpos,  hc⟩  := h₁,
    ⟨c', c'pos, hc'⟩ := h₂ in
begin
  use [c * c', mul_pos cpos c'pos],
  filter_upwards [hc, hc'], dsimp,
  intros x h₁x h₂x, rw mul_assoc,
  exact le_trans h₁x (mul_le_mul_of_nonneg_left h₂x (le_of_lt cpos))
end

theorem is_littleo.trans_is_bigo {f : α → β} {g : α → γ} {k : α → δ} {l : filter α}
    (h₁ : is_littleo f g l)
    (h₂ : is_bigo g k l) :
  is_littleo f k l :=
begin
  intros c cpos,
  rcases h₂ with ⟨c', c'pos, hc'⟩,
  have cc'pos := div_pos cpos c'pos,
  filter_upwards [h₁ (c / c') cc'pos, hc'], dsimp,
  intros x h₁x h₂x,
  refine le_trans h₁x (le_trans (mul_le_mul_of_nonneg_left h₂x (le_of_lt cc'pos)) _),
  rw [←mul_assoc, div_mul_cancel _ (ne_of_gt c'pos)]
end

theorem is_bigo.trans_is_littleo {f : α → β} {g : α → γ} {k : α → δ} {l : filter α}
    (h₁ : is_bigo f g l)
    (h₂ : is_littleo g k l) :
  is_littleo f k l :=
begin
  intros c cpos,
  rcases h₁ with ⟨c', c'pos, hc'⟩,
  have cc'pos := div_pos cpos c'pos,
  filter_upwards [hc', h₂ (c / c') cc'pos], dsimp,
  intros x h₁x h₂x,
  refine le_trans h₁x (le_trans (mul_le_mul_of_nonneg_left h₂x (le_of_lt c'pos)) _),
  rw [←mul_assoc, mul_div_cancel' _ (ne_of_gt c'pos)]
end

theorem is_littleo.trans {f : α → β} {g : α → γ} {k : α → δ} {l : filter α}
    (h₁ : is_littleo f g l)
    (h₂ : is_littleo g k l) :
  is_littleo f k l :=
h₁.to_is_bigo.trans_is_littleo h₂

theorem is_littleo_join {f : α → β} {g : α → γ} {l₁ l₂ : filter α}
    (h₁ : is_littleo f g l₁) (h₂ : is_littleo f g l₂) :
  is_littleo f g (l₁ ⊔ l₂) :=
begin
  intros c cpos,
  rw mem_sup_sets,
  exact ⟨h₁ c cpos, h₂ c cpos⟩
end

private theorem congr_aux1 (f₁ f₂ : α → β) (g : α → γ) (l : filter α)
    (h : {x | f₁ x = f₂ x} ∈ l.sets) :
  ∀ c, {x : α | ∥f₁ x∥ ≤ c * ∥g x∥} ∈ l.sets ↔ {x : α | ∥f₂ x∥ ≤ c * ∥g x∥} ∈ l.sets :=
begin
  intro c, split,
  { intro h₀, filter_upwards [h₀, h], dsimp, intros x hx e, rw ←e, apply hx },
  intro h₀, filter_upwards [h₀, h], dsimp, intros x hx e, rw e, apply hx
end

theorem is_bigo.congr_left {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h : {x | f₁ x = f₂ x} ∈ l.sets) :
  is_bigo f₁ g l ↔ is_bigo f₂ g l :=
by simp only [is_bigo, congr_aux1 f₁ f₂ g l h]

theorem is_littleo.congr_left {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h : {x | f₁ x = f₂ x} ∈ l.sets) :
  is_littleo f₁ g l ↔ is_littleo f₂ g l :=
by simp only [is_littleo, congr_aux1 f₁ f₂ g l h]

private theorem congr_aux2 (f : α → β) (g₁ g₂ : α → γ) (l : filter α)
    (h : {x | g₁ x = g₂ x} ∈ l.sets) :
  ∀ c, {x : α | ∥f x∥ ≤ c * ∥g₁ x∥} ∈ l.sets ↔ {x : α | ∥f x∥ ≤ c * ∥g₂ x∥} ∈ l.sets :=
begin
  intro c, split,
  { intro h₀, filter_upwards [h₀, h], dsimp, intros x hx e, rw ←e, apply hx },
  intro h₀, filter_upwards [h₀, h], dsimp, intros x hx e, rw e, apply hx
end

theorem is_bigo.congr_right {f : α → β} {g₁ g₂ : α → γ} {l : filter α}
    (h : {x | g₁ x = g₂ x} ∈ l.sets) :
  is_bigo f g₁ l ↔ is_bigo f g₂ l :=
by simp only [is_bigo, congr_aux2 f g₁ g₂ l h]

theorem is_littleo.congr_right {f : α → β} {g₁ g₂ : α → γ} {l : filter α}
    (h : {x | g₁ x = g₂ x} ∈ l.sets) :
  is_littleo f g₁ l ↔ is_littleo f g₂ l :=
by simp only [is_littleo, congr_aux2 f g₁ g₂ l h]

end

section
variables [has_norm β] [normed_group γ]

@[simp]
theorem is_bigo_norm_right {f : α → β} {g : α → γ} {l : filter α} :
  is_bigo f (λ x, ∥g x∥) l ↔ is_bigo f g l :=
by simp only [is_bigo, norm_norm]

@[simp]
theorem is_littleo_norm_right {f : α → β} {g : α → γ} {l : filter α} :
  is_littleo f (λ x, ∥g x∥) l ↔ is_littleo f g l :=
by simp only [is_littleo, norm_norm]

@[simp]
theorem is_bigo_neg_right {f : α → β} {g : α → γ} {l : filter α} :
  is_bigo f (λ x, -(g x)) l ↔ is_bigo f g l :=
by { rw ←is_bigo_norm_right, simp only [norm_neg], rw is_bigo_norm_right }

@[simp]
theorem is_littleo_neg_right {f : α → β} {g : α → γ} {l : filter α} :
  is_littleo f (λ x, -(g x)) l ↔ is_littleo f g l :=
by { rw ←is_littleo_norm_right, simp only [norm_neg], rw is_littleo_norm_right }

theorem is_bigo_iff {f : α → β} {g : α → γ} {l : filter α} :
  is_bigo f g l ↔ ∃ c, { x | ∥f x∥ ≤ c * ∥g x∥ } ∈ l.sets :=
suffices (∃ c, { x | ∥f x∥ ≤ c * ∥g x∥ } ∈ l.sets) → is_bigo f g l,
  from ⟨λ ⟨c, cpos, hc⟩, ⟨c, hc⟩, this⟩,
assume ⟨c, hc⟩,
or.elim (lt_or_ge 0 c)
  (assume : c > 0, ⟨c, this, hc⟩)
  (assume h'c : c ≤ 0,
    have {x : α | ∥f x∥ ≤ 1 * ∥g x∥} ∈ l.sets,
      begin
        filter_upwards [hc], intros x,
        show ∥f x∥ ≤ c * ∥g x∥ → ∥f x∥ ≤ 1 * ∥g x∥,
        { intro hx, apply le_trans hx,
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
          show c ≤ 1, from le_trans h'c zero_le_one }
      end,
    ⟨1, zero_lt_one, this⟩)

theorem is_bigo_join {f : α → β} {g : α → γ} {l₁ l₂ : filter α}
    (h₁ : is_bigo f g l₁) (h₂ : is_bigo f g l₂) :
  is_bigo f g (l₁ ⊔ l₂) :=
begin
  rcases h₁ with ⟨c₁, c₁pos, hc₁⟩,
  rcases h₂ with ⟨c₂, c₂pos, hc₂⟩,
  have : 0 < max c₁ c₂, by { rw lt_max_iff, left, exact c₁pos },
  use [max c₁ c₂, this],
  rw mem_sup_sets, split,
  { filter_upwards [hc₁], dsimp, intros x hx,
    exact le_trans hx (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)) },
  filter_upwards [hc₂], dsimp, intros x hx,
    exact le_trans hx (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
end

end

section
variables [normed_group β] [has_norm γ]

@[simp]
theorem is_bigo_norm_left {f : α → β} {g : α → γ} {l : filter α} :
  is_bigo (λ x, ∥f x∥) g l ↔ is_bigo f g l :=
by simp only [is_bigo, norm_norm]

@[simp]
theorem is_littleo_norm_left {f : α → β} {g : α → γ} {l : filter α} :
  is_littleo (λ x, ∥f x∥) g l ↔ is_littleo f g l :=
by simp only [is_littleo, norm_norm]

@[simp]
theorem is_bigo_neg_left {f : α → β} {g : α → γ} {l : filter α} :
  is_bigo (λ x, -f x) g l ↔ is_bigo f g l :=
by { rw ←is_bigo_norm_left, simp only [norm_neg], rw is_bigo_norm_left }

@[simp]
theorem is_littleo_neg_left {f : α → β} {g : α → γ} {l : filter α} :
  is_littleo (λ x, -f x) g l ↔ is_littleo f g l :=
by { rw ←is_littleo_norm_left, simp only [norm_neg], rw is_littleo_norm_left }

theorem is_bigo.add {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h₁ : is_bigo f₁ g l) (h₂ : is_bigo f₂ g l) :
  is_bigo (λ x, f₁ x + f₂ x) g l :=
let ⟨c₁, c₁pos, hc₁⟩ := h₁,
    ⟨c₂, c₂pos, hc₂⟩ := h₂ in
begin
  use [c₁ + c₂, add_pos c₁pos c₂pos],
  filter_upwards [hc₁, hc₂],
  intros x hx₁ hx₂,
  show ∥f₁ x + f₂ x∥ ≤ (c₁ + c₂) * ∥g x∥,
  apply le_trans (norm_triangle _ _),
  rw add_mul,
  exact add_le_add hx₁ hx₂
end

theorem is_littleo.add {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h₁ : is_littleo f₁ g l) (h₂ : is_littleo f₂ g l) :
  is_littleo (λ x, f₁ x + f₂ x) g l :=
begin
  intros c cpos,
  filter_upwards [h₁ (c / 2) (half_pos cpos), h₂ (c / 2) (half_pos cpos)],
  intros x hx₁ hx₂, dsimp at hx₁ hx₂,
  apply le_trans (norm_triangle _ _),
  apply le_trans (add_le_add hx₁ hx₂),
  rw [←mul_add, ←two_mul, ←mul_assoc, div_mul_cancel _ two_ne_zero]
end

theorem is_bigo.sub {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h₁ : is_bigo f₁ g l) (h₂ : is_bigo f₂ g l) :
  is_bigo (λ x, f₁ x - f₂ x) g l :=
h₁.add (is_bigo_neg_left.mpr h₂)

theorem is_littleo.sub {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h₁ : is_littleo f₁ g l) (h₂ : is_littleo f₂ g l) :
  is_littleo (λ x, f₁ x - f₂ x) g l :=
h₁.add (is_littleo_neg_left.mpr h₂)

end

section
variables [normed_group β] [normed_group γ]

theorem is_bigo_zero (g : α → γ) (l : filter α) :
  is_bigo (λ x, (0 : β)) g l :=
⟨1, zero_lt_one, by { filter_upwards [univ_mem_sets], intros x _, simp }⟩

theorem is_bigo_zero_right_iff {f : α → β} {l : filter α} :
  is_bigo f (λ x, (0 : γ)) l ↔ {x | f x = 0} ∈ l.sets :=
begin
  rw [is_bigo_iff], split,
  { rintros ⟨c, hc⟩,
    filter_upwards [hc], dsimp,
    intro x, rw [norm_zero, mul_zero], intro hx,
    rw ←norm_eq_zero,
    exact le_antisymm hx (norm_nonneg _) },
  intro h, use 0,
  filter_upwards [h], dsimp,
  intros x hx,
  rw [hx, norm_zero, zero_mul]
end

theorem is_littleo_zero (g : α → γ) (l : filter α) :
  is_littleo (λ x, (0 : β)) g l :=
λ c cpos,
by { filter_upwards [univ_mem_sets], intros x _, simp,
     exact mul_nonneg (le_of_lt cpos) (norm_nonneg _)}

theorem is_littleo_zero_right_iff {f : α → β} (l : filter α) :
  is_littleo f (λ x, (0 : γ)) l ↔ {x | f x = 0} ∈ l.sets :=
begin
  split,
  { intro h, exact is_bigo_zero_right_iff.mp h.to_is_bigo },
  intros h c cpos,
  filter_upwards [h], dsimp,
  intros x hx,
  rw [hx, norm_zero, norm_zero, mul_zero]
end

end

section
variables [has_norm β] [normed_field γ]

theorem is_bigo_const_one (c : β) (l : filter α) :
  is_bigo (λ x : α, c) (λ x, (1 : γ)) l :=
begin
  rw is_bigo_iff,
  use ∥c∥, simp only [norm_one, mul_one],
  convert univ_mem_sets, simp only [le_refl]
end

end

section
variables [normed_field β] [normed_group γ]

theorem is_bigo_const_mul_left {f : α → β} {g : α → γ} {l : filter α}
    (h : is_bigo f g l) (c : β) :
  is_bigo (λ x, c * f x) g l :=
begin
  cases classical.em (c = 0) with h'' h'',
  { simp [h''], apply is_bigo_zero },
  rcases h with ⟨c', c'pos, h'⟩,
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp h'',
  have cpos : ∥c∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm cne0),
  use [∥c∥ * c', mul_pos cpos c'pos],
  filter_upwards [h'], dsimp,
  intros x h₀,
  rw [normed_field.norm_mul, mul_assoc],
  exact mul_le_mul_of_nonneg_left h₀ (norm_nonneg _)
end

theorem is_bigo_const_mul_left_iff {f : α → β} {g : α → γ} {l : filter α} {c : β} (hc : c ≠ 0) :
  is_bigo (λ x, c * f x) g l ↔ is_bigo f g l :=
begin
  split,
  { intro h,
    convert is_bigo_const_mul_left h c⁻¹, ext,
    rw [←mul_assoc, inv_mul_cancel hc, one_mul] },
  intro h, apply is_bigo_const_mul_left h
end

theorem is_littleo_const_mul_left {f : α → β} {g : α → γ} {l : filter α}
    (h : is_littleo f g l) (c : β) :
  is_littleo (λ x, c * f x) g l :=
begin
  cases classical.em (c = 0) with h'' h'',
  { simp [h''], apply is_littleo_zero },
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp h'',
  have cpos : ∥c∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm cne0),
  intros c' c'pos, dsimp,
  filter_upwards [h (c' / ∥c∥) (div_pos c'pos cpos)], dsimp,
  intros x hx, rw [normed_field.norm_mul],
  apply le_trans (mul_le_mul_of_nonneg_left hx (le_of_lt cpos)),
  rw [←mul_assoc, mul_div_cancel' _ cne0]
end

theorem is_littleo_const_mul_left_iff {f : α → β} {g : α → γ} {l : filter α} {c : β} (hc : c ≠ 0) :
  is_littleo (λ x, c * f x) g l ↔ is_littleo f g l :=
begin
  split,
  { intro h,
    convert is_littleo_const_mul_left h c⁻¹, ext,
    rw [←mul_assoc, inv_mul_cancel hc, one_mul] },
  intro h',
  apply is_littleo_const_mul_left h'
end

end

section
variables [normed_group β] [normed_field γ]

theorem is_bigo_of_is_bigo_const_mul_right {f : α → β} {g : α → γ} {l : filter α} {c : γ}
    (h : is_bigo f (λ x, c * g x) l) :
  is_bigo f g l  :=
begin
  cases classical.em (c = 0) with h' h',
  { simp [h', is_bigo_zero_right_iff] at h, rw is_bigo.congr_left h, apply is_bigo_zero },
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp h',
  have cpos : ∥c∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm cne0),
  rcases h with ⟨c', c'pos, h''⟩,
  use [c' * ∥c∥, mul_pos c'pos cpos],
  convert h'', ext x, dsimp,
  rw [normed_field.norm_mul, mul_assoc]
end

theorem is_bigo_const_mul_right_iff {f : α → β} {g : α → γ} {l : filter α} {c : γ} (hc : c ≠ 0) :
  is_bigo f (λ x, c * g x) l ↔ is_bigo f g l :=
begin
  split,
  { intro h, exact is_bigo_of_is_bigo_const_mul_right h },
  intro h,
  apply is_bigo_of_is_bigo_const_mul_right,
  show is_bigo f (λ (x : α), c⁻¹ * (c * g x)) l,
  convert h, ext, rw [←mul_assoc, inv_mul_cancel hc, one_mul]
end

theorem is_littleo_of_is_littleo_const_mul_right {f : α → β} {g : α → γ} {l : filter α} {c : γ}
    (h : is_littleo f (λ x, c * g x) l) :
  is_littleo f g l  :=
begin
  cases classical.em (c = 0) with h' h',
  { simp [h', is_littleo_zero_right_iff] at h, rw is_littleo.congr_left h, apply is_littleo_zero },
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp h',
  have cpos : ∥c∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm cne0),
  intros c' c'pos,
  convert h (c' / ∥c∥) (div_pos c'pos cpos), dsimp,
  ext x, rw [normed_field.norm_mul, ←mul_assoc, div_mul_cancel _ cne0]
end

theorem is_littleo_const_mul_right {f : α → β} {g : α → γ} {l : filter α} {c : γ} (hc : c ≠ 0) :
  is_littleo f (λ x, c * g x) l ↔ is_littleo f g l :=
begin
  split,
  { intro h, exact is_littleo_of_is_littleo_const_mul_right h },
  intro h,
  apply is_littleo_of_is_littleo_const_mul_right,
  show is_littleo f (λ (x : α), c⁻¹ * (c * g x)) l,
  convert h, ext, rw [←mul_assoc, inv_mul_cancel hc, one_mul]
end

theorem is_littleo_one_iff {f : α → β} {l : filter α} :
  is_littleo f (λ x, (1 : γ)) l ↔ tendsto f l (nhds 0) :=
begin
  rw [normed_space.tendsto_nhds_zero, is_littleo], split,
  { intros h e epos,
    filter_upwards [h (e / 2) (half_pos epos)], simp,
    intros x hx,
    exact lt_of_le_of_lt hx (half_lt_self epos) },
  intros h e epos,
  filter_upwards [h e epos], simp,
  intros x hx,
  exact le_of_lt hx
end

end

section
variables [normed_field β] [normed_field γ]

theorem is_bigo_mul {f₁ f₂ : α → β} {g₁ g₂ : α → γ} {l : filter α}
    (h₁ : is_bigo f₁ g₁ l) (h₂ : is_bigo f₂ g₂ l):
  is_bigo (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
begin
  rcases h₁ with ⟨c₁, c₁pos, hc₁⟩,
  rcases h₂ with ⟨c₂, c₂pos, hc₂⟩,
  use [c₁ * c₂, mul_pos c₁pos c₂pos],
  filter_upwards [hc₁, hc₂], dsimp,
  intros x hx₁ hx₂,
  rw [normed_field.norm_mul, normed_field.norm_mul, mul_assoc, mul_left_comm c₂, ←mul_assoc],
  exact mul_le_mul hx₁ hx₂ (norm_nonneg _) (mul_nonneg (le_of_lt c₁pos) (norm_nonneg _))
end

theorem is_littleo_mul_left {f₁ f₂ : α → β} {g₁ g₂ : α → γ} {l : filter α}
    (h₁ : is_bigo f₁ g₁ l) (h₂ : is_littleo f₂ g₂ l):
  is_littleo (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
begin
  intros c cpos,
  rcases h₁ with ⟨c₁, c₁pos, hc₁⟩,
  filter_upwards [hc₁, h₂ (c / c₁) (div_pos cpos c₁pos)], dsimp,
  intros x hx₁ hx₂,
  rw [normed_field.norm_mul, normed_field.norm_mul],
  apply le_trans (mul_le_mul hx₁ hx₂ (norm_nonneg _) (mul_nonneg (le_of_lt c₁pos) (norm_nonneg _))),
  rw [mul_comm c₁, mul_assoc, mul_left_comm c₁, ←mul_assoc _ c₁, div_mul_cancel _ (ne_of_gt c₁pos)],
  rw [mul_left_comm]
end

theorem is_littleo_mul_right {f₁ f₂ : α → β} {g₁ g₂ : α → γ} {l : filter α}
    (h₁ : is_littleo f₁ g₁ l) (h₂ : is_bigo f₂ g₂ l):
  is_littleo (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
by convert is_littleo_mul_left h₂ h₁; simp only [mul_comm]

theorem is_littleo_mul {f₁ f₂ : α → β} {g₁ g₂ : α → γ} {l : filter α}
    (h₁ : is_littleo f₁ g₁ l) (h₂ : is_littleo f₂ g₂ l):
  is_littleo (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
is_littleo_mul_left h₁.to_is_bigo h₂

end

/-
Note: the theorems in the next two sections can also be used for the integers, since
scalar multiplication is multiplication.
-/

section
variables {K : Type*} [normed_field K] [normed_space K β] [normed_group γ]

theorem is_bigo_const_smul_left {f : α → β} {g : α → γ} {l : filter α} (h : is_bigo f g l) (c : K) :
  is_bigo (λ x, c • f x) g l :=
begin
  rw [←is_bigo_norm_left], simp only [norm_smul],
  apply is_bigo_const_mul_left,
  rw [is_bigo_norm_left],
  apply h
end

theorem is_bigo_const_smul_left_iff {f : α → β} {g : α → γ} {l : filter α}
    {c : K} (hc : c ≠ 0) :
  is_bigo (λ x, c • f x) g l ↔ is_bigo f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp hc,
  rw [←is_bigo_norm_left], simp only [norm_smul],
  rw [is_bigo_const_mul_left_iff cne0, is_bigo_norm_left]
end

theorem is_littleo_const_smul_left {f : α → β} {g : α → γ} {l : filter α}
    (h : is_littleo f g l) (c : K) :
  is_littleo (λ x, c • f x) g l :=
begin
  rw [←is_littleo_norm_left], simp only [norm_smul],
  apply is_littleo_const_mul_left,
  rw [is_littleo_norm_left],
  apply h
end

theorem is_littleo_const_smul_left_iff {f : α → β} {g : α → γ} {l : filter α} {c : K} (hc : c ≠ 0) :
  is_littleo (λ x, c • f x) g l ↔ is_littleo f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp hc,
  rw [←is_littleo_norm_left], simp only [norm_smul],
  rw [is_littleo_const_mul_left_iff cne0, is_littleo_norm_left]
end

end

section
variables {K : Type*} [normed_group β] [normed_field K] [normed_space K γ]

theorem is_bigo_const_smul_right {f : α → β} {g : α → γ} {l : filter α} {c : K} (hc : c ≠ 0) :
  is_bigo f (λ x, c • g x) l ↔ is_bigo f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp hc,
  rw [←is_bigo_norm_right], simp only [norm_smul],
  rw [is_bigo_const_mul_right_iff cne0, is_bigo_norm_right]
end

theorem is_littleo_const_smul_right {f : α → β} {g : α → γ} {l : filter α} {c : K} (hc : c ≠ 0) :
  is_littleo f (λ x, c • g x) l ↔ is_littleo f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp hc,
  rw [←is_littleo_norm_right], simp only [norm_smul],
  rw [is_littleo_const_mul_right cne0, is_littleo_norm_right]
end

end

section
variables {K : Type*} [normed_field K] [normed_space K β] [normed_space K γ]

theorem is_bigo_smul {k : α → K} {f : α → β} {g : α → γ} {l : filter α} (h : is_bigo f g l) :
  is_bigo (λ x, k x • f x) (λ x, k x • g x) l :=
begin
  rw [←is_bigo_norm_left, ←is_bigo_norm_right], simp only [norm_smul],
  apply is_bigo_mul (is_bigo_refl _ _),
  rw [is_bigo_norm_left, is_bigo_norm_right],
  exact h
end

theorem is_littleo_smul {k : α → K} {f : α → β} {g : α → γ} {l : filter α} (h : is_littleo f g l) :
  is_littleo (λ x, k x • f x) (λ x, k x • g x) l :=
begin
  rw [←is_littleo_norm_left, ←is_littleo_norm_right], simp only [norm_smul],
  apply is_littleo_mul_left (is_bigo_refl _ _),
  rw [is_littleo_norm_left, is_littleo_norm_right],
  exact h
end

end

section
variables [normed_field β]

theorem tendsto_nhds_zero_of_is_littleo {f g : α → β} {l : filter α}
    (h : is_littleo f g l) :
  tendsto (λ x, f x / (g x)) l (nhds 0) :=
have eq₁ : is_littleo (λ x, f x / g x) (λ x, g x / g x) l,
  from is_littleo_mul_right h (is_bigo_refl _ _),
have eq₂ : is_bigo (λ x, g x / g x) (λ x, (1 : β)) l,
  begin
    use [1, zero_lt_one],
    filter_upwards [univ_mem_sets], simp,
    intro x,
    cases classical.em (∥g x∥ = 0) with h' h'; simp [h'],
    exact zero_le_one
  end,
is_littleo_one_iff.mp (eq₁.trans_is_bigo eq₂)

private theorem is_littleo_of_tendsto {f g : α → β} {l : filter α}
    (hgf : ∀ x, g x = 0 → f x = 0) (h : tendsto (λ x, f x / (g x)) l (nhds 0)) :
  is_littleo f g l :=
have eq₁ : is_littleo (λ x, f x / (g x)) (λ x, (1 : β)) l,
  from is_littleo_one_iff.mpr h,
have eq₂ : is_littleo (λ x, f x / g x * g x) g l,
  by convert is_littleo_mul_right eq₁ (is_bigo_refl _ _); simp,
have eq₃ : is_bigo f (λ x, f x / g x * g x) l,
  begin
    use [1, zero_lt_one],
    filter_upwards [univ_mem_sets], simp,
    intro x,
    cases classical.em (∥g x∥ = 0) with h' h',
    { rw hgf _ ((norm_eq_zero _).mp h'), simp },
    rw [normed_field.norm_mul, norm_div, div_mul_cancel _ h']
  end,
eq₃.trans_is_littleo eq₂

theorem is_littleo_iff_tendsto [normed_field β] {f g : α → β} {l : filter α}
    (hgf : ∀ x, g x = 0 → f x = 0) :
  is_littleo f g l ↔ tendsto (λ x, f x / (g x)) l (nhds 0) :=
iff.intro tendsto_nhds_zero_of_is_littleo (is_littleo_of_tendsto hgf)

end

end asymptotics
