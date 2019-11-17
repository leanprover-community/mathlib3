/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad
-/

import analysis.normed_space.basic

/-!
# Asymptotics

We introduce these relations:

  `is_O f g l` : "f is big O of g along l"
  `is_o f g l` : "f is little o of g along l"

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed that there is a norm associated with
these types, and it is the norm that is compared asymptotically.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `is_O f g l ↔ is_O (λ x, ∥f x∥) (λ x, ∥g x∥) l`,

and similarly for `is_o`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `is_o f g l ↔ tendsto (λ x, f x / (g x)) (𝓝 0) l`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)
-/

open filter
open_locale topological_space

namespace asymptotics

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {𝕜 : Type*} {𝕜' : Type*}

section
variables [has_norm β] [has_norm γ] [has_norm δ]

/-- The Landau notation `is_O f g l` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by a constant multiple of `∥g∥`.
In other words, `∥f∥ / ∥g∥` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
def is_O (f : α → β) (g : α → γ) (l : filter α) : Prop :=
∃ c > 0, { x | ∥ f x ∥ ≤ c * ∥ g x ∥ } ∈ l

/-- The Landau notation `is_o f g l` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by an arbitrarily small constant
multiple of `∥g∥`. In other words, `∥f∥ / ∥g∥` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
def is_o (f : α → β) (g : α → γ) (l : filter α) : Prop :=
∀ c > 0, { x | ∥ f x ∥ ≤  c * ∥ g x ∥ } ∈ l

theorem is_O_refl (f : α → β) (l : filter α) : is_O f f l :=
⟨1, zero_lt_one, by { filter_upwards [univ_mem_sets], intros x _, simp }⟩

theorem is_O.comp {f : α → β} {g : α → γ} {l : filter α} (hfg : is_O f g l)
    {δ : Type*} (k : δ → α) :
  is_O (f ∘ k) (g ∘ k) (l.comap k) :=
let ⟨c, cpos, hfgc⟩ := hfg in
⟨c, cpos, mem_comap_sets.mpr ⟨_, hfgc, set.subset.refl _⟩⟩

theorem is_o.comp {f : α → β} {g : α → γ} {l : filter α} (hfg : is_o f g l)
    {δ : Type*} (k : δ → α) :
  is_o (f ∘ k) (g ∘ k) (l.comap k) :=
λ c cpos, mem_comap_sets.mpr ⟨_, hfg c cpos, set.subset.refl _⟩

theorem is_O.mono {f : α → β} {g : α → γ} {l₁ l₂ : filter α} (h : l₁ ≤ l₂)
  (h' : is_O f g l₂) : is_O f g l₁ :=
let ⟨c, cpos, h'c⟩ := h' in ⟨c, cpos, h (h'c)⟩

theorem is_o.mono {f : α → β} {g : α → γ} {l₁ l₂ : filter α} (h : l₁ ≤ l₂)
  (h' : is_o f g l₂) : is_o f g l₁ :=
λ c cpos, h (h' c cpos)

theorem is_o.to_is_O {f : α → β} {g : α → γ} {l : filter α} (hgf : is_o f g l) : is_O f g l :=
⟨1, zero_lt_one, hgf 1 zero_lt_one⟩

theorem is_O.trans {f : α → β} {g : α → γ} {k : α → δ} {l : filter α}
    (h₁ : is_O f g l) (h₂ : is_O g k l) :
  is_O f k l :=
let ⟨c,  cpos,  hc⟩  := h₁,
    ⟨c', c'pos, hc'⟩ := h₂ in
begin
  use [c * c', mul_pos cpos c'pos],
  filter_upwards [hc, hc'], dsimp,
  intros x h₁x h₂x, rw mul_assoc,
  exact le_trans h₁x (mul_le_mul_of_nonneg_left h₂x (le_of_lt cpos))
end

theorem is_o.trans_is_O {f : α → β} {g : α → γ} {k : α → δ} {l : filter α}
    (h₁ : is_o f g l) (h₂ : is_O g k l) :
  is_o f k l :=
begin
  intros c cpos,
  rcases h₂ with ⟨c', c'pos, hc'⟩,
  have cc'pos := div_pos cpos c'pos,
  filter_upwards [h₁ (c / c') cc'pos, hc'], dsimp,
  intros x h₁x h₂x,
  refine le_trans h₁x (le_trans (mul_le_mul_of_nonneg_left h₂x (le_of_lt cc'pos)) _),
  rw [←mul_assoc, div_mul_cancel _ (ne_of_gt c'pos)]
end

theorem is_O.trans_is_o {f : α → β} {g : α → γ} {k : α → δ} {l : filter α}
    (h₁ : is_O f g l) (h₂ : is_o g k l) :
  is_o f k l :=
begin
  intros c cpos,
  rcases h₁ with ⟨c', c'pos, hc'⟩,
  have cc'pos := div_pos cpos c'pos,
  filter_upwards [hc', h₂ (c / c') cc'pos], dsimp,
  intros x h₁x h₂x,
  refine le_trans h₁x (le_trans (mul_le_mul_of_nonneg_left h₂x (le_of_lt c'pos)) _),
  rw [←mul_assoc, mul_div_cancel' _ (ne_of_gt c'pos)]
end

theorem is_o.trans {f : α → β} {g : α → γ} {k : α → δ} {l : filter α}
    (h₁ : is_o f g l) (h₂ : is_o g k l) :
  is_o f k l :=
h₁.to_is_O.trans_is_o h₂

theorem is_o_join {f : α → β} {g : α → γ} {l₁ l₂ : filter α}
    (h₁ : is_o f g l₁) (h₂ : is_o f g l₂) :
  is_o f g (l₁ ⊔ l₂) :=
begin
  intros c cpos,
  rw mem_sup_sets,
  exact ⟨h₁ c cpos, h₂ c cpos⟩
end

theorem is_O_congr {f₁ f₂ : α → β} {g₁ g₂ : α → γ} {l : filter α}
    (hf : {x | f₁ x = f₂ x} ∈ l) (hg : {x | g₁ x = g₂ x} ∈ l) :
  is_O f₁ g₁ l ↔ is_O f₂ g₂ l :=
bex_congr $ λ c _, filter.congr_sets $
by filter_upwards [hf, hg] λ x e₁ e₂,
  by dsimp at e₁ e₂ ⊢; rw [e₁, e₂]

theorem is_o_congr {f₁ f₂ : α → β} {g₁ g₂ : α → γ} {l : filter α}
    (hf : {x | f₁ x = f₂ x} ∈ l) (hg : {x | g₁ x = g₂ x} ∈ l) :
  is_o f₁ g₁ l ↔ is_o f₂ g₂ l :=
ball_congr $ λ c _, filter.congr_sets $
by filter_upwards [hf, hg] λ x e₁ e₂,
  by dsimp at e₁ e₂ ⊢; rw [e₁, e₂]

theorem is_O.congr {f₁ f₂ : α → β} {g₁ g₂ : α → γ} {l : filter α}
    (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
  is_O f₁ g₁ l → is_O f₂ g₂ l :=
(is_O_congr (univ_mem_sets' hf) (univ_mem_sets' hg)).1

theorem is_o.congr {f₁ f₂ : α → β} {g₁ g₂ : α → γ} {l : filter α}
    (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
  is_o f₁ g₁ l → is_o f₂ g₂ l :=
(is_o_congr (univ_mem_sets' hf) (univ_mem_sets' hg)).1

theorem is_O_congr_left {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h : {x | f₁ x = f₂ x} ∈ l) :
  is_O f₁ g l ↔ is_O f₂ g l :=
is_O_congr h (univ_mem_sets' $ λ _, rfl)

theorem is_o_congr_left {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h : {x | f₁ x = f₂ x} ∈ l) :
  is_o f₁ g l ↔ is_o f₂ g l :=
is_o_congr h (univ_mem_sets' $ λ _, rfl)

theorem is_O.congr_left {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
  (hf : ∀ x, f₁ x = f₂ x) : is_O f₁ g l → is_O f₂ g l :=
is_O.congr hf (λ _, rfl)

theorem is_o.congr_left {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
  (hf : ∀ x, f₁ x = f₂ x) : is_o f₁ g l → is_o f₂ g l :=
is_o.congr hf (λ _, rfl)

theorem is_O_congr_right {f : α → β} {g₁ g₂ : α → γ} {l : filter α}
    (h : {x | g₁ x = g₂ x} ∈ l) :
  is_O f g₁ l ↔ is_O f g₂ l :=
is_O_congr (univ_mem_sets' $ λ _, rfl) h

theorem is_o_congr_right {f : α → β} {g₁ g₂ : α → γ} {l : filter α}
    (h : {x | g₁ x = g₂ x} ∈ l) :
  is_o f g₁ l ↔ is_o f g₂ l :=
is_o_congr (univ_mem_sets' $ λ _, rfl) h

theorem is_O.congr_right {f : α → β} {g₁ g₂ : α → γ} {l : filter α}
  (hg : ∀ x, g₁ x = g₂ x) : is_O f g₁ l → is_O f g₂ l :=
is_O.congr (λ _, rfl) hg

theorem is_o.congr_right {f : α → β} {g₁ g₂ : α → γ} {l : filter α}
  (hg : ∀ x, g₁ x = g₂ x) : is_o f g₁ l → is_o f g₂ l :=
is_o.congr (λ _, rfl) hg

end

section
variables [has_norm β] [normed_group γ] [normed_group δ]

@[simp]
theorem is_O_norm_right {f : α → β} {g : α → γ} {l : filter α} :
  is_O f (λ x, ∥g x∥) l ↔ is_O f g l :=
by simp only [is_O, norm_norm]

@[simp]
theorem is_o_norm_right {f : α → β} {g : α → γ} {l : filter α} :
  is_o f (λ x, ∥g x∥) l ↔ is_o f g l :=
by simp only [is_o, norm_norm]

@[simp]
theorem is_O_neg_right {f : α → β} {g : α → γ} {l : filter α} :
  is_O f (λ x, -(g x)) l ↔ is_O f g l :=
by { rw ←is_O_norm_right, simp only [norm_neg], rw is_O_norm_right }

@[simp]
theorem is_o_neg_right {f : α → β} {g : α → γ} {l : filter α} :
  is_o f (λ x, -(g x)) l ↔ is_o f g l :=
by { rw ←is_o_norm_right, simp only [norm_neg], rw is_o_norm_right }

theorem is_O_iff {f : α → β} {g : α → γ} {l : filter α} :
  is_O f g l ↔ ∃ c, { x | ∥f x∥ ≤ c * ∥g x∥ } ∈ l :=
suffices (∃ c, { x | ∥f x∥ ≤ c * ∥g x∥ } ∈ l) → is_O f g l,
  from ⟨λ ⟨c, cpos, hc⟩, ⟨c, hc⟩, this⟩,
assume ⟨c, hc⟩,
or.elim (lt_or_ge 0 c)
  (assume : c > 0, ⟨c, this, hc⟩)
  (assume h'c : c ≤ 0,
    have {x : α | ∥f x∥ ≤ 1 * ∥g x∥} ∈ l,
      begin
        filter_upwards [hc], intros x,
        show ∥f x∥ ≤ c * ∥g x∥ → ∥f x∥ ≤ 1 * ∥g x∥,
        { intro hx, apply le_trans hx,
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
          show c ≤ 1, from le_trans h'c zero_le_one }
      end,
    ⟨1, zero_lt_one, this⟩)

theorem is_O_join {f : α → β} {g : α → γ} {l₁ l₂ : filter α}
    (h₁ : is_O f g l₁) (h₂ : is_O f g l₂) :
  is_O f g (l₁ ⊔ l₂) :=
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

lemma is_O.prod_rightl {f : α → β} {g₁ : α → γ} {g₂ : α → δ} {l : filter α}
  (h : is_O f g₁ l) : is_O f (λx, (g₁ x, g₂ x)) l :=
begin
  have : is_O g₁ (λx, (g₁ x, g₂ x)) l :=
    ⟨1, zero_lt_one, filter.univ_mem_sets' (λx, by simp [norm, le_refl])⟩,
  exact is_O.trans h this
end

lemma is_O.prod_rightr {f : α → β} {g₁ : α → γ} {g₂ : α → δ} {l : filter α}
  (h : is_O f g₂ l) : is_O f (λx, (g₁ x, g₂ x)) l :=
begin
  have : is_O g₂ (λx, (g₁ x, g₂ x)) l :=
    ⟨1, zero_lt_one, filter.univ_mem_sets' (λx, by simp [norm, le_refl])⟩,
  exact is_O.trans h this
end

lemma is_o.prod_rightl {f : α → β} {g₁ : α → γ} {g₂ : α → δ} {l : filter α}
  (h : is_o f g₁ l) : is_o f (λx, (g₁ x, g₂ x)) l :=
is_o.trans_is_O h (is_O.prod_rightl (is_O_refl g₁ l))

lemma is_o.prod_rightr {f : α → β} {g₁ : α → γ} {g₂ : α → δ} {l : filter α}
  (h : is_o f g₂ l) : is_o f (λx, (g₁ x, g₂ x)) l :=
is_o.trans_is_O h (is_O.prod_rightr (is_O_refl g₂ l))

end

section
variables [normed_group β] [normed_group δ] [has_norm γ]

@[simp] theorem is_O_norm_left {f : α → β} {g : α → γ} {l : filter α} :
  is_O (λ x, ∥f x∥) g l ↔ is_O f g l :=
by simp only [is_O, norm_norm]

@[simp] theorem is_o_norm_left {f : α → β} {g : α → γ} {l : filter α} :
  is_o (λ x, ∥f x∥) g l ↔ is_o f g l :=
by simp only [is_o, norm_norm]

@[simp] theorem is_O_neg_left {f : α → β} {g : α → γ} {l : filter α} :
  is_O (λ x, -f x) g l ↔ is_O f g l :=
by { rw ←is_O_norm_left, simp only [norm_neg], rw is_O_norm_left }

@[simp] theorem is_o_neg_left {f : α → β} {g : α → γ} {l : filter α} :
  is_o (λ x, -f x) g l ↔ is_o f g l :=
by { rw ←is_o_norm_left, simp only [norm_neg], rw is_o_norm_left }

theorem is_O.add {f₁ f₂ : α → β} {g : α → γ} {l : filter α} (h₁ : is_O f₁ g l) (h₂ : is_O f₂ g l) :
  is_O (λ x, f₁ x + f₂ x) g l :=
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

theorem is_o.add {f₁ f₂ : α → β} {g : α → γ} {l : filter α} (h₁ : is_o f₁ g l) (h₂ : is_o f₂ g l) :
  is_o (λ x, f₁ x + f₂ x) g l :=
begin
  intros c cpos,
  filter_upwards [h₁ (c / 2) (half_pos cpos), h₂ (c / 2) (half_pos cpos)],
  intros x hx₁ hx₂, dsimp at hx₁ hx₂,
  apply le_trans (norm_triangle _ _),
  apply le_trans (add_le_add hx₁ hx₂),
  rw [←mul_add, ←two_mul, ←mul_assoc, div_mul_cancel _ two_ne_zero]
end

theorem is_O.sub {f₁ f₂ : α → β} {g : α → γ} {l : filter α} (h₁ : is_O f₁ g l) (h₂ : is_O f₂ g l) :
  is_O (λ x, f₁ x - f₂ x) g l :=
h₁.add (is_O_neg_left.mpr h₂)

theorem is_o.sub {f₁ f₂ : α → β} {g : α → γ} {l : filter α} (h₁ : is_o f₁ g l) (h₂ : is_o f₂ g l) :
  is_o (λ x, f₁ x - f₂ x) g l :=
h₁.add (is_o_neg_left.mpr h₂)

theorem is_O_comm {f₁ f₂ : α → β} {g : α → γ} {l : filter α} :
  is_O (λ x, f₁ x - f₂ x) g l ↔ is_O (λ x, f₂ x - f₁ x) g l :=
by simpa using @is_O_neg_left _ _ _ _ _ (λ x, f₂ x - f₁ x) g l

theorem is_O.symm {f₁ f₂ : α → β} {g : α → γ} {l : filter α} :
  is_O (λ x, f₁ x - f₂ x) g l → is_O (λ x, f₂ x - f₁ x) g l :=
is_O_comm.1

theorem is_O.tri {f₁ f₂ f₃ : α → β} {g : α → γ} {l : filter α}
    (h₁ : is_O (λ x, f₁ x - f₂ x) g l)
    (h₂ : is_O (λ x, f₂ x - f₃ x) g l) :
  is_O (λ x, f₁ x - f₃ x) g l :=
(h₁.add h₂).congr_left (by simp)

theorem is_O.congr_of_sub {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h : is_O (λ x, f₁ x - f₂ x) g l) :
  is_O f₁ g l ↔ is_O f₂ g l :=
⟨λ h', (h'.sub h).congr_left (λ x, sub_sub_cancel _ _),
 λ h', (h.add h').congr_left (λ x, sub_add_cancel _ _)⟩

theorem is_o_comm {f₁ f₂ : α → β} {g : α → γ} {l : filter α} :
  is_o (λ x, f₁ x - f₂ x) g l ↔ is_o (λ x, f₂ x - f₁ x) g l :=
by simpa using @is_o_neg_left _ _ _ _ _ (λ x, f₂ x - f₁ x) g l

theorem is_o.symm {f₁ f₂ : α → β} {g : α → γ} {l : filter α} :
  is_o (λ x, f₁ x - f₂ x) g l → is_o (λ x, f₂ x - f₁ x) g l :=
is_o_comm.1

theorem is_o.tri {f₁ f₂ f₃ : α → β} {g : α → γ} {l : filter α}
    (h₁ : is_o (λ x, f₁ x - f₂ x) g l)
    (h₂ : is_o (λ x, f₂ x - f₃ x) g l) :
  is_o (λ x, f₁ x - f₃ x) g l :=
(h₁.add h₂).congr_left (by simp)

theorem is_o.congr_of_sub {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h : is_o (λ x, f₁ x - f₂ x) g l) :
  is_o f₁ g l ↔ is_o f₂ g l :=
⟨λ h', (h'.sub h).congr_left (λ x, sub_sub_cancel _ _),
 λ h', (h.add h').congr_left (λ x, sub_add_cancel _ _)⟩

@[simp] theorem is_O_prod_left {f₁ : α → β} {f₂ : α → δ} {g : α → γ} {l : filter α} :
  is_O (λx, (f₁ x, f₂ x)) g l ↔ is_O f₁ g l ∧ is_O f₂ g l :=
begin
  split,
  { assume h,
    split,
    { exact is_O.trans (is_O.prod_rightl (is_O_refl f₁ l)) h },
    { exact is_O.trans (is_O.prod_rightr (is_O_refl f₂ l)) h } },
  { rintros ⟨h₁, h₂⟩,
    have : is_O (λx, ∥f₁ x∥ + ∥f₂ x∥) g l :=
      is_O.add (is_O_norm_left.2 h₁) (is_O_norm_left.2 h₂),
    apply is_O.trans _ this,
    refine ⟨1, zero_lt_one, filter.univ_mem_sets' (λx, _)⟩,
    simp only [norm, max_le_iff, one_mul, set.mem_set_of_eq],
    split; exact le_trans (by simp) (le_abs_self _) }
end

@[simp] theorem is_o_prod_left {f₁ : α → β} {f₂ : α → δ} {g : α → γ} {l : filter α} :
  is_o (λx, (f₁ x, f₂ x)) g l ↔ is_o f₁ g l ∧ is_o f₂ g l :=
begin
  split,
  { assume h,
    split,
    { exact is_O.trans_is_o (is_O.prod_rightl (is_O_refl f₁ l)) h },
    { exact is_O.trans_is_o (is_O.prod_rightr (is_O_refl f₂ l)) h } },
  { rintros ⟨h₁, h₂⟩,
    have : is_o (λx, ∥f₁ x∥ + ∥f₂ x∥) g l :=
      is_o.add (is_o_norm_left.2 h₁) (is_o_norm_left.2 h₂),
    apply is_O.trans_is_o _ this,
    refine ⟨1, zero_lt_one, filter.univ_mem_sets' (λx, _)⟩,
    simp only [norm, max_le_iff, one_mul, set.mem_set_of_eq],
    split; exact le_trans (by simp) (le_abs_self _) }
end

end

section
variables [normed_group β] [normed_group γ]

theorem is_O_zero (g : α → γ) (l : filter α) :
  is_O (λ x, (0 : β)) g l :=
⟨1, zero_lt_one, by { filter_upwards [univ_mem_sets], intros x _, simp }⟩

theorem is_O_refl_left {f : α → β} {g : α → γ} {l : filter α} :
  is_O (λ x, f x - f x) g l :=
by simpa using is_O_zero g l

theorem is_O_zero_right_iff {f : α → β} {l : filter α} :
  is_O f (λ x, (0 : γ)) l ↔ {x | f x = 0} ∈ l :=
begin
  rw [is_O_iff], split,
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

theorem is_o_zero (g : α → γ) (l : filter α) :
  is_o (λ x, (0 : β)) g l :=
λ c cpos,
by { filter_upwards [univ_mem_sets], intros x _, simp,
     exact mul_nonneg (le_of_lt cpos) (norm_nonneg _)}

theorem is_o_refl_left {f : α → β} {g : α → γ} {l : filter α} :
  is_o (λ x, f x - f x) g l :=
by simpa using is_o_zero g l

theorem is_o_zero_right_iff {f : α → β} (l : filter α) :
  is_o f (λ x, (0 : γ)) l ↔ {x | f x = 0} ∈ l :=
begin
  split,
  { intro h, exact is_O_zero_right_iff.mp h.to_is_O },
  intros h c cpos,
  filter_upwards [h], dsimp,
  intros x hx,
  rw [hx, norm_zero, norm_zero, mul_zero]
end

end

section
variables [has_norm β] [normed_field 𝕜]

open normed_field

theorem is_O_const_one (c : β) (l : filter α) :
  is_O (λ x : α, c) (λ x, (1 : 𝕜)) l :=
begin
  rw is_O_iff,
  refine ⟨∥c∥, _⟩,
  simp only [norm_one, mul_one],
  apply univ_mem_sets',
  simp [le_refl],
end

end

section
variables [normed_field 𝕜] [normed_group γ]

theorem is_O_const_mul_left {f : α → 𝕜} {g : α → γ} {l : filter α} (h : is_O f g l) (c : 𝕜) :
  is_O (λ x, c * f x) g l :=
 begin
  cases classical.em (c = 0) with h'' h'',
  { simp [h''], apply is_O_zero },
  rcases h with ⟨c', c'pos, h'⟩,
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp h'',
  have cpos : ∥c∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm cne0),
  refine ⟨∥c∥ * c', mul_pos cpos c'pos, _⟩,
  filter_upwards [h'], dsimp,
  intros x h₀,
  rw [normed_field.norm_mul, mul_assoc],
  exact mul_le_mul_of_nonneg_left h₀ (norm_nonneg _)
end

theorem is_O_const_mul_left_iff {f : α → 𝕜} {g : α → γ} {l : filter α} {c : 𝕜} (hc : c ≠ 0) :
  is_O (λ x, c * f x) g l ↔ is_O f g l :=
begin
  split,
  { intro h,
    convert is_O_const_mul_left h c⁻¹, ext,
    rw [←mul_assoc, inv_mul_cancel hc, one_mul] },
  intro h, apply is_O_const_mul_left h
end

theorem is_o_const_mul_left {f : α → 𝕜} {g : α → γ} {l : filter α} (h : is_o f g l) (c : 𝕜) :
  is_o (λ x, c * f x) g l :=
begin
  cases classical.em (c = 0) with h'' h'',
  { simp [h''], apply is_o_zero },
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp h'',
  have cpos : ∥c∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm cne0),
  intros c' c'pos, dsimp,
  filter_upwards [h (c' / ∥c∥) (div_pos c'pos cpos)], dsimp,
  intros x hx, rw [normed_field.norm_mul],
  apply le_trans (mul_le_mul_of_nonneg_left hx (le_of_lt cpos)),
  rw [←mul_assoc, mul_div_cancel' _ cne0]
end

theorem is_o_const_mul_left_iff {f : α → 𝕜} {g : α → γ} {l : filter α} {c : 𝕜} (hc : c ≠ 0) :
  is_o (λ x, c * f x) g l ↔ is_o f g l :=
begin
  split,
  { intro h,
    convert is_o_const_mul_left h c⁻¹, ext,
    rw [←mul_assoc, inv_mul_cancel hc, one_mul] },
  intro h',
  apply is_o_const_mul_left h'
end

end

section
variables [normed_group β] [normed_field 𝕜]

theorem is_O_of_is_O_const_mul_right {f : α → β} {g : α → 𝕜} {l : filter α} {c : 𝕜}
    (h : is_O f (λ x, c * g x) l) :
  is_O f g l  :=
begin
  cases classical.em (c = 0) with h' h',
  { simp [h', is_O_zero_right_iff] at h, rw is_O_congr_left h, apply is_O_zero },
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp h',
  have cpos : ∥c∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm cne0),
  rcases h with ⟨c', c'pos, h''⟩,
  refine ⟨c' * ∥c∥, mul_pos c'pos cpos, _⟩,
  convert h'', ext x, dsimp,
  rw [normed_field.norm_mul, mul_assoc]
end

theorem is_O_const_mul_right_iff {f : α → β} {g : α → 𝕜} {l : filter α} {c : 𝕜} (hc : c ≠ 0) :
  is_O f (λ x, c * g x) l ↔ is_O f g l :=
begin
  split,
  { intro h, exact is_O_of_is_O_const_mul_right h },
  intro h,
  apply is_O_of_is_O_const_mul_right,
  show is_O f (λ (x : α), c⁻¹ * (c * g x)) l,
  convert h, ext, rw [←mul_assoc, inv_mul_cancel hc, one_mul]
end

theorem is_o_of_is_o_const_mul_right {f : α → β} {g : α → 𝕜} {l : filter α} {c : 𝕜}
    (h : is_o f (λ x, c * g x) l) :
  is_o f g l  :=
begin
  cases classical.em (c = 0) with h' h',
  { simp [h', is_o_zero_right_iff] at h, rw is_o_congr_left h, apply is_o_zero },
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp h',
  have cpos : ∥c∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm cne0),
  intros c' c'pos,
  convert h (c' / ∥c∥) (div_pos c'pos cpos), dsimp,
  ext x, rw [normed_field.norm_mul, ←mul_assoc, div_mul_cancel _ cne0]
end

theorem is_o_const_mul_right {f : α → β} {g : α → 𝕜} {l : filter α} {c : 𝕜} (hc : c ≠ 0) :
  is_o f (λ x, c * g x) l ↔ is_o f g l :=
begin
  split,
  { intro h, exact is_o_of_is_o_const_mul_right h },
  intro h,
  apply is_o_of_is_o_const_mul_right,
  show is_o f (λ (x : α), c⁻¹ * (c * g x)) l,
  convert h, ext, rw [←mul_assoc, inv_mul_cancel hc, one_mul]
end

theorem is_o_one_iff {f : α → β} {l : filter α} :
  is_o f (λ x, (1 : 𝕜)) l ↔ tendsto f l (𝓝 0) :=
begin
  rw [normed_group.tendsto_nhds_zero, is_o], split,
  { intros h e epos,
    filter_upwards [h (e / 2) (half_pos epos)], simp,
    intros x hx,
    exact lt_of_le_of_lt hx (half_lt_self epos) },
  intros h e epos,
  filter_upwards [h e epos], simp,
  intros x hx,
  exact le_of_lt hx
end

theorem is_O_one_of_tendsto {f : α → β} {l : filter α} {y : β}
  (h : tendsto f l (𝓝 y)) : is_O f (λ x, (1 : 𝕜)) l :=
begin
  have Iy : ∥y∥ < ∥y∥ + 1 := lt_add_one _,
  refine ⟨∥y∥ + 1, lt_of_le_of_lt (norm_nonneg _) Iy, _⟩,
  simp only [mul_one, normed_field.norm_one],
  have : tendsto (λx, ∥f x∥) l (𝓝 ∥y∥) :=
    (continuous_norm.tendsto _).comp h,
  exact this (ge_mem_nhds Iy)
end

end

section
variables [normed_group β] [normed_group γ]

theorem is_O.trans_tendsto {f : α → β} {g : α → γ} {l : filter α}
    (h₁ : is_O f g l) (h₂ : tendsto g l (𝓝 0)) :
  tendsto f l (𝓝 0) :=
(@is_o_one_iff _ _ ℝ _ _ _ _).1 $ h₁.trans_is_o $ is_o_one_iff.2 h₂

theorem is_o.trans_tendsto {f : α → β} {g : α → γ} {l : filter α}
  (h₁ : is_o f g l) : tendsto g l (𝓝 0) → tendsto f l (𝓝 0) :=
h₁.to_is_O.trans_tendsto

end

section
variables [normed_field 𝕜] [normed_field 𝕜']

theorem is_O_mul {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} {l : filter α}
    (h₁ : is_O f₁ g₁ l) (h₂ : is_O f₂ g₂ l) :
  is_O (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
begin
  rcases h₁ with ⟨c₁, c₁pos, hc₁⟩,
  rcases h₂ with ⟨c₂, c₂pos, hc₂⟩,
  refine ⟨c₁ * c₂, mul_pos c₁pos c₂pos, _⟩,
  filter_upwards [hc₁, hc₂], dsimp,
  intros x hx₁ hx₂,
  rw [normed_field.norm_mul, normed_field.norm_mul, mul_assoc, mul_left_comm c₂, ←mul_assoc],
  exact mul_le_mul hx₁ hx₂ (norm_nonneg _) (mul_nonneg (le_of_lt c₁pos) (norm_nonneg _))
end

theorem is_o_mul_left {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} {l : filter α}
    (h₁ : is_O f₁ g₁ l) (h₂ : is_o f₂ g₂ l) :
  is_o (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
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

theorem is_o_mul_right {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} {l : filter α}
    (h₁ : is_o f₁ g₁ l) (h₂ : is_O f₂ g₂ l) :
  is_o (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
by convert is_o_mul_left h₂ h₁; simp only [mul_comm]

theorem is_o_mul {f₁ f₂ : α → 𝕜} {g₁ g₂ : α → 𝕜'} {l : filter α}
    (h₁ : is_o f₁ g₁ l) (h₂ : is_o f₂ g₂ l) :
  is_o (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) l :=
is_o_mul_left h₁.to_is_O h₂

end

/-
Note: the theorems in the next two sections can also be used for the integers, since
scalar multiplication is multiplication.
-/

section
variables [normed_field 𝕜] [normed_group β] [normed_space 𝕜 β] [normed_group γ]

set_option class.instance_max_depth 43

theorem is_O_const_smul_left {f : α → β} {g : α → γ} {l : filter α} (h : is_O f g l) (c : 𝕜) :
  is_O (λ x, c • f x) g l :=
begin
  rw [←is_O_norm_left], simp only [norm_smul],
  apply is_O_const_mul_left,
  rw [is_O_norm_left],
  apply h
end

theorem is_O_const_smul_left_iff {f : α → β} {g : α → γ} {l : filter α} {c : 𝕜} (hc : c ≠ 0) :
  is_O (λ x, c • f x) g l ↔ is_O f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp hc,
  rw [←is_O_norm_left], simp only [norm_smul],
  rw [is_O_const_mul_left_iff cne0, is_O_norm_left]
end

theorem is_o_const_smul_left {f : α → β} {g : α → γ} {l : filter α} (h : is_o f g l) (c : 𝕜) :
  is_o (λ x, c • f x) g l :=
begin
  rw [←is_o_norm_left], simp only [norm_smul],
  apply is_o_const_mul_left,
  rw [is_o_norm_left],
  apply h
end

theorem is_o_const_smul_left_iff {f : α → β} {g : α → γ} {l : filter α} {c : 𝕜} (hc : c ≠ 0) :
  is_o (λ x, c • f x) g l ↔ is_o f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp hc,
  rw [←is_o_norm_left], simp only [norm_smul],
  rw [is_o_const_mul_left_iff cne0, is_o_norm_left]
end

end

section
variables [normed_group β] [normed_field 𝕜] [normed_group γ] [normed_space 𝕜 γ]

set_option class.instance_max_depth 43

theorem is_O_const_smul_right {f : α → β} {g : α → γ} {l : filter α} {c : 𝕜} (hc : c ≠ 0) :
  is_O f (λ x, c • g x) l ↔ is_O f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp hc,
  rw [←is_O_norm_right], simp only [norm_smul],
  rw [is_O_const_mul_right_iff cne0, is_O_norm_right]
end

theorem is_o_const_smul_right {f : α → β} {g : α → γ} {l : filter α} {c : 𝕜} (hc : c ≠ 0) :
  is_o f (λ x, c • g x) l ↔ is_o f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, from mt (norm_eq_zero _).mp hc,
  rw [←is_o_norm_right], simp only [norm_smul],
  rw [is_o_const_mul_right cne0, is_o_norm_right]
end

end

section
variables [normed_field 𝕜] [normed_group β] [normed_space 𝕜 β]
[normed_group γ] [normed_space 𝕜 γ]

set_option class.instance_max_depth 43

theorem is_O_smul {k : α → 𝕜} {f : α → β} {g : α → γ} {l : filter α} (h : is_O f g l) :
  is_O (λ x, k x • f x) (λ x, k x • g x) l :=
begin
  rw [←is_O_norm_left, ←is_O_norm_right], simp only [norm_smul],
  apply is_O_mul (is_O_refl _ _),
  rw [is_O_norm_left, is_O_norm_right],
  exact h
end

theorem is_o_smul {k : α → 𝕜} {f : α → β} {g : α → γ} {l : filter α} (h : is_o f g l) :
  is_o (λ x, k x • f x) (λ x, k x • g x) l :=
begin
  rw [←is_o_norm_left, ←is_o_norm_right], simp only [norm_smul],
  apply is_o_mul_left (is_O_refl _ _),
  rw [is_o_norm_left, is_o_norm_right],
  exact h
end

end

section
variables [normed_field 𝕜]

theorem tendsto_nhds_zero_of_is_o {f g : α → 𝕜} {l : filter α} (h : is_o f g l) :
  tendsto (λ x, f x / (g x)) l (𝓝 0) :=
have eq₁ : is_o (λ x, f x / g x) (λ x, g x / g x) l,
  from is_o_mul_right h (is_O_refl _ _),
have eq₂ : is_O (λ x, g x / g x) (λ x, (1 : 𝕜)) l,
  begin
    use [1, zero_lt_one],
    filter_upwards [univ_mem_sets], simp,
    intro x,
    cases classical.em (∥g x∥ = 0) with h' h'; simp [h'],
    exact zero_le_one
  end,
is_o_one_iff.mp (eq₁.trans_is_O eq₂)

private theorem is_o_of_tendsto {f g : α → 𝕜} {l : filter α}
    (hgf : ∀ x, g x = 0 → f x = 0) (h : tendsto (λ x, f x / (g x)) l (𝓝 0)) :
  is_o f g l :=
have eq₁ : is_o (λ x, f x / (g x)) (λ x, (1 : 𝕜)) l,
  from is_o_one_iff.mpr h,
have eq₂ : is_o (λ x, f x / g x * g x) g l,
  by convert is_o_mul_right eq₁ (is_O_refl _ _); simp,
have eq₃ : is_O f (λ x, f x / g x * g x) l,
  begin
    use [1, zero_lt_one],
    refine filter.univ_mem_sets' (assume x, _),
    suffices : ∥f x∥ ≤ ∥f x∥ / ∥g x∥ * ∥g x∥, { simpa },
    by_cases g x = 0,
    { simp only [h, hgf x h, norm_zero, mul_zero] },
    { rw [div_mul_cancel], exact mt (norm_eq_zero _).1 h }
  end,
eq₃.trans_is_o eq₂

theorem is_o_iff_tendsto {f g : α → 𝕜} {l : filter α}
    (hgf : ∀ x, g x = 0 → f x = 0) :
  is_o f g l ↔ tendsto (λ x, f x / (g x)) l (𝓝 0) :=
iff.intro tendsto_nhds_zero_of_is_o (is_o_of_tendsto hgf)

theorem is_o_pow_pow {m n : ℕ} (h : m < n) :
  is_o (λ(x : 𝕜), x^n) (λx, x^m) (𝓝 0) :=
begin
  let p := n - m,
  have p_pos : 0 < p := nat.sub_pos_of_lt h,
  have : n = m + p := (nat.add_sub_cancel' (le_of_lt h)).symm,
  simp [this, pow_add],
  have : (λ(x : 𝕜), x^m) = (λx, x^m * 1), by simp,
  rw this,
  apply is_o_mul_left (is_O_refl _ _) _,
  rw is_o_iff_tendsto,
  { simp only [div_one],
    convert (continuous_pow p).tendsto (0 : 𝕜),
    exact (zero_pow p_pos).symm },
  { simp }
end

theorem is_o_pow_id {n : ℕ} (h : 1 < n) :
  is_o (λ(x : 𝕜), x^n) (λx, x) (𝓝 0) :=
by { convert is_o_pow_pow h, simp }

end

end asymptotics
