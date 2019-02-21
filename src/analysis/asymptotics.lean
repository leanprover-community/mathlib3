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
∃ c, { x | ∥ f x ∥ ≤ c * ∥ g x ∥ } ∈ l.sets

def is_littleo (f : α → β) (g : α → γ) (l : filter α) : Prop :=
∀ c, { x | c * ∥ f x ∥ ≤ ∥ g x ∥ } ∈ l.sets

theorem is_bigo.comp {f : α → β} {g : α → γ} {l : filter α} (hfg : is_bigo f g l)
    {δ : Type*} (k : δ → α) :
  is_bigo (f ∘ k) (g ∘ k) (l.comap k) :=
let ⟨c, hfgc⟩ := hfg in
⟨c, mem_comap_sets.mpr ⟨_, hfgc, set.subset.refl _⟩⟩

theorem is_littleo.comp {f : α → β} {g : α → γ} {l : filter α} (hfg : is_littleo f g l)
    {δ : Type*} (k : δ → α) :
  is_littleo (f ∘ k) (g ∘ k) (l.comap k) :=
λ c, mem_comap_sets.mpr ⟨_, hfg c, set.subset.refl _⟩

theorem is_bigo.mono {f : α → β} {g : α → γ} {l₁ l₂ : filter α} (h : l₁ ≤ l₂)
  (h' : is_bigo f g l₂) : is_bigo f g l₁ :=
let ⟨c, h'c⟩ := h' in ⟨c, h (h'c)⟩

theorem is_littleo.mono {f : α → β} {g : α → γ} {l₁ l₂ : filter α} (h : l₁ ≤ l₂)
  (h' : is_littleo f g l₂) : is_littleo f g l₁ :=
λ c, h (h' c)

theorem is_littleo.to_is_bigo {f : α → β} {g : α → γ} {l : filter α} (hgf : is_littleo f g l) :
  is_bigo f g l :=
by { use 1, convert hgf 1, ext x, rw [one_mul, one_mul] }

end

section

variables [has_norm β] [normed_group γ]

theorem is_bigo_zero {g : α → γ} {l : filter α} :
  is_bigo (λ x, (0 : γ)) g l :=
⟨0, by { filter_upwards [univ_mem_sets], intros x _, simp }⟩

theorem is_littleo_zero {g : α → γ} {l : filter α} :
  is_littleo (λ x, (0 : γ)) g l :=
λ c, by { filter_upwards [univ_mem_sets], intros x _, simp }

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

theorem is_bigo_iff_pos {f : α → β} {g : α → γ} {l : filter α} :
  is_bigo f g l ↔ ∃ c > 0, { x | ∥f x∥ ≤ c * ∥g x∥ } ∈ l.sets :=
suffices is_bigo f g l → ∃ c > 0, { x | ∥f x∥ ≤ c * ∥g x∥ } ∈ l.sets,
  from ⟨this, λ ⟨c, cpos, hc⟩, ⟨c, hc⟩⟩,
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
let ⟨c₁, hc₁⟩ := h₁,
    ⟨c₂, hc₂⟩ := h₂ in
begin
  use c₁ + c₂,
  filter_upwards [hc₁, hc₂],
  intros x hx₁ hx₂,
  show ∥f₁ x + f₂ x∥ ≤ (c₁ + c₂) * ∥g x∥,
  apply le_trans (norm_triangle _ _),
  rw add_mul,
  exact add_le_add hx₁ hx₂
end

theorem is_bigo.sub {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h₁ : is_bigo f₁ g l) (h₂ : is_bigo f₂ g l) :
  is_bigo (λ x, f₁ x - f₂ x) g l :=
h₁.add (is_bigo_neg_left.mpr h₂)

end

section
variables [normed_group β] [normed_group γ]

theorem is_littleo_iff_pos {f : α → β} {g : α → γ} {l : filter α} :
  is_littleo f g l ↔ ∀ c > 0, { x | c * ∥f x∥ ≤ ∥g x∥ } ∈ l.sets :=
suffices (∀ c > 0, { x | c * ∥f x∥ ≤ ∥g x∥ } ∈ l.sets) → is_littleo f g l,
  from ⟨λ h c cpos, h c, this⟩,
assume h c,
or.elim (lt_or_ge 0 c)
  (assume : c > 0, h c this)
  (assume h'c : c ≤ 0,
    begin
      filter_upwards [univ_mem_sets], intros x _,
      show c * ∥f x∥ ≤ ∥g x∥,
      { apply le_trans (mul_le_mul_of_nonpos_left (norm_nonneg _) h'c),
        rw mul_zero, apply norm_nonneg }
    end)

theorem is_littleo.add {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h₁ : is_littleo f₁ g l) (h₂ : is_littleo f₂ g l) :
  is_littleo (f₁ + f₂) g l :=
begin
  rw is_littleo_iff_pos,
  intros c cpos,
  filter_upwards [h₁ (2 * c), h₂ (2 * c)],
  intros x hx₁ hx₂, dsimp at hx₁ hx₂,
  have : 0 < (2 : real), by norm_num,
  apply le_of_mul_le_mul_left _ this, rw ←mul_assoc,
  show 2 * c * ∥f₁ x + f₂ x∥ ≤ 2 * ∥g x∥,
  { transitivity 2 * c * (∥f₁ x∥ + ∥f₂ x∥),
    apply (mul_le_mul_of_nonneg_left (norm_triangle _ _) (le_of_lt (mul_pos this cpos))),
    rw [mul_add, mul_comm _ ∥g x∥, mul_two ∥g x∥],
    exact add_le_add hx₁ hx₂}
end

theorem is_littleo.sub {f₁ f₂ : α → β} {g : α → γ} {l : filter α}
    (h₁ : is_littleo f₁ g l) (h₂ : is_littleo f₂ g l) :
  is_littleo (λ x, f₁ x - f₂ x) g l :=
h₁.add (is_littleo_neg_left.mpr h₂)

end

section
variables [normed_field β] [has_norm γ]

theorem is_bigo_mul_left {f : α → β} {g : α → γ} {l : filter α} {c : β} (hc : c ≠ 0) :
  is_bigo (λ x, c * f x) g l ↔ is_bigo f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, by rw [ne, norm_eq_zero]; exact hc,
  have cpos : ∥c∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm cne0),
  split,
  { rintro ⟨c', h'⟩,
    use (∥c∥⁻¹ * c'),
    convert h', ext x, dsimp,
    rw [normed_field.norm_mul, mul_assoc, mul_comm, mul_comm ∥c∥],
    apply le_div_iff cpos },
  rintro ⟨c', h'⟩,
  use (∥c∥ * c'),
  filter_upwards [h'], dsimp,
  intros x h₀,
  rw [normed_field.norm_mul, mul_assoc],
  exact mul_le_mul_of_nonneg_left h₀ (norm_nonneg _)
end

theorem is_littleo_mul_left {f : α → β} {g : α → γ} {l : filter α} {c : β} (hc : c ≠ 0) :
  is_littleo (λ x, c * f x) g l ↔ is_littleo f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, by rw [ne, norm_eq_zero]; exact hc,
  have cpos : ∥c∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm cne0),
  split,
  { intros h' c',
    convert h' (c' * ∥c∥⁻¹), ext x, dsimp,
    rw [normed_field.norm_mul, mul_assoc, ←mul_assoc ∥c∥⁻¹, inv_mul_cancel cne0, one_mul] },
  intros h' c',
  convert h' (c' * ∥c∥), ext x, dsimp,
  rw [normed_field.norm_mul, mul_assoc]
end

end

section
variables [has_norm β] [normed_field γ]

theorem is_bigo_mul_right {f : α → β} {g : α → γ} {l : filter α} {c : γ} (hc : c ≠ 0) :
  is_bigo f (λ x, c * g x) l ↔ is_bigo f g l :=
begin
  split,
  { rintro ⟨c', h'⟩,
    use (c' * ∥c∥),
    convert h', ext x, dsimp,
    rw [normed_field.norm_mul, mul_assoc] },
  have cne0 : ∥c∥ ≠ 0, by rw [ne, norm_eq_zero]; exact hc,
  rintro ⟨c', h'⟩,
  use (c' * ∥c∥⁻¹),
  convert h', ext x, dsimp,
  rw [normed_field.norm_mul, mul_assoc, ←mul_assoc ∥c∥⁻¹, inv_mul_cancel cne0, one_mul]
end

theorem is_littleo_mul_right {f : α → β} {g : α → γ} {l : filter α} {c : γ} (hc : c ≠ 0) :
  is_littleo f (λ x, c * g x) l ↔ is_littleo f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, by rw [ne, norm_eq_zero]; exact hc,
  have cpos : ∥c∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm cne0),
  split,
  { intros h' c',
    filter_upwards [h' (∥c∥ * c')], dsimp,
    intro x, rw [normed_field.norm_mul, mul_assoc],
    intro h₀, exact le_of_mul_le_mul_left h₀ cpos },
  intros h' c',
  convert h' (∥c∥⁻¹ * c'), ext x, dsimp,
  symmetry,
  rw [normed_field.norm_mul, mul_assoc, mul_comm],
  apply div_le_iff' cpos
end

end

/-
Note: the method in the next two sections can be used for the integers, or more generally any normed
ring satisfying `∥a * b∥ = ∥a∥ * ∥b∥`. It is not clear whether it is worth stating it in that
generality.
-/

section
variables {k : Type*} [normed_field k] [normed_space k β] [has_norm γ]

theorem is_bigo_smul_left {f : α → β} {g : α → γ} {l : filter α} {c : k} (hc : c ≠ 0) :
  is_bigo (λ x, c • f x) g l ↔ is_bigo f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, by rw [ne, norm_eq_zero]; exact hc,
  rw [←is_bigo_norm_left], simp only [norm_smul],
  rw [is_bigo_mul_left cne0, is_bigo_norm_left]
end

theorem is_littleo_smul_left {f : α → β} {g : α → γ} {l : filter α} {c : k} (hc : c ≠ 0) :
  is_littleo (λ x, c • f x) g l ↔ is_littleo f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, by rw [ne, norm_eq_zero]; exact hc,
  rw [←is_littleo_norm_left], simp only [norm_smul],
  rw [is_littleo_mul_left cne0, is_littleo_norm_left]
end

end

section
variables {k : Type*} [has_norm β] [normed_field k] [normed_space k γ]

theorem is_bigo_smul_right {f : α → β} {g : α → γ} {l : filter α} {c : k} (hc : c ≠ 0) :
  is_bigo f (λ x, c • g x) l ↔ is_bigo f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, by rw [ne, norm_eq_zero]; exact hc,
  rw [←is_bigo_norm_right], simp only [norm_smul],
  rw [is_bigo_mul_right cne0, is_bigo_norm_right]
end

theorem is_littleo_smul_right {f : α → β} {g : α → γ} {l : filter α} {c : k} (hc : c ≠ 0) :
  is_littleo f (λ x, c • g x) l ↔ is_littleo f g l :=
begin
  have cne0 : ∥c∥ ≠ 0, by rw [ne, norm_eq_zero]; exact hc,
  rw [←is_littleo_norm_right], simp only [norm_smul],
  rw [is_littleo_mul_right cne0, is_littleo_norm_right]
end

end

/-
"transitivity" rules
-/

theorem is_bigo_of_is_bigo_of_is_bigo [has_norm β] [normed_group γ] [has_norm δ]
      {f : α → β} {g : α → γ} {k : α → δ} {l : filter α}
    (h₁ : is_bigo f g l)
    (h₂ : is_bigo g k l) :
  is_bigo f k l :=
let ⟨c, cpos, hc⟩ := is_bigo_iff_pos.mp h₁,
    ⟨c', hc'⟩     := h₂ in
begin
  use c * c',
  filter_upwards [hc, hc'], dsimp,
  intros x h₁x h₂x, rw mul_assoc,
  exact le_trans h₁x (mul_le_mul_of_nonneg_left h₂x (le_of_lt cpos))
end

theorem is_littleo_of_is_littleo_of_is_bigo [has_norm β] [has_norm γ] [normed_group δ]
      {f : α → β} {g : α → γ} {k : α → δ} {l : filter α}
    (h₁ : is_littleo f g l)
    (h₂ : is_bigo g k l) :
  is_littleo f k l :=
λ c,
let ⟨c', c'pos, hc'⟩ := is_bigo_iff_pos.mp h₂ in
mem_sets_of_superset (inter_mem_sets hc' (h₁ (c * c'))) $
assume x,
assume : ∥g x∥ ≤ c' * ∥k x∥ ∧ c * c' * ∥f x∥ ≤ ∥g x∥,
have c' * (c * ∥f x∥) ≤ c' * ∥k x∥,
  by rw [←mul_assoc, mul_comm c']; exact le_trans this.right this.left,
show c * ∥f x∥ ≤ ∥k x∥, from le_of_mul_le_mul_left this c'pos

theorem is_littleo_of_is_bigo_of_is_littleo [normed_group β] [has_norm γ] [normed_group δ]
      {f : α → β} {g : α → γ} {k : α → δ} {l : filter α}
    (h₁ : is_bigo f g l)
    (h₂ : is_littleo g k l) :
  is_littleo f k l :=
is_littleo_iff_pos.mpr $
λ c cpos,
let ⟨c', hc'⟩ := h₁ in
begin
  filter_upwards [hc', h₂ (c * c')], dsimp,
  intro x, rw [mul_assoc], intros h₃ h₄,
  show c * ∥f x∥ ≤ ∥k x∥,
  exact le_trans (mul_le_mul_of_nonneg_left h₃ (le_of_lt cpos)) h₄
end

/-
littleo and tendsto in a normed field
-/

theorem tendsto_nhds_zero_of_is_littleo [normed_field β] {f g : α → β} {l : filter α}
    (h : is_littleo f g l) :
  tendsto (λ x, f x / (g x)) l (nhds 0) :=
begin
  rw normed_space.tendsto_nhds_zero,
  intros ε hε,
  show {x : α | ∥f x / (g x)∥ < ε} ∈ l.sets,
  apply mem_sets_of_superset (h (ε⁻¹ + 1)),
  intro x, dsimp, intro hx,
  rw [division_def, normed_field.norm_mul, norm_inv],
  show ∥f x∥ * ∥g x∥⁻¹ < ε,
  cases classical.em (∥g x∥ = 0) with h gne0,
  { rw [h, inv_zero, mul_zero], exact hε },
  cases classical.em (∥f x∥ = 0) with h fne0,
  { rw [h, zero_mul], exact hε },
  have fnpos : ∥f x∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm fne0),
  have gnpos : ∥g x∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm gne0),
  have enlt : ε⁻¹ < ε⁻¹ + 1, from lt_add_of_pos_right _ zero_lt_one,
  rw [←division_def, div_lt_iff gnpos, mul_comm, ←div_lt_iff hε, division_def, mul_comm],
  show ε⁻¹ * ∥f x∥ < ∥g x∥, from calc
    ε⁻¹ * ∥f x∥ < (ε⁻¹ + 1) * ∥f x∥ : by rw (mul_lt_mul_right fnpos); exact enlt
            ... ≤ ∥g x∥             : hx
end

theorem is_littleo_of_tendsto [normed_field β] {f g : α → β} {l : filter α}
    (hgf : ∀ x, g x = 0 → f x = 0) (h : tendsto (λ x, f x / (g x)) l (nhds 0)) :
  is_littleo f g l :=
begin
  rw normed_space.tendsto_nhds_zero at h,
  rw is_littleo_iff_pos,
  intros c cpos,
  show {x : α | c * ∥f x∥ ≤ ∥g x∥} ∈ l.sets,
  apply mem_sets_of_superset (h c⁻¹ (inv_pos cpos)),
  intro x,
  intro hx,
  change ∥f x * (g x)⁻¹∥ < c⁻¹ at hx,
  show c * ∥f x∥ ≤ ∥g x∥,
  cases classical.em (∥g x∥ = 0) with h gne0,
  { have : g x = 0, from (norm_eq_zero (g x)).mp h,
    rw [hgf _ this, norm_zero, mul_zero], exact norm_nonneg _ },
  have gnpos : ∥g x∥ > 0, from lt_of_le_of_ne (norm_nonneg _) (ne.symm gne0),
  show c * ∥f x∥ ≤ ∥g x∥,
  rw [mul_comm, ←le_div_iff cpos, division_def, mul_comm],
  rw [normed_field.norm_mul, norm_inv, ←division_def, div_lt_iff gnpos] at hx,
  exact le_of_lt hx
end

theorem is_littleo_iff_tendsto [normed_field β] {f g : α → β} {l : filter α}
    (hgf : ∀ x, g x = 0 → f x = 0) :
  is_littleo f g l ↔ tendsto (λ x, f x / (g x)) l (nhds 0) :=
iff.intro tendsto_nhds_zero_of_is_littleo (is_littleo_of_tendsto hgf)

end asymptotics
