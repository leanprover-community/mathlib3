/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
import analysis.normed.group.infinite_sum
import analysis.normed_space.basic
import topology.algebra.order.liminf_limsup
import topology.local_homeomorph

/-!
# Asymptotics

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We introduce these relations:

* `is_O_with c l f g` : "f is big O of g along l with constant c";
* `f =O[l] g` : "f is big O of g along l";
* `f =o[l] g` : "f is little o of g along l".

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed that there is a norm associated with
these types, and it is the norm that is compared asymptotically.

The relation `is_O_with c` is introduced to factor out common algebraic arguments in the proofs of
similar properties of `is_O` and `is_o`. Usually proofs outside of this file should use `is_O`
instead.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `f =O[l] g ↔ (λ x, ‖f x‖) =O[l] (λ x, ‖g x‖)`,

and similarly for `is_o`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `f =o[l] g ↔ tendsto (λ x, f x / (g x)) l (𝓝 0)`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)
-/

open filter set
open_locale topology big_operators classical filter nnreal

namespace asymptotics

variables {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*}
  {E' : Type*} {F' : Type*} {G' : Type*}
  {E'' : Type*} {F'' : Type*} {G'' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variables [has_norm E] [has_norm F] [has_norm G]
variables [seminormed_add_comm_group E'] [seminormed_add_comm_group F']
  [seminormed_add_comm_group G'] [normed_add_comm_group E''] [normed_add_comm_group F'']
  [normed_add_comm_group G''] [semi_normed_ring R] [semi_normed_ring R']
variables [normed_field 𝕜] [normed_field 𝕜']
variables {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}
variables {f' : α → E'} {g' : α → F'} {k' : α → G'}
variables {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}
variables {l l' : filter α}

section defs

/-! ### Definitions -/

/-- This version of the Landau notation `is_O_with C l f g` where `f` and `g` are two functions on
a type `α` and `l` is a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by `C * ‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded by `C`, modulo division by zero issues that are
avoided by this definition. Probably you want to use `is_O` instead of this relation. -/
@[irreducible]
def is_O_with (c : ℝ) (l : filter α) (f : α → E) (g : α → F) : Prop :=
∀ᶠ x in l, ‖ f x ‖ ≤ c * ‖ g x ‖

/-- Definition of `is_O_with`. We record it in a lemma as `is_O_with` is irreducible. -/
lemma is_O_with_iff : is_O_with c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := by rw is_O_with

alias is_O_with_iff ↔ is_O_with.bound is_O_with.of_bound

/-- The Landau notation `f =O[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by a constant multiple of `‖g‖`.
In other words, `‖f‖ / ‖g‖` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
@[irreducible]
def is_O (l : filter α) (f : α → E) (g : α → F) : Prop := ∃ c : ℝ, is_O_with c l f g

notation f ` =O[`:100 l `] ` g:100 := is_O l f g

/-- Definition of `is_O` in terms of `is_O_with`. We record it in a lemma as `is_O` is
irreducible. -/
lemma is_O_iff_is_O_with : f =O[l] g ↔ ∃ c : ℝ, is_O_with c l f g := by rw is_O

/-- Definition of `is_O` in terms of filters. We record it in a lemma as we will set
`is_O` to be irreducible at the end of this file. -/
lemma is_O_iff : f =O[l] g ↔ ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
by simp only [is_O, is_O_with]

lemma is_O.of_bound (c : ℝ) (h : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
is_O_iff.2 ⟨c, h⟩

lemma is_O.of_bound' (h : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
is_O.of_bound 1 $ by { simp_rw one_mul, exact h }

lemma is_O.bound : f =O[l] g → ∃ c : ℝ, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ := is_O_iff.1

/-- The Landau notation `f =o[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `‖f‖` is bounded by an arbitrarily small constant
multiple of `‖g‖`. In other words, `‖f‖ / ‖g‖` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
@[irreducible]
def is_o (l : filter α) (f : α → E) (g : α → F) : Prop := ∀ ⦃c : ℝ⦄, 0 < c → is_O_with c l f g

notation f ` =o[`:100 l `] ` g:100 := is_o l f g

/-- Definition of `is_o` in terms of `is_O_with`. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
lemma is_o_iff_forall_is_O_with : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → is_O_with c l f g := by rw is_o

alias is_o_iff_forall_is_O_with ↔ is_o.forall_is_O_with is_o.of_is_O_with

/-- Definition of `is_o` in terms of filters. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
lemma is_o_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
by simp only [is_o, is_O_with]

alias is_o_iff ↔ is_o.bound is_o.of_bound

lemma is_o.def (h : f =o[l] g) (hc : 0 < c) : ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
is_o_iff.1 h hc

lemma is_o.def' (h : f =o[l] g) (hc : 0 < c) : is_O_with c l f g :=
is_O_with_iff.2 $ is_o_iff.1 h hc

end defs

/-! ### Conversions -/

theorem is_O_with.is_O (h : is_O_with c l f g) : f =O[l] g := by rw is_O; exact ⟨c, h⟩

theorem is_o.is_O_with (hgf : f =o[l] g) : is_O_with 1 l f g := hgf.def' zero_lt_one

theorem is_o.is_O (hgf : f =o[l] g) : f =O[l] g := hgf.is_O_with.is_O

lemma is_O.is_O_with : f =O[l] g → ∃ c : ℝ, is_O_with c l f g := is_O_iff_is_O_with.1

theorem is_O_with.weaken (h : is_O_with c l f g') (hc : c ≤ c') : is_O_with c' l f g' :=
is_O_with.of_bound $ mem_of_superset h.bound $ λ x hx,
calc ‖f x‖ ≤ c * ‖g' x‖ : hx
... ≤ _ : mul_le_mul_of_nonneg_right hc (norm_nonneg _)

theorem is_O_with.exists_pos (h : is_O_with c l f g') :
  ∃ c' (H : 0 < c'), is_O_with c' l f g' :=
⟨max c 1, lt_of_lt_of_le zero_lt_one (le_max_right c 1), h.weaken $ le_max_left c 1⟩

theorem is_O.exists_pos (h : f =O[l] g') : ∃ c (H : 0 < c), is_O_with c l f g' :=
let ⟨c, hc⟩ := h.is_O_with in hc.exists_pos

theorem is_O_with.exists_nonneg (h : is_O_with c l f g') :
  ∃ c' (H : 0 ≤ c'), is_O_with c' l f g' :=
let ⟨c, cpos, hc⟩ := h.exists_pos in ⟨c, le_of_lt cpos, hc⟩

theorem is_O.exists_nonneg (h : f =O[l] g') :
  ∃ c (H : 0 ≤ c), is_O_with c l f g' :=
let ⟨c, hc⟩ := h.is_O_with in hc.exists_nonneg

/-- `f = O(g)` if and only if `is_O_with c f g` for all sufficiently large `c`. -/
lemma is_O_iff_eventually_is_O_with : f =O[l] g' ↔ ∀ᶠ c in at_top, is_O_with c l f g' :=
is_O_iff_is_O_with.trans
  ⟨λ ⟨c, hc⟩, mem_at_top_sets.2 ⟨c, λ c' hc', hc.weaken hc'⟩, λ h, h.exists⟩

/-- `f = O(g)` if and only if `∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖` for all sufficiently large `c`. -/
lemma is_O_iff_eventually : f =O[l] g' ↔ ∀ᶠ c in at_top, ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g' x‖ :=
is_O_iff_eventually_is_O_with.trans $ by simp only [is_O_with]

lemma is_O.exists_mem_basis {ι} {p : ι → Prop} {s : ι → set α} (h : f =O[l] g')
  (hb : l.has_basis p s) :
  ∃ (c : ℝ) (hc : 0 < c) (i : ι) (hi : p i), ∀ x ∈ s i, ‖f x‖ ≤ c * ‖g' x‖ :=
flip Exists₂.imp h.exists_pos $ λ c hc h,
  by simpa only [is_O_with_iff, hb.eventually_iff, exists_prop] using h

lemma is_O_with_inv (hc : 0 < c) : is_O_with c⁻¹ l f g ↔ ∀ᶠ x in l, c * ‖f x‖ ≤ ‖g x‖ :=
by simp only [is_O_with, ← div_eq_inv_mul, le_div_iff' hc]

-- We prove this lemma with strange assumptions to get two lemmas below automatically
lemma is_o_iff_nat_mul_le_aux (h₀ : (∀ x, 0 ≤ ‖f x‖) ∨ ∀ x, 0 ≤ ‖g x‖) :
  f =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g x‖ :=
begin
  split,
  { rintro H (_|n),
    { refine (H.def one_pos).mono (λ x h₀', _),
      rw [nat.cast_zero, zero_mul],
      refine h₀.elim (λ hf, (hf x).trans _) (λ hg, hg x),
      rwa one_mul at h₀' },
    { have : (0 : ℝ) < n.succ, from nat.cast_pos.2 n.succ_pos,
      exact (is_O_with_inv this).1 (H.def' $ inv_pos.2 this) } },
  { refine λ H, is_o_iff.2 (λ ε ε0, _),
    rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩,
    have hn₀ : (0 : ℝ) < n, from (inv_pos.2 ε0).trans hn,
    refine ((is_O_with_inv hn₀).2 (H n)).bound.mono (λ x hfg, _),
    refine hfg.trans (mul_le_mul_of_nonneg_right (inv_le_of_inv_le ε0 hn.le) _),
    refine h₀.elim (λ hf, nonneg_of_mul_nonneg_right ((hf x).trans hfg) _) (λ h, h x),
    exact inv_pos.2 hn₀ }
end

lemma is_o_iff_nat_mul_le : f =o[l] g' ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f x‖ ≤ ‖g' x‖ :=
is_o_iff_nat_mul_le_aux (or.inr $ λ x, norm_nonneg _)

lemma is_o_iff_nat_mul_le' : f' =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖f' x‖ ≤ ‖g x‖ :=
is_o_iff_nat_mul_le_aux (or.inl $ λ x, norm_nonneg _)

/-! ### Subsingleton -/

@[nontriviality] lemma is_o_of_subsingleton [subsingleton E'] : f' =o[l] g' :=
is_o.of_bound $ λ c hc, by simp [subsingleton.elim (f' _) 0, mul_nonneg hc.le]

@[nontriviality] lemma is_O_of_subsingleton [subsingleton E'] : f' =O[l] g' :=
is_o_of_subsingleton.is_O

section congr

variables {f₁ f₂ : α → E} {g₁ g₂ : α → F}

/-! ### Congruence -/

theorem is_O_with_congr (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
  is_O_with c₁ l f₁ g₁ ↔ is_O_with c₂ l f₂ g₂ :=
begin
  unfold is_O_with,
  subst c₂,
  apply filter.eventually_congr,
  filter_upwards [hf, hg] with _ e₁ e₂,
  rw [e₁, e₂],
end

theorem is_O_with.congr' (h : is_O_with c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂)
  (hg : g₁ =ᶠ[l] g₂) : is_O_with c₂ l f₂ g₂ :=
(is_O_with_congr hc hf hg).mp h

theorem is_O_with.congr (h : is_O_with c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : ∀ x, f₁ x = f₂ x)
  (hg : ∀ x, g₁ x = g₂ x) : is_O_with c₂ l f₂ g₂ :=
h.congr' hc (univ_mem' hf) (univ_mem' hg)

theorem is_O_with.congr_left (h : is_O_with c l f₁ g) (hf : ∀ x, f₁ x = f₂ x) :
  is_O_with c l f₂ g :=
h.congr rfl hf (λ _, rfl)

theorem is_O_with.congr_right (h : is_O_with c l f g₁) (hg : ∀ x, g₁ x = g₂ x) :
  is_O_with c l f g₂ :=
h.congr rfl (λ _, rfl) hg

theorem is_O_with.congr_const (h : is_O_with c₁ l f g) (hc : c₁ = c₂) : is_O_with c₂ l f g :=
h.congr hc (λ _, rfl) (λ _, rfl)

theorem is_O_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l] g₂ :=
by { unfold is_O, exact exists_congr (λ c, is_O_with_congr rfl hf hg) }

theorem is_O.congr' (h : f₁ =O[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =O[l] g₂ :=
(is_O_congr hf hg).mp h

theorem is_O.congr (h : f₁ =O[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
  f₂ =O[l] g₂ :=
h.congr' (univ_mem' hf) (univ_mem' hg)

theorem is_O.congr_left (h : f₁ =O[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =O[l] g :=
h.congr hf (λ _, rfl)

theorem is_O.congr_right (h : f =O[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =O[l] g₂ :=
h.congr (λ _, rfl) hg

theorem is_o_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂ :=
by { unfold is_o, exact forall₂_congr (λ c hc, is_O_with_congr (eq.refl c) hf hg) }

theorem is_o.congr' (h : f₁ =o[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =o[l] g₂ :=
(is_o_congr hf hg).mp h

theorem is_o.congr (h : f₁ =o[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
  f₂ =o[l] g₂ :=
h.congr' (univ_mem' hf) (univ_mem' hg)

theorem is_o.congr_left (h : f₁ =o[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =o[l] g :=
h.congr hf (λ _, rfl)

theorem is_o.congr_right (h : f =o[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =o[l] g₂ :=
h.congr (λ _, rfl) hg

@[trans] theorem _root_.filter.eventually_eq.trans_is_O {f₁ f₂ : α → E} {g : α → F}
  (hf : f₁ =ᶠ[l] f₂) (h : f₂ =O[l] g) : f₁ =O[l] g :=
h.congr' hf.symm eventually_eq.rfl

@[trans] theorem _root_.filter.eventually_eq.trans_is_o {f₁ f₂ : α → E} {g : α → F}
  (hf : f₁ =ᶠ[l] f₂) (h : f₂ =o[l] g) : f₁ =o[l] g :=
h.congr' hf.symm eventually_eq.rfl

@[trans] theorem is_O.trans_eventually_eq {f : α → E} {g₁ g₂ : α → F}
  (h : f =O[l] g₁) (hg : g₁ =ᶠ[l] g₂) : f =O[l] g₂ :=
h.congr' eventually_eq.rfl hg

@[trans] theorem is_o.trans_eventually_eq {f : α → E} {g₁ g₂ : α → F}
  (h : f =o[l] g₁) (hg : g₁ =ᶠ[l] g₂) : f =o[l] g₂ :=
h.congr' eventually_eq.rfl hg

end congr

/-! ### Filter operations and transitivity -/

theorem is_O_with.comp_tendsto (hcfg : is_O_with c l f g)
  {k : β → α} {l' : filter β} (hk : tendsto k l' l):
  is_O_with c l' (f ∘ k) (g ∘ k) :=
is_O_with.of_bound $ hk hcfg.bound

theorem is_O.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : filter β} (hk : tendsto k l' l) :
  (f ∘ k) =O[l'] (g ∘ k) :=
is_O_iff_is_O_with.2 $ hfg.is_O_with.imp (λ c h, h.comp_tendsto hk)

theorem is_o.comp_tendsto (hfg : f =o[l] g) {k : β → α} {l' : filter β} (hk : tendsto k l' l) :
  (f ∘ k) =o[l'] (g ∘ k) :=
is_o.of_is_O_with $ λ c cpos, (hfg.forall_is_O_with cpos).comp_tendsto hk

@[simp] theorem is_O_with_map {k : β → α} {l : filter β} :
  is_O_with c (map k l) f g ↔ is_O_with c l (f ∘ k) (g ∘ k) :=
by { unfold is_O_with, exact eventually_map }

@[simp] theorem is_O_map {k : β → α} {l : filter β} : f =O[map k l] g ↔ (f ∘ k) =O[l] (g ∘ k) :=
by simp only [is_O, is_O_with_map]

@[simp] theorem is_o_map {k : β → α} {l : filter β} : f =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k) :=
by simp only [is_o, is_O_with_map]

theorem is_O_with.mono (h : is_O_with c l' f g) (hl : l ≤ l') : is_O_with c l f g :=
is_O_with.of_bound $ hl h.bound

theorem is_O.mono (h : f =O[l'] g) (hl : l ≤ l') : f =O[l] g :=
is_O_iff_is_O_with.2 $ h.is_O_with.imp (λ c h, h.mono hl)

theorem is_o.mono (h : f =o[l'] g) (hl : l ≤ l') : f =o[l] g :=
is_o.of_is_O_with $ λ c cpos, (h.forall_is_O_with cpos).mono hl

theorem is_O_with.trans (hfg : is_O_with c l f g) (hgk : is_O_with c' l g k) (hc : 0 ≤ c) :
  is_O_with (c * c') l f k :=
begin
  unfold is_O_with at *,
  filter_upwards [hfg, hgk] with x hx hx',
  calc ‖f x‖ ≤ c * ‖g x‖ : hx
  ... ≤ c * (c' * ‖k x‖) : mul_le_mul_of_nonneg_left hx' hc
  ... = c * c' * ‖k x‖ : (mul_assoc _ _ _).symm
end

@[trans] theorem is_O.trans {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g)
  (hgk : g =O[l] k) : f =O[l] k :=
let ⟨c, cnonneg, hc⟩ := hfg.exists_nonneg, ⟨c', hc'⟩ := hgk.is_O_with in
(hc.trans hc' cnonneg).is_O

theorem is_o.trans_is_O_with (hfg : f =o[l] g) (hgk : is_O_with c l g k) (hc : 0 < c) :
  f =o[l] k :=
begin
  unfold is_o at *,
  intros c' c'pos,
  have : 0 < c' / c, from div_pos c'pos hc,
  exact ((hfg this).trans hgk this.le).congr_const (div_mul_cancel _ hc.ne')
end

@[trans] theorem is_o.trans_is_O {f : α → E} {g : α → F} {k : α → G'} (hfg : f =o[l] g)
  (hgk : g =O[l] k) :
  f =o[l] k :=
let ⟨c, cpos, hc⟩ := hgk.exists_pos in hfg.trans_is_O_with hc cpos

theorem is_O_with.trans_is_o (hfg : is_O_with c l f g) (hgk : g =o[l] k) (hc : 0 < c) :
  f =o[l] k :=
begin
  unfold is_o at *,
  intros c' c'pos,
  have : 0 < c' / c, from div_pos c'pos hc,
  exact (hfg.trans (hgk this) hc.le).congr_const (mul_div_cancel' _ hc.ne')
end

@[trans] theorem is_O.trans_is_o {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g)
  (hgk : g =o[l] k) :
  f =o[l] k :=
let ⟨c, cpos, hc⟩ := hfg.exists_pos in hc.trans_is_o hgk cpos

@[trans] theorem is_o.trans {f : α → E} {g : α → F} {k : α → G} (hfg : f =o[l] g)
  (hgk : g =o[l] k) : f =o[l] k :=
hfg.trans_is_O_with hgk.is_O_with one_pos

lemma _root_.filter.eventually.trans_is_O {f : α → E} {g : α → F'} {k : α → G}
  (hfg : ∀ᶠ x in l, ‖f x‖ ≤ ‖g x‖) (hgk : g =O[l] k) : f =O[l] k :=
(is_O.of_bound' hfg).trans hgk

lemma _root_.filter.eventually.is_O {f : α → E} {g : α → ℝ} {l : filter α}
  (hfg : ∀ᶠ x in l, ‖f x‖ ≤ g x) : f =O[l] g :=
is_O.of_bound' $ hfg.mono $ λ x hx, hx.trans $ real.le_norm_self _

section

variable (l)

theorem is_O_with_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : is_O_with c l f g :=
is_O_with.of_bound $ univ_mem' hfg

theorem is_O_with_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : is_O_with 1 l f g :=
is_O_with_of_le' l $ λ x, by { rw one_mul, exact hfg x }

theorem is_O_of_le' (hfg : ∀ x, ‖f x‖ ≤ c * ‖g x‖) : f =O[l] g :=
(is_O_with_of_le' l hfg).is_O

theorem is_O_of_le (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖) : f =O[l] g :=
(is_O_with_of_le l hfg).is_O

end

theorem is_O_with_refl (f : α → E) (l : filter α) : is_O_with 1 l f f :=
is_O_with_of_le l $ λ _, le_rfl

theorem is_O_refl (f : α → E) (l : filter α) : f =O[l] f := (is_O_with_refl f l).is_O

theorem is_O_with.trans_le (hfg : is_O_with c l f g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) (hc : 0 ≤ c) :
  is_O_with c l f k :=
(hfg.trans (is_O_with_of_le l hgk) hc).congr_const $ mul_one c

theorem is_O.trans_le (hfg : f =O[l] g') (hgk : ∀ x, ‖g' x‖ ≤ ‖k x‖) : f =O[l] k :=
hfg.trans (is_O_of_le l hgk)

theorem is_o.trans_le (hfg : f =o[l] g) (hgk : ∀ x, ‖g x‖ ≤ ‖k x‖) : f =o[l] k :=
hfg.trans_is_O_with (is_O_with_of_le _ hgk) zero_lt_one

theorem is_o_irrefl' (h : ∃ᶠ x in l, ‖f' x‖ ≠ 0) : ¬f' =o[l] f' :=
begin
  intro ho,
  rcases ((ho.bound one_half_pos).and_frequently h).exists with ⟨x, hle, hne⟩,
  rw [one_div, ← div_eq_inv_mul] at hle,
  exact (half_lt_self (lt_of_le_of_ne (norm_nonneg _) hne.symm)).not_le hle
end

theorem is_o_irrefl (h : ∃ᶠ x in l, f'' x ≠ 0) : ¬f'' =o[l] f'' :=
is_o_irrefl' $ h.mono $ λ x, norm_ne_zero_iff.mpr

theorem is_O.not_is_o (h : f'' =O[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) : ¬g' =o[l] f'' :=
λ h', is_o_irrefl hf (h.trans_is_o h')

theorem is_o.not_is_O (h : f'' =o[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) : ¬g' =O[l] f'' :=
λ h', is_o_irrefl hf (h.trans_is_O h')

section bot

variables (c f g)

@[simp] theorem is_O_with_bot : is_O_with c ⊥ f g := is_O_with.of_bound $ trivial

@[simp] theorem is_O_bot : f =O[⊥] g := (is_O_with_bot 1 f g).is_O

@[simp] theorem is_o_bot : f =o[⊥] g := is_o.of_is_O_with $ λ c _, is_O_with_bot c f g

end bot

@[simp] theorem is_O_with_pure {x} : is_O_with c (pure x) f g ↔ ‖f x‖ ≤ c * ‖g x‖ := is_O_with_iff

theorem is_O_with.sup (h : is_O_with c l f g) (h' : is_O_with c l' f g) :
  is_O_with c (l ⊔ l') f g :=
is_O_with.of_bound $ mem_sup.2 ⟨h.bound, h'.bound⟩

theorem is_O_with.sup' (h : is_O_with c l f g') (h' : is_O_with c' l' f g') :
  is_O_with (max c c') (l ⊔ l') f g' :=
is_O_with.of_bound $
mem_sup.2 ⟨(h.weaken $ le_max_left c c').bound, (h'.weaken $ le_max_right c c').bound⟩

theorem is_O.sup (h : f =O[l] g') (h' : f =O[l'] g') : f =O[l ⊔ l'] g' :=
let ⟨c, hc⟩ := h.is_O_with, ⟨c', hc'⟩ := h'.is_O_with in (hc.sup' hc').is_O

theorem is_o.sup (h : f =o[l] g) (h' : f =o[l'] g) : f =o[l ⊔ l'] g :=
is_o.of_is_O_with $ λ c cpos, (h.forall_is_O_with cpos).sup (h'.forall_is_O_with cpos)

@[simp] lemma is_O_sup : f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O[l'] g' :=
⟨λ h, ⟨h.mono le_sup_left, h.mono le_sup_right⟩, λ h, h.1.sup h.2⟩

@[simp] lemma is_o_sup : f =o[l ⊔ l'] g ↔ f =o[l] g ∧ f =o[l'] g :=
⟨λ h, ⟨h.mono le_sup_left, h.mono le_sup_right⟩, λ h, h.1.sup h.2⟩

lemma is_O_with_insert [topological_space α] {x : α} {s : set α} {C : ℝ} {g : α → E} {g' : α → F}
  (h : ‖g x‖ ≤ C * ‖g' x‖) :
  is_O_with C (𝓝[insert x s] x) g g' ↔ is_O_with C (𝓝[s] x) g g' :=
by simp_rw [is_O_with, nhds_within_insert, eventually_sup, eventually_pure, h, true_and]

lemma is_O_with.insert [topological_space α] {x : α} {s : set α} {C : ℝ} {g : α → E} {g' : α → F}
  (h1 : is_O_with C (𝓝[s] x) g g') (h2 : ‖g x‖ ≤ C * ‖g' x‖) :
  is_O_with C (𝓝[insert x s] x) g g' :=
(is_O_with_insert h2).mpr h1

lemma is_o_insert [topological_space α] {x : α} {s : set α} {g : α → E'} {g' : α → F'}
  (h : g x = 0) : g =o[𝓝[insert x s] x] g' ↔ g =o[𝓝[s] x] g' :=
begin
  simp_rw [is_o],
  refine forall_congr (λ c, forall_congr (λ hc, _)),
  rw [is_O_with_insert],
  rw [h, norm_zero],
  exact mul_nonneg hc.le (norm_nonneg _)
end

lemma is_o.insert [topological_space α] {x : α} {s : set α} {g : α → E'} {g' : α → F'}
  (h1 : g =o[𝓝[s] x] g') (h2 : g x = 0) : g =o[𝓝[insert x s] x] g' :=
(is_o_insert h2).mpr h1

/-! ### Simplification : norm, abs -/

section norm_abs

variables {u v : α → ℝ}

@[simp] theorem is_O_with_norm_right : is_O_with c l f (λ x, ‖g' x‖) ↔ is_O_with c l f g' :=
by simp only [is_O_with, norm_norm]

@[simp] theorem is_O_with_abs_right : is_O_with c l f (λ x, |u x|) ↔ is_O_with c l f u :=
@is_O_with_norm_right _ _ _ _ _ _ f u l

alias is_O_with_norm_right ↔ is_O_with.of_norm_right is_O_with.norm_right
alias is_O_with_abs_right ↔ is_O_with.of_abs_right is_O_with.abs_right

@[simp] theorem is_O_norm_right : f =O[l] (λ x, ‖g' x‖) ↔ f =O[l] g' :=
by { unfold is_O, exact exists_congr (λ _, is_O_with_norm_right) }

@[simp] theorem is_O_abs_right : f =O[l] (λ x, |u x|) ↔ f =O[l] u :=
@is_O_norm_right _ _ ℝ _ _ _ _ _

alias is_O_norm_right ↔ is_O.of_norm_right is_O.norm_right
alias is_O_abs_right ↔ is_O.of_abs_right is_O.abs_right

@[simp] theorem is_o_norm_right : f =o[l] (λ x, ‖g' x‖) ↔ f =o[l] g' :=
by { unfold is_o, exact forall₂_congr (λ _ _, is_O_with_norm_right) }

@[simp] theorem is_o_abs_right : f =o[l] (λ x, |u x|) ↔ f =o[l] u :=
@is_o_norm_right _ _ ℝ _ _ _ _ _

alias is_o_norm_right ↔ is_o.of_norm_right is_o.norm_right
alias is_o_abs_right ↔ is_o.of_abs_right is_o.abs_right

@[simp] theorem is_O_with_norm_left : is_O_with c l (λ x, ‖f' x‖) g ↔ is_O_with c l f' g :=
by simp only [is_O_with, norm_norm]

@[simp] theorem is_O_with_abs_left : is_O_with c l (λ x, |u x|) g ↔ is_O_with c l u g :=
@is_O_with_norm_left _ _ _ _ _ _ g u l

alias is_O_with_norm_left ↔ is_O_with.of_norm_left is_O_with.norm_left
alias is_O_with_abs_left ↔ is_O_with.of_abs_left is_O_with.abs_left

@[simp] theorem is_O_norm_left : (λ x, ‖f' x‖) =O[l] g ↔ f' =O[l] g :=
by { unfold is_O, exact exists_congr (λ _, is_O_with_norm_left) }

@[simp] theorem is_O_abs_left : (λ x, |u x|) =O[l] g ↔ u =O[l] g :=
@is_O_norm_left _ _ _ _ _ g u l

alias is_O_norm_left ↔ is_O.of_norm_left is_O.norm_left
alias is_O_abs_left ↔ is_O.of_abs_left is_O.abs_left

@[simp] theorem is_o_norm_left : (λ x, ‖f' x‖) =o[l] g ↔ f' =o[l] g :=
by { unfold is_o, exact forall₂_congr (λ _ _, is_O_with_norm_left) }

@[simp] theorem is_o_abs_left : (λ x, |u x|) =o[l] g ↔ u =o[l] g :=
@is_o_norm_left _ _ _ _ _ g u l

alias is_o_norm_left ↔ is_o.of_norm_left is_o.norm_left
alias is_o_abs_left ↔ is_o.of_abs_left is_o.abs_left

theorem is_O_with_norm_norm : is_O_with c l (λ x, ‖f' x‖) (λ x, ‖g' x‖) ↔ is_O_with c l f' g' :=
is_O_with_norm_left.trans is_O_with_norm_right

theorem is_O_with_abs_abs : is_O_with c l (λ x, |u x|) (λ x, |v x|) ↔ is_O_with c l u v :=
is_O_with_abs_left.trans is_O_with_abs_right

alias is_O_with_norm_norm ↔ is_O_with.of_norm_norm is_O_with.norm_norm
alias is_O_with_abs_abs ↔ is_O_with.of_abs_abs is_O_with.abs_abs

theorem is_O_norm_norm : (λ x, ‖f' x‖) =O[l] (λ x, ‖g' x‖) ↔ f' =O[l] g' :=
is_O_norm_left.trans is_O_norm_right

theorem is_O_abs_abs : (λ x, |u x|) =O[l] (λ x, |v x|) ↔ u =O[l] v :=
is_O_abs_left.trans is_O_abs_right

alias is_O_norm_norm ↔ is_O.of_norm_norm is_O.norm_norm
alias is_O_abs_abs ↔ is_O.of_abs_abs is_O.abs_abs

theorem is_o_norm_norm : (λ x, ‖f' x‖) =o[l] (λ x, ‖g' x‖) ↔ f' =o[l] g' :=
is_o_norm_left.trans is_o_norm_right

theorem is_o_abs_abs : (λ x, |u x|) =o[l] (λ x, |v x|) ↔ u =o[l] v :=
is_o_abs_left.trans is_o_abs_right

alias is_o_norm_norm ↔ is_o.of_norm_norm is_o.norm_norm
alias is_o_abs_abs ↔ is_o.of_abs_abs is_o.abs_abs

end norm_abs

/-! ### Simplification: negate -/

@[simp] theorem is_O_with_neg_right : is_O_with c l f (λ x, -(g' x)) ↔ is_O_with c l f g' :=
by simp only [is_O_with, norm_neg]

alias is_O_with_neg_right ↔ is_O_with.of_neg_right is_O_with.neg_right

@[simp] theorem is_O_neg_right : f =O[l] (λ x, -(g' x)) ↔ f =O[l] g' :=
by { unfold is_O, exact exists_congr (λ _, is_O_with_neg_right) }

alias is_O_neg_right ↔ is_O.of_neg_right is_O.neg_right

@[simp] theorem is_o_neg_right : f =o[l] (λ x, -(g' x)) ↔ f =o[l] g' :=
by { unfold is_o, exact forall₂_congr (λ _ _, is_O_with_neg_right) }

alias is_o_neg_right ↔ is_o.of_neg_right is_o.neg_right

@[simp] theorem is_O_with_neg_left : is_O_with c l (λ x, -(f' x)) g ↔ is_O_with c l f' g :=
by simp only [is_O_with, norm_neg]

alias is_O_with_neg_left ↔ is_O_with.of_neg_left is_O_with.neg_left

@[simp] theorem is_O_neg_left : (λ x, -(f' x)) =O[l] g ↔ f' =O[l] g :=
by { unfold is_O, exact exists_congr (λ _, is_O_with_neg_left) }

alias is_O_neg_left ↔ is_O.of_neg_left is_O.neg_left

@[simp] theorem is_o_neg_left : (λ x, -(f' x)) =o[l] g ↔ f' =o[l] g :=
by { unfold is_o, exact forall₂_congr (λ _ _, is_O_with_neg_left) }

alias is_o_neg_left ↔ is_o.of_neg_right is_o.neg_left

/-! ### Product of functions (right) -/

lemma is_O_with_fst_prod : is_O_with 1 l f' (λ x, (f' x, g' x)) :=
is_O_with_of_le l $ λ x, le_max_left _ _

lemma is_O_with_snd_prod : is_O_with 1 l g' (λ x, (f' x, g' x)) :=
is_O_with_of_le l $ λ x, le_max_right _ _

lemma is_O_fst_prod : f' =O[l] (λ x, (f' x, g' x)) := is_O_with_fst_prod.is_O

lemma is_O_snd_prod : g' =O[l] (λ x, (f' x, g' x)) := is_O_with_snd_prod.is_O

lemma is_O_fst_prod' {f' : α → E' × F'} : (λ x, (f' x).1) =O[l] f' :=
by simpa [is_O, is_O_with] using is_O_fst_prod

lemma is_O_snd_prod' {f' : α → E' × F'} : (λ x, (f' x).2) =O[l] f' :=
by simpa [is_O, is_O_with] using is_O_snd_prod

section

variables (f' k')

lemma is_O_with.prod_rightl (h : is_O_with c l f g') (hc : 0 ≤ c) :
  is_O_with c l f (λ x, (g' x, k' x)) :=
(h.trans is_O_with_fst_prod hc).congr_const (mul_one c)

lemma is_O.prod_rightl (h : f =O[l] g') : f =O[l] (λ x, (g' x, k' x)) :=
let ⟨c, cnonneg, hc⟩ := h.exists_nonneg in (hc.prod_rightl k' cnonneg).is_O

lemma is_o.prod_rightl (h : f =o[l] g') : f =o[l] (λ x, (g' x, k' x)) :=
is_o.of_is_O_with $ λ c cpos, (h.forall_is_O_with cpos).prod_rightl k' cpos.le

lemma is_O_with.prod_rightr (h : is_O_with c l f g') (hc : 0 ≤ c) :
  is_O_with c l f (λ x, (f' x, g' x)) :=
(h.trans is_O_with_snd_prod hc).congr_const (mul_one c)

lemma is_O.prod_rightr (h : f =O[l] g') : f =O[l] (λ x, (f' x, g' x)) :=
let ⟨c, cnonneg, hc⟩ := h.exists_nonneg in (hc.prod_rightr f' cnonneg).is_O

lemma is_o.prod_rightr (h : f =o[l] g') : f =o[l] (λx, (f' x, g' x)) :=
is_o.of_is_O_with $ λ c cpos, (h.forall_is_O_with cpos).prod_rightr f' cpos.le

end

lemma is_O_with.prod_left_same (hf : is_O_with c l f' k') (hg : is_O_with c l g' k') :
  is_O_with c l (λ x, (f' x, g' x)) k' :=
by rw is_O_with_iff at *; filter_upwards [hf, hg] with x using max_le

lemma is_O_with.prod_left (hf : is_O_with c l f' k') (hg : is_O_with c' l g' k') :
  is_O_with (max c c') l (λ x, (f' x, g' x)) k' :=
(hf.weaken $ le_max_left c c').prod_left_same (hg.weaken $ le_max_right c c')

lemma is_O_with.prod_left_fst (h : is_O_with c l (λ x, (f' x, g' x)) k') :
  is_O_with c l f' k' :=
(is_O_with_fst_prod.trans h zero_le_one).congr_const $ one_mul c

lemma is_O_with.prod_left_snd (h : is_O_with c l (λ x, (f' x, g' x)) k') :
  is_O_with c l g' k' :=
(is_O_with_snd_prod.trans h zero_le_one).congr_const $ one_mul c

lemma is_O_with_prod_left :
   is_O_with c l (λ x, (f' x, g' x)) k' ↔ is_O_with c l f' k' ∧ is_O_with c l g' k' :=
⟨λ h, ⟨h.prod_left_fst, h.prod_left_snd⟩, λ h, h.1.prod_left_same h.2⟩

lemma is_O.prod_left (hf : f' =O[l] k') (hg : g' =O[l] k') : (λ x, (f' x, g' x)) =O[l] k' :=
let ⟨c, hf⟩ := hf.is_O_with, ⟨c', hg⟩ := hg.is_O_with in (hf.prod_left hg).is_O

lemma is_O.prod_left_fst : (λ x, (f' x, g' x)) =O[l] k' → f' =O[l] k' := is_O.trans is_O_fst_prod
lemma is_O.prod_left_snd : (λ x, (f' x, g' x)) =O[l] k' → g' =O[l] k' := is_O.trans is_O_snd_prod

@[simp] lemma is_O_prod_left : (λ x, (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k' :=
⟨λ h, ⟨h.prod_left_fst, h.prod_left_snd⟩, λ h, h.1.prod_left h.2⟩

lemma is_o.prod_left (hf : f' =o[l] k') (hg : g' =o[l] k') : (λ x, (f' x, g' x)) =o[l] k' :=
is_o.of_is_O_with $ λ c hc, (hf.forall_is_O_with hc).prod_left_same (hg.forall_is_O_with hc)

lemma is_o.prod_left_fst : (λ x, (f' x, g' x)) =o[l] k' → f' =o[l] k' :=
is_O.trans_is_o is_O_fst_prod

lemma is_o.prod_left_snd : (λ x, (f' x, g' x)) =o[l] k' → g' =o[l] k' :=
is_O.trans_is_o is_O_snd_prod

@[simp] lemma is_o_prod_left : (λ x, (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k' :=
⟨λ h, ⟨h.prod_left_fst, h.prod_left_snd⟩, λ h, h.1.prod_left h.2⟩

lemma is_O_with.eq_zero_imp (h : is_O_with c l f'' g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
eventually.mono h.bound $ λ x hx hg, norm_le_zero_iff.1 $ by simpa [hg] using hx

lemma is_O.eq_zero_imp (h : f'' =O[l] g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
let ⟨C, hC⟩ := h.is_O_with in hC.eq_zero_imp

/-! ### Addition and subtraction -/

section add_sub

variables {f₁ f₂ : α → E'} {g₁ g₂ : α → F'}

theorem is_O_with.add (h₁ : is_O_with c₁ l f₁ g) (h₂ : is_O_with c₂ l f₂ g) :
  is_O_with (c₁ + c₂) l (λ x, f₁ x + f₂ x) g :=
by rw is_O_with at *; filter_upwards [h₁, h₂] with x hx₁ hx₂ using
calc ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g x‖ + c₂ * ‖g x‖ : norm_add_le_of_le hx₁ hx₂
               ... = (c₁ + c₂) * ‖g x‖       : (add_mul _ _ _).symm

theorem is_O.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (λ x, f₁ x + f₂ x) =O[l] g :=
let ⟨c₁, hc₁⟩ := h₁.is_O_with, ⟨c₂, hc₂⟩ := h₂.is_O_with in (hc₁.add hc₂).is_O

theorem is_o.add (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (λ x, f₁ x + f₂ x) =o[l] g :=
is_o.of_is_O_with $ λ c cpos, ((h₁.forall_is_O_with $ half_pos cpos).add
  (h₂.forall_is_O_with $ half_pos cpos)).congr_const (add_halves c)

theorem is_o.add_add (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
  (λ x, f₁ x + f₂ x) =o[l] (λ x, ‖g₁ x‖ + ‖g₂ x‖) :=
by refine (h₁.trans_le $ λ x, _).add (h₂.trans_le _);
  simp [abs_of_nonneg, add_nonneg]

theorem is_O.add_is_o (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g) : (λ x, f₁ x + f₂ x) =O[l] g :=
h₁.add h₂.is_O

theorem is_o.add_is_O (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g) : (λ x, f₁ x + f₂ x) =O[l] g :=
h₁.is_O.add h₂

theorem is_O_with.add_is_o (h₁ : is_O_with c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
  is_O_with c₂ l (λx, f₁ x + f₂ x) g :=
(h₁.add (h₂.forall_is_O_with (sub_pos.2 hc))).congr_const (add_sub_cancel'_right _ _)

theorem is_o.add_is_O_with (h₁ : f₁ =o[l] g) (h₂ : is_O_with c₁ l f₂ g) (hc : c₁ < c₂) :
  is_O_with c₂ l (λx, f₁ x + f₂ x) g :=
(h₂.add_is_o h₁ hc).congr_left $ λ _, add_comm _ _

theorem is_O_with.sub (h₁ : is_O_with c₁ l f₁ g) (h₂ : is_O_with c₂ l f₂ g) :
  is_O_with (c₁ + c₂) l (λ x, f₁ x - f₂ x) g :=
by simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

theorem is_O_with.sub_is_o (h₁ : is_O_with c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
  is_O_with c₂ l (λ x, f₁ x - f₂ x) g :=
by simpa only [sub_eq_add_neg] using h₁.add_is_o h₂.neg_left hc

theorem is_O.sub (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (λ x, f₁ x - f₂ x) =O[l] g :=
by simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

theorem is_o.sub (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (λ x, f₁ x - f₂ x) =o[l] g :=
by simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

end add_sub

/-! ### Lemmas about `is_O (f₁ - f₂) g l` / `is_o (f₁ - f₂) g l` treated as a binary relation -/

section is_oO_as_rel

variables {f₁ f₂ f₃ : α → E'}

theorem is_O_with.symm (h : is_O_with c l (λ x, f₁ x - f₂ x) g) :
  is_O_with c l (λ x, f₂ x - f₁ x) g :=
h.neg_left.congr_left $ λ x, neg_sub _ _

theorem is_O_with_comm :
  is_O_with c l (λ x, f₁ x - f₂ x) g ↔ is_O_with c l (λ x, f₂ x - f₁ x) g :=
⟨is_O_with.symm, is_O_with.symm⟩

theorem is_O.symm (h : (λ x, f₁ x - f₂ x) =O[l] g) : (λ x, f₂ x - f₁ x) =O[l] g :=
h.neg_left.congr_left $ λ x, neg_sub _ _

theorem is_O_comm : (λ x, f₁ x - f₂ x) =O[l] g ↔ (λ x, f₂ x - f₁ x) =O[l] g :=
⟨is_O.symm, is_O.symm⟩

theorem is_o.symm (h : (λ x, f₁ x - f₂ x) =o[l] g) : (λ x, f₂ x - f₁ x) =o[l] g :=
by simpa only [neg_sub] using h.neg_left

theorem is_o_comm : (λ x, f₁ x - f₂ x) =o[l] g ↔ (λ x, f₂ x - f₁ x) =o[l] g :=
⟨is_o.symm, is_o.symm⟩

theorem is_O_with.triangle (h₁ : is_O_with c l (λ x, f₁ x - f₂ x) g)
  (h₂ : is_O_with c' l (λ x, f₂ x - f₃ x) g) :
  is_O_with (c + c') l (λ x, f₁ x - f₃ x) g :=
(h₁.add h₂).congr_left $ λ x, sub_add_sub_cancel _ _ _

theorem is_O.triangle (h₁ : (λ x, f₁ x - f₂ x) =O[l] g) (h₂ : (λ x, f₂ x - f₃ x) =O[l] g) :
  (λ x, f₁ x - f₃ x) =O[l] g :=
(h₁.add h₂).congr_left $ λ x, sub_add_sub_cancel _ _ _

theorem is_o.triangle (h₁ : (λ x, f₁ x - f₂ x) =o[l] g) (h₂ : (λ x, f₂ x - f₃ x) =o[l] g) :
  (λ x, f₁ x - f₃ x) =o[l] g :=
(h₁.add h₂).congr_left $ λ x, sub_add_sub_cancel _ _ _

theorem is_O.congr_of_sub (h : (λ x, f₁ x - f₂ x) =O[l] g) : f₁ =O[l] g ↔ f₂ =O[l] g :=
⟨λ h', (h'.sub h).congr_left (λ x, sub_sub_cancel _ _),
 λ h', (h.add h').congr_left (λ x, sub_add_cancel _ _)⟩

theorem is_o.congr_of_sub (h : (λ x, f₁ x - f₂ x) =o[l] g) : f₁ =o[l] g ↔ f₂ =o[l] g :=
⟨λ h', (h'.sub h).congr_left (λ x, sub_sub_cancel _ _),
 λ h', (h.add h').congr_left (λ x, sub_add_cancel _ _)⟩

end is_oO_as_rel

/-! ### Zero, one, and other constants -/

section zero_const

variables (g g' l)

theorem is_o_zero : (λ x, (0 : E')) =o[l] g' :=
is_o.of_bound $ λ c hc, univ_mem' $ λ x,
by simpa using mul_nonneg hc.le (norm_nonneg $ g' x)

theorem is_O_with_zero (hc : 0 ≤ c) : is_O_with c l (λ x, (0 : E')) g' :=
is_O_with.of_bound $ univ_mem' $ λ x, by simpa using mul_nonneg hc (norm_nonneg $ g' x)

theorem is_O_with_zero' : is_O_with 0 l (λ x, (0 : E')) g :=
is_O_with.of_bound $ univ_mem' $ λ x, by simp

theorem is_O_zero : (λ x, (0 : E')) =O[l] g :=
is_O_iff_is_O_with.2 ⟨0, is_O_with_zero' _ _⟩

theorem is_O_refl_left : (λ x, f' x - f' x) =O[l] g' :=
(is_O_zero g' l).congr_left $ λ x, (sub_self _).symm

theorem is_o_refl_left : (λ x, f' x - f' x) =o[l] g' :=
(is_o_zero g' l).congr_left $ λ x, (sub_self _).symm

variables {g g' l}

@[simp] theorem is_O_with_zero_right_iff :
  is_O_with c l f'' (λ x, (0 : F')) ↔ f'' =ᶠ[l] 0 :=
by simp only [is_O_with, exists_prop, true_and, norm_zero, mul_zero, norm_le_zero_iff,
  eventually_eq, pi.zero_apply]

@[simp] theorem is_O_zero_right_iff : f'' =O[l] (λ x, (0 : F')) ↔ f'' =ᶠ[l] 0 :=
⟨λ h, let ⟨c, hc⟩ := h.is_O_with in is_O_with_zero_right_iff.1 hc,
  λ h, (is_O_with_zero_right_iff.2 h : is_O_with 1 _ _ _).is_O⟩

@[simp] theorem is_o_zero_right_iff :
  f'' =o[l] (λ x, (0 : F')) ↔ f'' =ᶠ[l] 0 :=
⟨λ h, is_O_zero_right_iff.1 h.is_O, λ h, is_o.of_is_O_with $ λ c hc, is_O_with_zero_right_iff.2 h⟩

theorem is_O_with_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : filter α) :
  is_O_with (‖c‖ / ‖c'‖) l (λ x : α, c) (λ x, c') :=
begin
  unfold is_O_with,
  apply univ_mem',
  intro x,
  rw [mem_set_of_eq, div_mul_cancel],
  rwa [ne.def, norm_eq_zero]
end

theorem is_O_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : filter α) :
  (λ x : α, c) =O[l] (λ x, c') :=
(is_O_with_const_const c hc' l).is_O

@[simp] theorem is_O_const_const_iff {c : E''} {c' : F''} (l : filter α) [l.ne_bot] :
  (λ x : α, c) =O[l] (λ x, c') ↔ (c' = 0 → c = 0) :=
begin
  rcases eq_or_ne c' 0 with rfl|hc',
  { simp [eventually_eq] },
  { simp [hc', is_O_const_const _ hc'] }
end

@[simp] lemma is_O_pure {x} : f'' =O[pure x] g'' ↔ (g'' x = 0 → f'' x = 0) :=
calc f'' =O[pure x] g'' ↔ (λ y : α, f'' x) =O[pure x] (λ _, g'' x) : is_O_congr rfl rfl
                    ... ↔ g'' x = 0 → f'' x = 0                    : is_O_const_const_iff _

end zero_const

@[simp] lemma is_O_with_top : is_O_with c ⊤ f g ↔ ∀ x, ‖f x‖ ≤ c * ‖g x‖ := by rw is_O_with; refl

@[simp] lemma is_O_top : f =O[⊤] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by rw is_O_iff; refl

@[simp] lemma is_o_top : f'' =o[⊤] g'' ↔ ∀ x, f'' x = 0 :=
begin
  refine ⟨_, λ h, (is_o_zero g'' ⊤).congr (λ x, (h x).symm) (λ x, rfl)⟩,
  simp only [is_o_iff, eventually_top],
  refine λ h x, norm_le_zero_iff.1 _,
  have : tendsto (λ c : ℝ, c * ‖g'' x‖) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_id.mul continuous_const).tendsto' _ _ (zero_mul _)).mono_left inf_le_left,
  exact le_of_tendsto_of_tendsto tendsto_const_nhds this
    (eventually_nhds_within_iff.2 $ eventually_of_forall $ λ c hc, h hc x)
end

@[simp] lemma is_O_with_principal {s : set α} :
  is_O_with c (𝓟 s) f g ↔ ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ :=
by rw is_O_with; refl

lemma is_O_principal {s : set α} : f =O[𝓟 s] g ↔ ∃ c, ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ :=
by rw is_O_iff; refl

section

variables (F) [has_one F] [norm_one_class F]

theorem is_O_with_const_one (c : E) (l : filter α) : is_O_with ‖c‖ l (λ x : α, c) (λ x, (1 : F)) :=
by simp [is_O_with_iff]

theorem is_O_const_one (c : E) (l : filter α) : (λ x : α, c) =O[l] (λ x, (1 : F)) :=
(is_O_with_const_one F c l).is_O

theorem is_o_const_iff_is_o_one {c : F''} (hc : c ≠ 0) :
  f =o[l] (λ x, c) ↔ f =o[l] (λ x, (1 : F)) :=
⟨λ h, h.trans_is_O_with (is_O_with_const_one _ _ _) (norm_pos_iff.2 hc),
  λ h, h.trans_is_O $ is_O_const_const _ hc _⟩

@[simp] theorem is_o_one_iff : f' =o[l] (λ x, 1 : α → F) ↔ tendsto f' l (𝓝 0) :=
by simp only [is_o_iff, norm_one, mul_one, metric.nhds_basis_closed_ball.tendsto_right_iff,
  metric.mem_closed_ball, dist_zero_right]

@[simp] theorem is_O_one_iff : f =O[l] (λ x, 1 : α → F) ↔ is_bounded_under (≤) l (λ x, ‖f x‖) :=
by { simp only [is_O_iff, norm_one, mul_one], refl }

alias is_O_one_iff ↔ _ _root_.filter.is_bounded_under.is_O_one

@[simp] theorem is_o_one_left_iff : (λ x, 1 : α → F) =o[l] f ↔ tendsto (λ x, ‖f x‖) l at_top :=
calc (λ x, 1 : α → F) =o[l] f ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖(1 : F)‖ ≤ ‖f x‖ :
  is_o_iff_nat_mul_le_aux $ or.inl $ λ x, by simp only [norm_one, zero_le_one]
... ↔ ∀ n : ℕ, true → ∀ᶠ x in l, ‖f x‖ ∈ Ici (n : ℝ) :
  by simp only [norm_one, mul_one, true_implies_iff, mem_Ici]
... ↔ tendsto (λ x, ‖f x‖) l at_top : at_top_countable_basis_of_archimedean.1.tendsto_right_iff.symm

theorem _root_.filter.tendsto.is_O_one {c : E'} (h : tendsto f' l (𝓝 c)) :
  f' =O[l] (λ x, 1 : α → F) :=
h.norm.is_bounded_under_le.is_O_one F

theorem is_O.trans_tendsto_nhds (hfg : f =O[l] g') {y : F'} (hg : tendsto g' l (𝓝 y)) :
  f =O[l] (λ x, 1 : α → F) :=
hfg.trans $ hg.is_O_one F

end

theorem is_o_const_iff {c : F''} (hc : c ≠ 0) :
  f'' =o[l] (λ x, c) ↔ tendsto f'' l (𝓝 0) :=
(is_o_const_iff_is_o_one ℝ hc).trans (is_o_one_iff _)

lemma is_o_id_const {c : F''} (hc : c ≠ 0) :
  (λ (x : E''), x) =o[𝓝 0] (λ x, c) :=
(is_o_const_iff hc).mpr (continuous_id.tendsto 0)

theorem _root_.filter.is_bounded_under.is_O_const (h : is_bounded_under (≤) l (norm ∘ f))
  {c : F''} (hc : c ≠ 0) : f =O[l] (λ x, c) :=
(h.is_O_one ℝ).trans (is_O_const_const _ hc _)

theorem is_O_const_of_tendsto {y : E''} (h : tendsto f'' l (𝓝 y)) {c : F''} (hc : c ≠ 0) :
  f'' =O[l] (λ x, c) :=
h.norm.is_bounded_under_le.is_O_const hc

lemma is_O.is_bounded_under_le {c : F} (h : f =O[l] (λ x, c)) :
  is_bounded_under (≤) l (norm ∘ f) :=
let ⟨c', hc'⟩ := h.bound in ⟨c' * ‖c‖, eventually_map.2 hc'⟩

theorem is_O_const_of_ne {c : F''} (hc : c ≠ 0) :
  f =O[l] (λ x, c) ↔ is_bounded_under (≤) l (norm ∘ f) :=
⟨λ h, h.is_bounded_under_le, λ h, h.is_O_const hc⟩

theorem is_O_const_iff {c : F''} :
  f'' =O[l] (λ x, c) ↔ (c = 0 → f'' =ᶠ[l] 0) ∧ is_bounded_under (≤) l (λ x, ‖f'' x‖) :=
begin
  refine ⟨λ h, ⟨λ hc, is_O_zero_right_iff.1 (by rwa ← hc), h.is_bounded_under_le⟩, _⟩,
  rintro ⟨hcf, hf⟩,
  rcases eq_or_ne c 0 with hc|hc,
  exacts [(hcf hc).trans_is_O (is_O_zero _ _), hf.is_O_const hc]
end

theorem is_O_iff_is_bounded_under_le_div (h : ∀ᶠ x in l, g'' x ≠ 0) :
  f =O[l] g'' ↔ is_bounded_under (≤) l (λ x, ‖f x‖ / ‖g'' x‖) :=
begin
  simp only [is_O_iff, is_bounded_under, is_bounded, eventually_map],
  exact exists_congr (λ c, eventually_congr $ h.mono $
    λ x hx, (div_le_iff $ norm_pos_iff.2 hx).symm)
end

/-- `(λ x, c) =O[l] f` if and only if `f` is bounded away from zero. -/
lemma is_O_const_left_iff_pos_le_norm {c : E''} (hc : c ≠ 0) :
  (λ x, c) =O[l] f' ↔ ∃ b, 0 < b ∧ ∀ᶠ x in l, b ≤ ‖f' x‖ :=
begin
  split,
  { intro h,
    rcases h.exists_pos with ⟨C, hC₀, hC⟩,
    refine ⟨‖c‖ / C, div_pos (norm_pos_iff.2 hc) hC₀, _⟩,
    exact hC.bound.mono (λ x, (div_le_iff' hC₀).2) },
  { rintro ⟨b, hb₀, hb⟩,
    refine is_O.of_bound (‖c‖ / b) (hb.mono $ λ x hx, _),
    rw [div_mul_eq_mul_div, mul_div_assoc],
    exact le_mul_of_one_le_right (norm_nonneg _) ((one_le_div hb₀).2 hx) }
end

section

variable (𝕜)

end

theorem is_O.trans_tendsto (hfg : f'' =O[l] g'') (hg : tendsto g'' l (𝓝 0)) :
  tendsto f'' l (𝓝 0) :=
(is_o_one_iff ℝ).1 $ hfg.trans_is_o $ (is_o_one_iff ℝ).2 hg

theorem is_o.trans_tendsto (hfg : f'' =o[l] g'') (hg : tendsto g'' l (𝓝 0)) :
  tendsto f'' l (𝓝 0) :=
hfg.is_O.trans_tendsto hg

/-! ### Multiplication by a constant -/

theorem is_O_with_const_mul_self (c : R) (f : α → R) (l : filter α) :
  is_O_with ‖c‖ l (λ x, c * f x) f :=
is_O_with_of_le' _ $ λ x, norm_mul_le _ _

theorem is_O_const_mul_self (c : R) (f : α → R) (l : filter α) : (λ x, c * f x) =O[l] f :=
(is_O_with_const_mul_self c f l).is_O

theorem is_O_with.const_mul_left {f : α → R} (h : is_O_with c l f g) (c' : R) :
  is_O_with (‖c'‖ * c) l (λ x, c' * f x) g :=
(is_O_with_const_mul_self c' f l).trans h (norm_nonneg c')

theorem is_O.const_mul_left {f : α → R} (h : f =O[l] g) (c' : R) :
  (λ x, c' * f x) =O[l] g :=
let ⟨c, hc⟩ := h.is_O_with in (hc.const_mul_left c').is_O

theorem is_O_with_self_const_mul' (u : Rˣ) (f : α → R) (l : filter α) :
  is_O_with ‖(↑u⁻¹:R)‖ l f (λ x, ↑u * f x) :=
(is_O_with_const_mul_self ↑u⁻¹ _ l).congr_left $ λ x, u.inv_mul_cancel_left (f x)

theorem is_O_with_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : filter α) :
  is_O_with ‖c‖⁻¹ l f (λ x, c * f x) :=
(is_O_with_self_const_mul' (units.mk0 c hc) f l).congr_const $
  norm_inv c

theorem is_O_self_const_mul' {c : R} (hc : is_unit c) (f : α → R) (l : filter α) :
  f =O[l] (λ x, c * f x) :=
let ⟨u, hu⟩ := hc in hu ▸ (is_O_with_self_const_mul' u f l).is_O

theorem is_O_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : filter α) :
  f =O[l] (λ x, c * f x) :=
is_O_self_const_mul' (is_unit.mk0 c hc) f l

theorem is_O_const_mul_left_iff' {f : α → R} {c : R} (hc : is_unit c) :
  (λ x, c * f x) =O[l] g ↔ f =O[l] g :=
⟨(is_O_self_const_mul' hc f l).trans, λ h, h.const_mul_left c⟩

theorem is_O_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
  (λ x, c * f x) =O[l] g ↔ f =O[l] g :=
is_O_const_mul_left_iff' $ is_unit.mk0 c hc

theorem is_o.const_mul_left {f : α → R} (h : f =o[l] g) (c : R) : (λ x, c * f x) =o[l] g :=
(is_O_const_mul_self c f l).trans_is_o h

theorem is_o_const_mul_left_iff' {f : α → R} {c : R} (hc : is_unit c) :
  (λ x, c * f x) =o[l] g ↔ f =o[l] g :=
⟨(is_O_self_const_mul' hc f l).trans_is_o, λ h, h.const_mul_left c⟩

theorem is_o_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
  (λ x, c * f x) =o[l] g ↔ f =o[l] g :=
is_o_const_mul_left_iff' $ is_unit.mk0 c hc

theorem is_O_with.of_const_mul_right {g : α → R} {c : R} (hc' : 0 ≤ c')
  (h : is_O_with c' l f (λ x, c * g x)) :
  is_O_with (c' * ‖c‖) l f g :=
h.trans (is_O_with_const_mul_self c g l) hc'

theorem is_O.of_const_mul_right {g : α → R} {c : R} (h : f =O[l] (λ x, c * g x)) :
  f =O[l] g :=
let ⟨c, cnonneg, hc⟩ := h.exists_nonneg in (hc.of_const_mul_right cnonneg).is_O

theorem is_O_with.const_mul_right' {g : α → R} {u : Rˣ} {c' : ℝ} (hc' : 0 ≤ c')
  (h : is_O_with c' l f g) :
  is_O_with (c' * ‖(↑u⁻¹:R)‖) l f (λ x, ↑u * g x) :=
h.trans (is_O_with_self_const_mul' _ _ _) hc'

theorem is_O_with.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0)
  {c' : ℝ} (hc' : 0 ≤ c') (h : is_O_with c' l f g) :
  is_O_with (c' * ‖c‖⁻¹) l f (λ x, c * g x) :=
h.trans (is_O_with_self_const_mul c hc g l) hc'

theorem is_O.const_mul_right' {g : α → R} {c : R} (hc : is_unit c) (h : f =O[l] g) :
  f =O[l] (λ x, c * g x) :=
h.trans (is_O_self_const_mul' hc g l)

theorem is_O.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =O[l] g) :
  f =O[l] (λ x, c * g x) :=
h.const_mul_right' $ is_unit.mk0 c hc

theorem is_O_const_mul_right_iff' {g : α → R} {c : R} (hc : is_unit c) :
  f =O[l] (λ x, c * g x) ↔ f =O[l] g :=
⟨λ h, h.of_const_mul_right, λ h, h.const_mul_right' hc⟩

theorem is_O_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
  f =O[l] (λ x, c * g x) ↔ f =O[l] g :=
is_O_const_mul_right_iff' $ is_unit.mk0 c hc

theorem is_o.of_const_mul_right {g : α → R} {c : R} (h : f =o[l] (λ x, c * g x)) :
  f =o[l] g :=
h.trans_is_O (is_O_const_mul_self c g l)

theorem is_o.const_mul_right' {g : α → R} {c : R} (hc : is_unit c) (h : f =o[l] g) :
  f =o[l] (λ x, c * g x) :=
h.trans_is_O (is_O_self_const_mul' hc g l)

theorem is_o.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =o[l] g) :
  f =o[l] (λ x, c * g x) :=
h.const_mul_right' $ is_unit.mk0 c hc

theorem is_o_const_mul_right_iff' {g : α → R} {c : R} (hc : is_unit c) :
  f =o[l] (λ x, c * g x) ↔ f =o[l] g :=
⟨λ h, h.of_const_mul_right, λ h, h.const_mul_right' hc⟩

theorem is_o_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) :
  f =o[l] (λ x, c * g x) ↔ f =o[l] g :=
is_o_const_mul_right_iff' $ is_unit.mk0 c hc

/-! ### Multiplication -/

theorem is_O_with.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} {c₁ c₂ : ℝ}
  (h₁ : is_O_with c₁ l f₁ g₁) (h₂ : is_O_with c₂ l f₂ g₂) :
  is_O_with (c₁ * c₂) l (λ x, f₁ x * f₂ x) (λ x, g₁ x * g₂ x) :=
begin
  unfold is_O_with at *,
  filter_upwards [h₁, h₂] with _ hx₁ hx₂,
  apply le_trans (norm_mul_le _ _),
  convert mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1,
  rw [norm_mul, mul_mul_mul_comm]
end

theorem is_O.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
  (λ x, f₁ x * f₂ x) =O[l] (λ x, g₁ x * g₂ x) :=
let ⟨c, hc⟩ := h₁.is_O_with, ⟨c', hc'⟩ := h₂.is_O_with in (hc.mul hc').is_O

theorem is_O.mul_is_o {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜}
  (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) :
  (λ x, f₁ x * f₂ x) =o[l] (λ x, g₁ x * g₂ x) :=
begin
  unfold is_o at *,
  intros c cpos,
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩,
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel' _ (ne_of_gt c'pos))
end

theorem is_o.mul_is_O {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) :
  (λ x, f₁ x * f₂ x) =o[l] (λ x, g₁ x * g₂ x) :=
begin
  unfold is_o at *,
  intros c cpos,
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩,
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel _ (ne_of_gt c'pos))
end

theorem is_o.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
  (λ x, f₁ x * f₂ x) =o[l] (λ x, g₁ x * g₂ x) :=
h₁.mul_is_O h₂.is_O

theorem is_O_with.pow' {f : α → R} {g : α → 𝕜} (h : is_O_with c l f g) :
  ∀ n : ℕ, is_O_with (nat.cases_on n ‖(1 : R)‖ (λ n, c ^ (n + 1))) l (λ x, f x ^ n) (λ x, g x ^ n)
| 0 := by simpa using is_O_with_const_const (1 : R) (one_ne_zero' 𝕜) l
| 1 := by simpa
| (n + 2) := by simpa [pow_succ] using h.mul (is_O_with.pow' (n + 1))

theorem is_O_with.pow [norm_one_class R] {f : α → R} {g : α → 𝕜} (h : is_O_with c l f g) :
  ∀ n : ℕ, is_O_with (c ^ n) l (λ x, f x ^ n) (λ x, g x ^ n)
| 0 := by simpa using h.pow' 0
| (n + 1) := h.pow' (n + 1)

theorem is_O_with.of_pow {n : ℕ} {f : α → 𝕜} {g : α → R} (h : is_O_with c l (f ^ n) (g ^ n))
  (hn : n ≠ 0) (hc : c ≤ c' ^ n) (hc' : 0 ≤ c') : is_O_with c' l f g :=
is_O_with.of_bound $ (h.weaken hc).bound.mono $ λ x hx,
  le_of_pow_le_pow n (mul_nonneg hc' $ norm_nonneg _) hn.bot_lt $
    calc ‖f x‖ ^ n = ‖(f x) ^ n‖ : (norm_pow _ _).symm
               ... ≤ c' ^ n * ‖(g x) ^ n‖ : hx
               ... ≤ c' ^ n * ‖g x‖ ^ n :
      mul_le_mul_of_nonneg_left (norm_pow_le' _ hn.bot_lt) (pow_nonneg hc' _)
               ... = (c' * ‖g x‖) ^ n : (mul_pow _ _ _).symm

theorem is_O.pow {f : α → R} {g : α → 𝕜} (h : f =O[l] g) (n : ℕ) :
  (λ x, f x ^ n) =O[l] (λ x, g x ^ n) :=
let ⟨C, hC⟩ := h.is_O_with in is_O_iff_is_O_with.2 ⟨_, hC.pow' n⟩

theorem is_O.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (hn : n ≠ 0) (h : (f ^ n) =O[l] (g ^ n)) :
  f =O[l] g :=
begin
  rcases h.exists_pos with ⟨C, hC₀, hC⟩,
  obtain ⟨c, hc₀, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ C ≤ c ^ n,
    from ((eventually_ge_at_top _).and $ (tendsto_pow_at_top hn).eventually_ge_at_top C).exists,
  exact (hC.of_pow hn hc hc₀).is_O
end

theorem is_o.pow {f : α → R} {g : α → 𝕜} (h : f =o[l] g) {n : ℕ} (hn : 0 < n) :
  (λ x, f x ^ n) =o[l] (λ x, g x ^ n) :=
begin
  cases n, exact hn.false.elim, clear hn,
  induction n with n ihn, { simpa only [pow_one] },
  convert h.mul ihn; simp [pow_succ]
end

theorem is_o.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (h : (f ^ n) =o[l] (g ^ n)) (hn : n ≠ 0) :
  f =o[l] g :=
is_o.of_is_O_with $ λ c hc, (h.def' $ pow_pos hc _).of_pow hn le_rfl hc.le

/-! ### Inverse -/

theorem is_O_with.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : is_O_with c l f g)
  (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : is_O_with c l (λ x, (g x)⁻¹) (λ x, (f x)⁻¹) :=
begin
  refine is_O_with.of_bound (h.bound.mp (h₀.mono $ λ x h₀ hle, _)),
  cases eq_or_ne (f x) 0 with hx hx,
  { simp only [hx, h₀ hx, inv_zero, norm_zero, mul_zero] },
  { have hc : 0 < c, from pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _),
    replace hle := inv_le_inv_of_le (norm_pos_iff.2 hx) hle,
    simpa only [norm_inv, mul_inv, ← div_eq_inv_mul, div_le_iff hc] using hle }
end

theorem is_O.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =O[l] g)
  (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (λ x, (g x)⁻¹) =O[l] (λ x, (f x)⁻¹) :=
let ⟨c, hc⟩ := h.is_O_with in (hc.inv_rev h₀).is_O

theorem is_o.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =o[l] g)
  (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (λ x, (g x)⁻¹) =o[l] (λ x, (f x)⁻¹) :=
is_o.of_is_O_with $ λ c hc, (h.def' hc).inv_rev h₀

/-! ### Scalar multiplication -/

section smul_const
variables [normed_space 𝕜 E']

theorem is_O_with.const_smul_left (h : is_O_with c l f' g) (c' : 𝕜) :
  is_O_with (‖c'‖ * c) l (λ x, c' • f' x) g :=
is_O_with.of_norm_left $
  by simpa only [← norm_smul, norm_norm] using h.norm_left.const_mul_left (‖c'‖)

lemma is_O.const_smul_left (h : f' =O[l] g) (c : 𝕜) : (c • f') =O[l] g :=
let ⟨b, hb⟩ := h.is_O_with in (hb.const_smul_left _).is_O

lemma is_o.const_smul_left (h : f' =o[l] g) (c : 𝕜) : (c • f') =o[l] g :=
is_o.of_norm_left $ by simpa only [← norm_smul] using h.norm_left.const_mul_left (‖c‖)

theorem is_O_const_smul_left {c : 𝕜} (hc : c ≠ 0) :
  (λ x, c • f' x) =O[l] g ↔ f' =O[l] g :=
begin
  have cne0 : ‖c‖ ≠ 0, from mt norm_eq_zero.mp hc,
  rw [←is_O_norm_left], simp only [norm_smul],
  rw [is_O_const_mul_left_iff cne0, is_O_norm_left],
end

theorem is_o_const_smul_left {c : 𝕜} (hc : c ≠ 0) :
  (λ x, c • f' x) =o[l] g ↔ f' =o[l] g :=
begin
  have cne0 : ‖c‖ ≠ 0, from mt norm_eq_zero.mp hc,
  rw [←is_o_norm_left], simp only [norm_smul],
  rw [is_o_const_mul_left_iff cne0, is_o_norm_left]
end

theorem is_O_const_smul_right {c : 𝕜} (hc : c ≠ 0) :
  f =O[l] (λ x, c • f' x) ↔ f =O[l] f' :=
begin
  have cne0 : ‖c‖ ≠ 0, from mt norm_eq_zero.mp hc,
  rw [←is_O_norm_right], simp only [norm_smul],
  rw [is_O_const_mul_right_iff cne0, is_O_norm_right]
end

theorem is_o_const_smul_right {c : 𝕜} (hc : c ≠ 0) :
  f =o[l] (λ x, c • f' x) ↔ f =o[l] f' :=
begin
  have cne0 : ‖c‖ ≠ 0, from mt norm_eq_zero.mp hc,
  rw [←is_o_norm_right], simp only [norm_smul],
  rw [is_o_const_mul_right_iff cne0, is_o_norm_right]
end

end smul_const

section smul

variables [normed_space 𝕜 E'] [normed_space 𝕜' F'] {k₁ : α → 𝕜} {k₂ : α → 𝕜'}

theorem is_O_with.smul (h₁ : is_O_with c l k₁ k₂) (h₂ : is_O_with c' l f' g') :
  is_O_with (c * c') l (λ x, k₁ x • f' x) (λ x, k₂ x • g' x) :=
by refine ((h₁.norm_norm.mul h₂.norm_norm).congr rfl _ _).of_norm_norm;
  by intros; simp only [norm_smul]

theorem is_O.smul (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g') :
  (λ x, k₁ x • f' x) =O[l] (λ x, k₂ x • g' x) :=
by refine ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm;
  by intros; simp only [norm_smul]

theorem is_O.smul_is_o (h₁ : k₁ =O[l] k₂) (h₂ : f' =o[l] g') :
  (λ x, k₁ x • f' x) =o[l] (λ x, k₂ x • g' x) :=
by refine ((h₁.norm_norm.mul_is_o h₂.norm_norm).congr _ _).of_norm_norm;
  by intros; simp only [norm_smul]

theorem is_o.smul_is_O (h₁ : k₁ =o[l] k₂) (h₂ : f' =O[l] g') :
  (λ x, k₁ x • f' x) =o[l] (λ x, k₂ x • g' x) :=
by refine ((h₁.norm_norm.mul_is_O h₂.norm_norm).congr _ _).of_norm_norm;
  by intros; simp only [norm_smul]

theorem is_o.smul (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g') :
  (λ x, k₁ x • f' x) =o[l] (λ x, k₂ x • g' x) :=
by refine ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm;
  by intros; simp only [norm_smul]

end smul

/-! ### Sum -/

section sum

variables {ι : Type*} {A : ι → α → E'} {C : ι → ℝ} {s : finset ι}

theorem is_O_with.sum (h : ∀ i ∈ s, is_O_with (C i) l (A i) g) :
  is_O_with (∑ i in s, C i) l (λ x, ∑ i in s, A i x) g :=
begin
  induction s using finset.induction_on with i s is IH,
  { simp only [is_O_with_zero', finset.sum_empty, forall_true_iff] },
  { simp only [is, finset.sum_insert, not_false_iff],
    exact (h _ (finset.mem_insert_self i s)).add (IH (λ j hj, h _ (finset.mem_insert_of_mem hj))) }
end

theorem is_O.sum (h : ∀ i ∈ s, A i =O[l] g) :
  (λ x, ∑ i in s, A i x) =O[l] g :=
begin
  unfold is_O at *,
  choose! C hC using h,
  exact ⟨_, is_O_with.sum hC⟩,
end

theorem is_o.sum (h : ∀ i ∈ s, (A i) =o[l] g') :
  (λ x, ∑ i in s, A i x) =o[l] g' :=
begin
  induction s using finset.induction_on with i s is IH,
  { simp only [is_o_zero, finset.sum_empty, forall_true_iff] },
  { simp only [is, finset.sum_insert, not_false_iff],
    exact (h _ (finset.mem_insert_self i s)).add (IH (λ j hj, h _ (finset.mem_insert_of_mem hj))) }
end

end sum

/-! ### Relation between `f = o(g)` and `f / g → 0` -/

theorem is_o.tendsto_div_nhds_zero {f g : α → 𝕜} (h : f =o[l] g) :
  tendsto (λ x, f x / (g x)) l (𝓝 0) :=
(is_o_one_iff 𝕜).mp $
calc (λ x, f x / g x) =o[l] (λ x, g x / g x) :
  by simpa only [div_eq_mul_inv] using h.mul_is_O (is_O_refl _ _)
... =O[l] (λ x, (1 : 𝕜)) :
  is_O_of_le _ (λ x, by simp [div_self_le_one])

theorem is_o.tendsto_inv_smul_nhds_zero [normed_space 𝕜 E'] {f : α → E'} {g : α → 𝕜} {l : filter α}
  (h : f =o[l] g) : tendsto (λ x, (g x)⁻¹ • f x) l (𝓝 0) :=
by simpa only [div_eq_inv_mul, ← norm_inv, ← norm_smul,
  ← tendsto_zero_iff_norm_tendsto_zero] using h.norm_norm.tendsto_div_nhds_zero

theorem is_o_iff_tendsto' {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
  f =o[l] g ↔ tendsto (λ x, f x / (g x)) l (𝓝 0) :=
⟨is_o.tendsto_div_nhds_zero, λ h,
  (((is_o_one_iff _).mpr h).mul_is_O (is_O_refl g l)).congr'
    (hgf.mono $ λ x, div_mul_cancel_of_imp) (eventually_of_forall $ λ x, one_mul _)⟩

theorem is_o_iff_tendsto {f g : α → 𝕜} (hgf : ∀ x, g x = 0 → f x = 0) :
  f =o[l] g ↔ tendsto (λ x, f x / (g x)) l (𝓝 0) :=
is_o_iff_tendsto' (eventually_of_forall hgf)

alias is_o_iff_tendsto' ↔ _ is_o_of_tendsto'
alias is_o_iff_tendsto ↔ _ is_o_of_tendsto

lemma is_o_const_left_of_ne {c : E''} (hc : c ≠ 0) :
  (λ x, c) =o[l] g ↔ tendsto (λ x, ‖g x‖) l at_top :=
begin
  simp only [← is_o_one_left_iff ℝ],
  exact ⟨(is_O_const_const (1 : ℝ) hc l).trans_is_o, (is_O_const_one ℝ c l).trans_is_o⟩
end

@[simp] lemma is_o_const_left {c : E''} :
  (λ x, c) =o[l] g'' ↔ c = 0 ∨ tendsto (norm ∘ g'') l at_top :=
begin
  rcases eq_or_ne c 0 with rfl | hc,
  { simp only [is_o_zero, eq_self_iff_true, true_or] },
  { simp only [hc, false_or, is_o_const_left_of_ne hc] }
end

@[simp] theorem is_o_const_const_iff [ne_bot l] {d : E''} {c : F''} :
  (λ x, d) =o[l] (λ x, c) ↔ d = 0 :=
have ¬tendsto (function.const α ‖c‖) l at_top,
  from not_tendsto_at_top_of_tendsto_nhds tendsto_const_nhds,
by simp [function.const, this]

@[simp] lemma is_o_pure {x} : f'' =o[pure x] g'' ↔ f'' x = 0 :=
calc f'' =o[pure x] g'' ↔ (λ y : α, f'' x) =o[pure x] (λ _, g'' x) : is_o_congr rfl rfl
                    ... ↔ f'' x = 0                                : is_o_const_const_iff

lemma is_o_const_id_comap_norm_at_top (c : F'') : (λ x : E'', c) =o[comap norm at_top] id :=
is_o_const_left.2 $ or.inr tendsto_comap

lemma is_o_const_id_at_top (c : E'') : (λ x : ℝ, c) =o[at_top] id :=
is_o_const_left.2 $ or.inr tendsto_abs_at_top_at_top

lemma is_o_const_id_at_bot (c : E'') : (λ x : ℝ, c) =o[at_bot] id :=
is_o_const_left.2 $ or.inr tendsto_abs_at_bot_at_top

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `is_O_with` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/

section eventually_mul_div_cancel

variables {u v : α → 𝕜}

lemma is_O_with.eventually_mul_div_cancel (h : is_O_with c l u v) :
  (u / v) * v =ᶠ[l] u :=
eventually.mono h.bound (λ y hy, div_mul_cancel_of_imp $ λ hv, by simpa [hv] using hy)

/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
lemma is_O.eventually_mul_div_cancel (h : u =O[l] v) :  (u / v) * v =ᶠ[l] u :=
let ⟨c, hc⟩ := h.is_O_with in hc.eventually_mul_div_cancel

/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
lemma is_o.eventually_mul_div_cancel (h : u =o[l] v) : (u / v) * v =ᶠ[l] u :=
(h.forall_is_O_with zero_lt_one).eventually_mul_div_cancel

end eventually_mul_div_cancel

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `normed_field`. -/

section exists_mul_eq

variables {u v : α → 𝕜}

/-- If `‖φ‖` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `is_O_with c u v l`.
    This does not require any assumptions on `c`, which is why we keep this version along with
    `is_O_with_iff_exists_eq_mul`. -/
lemma is_O_with_of_eq_mul (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c) (h : u =ᶠ[l] φ * v) :
  is_O_with c l u v :=
begin
  unfold is_O_with,
  refine h.symm.rw (λ x a, ‖a‖ ≤ c * ‖v x‖) (hφ.mono $ λ x hx, _),
  simp only [norm_mul, pi.mul_apply],
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
end

lemma is_O_with_iff_exists_eq_mul (hc : 0 ≤ c) :
  is_O_with c l u v ↔ ∃ (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c), u =ᶠ[l] φ * v :=
begin
  split,
  { intro h,
    use (λ x, u x / v x),
    refine ⟨eventually.mono h.bound (λ y hy, _), h.eventually_mul_div_cancel.symm⟩,
    simpa using div_le_of_nonneg_of_le_mul (norm_nonneg _) hc hy },
  { rintros ⟨φ, hφ, h⟩,
    exact is_O_with_of_eq_mul φ hφ h }
end

lemma is_O_with.exists_eq_mul (h : is_O_with c l u v) (hc : 0 ≤ c) :
  ∃ (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c), u =ᶠ[l] φ * v :=
(is_O_with_iff_exists_eq_mul hc).mp h

lemma is_O_iff_exists_eq_mul :
  u =O[l] v ↔ ∃ (φ : α → 𝕜) (hφ : l.is_bounded_under (≤) (norm ∘ φ)), u =ᶠ[l] φ * v :=
begin
  split,
  { rintros h,
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩,
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩,
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩ },
  { rintros ⟨φ, ⟨c, hφ⟩, huvφ⟩,
    exact is_O_iff_is_O_with.2 ⟨c, is_O_with_of_eq_mul φ hφ huvφ⟩ }
end

alias is_O_iff_exists_eq_mul ↔ is_O.exists_eq_mul _

lemma is_o_iff_exists_eq_mul :
  u =o[l] v ↔ ∃ (φ : α → 𝕜) (hφ : tendsto φ l (𝓝 0)), u =ᶠ[l] φ * v :=
begin
  split,
  { exact λ h, ⟨λ x, u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩ },
  { unfold is_o, rintros ⟨φ, hφ, huvφ⟩ c hpos,
    rw normed_add_comm_group.tendsto_nhds_zero at hφ,
    exact is_O_with_of_eq_mul _ ((hφ c hpos).mono $ λ x, le_of_lt)  huvφ }
end

alias is_o_iff_exists_eq_mul ↔ is_o.exists_eq_mul _

end exists_mul_eq

/-! ### Miscellanous lemmas -/

theorem div_is_bounded_under_of_is_O {α : Type*} {l : filter α}
  {f g : α → 𝕜} (h : f =O[l] g) :
  is_bounded_under (≤) l (λ x, ‖f x / g x‖) :=
begin
  obtain ⟨c, h₀, hc⟩ := h.exists_nonneg,
  refine ⟨c, eventually_map.2 (hc.bound.mono (λ x hx, _))⟩,
  rw [norm_div],
  exact div_le_of_nonneg_of_le_mul (norm_nonneg _) h₀ hx,
end

theorem is_O_iff_div_is_bounded_under {α : Type*} {l : filter α}
  {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
  f =O[l] g ↔ is_bounded_under (≤) l (λ x, ‖f x / g x‖) :=
begin
  refine ⟨div_is_bounded_under_of_is_O, λ h, _⟩,
  obtain ⟨c, hc⟩ := h,
  simp only [eventually_map, norm_div] at hc,
  refine is_O.of_bound c (hc.mp $ hgf.mono (λ x hx₁ hx₂, _)),
  by_cases hgx : g x = 0,
  { simp [hx₁ hgx, hgx] },
  { exact (div_le_iff (norm_pos_iff.2 hgx)).mp hx₂ },
end

theorem is_O_of_div_tendsto_nhds {α : Type*} {l : filter α}
  {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0)
  (c : 𝕜) (H : filter.tendsto (f / g) l (𝓝 c)) :
  f =O[l] g :=
(is_O_iff_div_is_bounded_under hgf).2 $ H.norm.is_bounded_under_le

lemma is_o.tendsto_zero_of_tendsto {α E 𝕜 : Type*} [normed_add_comm_group E] [normed_field 𝕜]
  {u : α → E} {v : α → 𝕜} {l : filter α} {y : 𝕜} (huv : u =o[l] v) (hv : tendsto v l (𝓝 y)) :
  tendsto u l (𝓝 0) :=
begin
  suffices h : u =o[l] (λ x, (1 : 𝕜)),
  { rwa is_o_one_iff at h },
  exact huv.trans_is_O (hv.is_O_one 𝕜),
end

theorem is_o_pow_pow {m n : ℕ} (h : m < n) :
  (λ x : 𝕜, x ^ n) =o[𝓝 0] (λ x, x ^ m) :=
begin
  rcases lt_iff_exists_add.1 h with ⟨p, hp0 : 0 < p, rfl⟩,
  suffices : (λ x : 𝕜, x ^ m * x ^ p) =o[𝓝 0] (λ x, x ^ m * 1 ^ p),
    by simpa only [pow_add, one_pow, mul_one],
  exact is_O.mul_is_o (is_O_refl _ _) (is_o.pow ((is_o_one_iff _).2 tendsto_id) hp0)
end

theorem is_o_norm_pow_norm_pow {m n : ℕ} (h : m < n) :
  (λ x : E', ‖x‖^n) =o[𝓝 0] (λ x, ‖x‖^m) :=
(is_o_pow_pow h).comp_tendsto tendsto_norm_zero

theorem is_o_pow_id {n : ℕ} (h : 1 < n) :
  (λ x : 𝕜, x^n) =o[𝓝 0] (λ x, x) :=
by { convert is_o_pow_pow h, simp only [pow_one] }

theorem is_o_norm_pow_id {n : ℕ} (h : 1 < n) :
  (λ x : E', ‖x‖^n) =o[𝓝 0] (λ x, x) :=
by simpa only [pow_one, is_o_norm_right] using @is_o_norm_pow_norm_pow E' _ _ _ h

lemma is_O.eq_zero_of_norm_pow_within {f : E'' → F''} {s : set E''} {x₀ : E''} {n : ℕ}
  (h : f =O[𝓝[s] x₀] λ x, ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : 0 < n) : f x₀ = 0 :=
mem_of_mem_nhds_within hx₀ h.eq_zero_imp $ by simp_rw [sub_self, norm_zero, zero_pow hn]

lemma is_O.eq_zero_of_norm_pow {f : E'' → F''} {x₀ : E''} {n : ℕ}
  (h : f =O[𝓝 x₀] λ x, ‖x - x₀‖ ^ n) (hn : 0 < n) : f x₀ = 0 :=
by { rw [← nhds_within_univ] at h, exact h.eq_zero_of_norm_pow_within (mem_univ _) hn }

lemma is_o_pow_sub_pow_sub (x₀ : E') {n m : ℕ} (h : n < m) :
    (λ x, ‖x - x₀‖ ^ m) =o[𝓝 x₀] λ x, ‖x - x₀‖^n :=
begin
  have : tendsto (λ x, ‖x - x₀‖) (𝓝 x₀) (𝓝 0),
  { apply tendsto_norm_zero.comp,
    rw ← sub_self x₀,
    exact tendsto_id.sub tendsto_const_nhds },
  exact (is_o_pow_pow h).comp_tendsto this
end

lemma is_o_pow_sub_sub (x₀ : E') {m : ℕ} (h : 1 < m) :
    (λ x, ‖x - x₀‖^m) =o[𝓝 x₀] λ x, x - x₀ :=
by simpa only [is_o_norm_right, pow_one] using is_o_pow_sub_pow_sub x₀ h

theorem is_O_with.right_le_sub_of_lt_1 {f₁ f₂ : α → E'} (h : is_O_with c l f₁ f₂) (hc : c < 1) :
  is_O_with (1 / (1 - c)) l f₂ (λx, f₂ x - f₁ x) :=
is_O_with.of_bound $ mem_of_superset h.bound $ λ x hx,
begin
  simp only [mem_set_of_eq] at hx ⊢,
  rw [mul_comm, one_div, ← div_eq_mul_inv, le_div_iff, mul_sub, mul_one, mul_comm],
  { exact le_trans (sub_le_sub_left hx _) (norm_sub_norm_le _ _) },
  { exact sub_pos.2 hc }
end

theorem is_O_with.right_le_add_of_lt_1 {f₁ f₂ : α → E'} (h : is_O_with c l f₁ f₂) (hc : c < 1) :
  is_O_with (1 / (1 - c)) l f₂ (λx, f₁ x + f₂ x) :=
(h.neg_right.right_le_sub_of_lt_1 hc).neg_right.of_neg_left.congr rfl (λ x, rfl)
  (λ x, by rw [neg_sub, sub_neg_eq_add])

theorem is_o.right_is_O_sub {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
  f₂ =O[l] (λx, f₂ x - f₁ x) :=
((h.def' one_half_pos).right_le_sub_of_lt_1 one_half_lt_one).is_O

theorem is_o.right_is_O_add {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
  f₂ =O[l] (λx, f₁ x + f₂ x) :=
((h.def' one_half_pos).right_le_add_of_lt_1 one_half_lt_one).is_O

/-- If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` such that
`‖f x‖ ≤ C * ‖g x‖` whenever `g x ≠ 0`. -/
theorem bound_of_is_O_cofinite (h : f =O[cofinite] g'') :
  ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ :=
begin
  rcases h.exists_pos with ⟨C, C₀, hC⟩,
  rw [is_O_with, eventually_cofinite] at hC,
  rcases (hC.to_finset.image (λ x, ‖f x‖ / ‖g'' x‖)).exists_le with ⟨C', hC'⟩,
  have : ∀ x, C * ‖g'' x‖ < ‖f x‖ → ‖f x‖ / ‖g'' x‖ ≤ C', by simpa using hC',
  refine ⟨max C C', lt_max_iff.2 (or.inl C₀), λ x h₀, _⟩,
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), le_max_iff, or_iff_not_imp_left, not_le],
  exact λ hx, (div_le_iff (norm_pos_iff.2 h₀)).1 (this _ hx)
end

theorem is_O_cofinite_iff (h : ∀ x, g'' x = 0 → f'' x = 0) :
  f'' =O[cofinite] g'' ↔ ∃ C, ∀ x, ‖f'' x‖ ≤ C * ‖g'' x‖ :=
⟨λ h', let ⟨C, C₀, hC⟩ := bound_of_is_O_cofinite h' in
  ⟨C, λ x, if hx : g'' x = 0 then by simp [h _ hx, hx] else hC hx⟩,
  λ h, (is_O_top.2 h).mono le_top⟩

theorem bound_of_is_O_nat_at_top {f : ℕ → E} {g'' : ℕ → E''} (h : f =O[at_top] g'') :
  ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ :=
bound_of_is_O_cofinite $ by rwa nat.cofinite_eq_at_top

theorem is_O_nat_at_top_iff {f : ℕ → E''} {g : ℕ → F''} (h : ∀ x, g x = 0 → f x = 0) :
  f =O[at_top] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ :=
by rw [← nat.cofinite_eq_at_top, is_O_cofinite_iff h]

theorem is_O_one_nat_at_top_iff {f : ℕ → E''} :
  f =O[at_top] (λ n, 1 : ℕ → ℝ) ↔ ∃ C, ∀ n, ‖f n‖ ≤ C :=
iff.trans (is_O_nat_at_top_iff (λ n h, (one_ne_zero h).elim)) $
  by simp only [norm_one, mul_one]

theorem is_O_with_pi {ι : Type*} [fintype ι] {E' : ι → Type*} [Π i, normed_add_comm_group (E' i)]
  {f : α → Π i, E' i} {C : ℝ} (hC : 0 ≤ C) :
  is_O_with C l f g' ↔ ∀ i, is_O_with C l (λ x, f x i) g' :=
have ∀ x, 0 ≤ C * ‖g' x‖, from λ x, mul_nonneg hC (norm_nonneg _),
by simp only [is_O_with_iff, pi_norm_le_iff_of_nonneg (this _), eventually_all]

@[simp] theorem is_O_pi {ι : Type*} [fintype ι] {E' : ι → Type*} [Π i, normed_add_comm_group (E' i)]
  {f : α → Π i, E' i} :
  f =O[l] g' ↔ ∀ i, (λ x, f x i) =O[l] g' :=
begin
  simp only [is_O_iff_eventually_is_O_with, ← eventually_all],
  exact eventually_congr (eventually_at_top.2 ⟨0, λ c, is_O_with_pi⟩)
end

@[simp] theorem is_o_pi {ι : Type*} [fintype ι] {E' : ι → Type*} [Π i, normed_add_comm_group (E' i)]
  {f : α → Π i, E' i} :
  f =o[l] g' ↔ ∀ i, (λ x, f x i) =o[l] g' :=
begin
  simp only [is_o, is_O_with_pi, le_of_lt] { contextual := tt },
  exact ⟨λ h i c hc, h hc i, λ h c hc i, h i hc⟩
end

end asymptotics

open asymptotics

lemma summable_of_is_O {ι E} [normed_add_comm_group E] [complete_space E] {f : ι → E} {g : ι → ℝ}
  (hg : summable g) (h : f =O[cofinite] g) : summable f :=
let ⟨C, hC⟩ := h.is_O_with in
summable_of_norm_bounded_eventually (λ x, C * ‖g x‖) (hg.abs.mul_left _) hC.bound

lemma summable_of_is_O_nat {E} [normed_add_comm_group E] [complete_space E] {f : ℕ → E} {g : ℕ → ℝ}
  (hg : summable g) (h : f =O[at_top] g) : summable f :=
summable_of_is_O hg $ nat.cofinite_eq_at_top.symm ▸ h

namespace local_homeomorph

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

variables {E : Type*} [has_norm E] {F : Type*} [has_norm F]

/-- Transfer `is_O_with` over a `local_homeomorph`. -/
lemma is_O_with_congr (e : local_homeomorph α β) {b : β} (hb : b ∈ e.target)
  {f : β → E} {g : β → F} {C : ℝ} :
  is_O_with C (𝓝 b) f g ↔ is_O_with C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
⟨λ h, h.comp_tendsto $
  by { convert e.continuous_at (e.map_target hb), exact (e.right_inv hb).symm },
  λ h, (h.comp_tendsto (e.continuous_at_symm hb)).congr' rfl
    ((e.eventually_right_inverse hb).mono $ λ x hx, congr_arg f hx)
    ((e.eventually_right_inverse hb).mono $ λ x hx, congr_arg g hx)⟩

/-- Transfer `is_O` over a `local_homeomorph`. -/
lemma is_O_congr (e : local_homeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
  f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) :=
by { unfold is_O, exact exists_congr (λ C, e.is_O_with_congr hb) }

/-- Transfer `is_o` over a `local_homeomorph`. -/
lemma is_o_congr (e : local_homeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E} {g : β → F} :
  f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) :=
by { unfold is_o, exact forall₂_congr (λ c hc, e.is_O_with_congr hb) }

end local_homeomorph

namespace homeomorph

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

variables {E : Type*} [has_norm E] {F : Type*} [has_norm F]

open asymptotics

/-- Transfer `is_O_with` over a `homeomorph`. -/
lemma is_O_with_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} {C : ℝ} :
  is_O_with C (𝓝 b) f g ↔ is_O_with C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
e.to_local_homeomorph.is_O_with_congr trivial

/-- Transfer `is_O` over a `homeomorph`. -/
lemma is_O_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
  f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) :=
by { unfold is_O, exact exists_congr (λ C, e.is_O_with_congr) }

/-- Transfer `is_o` over a `homeomorph`. -/
lemma is_o_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
  f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) :=
by { unfold is_o, exact forall₂_congr (λ c hc, e.is_O_with_congr) }

end homeomorph
