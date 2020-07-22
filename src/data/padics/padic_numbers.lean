/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis

-/
import data.padics.padic_norm
import analysis.normed_space.basic

/-!
# p-adic numbers

This file defines the p-adic numbers (rationals) ℚ_p as the completion of ℚ with respect to the
p-adic norm. We show that the p-adic norm on ℚ extends to ℚ_p, that ℚ is embedded in ℚ_p, and that
ℚ_p is Cauchy complete.

## Important definitions

* `padic` : the type of p-adic numbers
* `padic_norm_e` : the rational valued p-adic norm on ℚ_p

## Notation

We introduce the notation ℚ_[p] for the p-adic numbers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact (prime p)]` as a type class argument.

We use the same concrete Cauchy sequence construction that is used to construct ℝ. ℚ_p inherits a
field structure from this construction. The extension of the norm on ℚ to ℚ_p is *not* analogous to
extending the absolute value to ℝ, and hence the proof that ℚ_p is complete is different from the
proof that ℝ is complete.

A small special-purpose simplification tactic, `padic_index_simp`, is used to manipulate sequence
indices in the proof that the norm extends.

`padic_norm_e` is the rational-valued p-adic norm on ℚ_p. To instantiate ℚ_p as a normed field, we
must cast this into a ℝ-valued norm. The ℝ-valued norm, using notation ∥ ∥ from normed spaces, is
the canonical representation of this norm.

Coercions from ℚ to ℚ_p are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouêva, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/

noncomputable theory
open_locale classical

open nat multiplicity padic_norm cau_seq cau_seq.completion metric

/-- The type of Cauchy sequences of rationals with respect to the p-adic norm. -/
@[reducible] def padic_seq (p : ℕ) [fact p.prime] := cau_seq _ (padic_norm p)

namespace padic_seq

section
variables {p : ℕ} [fact p.prime]

/-- The p-adic norm of the entries of a nonzero Cauchy sequence of rationals is eventually
constant. -/
lemma stationary {f : cau_seq ℚ (padic_norm p)} (hf : ¬ f ≈ 0) :
  ∃ N, ∀ m n, N ≤ m → N ≤ n → padic_norm p (f n) = padic_norm p (f m) :=
have ∃ ε > 0, ∃ N1, ∀ j ≥ N1, ε ≤ padic_norm p (f j),
  from cau_seq.abv_pos_of_not_lim_zero $ not_lim_zero_of_not_congr_zero hf,
let ⟨ε, hε, N1, hN1⟩ := this,
    ⟨N2, hN2⟩ := cau_seq.cauchy₂ f hε in
⟨ max N1 N2,
  λ n m hn hm,
  have padic_norm p (f n - f m) < ε, from hN2 _ _ (max_le_iff.1 hn).2 (max_le_iff.1 hm).2,
  have padic_norm p (f n - f m) < padic_norm p (f n),
    from lt_of_lt_of_le this $ hN1 _ (max_le_iff.1 hn).1,
  have  padic_norm p (f n - f m) < max (padic_norm p (f n)) (padic_norm p (f m)),
    from lt_max_iff.2 (or.inl this),
  begin
    by_contradiction hne,
    rw ←padic_norm.neg p (f m) at hne,
    have hnam := add_eq_max_of_ne p hne,
    rw [padic_norm.neg, max_comm] at hnam,
    rw [←hnam, sub_eq_add_neg, add_comm] at this,
    apply _root_.lt_irrefl _ this
  end ⟩

/-- For all n ≥ stationary_point f hf, the p-adic norm of f n is the same. -/
def stationary_point {f : padic_seq p} (hf : ¬ f ≈ 0) : ℕ :=
classical.some $ stationary hf

lemma stationary_point_spec {f : padic_seq p} (hf : ¬ f ≈ 0) :
  ∀ {m n}, m ≥ stationary_point hf → n ≥ stationary_point hf →
    padic_norm p (f n) = padic_norm p (f m) :=
classical.some_spec $ stationary hf

/-- Since the norm of the entries of a Cauchy sequence is eventually stationary, we can lift the norm
to sequences. -/
def norm (f : padic_seq p) : ℚ :=
if hf : f ≈ 0 then 0 else padic_norm p (f (stationary_point hf))

lemma norm_zero_iff (f : padic_seq p) : f.norm = 0 ↔ f ≈ 0 :=
begin
  constructor,
  { intro h,
    by_contradiction hf,
    unfold norm at h, split_ifs at h,
    apply hf,
    intros ε hε,
    existsi stationary_point hf,
    intros j hj,
    have heq := stationary_point_spec hf (le_refl _) hj,
    simpa [h, heq] },
  { intro h,
    simp [norm, h] }
end

end

section embedding
open cau_seq
variables {p : ℕ} [fact p.prime]

lemma equiv_zero_of_val_eq_of_equiv_zero {f g : padic_seq p}
  (h : ∀ k, padic_norm p (f k) = padic_norm p (g k)) (hf : f ≈ 0) : g ≈ 0 :=
λ ε hε, let ⟨i, hi⟩ := hf _ hε in
⟨i, λ j hj, by simpa [h] using hi _ hj⟩

lemma norm_nonzero_of_not_equiv_zero {f : padic_seq p} (hf : ¬ f ≈ 0) :
  f.norm ≠ 0 :=
hf ∘ f.norm_zero_iff.1

lemma norm_eq_norm_app_of_nonzero {f : padic_seq p} (hf : ¬ f ≈ 0) :
  ∃ k, f.norm = padic_norm p k ∧ k ≠ 0 :=
have heq : f.norm = padic_norm p (f $ stationary_point hf), by simp [norm, hf],
⟨f $ stationary_point hf, heq,
  λ h, norm_nonzero_of_not_equiv_zero hf (by simpa [h] using heq)⟩

lemma not_lim_zero_const_of_nonzero {q : ℚ} (hq : q ≠ 0) : ¬ lim_zero (const (padic_norm p) q) :=
λ h', hq $ const_lim_zero.1 h'

lemma not_equiv_zero_const_of_nonzero {q : ℚ} (hq : q ≠ 0) : ¬ (const (padic_norm p) q) ≈ 0 :=
λ h : lim_zero (const (padic_norm p) q - 0), not_lim_zero_const_of_nonzero hq $ by simpa using h

lemma norm_nonneg (f : padic_seq p) : f.norm ≥ 0 :=
if hf : f ≈ 0 then by simp [hf, norm]
else by simp [norm, hf, padic_norm.nonneg]

/-- An auxiliary lemma for manipulating sequence indices. -/
lemma lift_index_left_left {f : padic_seq p} (hf : ¬ f ≈ 0) (v2 v3 : ℕ) :
  padic_norm p (f (stationary_point hf)) =
    padic_norm p (f (max (stationary_point hf) (max v2 v3))) :=
let i := max (stationary_point hf) (max v2 v3) in
begin
  apply stationary_point_spec hf,
  { apply le_max_left },
  { apply le_refl }
end

/-- An auxiliary lemma for manipulating sequence indices. -/
lemma lift_index_left {f : padic_seq p} (hf : ¬ f ≈ 0) (v1 v3 : ℕ) :
  padic_norm p (f (stationary_point hf)) =
    padic_norm p (f (max v1 (max (stationary_point hf) v3))) :=
let i := max v1 (max (stationary_point hf) v3) in
begin
  apply stationary_point_spec hf,
  { apply le_trans,
    { apply le_max_left _ v3 },
    { apply le_max_right } },
  { apply le_refl }
end

/-- An auxiliary lemma for manipulating sequence indices. -/
lemma lift_index_right {f : padic_seq p} (hf : ¬ f ≈ 0) (v1 v2 : ℕ) :
  padic_norm p (f (stationary_point hf)) =
    padic_norm p (f (max v1 (max v2 (stationary_point hf)))) :=
let i := max v1 (max v2 (stationary_point hf)) in
begin
  apply stationary_point_spec hf,
  { apply le_trans,
    { apply le_max_right v2 },
    { apply le_max_right } },
  { apply le_refl }
end

end embedding

end padic_seq

section
open padic_seq

private meta def index_simp_core (hh hf hg : expr)
  (at_ : interactive.loc := interactive.loc.ns [none]) : tactic unit :=
do [v1, v2, v3] ← [hh, hf, hg].mmap
     (λ n, tactic.mk_app ``stationary_point [n] <|> return n),
   e1 ← tactic.mk_app ``lift_index_left_left [hh, v2, v3] <|> return `(true),
   e2 ← tactic.mk_app ``lift_index_left [hf, v1, v3] <|> return `(true),
   e3 ← tactic.mk_app ``lift_index_right [hg, v1, v2] <|> return `(true),
   sl ← [e1, e2, e3].mfoldl (λ s e, simp_lemmas.add s e) simp_lemmas.mk,
   when at_.include_goal (tactic.simp_target sl),
   hs ← at_.get_locals, hs.mmap' (tactic.simp_hyp sl [])

/--
  This is a special-purpose tactic that lifts padic_norm (f (stationary_point f)) to
  padic_norm (f (max _ _ _)).
-/
meta def tactic.interactive.padic_index_simp (l : interactive.parse interactive.types.pexpr_list)
  (at_ : interactive.parse interactive.types.location) : tactic unit :=
do [h, f, g] ← l.mmap tactic.i_to_expr,
   index_simp_core h f g at_
end

namespace padic_seq
section embedding

open cau_seq
variables {p : ℕ} [hp : fact p.prime]
include hp

lemma norm_mul (f g : padic_seq p) : (f * g).norm = f.norm * g.norm :=
if hf : f ≈ 0 then
  have hg : f * g ≈ 0, from mul_equiv_zero' _ hf,
  by simp [hf, hg, norm]
else if hg : g ≈ 0 then
  have hf : f * g ≈ 0, from mul_equiv_zero _ hg,
  by simp [hf, hg, norm]
else
  have hfg : ¬ f * g ≈ 0, by apply mul_not_equiv_zero; assumption,
  begin
    unfold norm,
    split_ifs,
    padic_index_simp [hfg, hf, hg],
    apply padic_norm.mul
  end

lemma eq_zero_iff_equiv_zero (f : padic_seq p) : mk f = 0 ↔ f ≈ 0 :=
mk_eq

lemma ne_zero_iff_nequiv_zero (f : padic_seq p) : mk f ≠ 0 ↔ ¬ f ≈ 0 :=
not_iff_not.2 (eq_zero_iff_equiv_zero _)

lemma norm_const (q : ℚ) : norm (const (padic_norm p) q) = padic_norm p q :=
if hq : q = 0 then
  have (const (padic_norm p) q) ≈ 0,
    by simp [hq]; apply setoid.refl (const (padic_norm p) 0),
  by subst hq; simp [norm, this]
else
  have ¬ (const (padic_norm p) q) ≈ 0, from not_equiv_zero_const_of_nonzero hq,
  by simp [norm, this]

lemma norm_image (a : padic_seq p) (ha : ¬ a ≈ 0) :
  (∃ (n : ℤ), a.norm = ↑p ^ (-n)) :=
let ⟨k, hk, hk'⟩ := norm_eq_norm_app_of_nonzero ha in
by simpa [hk] using padic_norm.image p hk'

lemma norm_one : norm (1 : padic_seq p) = 1 :=
have h1 : ¬ (1 : padic_seq p) ≈ 0, from one_not_equiv_zero _,
by simp [h1, norm, hp.one_lt]

private lemma norm_eq_of_equiv_aux {f g : padic_seq p} (hf : ¬ f ≈ 0) (hg : ¬ g ≈ 0) (hfg : f ≈ g)
  (h : padic_norm p (f (stationary_point hf)) ≠ padic_norm p (g (stationary_point hg)))
  (hgt : padic_norm p (f (stationary_point hf)) > padic_norm p (g (stationary_point hg))) :
  false :=
begin
  have hpn : padic_norm p (f (stationary_point hf)) - padic_norm p (g (stationary_point hg)) > 0,
    from sub_pos_of_lt hgt,
  cases hfg _ hpn with N hN,
  let i := max N (max (stationary_point hf) (stationary_point hg)),
  have hi : i ≥ N, from le_max_left _ _,
  have hN' := hN _ hi,
  padic_index_simp [N, hf, hg] at hN' h hgt,
  have hpne : padic_norm p (f i) ≠ padic_norm p (-(g i)),
    by rwa [ ←padic_norm.neg p (g i)] at h,
  let hpnem := add_eq_max_of_ne p hpne,
  have hpeq : padic_norm p ((f - g) i) = max (padic_norm p (f i)) (padic_norm p (g i)),
  { rwa padic_norm.neg at hpnem },
  rw [hpeq, max_eq_left_of_lt hgt] at hN',
  have : padic_norm p (f i) < padic_norm p (f i),
  { apply lt_of_lt_of_le hN', apply sub_le_self, apply padic_norm.nonneg },
  exact lt_irrefl _ this
end

private lemma norm_eq_of_equiv {f g : padic_seq p} (hf : ¬ f ≈ 0) (hg : ¬ g ≈ 0) (hfg : f ≈ g) :
  padic_norm p (f (stationary_point hf)) = padic_norm p (g (stationary_point hg)) :=
begin
  by_contradiction h,
  cases (decidable.em (padic_norm p (f (stationary_point hf)) >
          padic_norm p (g (stationary_point hg))))
      with hgt hngt,
  { exact norm_eq_of_equiv_aux hf hg hfg h hgt },
  { apply norm_eq_of_equiv_aux hg hf (setoid.symm hfg) (ne.symm h),
    apply lt_of_le_of_ne,
    apply le_of_not_gt hngt,
    apply h }
end

theorem norm_equiv {f g : padic_seq p} (hfg : f ≈ g) : f.norm = g.norm :=
if hf : f ≈ 0 then
  have hg : g ≈ 0, from setoid.trans (setoid.symm hfg) hf,
  by simp [norm, hf, hg]
else have hg : ¬ g ≈ 0, from hf ∘ setoid.trans hfg,
by unfold norm; split_ifs; exact norm_eq_of_equiv hf hg hfg

private lemma norm_nonarchimedean_aux {f g : padic_seq p}
  (hfg : ¬ f + g ≈ 0) (hf : ¬ f ≈ 0) (hg : ¬ g ≈ 0) : (f + g).norm ≤ max (f.norm) (g.norm) :=
begin
  unfold norm, split_ifs,
  padic_index_simp [hfg, hf, hg],
  apply padic_norm.nonarchimedean
end

theorem norm_nonarchimedean (f g : padic_seq p) : (f + g).norm ≤ max (f.norm) (g.norm) :=
if hfg : f + g ≈ 0 then
  have 0 ≤ max (f.norm) (g.norm), from le_max_left_of_le (norm_nonneg _),
  by simpa [hfg, norm]
else if hf : f ≈ 0 then
  have hfg' : f + g ≈ g,
  { change lim_zero (f - 0) at hf,
    show lim_zero (f + g - g), by simpa using hf },
  have hcfg : (f + g).norm = g.norm, from norm_equiv hfg',
  have hcl : f.norm = 0, from (norm_zero_iff f).2 hf,
  have max (f.norm) (g.norm) = g.norm,
    by rw hcl; exact max_eq_right (norm_nonneg _),
  by rw [this, hcfg]
else if hg : g ≈ 0 then
  have hfg' : f + g ≈ f,
  { change lim_zero (g - 0) at hg,
    show lim_zero (f + g - f), by  simpa [add_sub_cancel'] using hg },
  have hcfg : (f + g).norm = f.norm, from norm_equiv hfg',
  have hcl : g.norm = 0, from (norm_zero_iff g).2 hg,
  have max (f.norm) (g.norm) = f.norm,
    by rw hcl; exact max_eq_left (norm_nonneg _),
  by rw [this, hcfg]
else norm_nonarchimedean_aux hfg hf hg

lemma norm_eq {f g : padic_seq p} (h : ∀ k, padic_norm p (f k) = padic_norm p (g k)) :
  f.norm = g.norm :=
if hf : f ≈ 0 then
  have hg : g ≈ 0, from equiv_zero_of_val_eq_of_equiv_zero h hf,
  by simp [hf, hg, norm]
else
  have hg : ¬ g ≈ 0, from λ hg, hf $ equiv_zero_of_val_eq_of_equiv_zero (by simp [h]) hg,
  begin
    simp [hg, hf, norm],
    let i := max (stationary_point hf) (stationary_point hg),
    have hpf : padic_norm p (f (stationary_point hf)) = padic_norm p (f i),
    { apply stationary_point_spec, apply le_max_left, apply le_refl },
    have hpg : padic_norm p (g (stationary_point hg)) = padic_norm p (g i),
    { apply stationary_point_spec, apply le_max_right, apply le_refl },
    rw [hpf, hpg, h]
  end

lemma norm_neg (a : padic_seq p) : (-a).norm = a.norm :=
norm_eq $ by simp

lemma norm_eq_of_add_equiv_zero {f g : padic_seq p} (h : f + g ≈ 0) : f.norm = g.norm :=
have lim_zero (f + g - 0), from h,
have f ≈ -g, from show lim_zero (f - (-g)), by simpa,
have f.norm = (-g).norm, from norm_equiv this,
by simpa [norm_neg] using this

lemma add_eq_max_of_ne {f g : padic_seq p} (hfgne : f.norm ≠ g.norm) :
  (f + g).norm = max f.norm g.norm :=
have hfg : ¬f + g ≈ 0, from mt norm_eq_of_add_equiv_zero hfgne,
if hf : f ≈ 0 then
  have lim_zero (f - 0), from hf,
  have f + g ≈ g, from show lim_zero ((f + g) - g), by simpa,
  have h1 : (f+g).norm = g.norm, from norm_equiv this,
  have h2 : f.norm = 0, from (norm_zero_iff _).2 hf,
  by rw [h1, h2]; rw max_eq_right (norm_nonneg _)
else if hg : g ≈ 0 then
  have lim_zero (g - 0), from hg,
  have f + g ≈ f, from show lim_zero ((f + g) - f), by rw [add_sub_cancel']; simpa,
  have h1 : (f+g).norm = f.norm, from norm_equiv this,
  have h2 : g.norm = 0, from (norm_zero_iff _).2 hg,
  by rw [h1, h2]; rw max_eq_left (norm_nonneg _)
else
begin
  unfold norm at ⊢ hfgne, split_ifs at ⊢ hfgne,
  padic_index_simp [hfg, hf, hg] at ⊢ hfgne,
  apply padic_norm.add_eq_max_of_ne,
  simpa [hf, hg, norm] using hfgne
end

end embedding
end padic_seq

/-- The p-adic numbers `Q_[p]` are the Cauchy completion of `ℚ` with respect to the p-adic norm. -/
def padic (p : ℕ) [fact p.prime] := @cau_seq.completion.Cauchy _ _ _ _ (padic_norm p) _
notation `ℚ_[` p `]` := padic p

namespace padic

section completion
variables {p : ℕ} [fact p.prime]

/-- The discrete field structure on ℚ_p is inherited from the Cauchy completion construction. -/
instance field : field (ℚ_[p]) :=
cau_seq.completion.field

instance : inhabited ℚ_[p] := ⟨0⟩

-- short circuits

instance : has_zero ℚ_[p] := by apply_instance
instance : has_one ℚ_[p] := by apply_instance
instance : has_add ℚ_[p] := by apply_instance
instance : has_mul ℚ_[p] := by apply_instance
instance : has_sub ℚ_[p] := by apply_instance
instance : has_neg ℚ_[p] := by apply_instance
instance : has_div ℚ_[p] := by apply_instance
instance : add_comm_group ℚ_[p] := by apply_instance
instance : comm_ring ℚ_[p] := by apply_instance

/-- Builds the equivalence class of a Cauchy sequence of rationals. -/
def mk : padic_seq p → ℚ_[p] := quotient.mk
end completion

section completion
variables (p : ℕ) [fact p.prime]

lemma mk_eq {f g : padic_seq p} : mk f = mk g ↔ f ≈ g := quotient.eq

/-- Embeds the rational numbers in the p-adic numbers. -/
def of_rat : ℚ → ℚ_[p] := cau_seq.completion.of_rat

@[simp] lemma of_rat_add : ∀ (x y : ℚ), of_rat p (x + y) = of_rat p x + of_rat p y :=
cau_seq.completion.of_rat_add

@[simp] lemma of_rat_neg : ∀ (x : ℚ), of_rat p (-x) = -of_rat p x :=
cau_seq.completion.of_rat_neg

@[simp] lemma of_rat_mul : ∀ (x y : ℚ), of_rat p (x * y) = of_rat p x * of_rat p y :=
cau_seq.completion.of_rat_mul

@[simp] lemma of_rat_sub : ∀ (x y : ℚ), of_rat p (x - y) = of_rat p x - of_rat p y :=
cau_seq.completion.of_rat_sub

@[simp] lemma of_rat_div : ∀ (x y : ℚ), of_rat p (x / y) = of_rat p x / of_rat p y :=
cau_seq.completion.of_rat_div

@[simp] lemma of_rat_one : of_rat p 1 = 1 := rfl

@[simp] lemma of_rat_zero : of_rat p 0 = 0 := rfl

@[simp] lemma cast_eq_of_rat_of_nat (n : ℕ) : (↑n : ℚ_[p]) = of_rat p n :=
begin
  induction n with n ih,
  { refl },
  { simpa using ih }
end

@[simp] lemma cast_eq_of_rat_of_int (n : ℤ) : ↑n = of_rat p n :=
by induction n; simp

lemma cast_eq_of_rat : ∀ (q : ℚ), (↑q : ℚ_[p]) = of_rat p q
| ⟨n, d, h1, h2⟩ :=
  show ↑n / ↑d = _, from
    have (⟨n, d, h1, h2⟩ : ℚ) = rat.mk n d, from rat.num_denom',
    by simp [this, rat.mk_eq_div, of_rat_div]

@[norm_cast] lemma coe_add : ∀ {x y : ℚ}, (↑(x + y) : ℚ_[p]) = ↑x + ↑y := by simp [cast_eq_of_rat]
@[norm_cast] lemma coe_neg : ∀ {x : ℚ}, (↑(-x) : ℚ_[p]) = -↑x := by simp [cast_eq_of_rat]
@[norm_cast] lemma coe_mul : ∀ {x y : ℚ}, (↑(x * y) : ℚ_[p]) = ↑x * ↑y := by simp [cast_eq_of_rat]
@[norm_cast] lemma coe_sub : ∀ {x y : ℚ}, (↑(x - y) : ℚ_[p]) = ↑x - ↑y := by simp [cast_eq_of_rat]
@[norm_cast] lemma coe_div : ∀ {x y : ℚ}, (↑(x / y) : ℚ_[p]) = ↑x / ↑y := by simp [cast_eq_of_rat]

@[norm_cast] lemma coe_one : (↑1 : ℚ_[p]) = 1 := rfl
@[norm_cast] lemma coe_zero : (↑0 : ℚ_[p]) = 0 := rfl

lemma const_equiv {q r : ℚ} : const (padic_norm p) q ≈ const (padic_norm p) r ↔ q = r :=
⟨ λ heq : lim_zero (const (padic_norm p) (q - r)),
    eq_of_sub_eq_zero $ const_lim_zero.1 heq,
  λ heq, by rw heq; apply setoid.refl _ ⟩

lemma of_rat_eq {q r : ℚ} : of_rat p q = of_rat p r ↔ q = r :=
⟨(const_equiv p).1 ∘ quotient.eq.1, λ h, by rw h⟩

@[norm_cast] lemma coe_inj {q r : ℚ} : (↑q : ℚ_[p]) = ↑r ↔ q = r :=
by simp [cast_eq_of_rat, of_rat_eq]

instance : char_zero ℚ_[p] :=
⟨λ m n, by { rw ← rat.cast_coe_nat, norm_cast, exact id }⟩

end completion
end padic

/-- The rational-valued p-adic norm on ℚ_p is lifted from the norm on Cauchy sequences. The
canonical form of this function is the normed space instance, with notation `∥ ∥`. -/
def padic_norm_e {p : ℕ} [hp : fact p.prime] : ℚ_[p] → ℚ :=
quotient.lift padic_seq.norm $ @padic_seq.norm_equiv _ _

namespace padic_norm_e
section embedding
open padic_seq
variables {p : ℕ} [fact p.prime]

lemma defn (f : padic_seq p) {ε : ℚ} (hε : ε > 0) : ∃ N, ∀ i ≥ N, padic_norm_e (⟦f⟧ - f i) < ε :=
begin
  simp only [padic.cast_eq_of_rat],
  change ∃ N, ∀ i ≥ N, (f - const _ (f i)).norm < ε,
  by_contradiction h,
  cases cauchy₂ f hε with N hN,
  have : ∀ N, ∃ i ≥ N, (f - const _ (f i)).norm ≥ ε,
    by simpa [not_forall] using h,
  rcases this N with ⟨i, hi, hge⟩,
  have hne : ¬ (f - const (padic_norm p) (f i)) ≈ 0,
  { intro h, unfold padic_seq.norm at hge; split_ifs at hge, exact not_lt_of_ge hge hε },
  unfold padic_seq.norm at hge; split_ifs at hge,
  apply not_le_of_gt _ hge,
  cases decidable.em ((stationary_point hne) ≥ N) with hgen hngen,
  { apply hN; assumption },
  { have := stationary_point_spec hne (le_refl _) (le_of_not_le hngen),
    rw ←this,
    apply hN,
    apply le_refl, assumption }
end

protected lemma nonneg (q : ℚ_[p]) : padic_norm_e q ≥ 0 :=
quotient.induction_on q $ norm_nonneg

lemma zero_def : (0 : ℚ_[p]) = ⟦0⟧ := rfl

lemma zero_iff (q : ℚ_[p]) : padic_norm_e q = 0 ↔ q = 0 :=
quotient.induction_on q $
  by simpa only [zero_def, quotient.eq] using norm_zero_iff

@[simp] protected lemma zero : padic_norm_e (0 : ℚ_[p]) = 0 :=
(zero_iff _).2 rfl

/-- Theorems about `padic_norm_e` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`∥ ∥`). -/
@[simp] protected lemma one' : padic_norm_e (1 : ℚ_[p]) = 1 :=
norm_one

@[simp] protected lemma neg (q : ℚ_[p]) : padic_norm_e (-q) = padic_norm_e q :=
quotient.induction_on q $ norm_neg

/-- Theorems about `padic_norm_e` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`∥ ∥`). -/
theorem nonarchimedean' (q r : ℚ_[p]) :
  padic_norm_e (q + r) ≤ max (padic_norm_e q) (padic_norm_e r) :=
quotient.induction_on₂ q r $ norm_nonarchimedean

/-- Theorems about `padic_norm_e` are named with a `'` so the names do not conflict with the
equivalent theorems about `norm` (`∥ ∥`). -/
theorem add_eq_max_of_ne' {q r : ℚ_[p]} :
  padic_norm_e q ≠ padic_norm_e r → padic_norm_e (q + r) = max (padic_norm_e q) (padic_norm_e r) :=
quotient.induction_on₂ q r $ λ _ _, padic_seq.add_eq_max_of_ne

lemma triangle_ineq (x y z : ℚ_[p]) :
  padic_norm_e (x - z) ≤ padic_norm_e (x - y) + padic_norm_e (y - z) :=
calc padic_norm_e (x - z) = padic_norm_e ((x - y) + (y - z)) : by rw sub_add_sub_cancel
  ... ≤ max (padic_norm_e (x - y)) (padic_norm_e (y - z)) : padic_norm_e.nonarchimedean' _ _
  ... ≤ padic_norm_e (x - y) + padic_norm_e (y - z) :
    max_le_add_of_nonneg (padic_norm_e.nonneg _) (padic_norm_e.nonneg _)

protected lemma add (q r : ℚ_[p]) : padic_norm_e (q + r) ≤ (padic_norm_e q) + (padic_norm_e r) :=
calc
  padic_norm_e (q + r) ≤ max (padic_norm_e q) (padic_norm_e r) : nonarchimedean' _ _
                      ... ≤ (padic_norm_e q) + (padic_norm_e r) :
                              max_le_add_of_nonneg (padic_norm_e.nonneg _) (padic_norm_e.nonneg _)

protected lemma mul' (q r : ℚ_[p]) : padic_norm_e (q * r) = (padic_norm_e q) * (padic_norm_e r) :=
quotient.induction_on₂ q r $ norm_mul

instance : is_absolute_value (@padic_norm_e p _) :=
{ abv_nonneg := padic_norm_e.nonneg,
  abv_eq_zero := zero_iff,
  abv_add := padic_norm_e.add,
  abv_mul := padic_norm_e.mul' }

@[simp] lemma eq_padic_norm' (q : ℚ) : padic_norm_e (padic.of_rat p q) = padic_norm p q :=
norm_const _

protected theorem image' {q : ℚ_[p]} : q ≠ 0 → ∃ n : ℤ, padic_norm_e q = p ^ (-n) :=
quotient.induction_on q $ λ f hf,
  have ¬ f ≈ 0, from (ne_zero_iff_nequiv_zero f).1 hf,
  norm_image f this

lemma sub_rev (q r : ℚ_[p]) : padic_norm_e (q - r) = padic_norm_e (r - q) :=
by rw ←(padic_norm_e.neg); simp

end embedding
end padic_norm_e

namespace padic

section complete
open padic_seq padic

theorem rat_dense' {p : ℕ} [fact p.prime] (q : ℚ_[p]) {ε : ℚ} (hε : ε > 0) :
  ∃ r : ℚ, padic_norm_e (q - r) < ε :=
quotient.induction_on q $ λ q',
  have ∃ N, ∀ m n ≥ N, padic_norm p (q' m - q' n) < ε, from cauchy₂ _ hε,
  let ⟨N, hN⟩ := this in
  ⟨q' N,
    begin
      simp only [padic.cast_eq_of_rat],
      change padic_seq.norm (q' - const _ (q' N)) < ε,
      cases decidable.em ((q' - const (padic_norm p) (q' N)) ≈ 0) with heq hne',
      { simpa only [heq, padic_seq.norm, dif_pos] },
      { simp only [padic_seq.norm, dif_neg hne'],
        change padic_norm p (q' _ - q' _) < ε,
        have := stationary_point_spec hne',
        cases decidable.em (N ≥ stationary_point hne') with hle hle,
        { have := eq.symm (this (le_refl _) hle),
          simp at this, simpa [this] },
        { apply hN,
          apply le_of_lt, apply lt_of_not_ge, apply hle, apply le_refl }}
    end⟩

variables {p : ℕ} [fact p.prime] (f : cau_seq _ (@padic_norm_e p _))
open classical

private lemma div_nat_pos (n : ℕ) : (1 / ((n + 1): ℚ)) > 0 :=
div_pos zero_lt_one (by exact_mod_cast succ_pos _)

def lim_seq : ℕ → ℚ := λ n, classical.some (rat_dense' (f n) (div_nat_pos n))

lemma exi_rat_seq_conv {ε : ℚ} (hε : 0 < ε) :
  ∃ N, ∀ i ≥ N, padic_norm_e (f i - ((lim_seq f) i : ℚ_[p])) < ε :=
begin
  refine (exists_nat_gt (1/ε)).imp (λ N hN i hi, _),
  have h := classical.some_spec (rat_dense' (f i) (div_nat_pos i)),
  refine lt_of_lt_of_le h (div_le_of_le_mul (by exact_mod_cast succ_pos _) _),
  rw right_distrib,
  apply le_add_of_le_of_nonneg,
  { exact le_mul_of_div_le hε (le_trans (le_of_lt hN) (by exact_mod_cast hi)) },
  { apply le_of_lt, simpa }
end

lemma exi_rat_seq_conv_cauchy : is_cau_seq (padic_norm p) (lim_seq f) :=
assume ε hε,
have hε3 : ε / 3 > 0, from div_pos hε (by norm_num),
let ⟨N, hN⟩ := exi_rat_seq_conv f hε3,
    ⟨N2, hN2⟩ := f.cauchy₂ hε3 in
begin
  existsi max N N2,
  intros j hj,
  suffices : padic_norm_e ((↑(lim_seq f j) - f (max N N2)) + (f (max N N2) - lim_seq f (max N N2))) < ε,
  { ring at this ⊢,
    rw [← padic_norm_e.eq_padic_norm', ← padic.cast_eq_of_rat],
    exact_mod_cast this },
  { apply lt_of_le_of_lt,
    { apply padic_norm_e.add },
    { have : (3 : ℚ) ≠ 0, by norm_num,
      have : ε = ε / 3 + ε / 3 + ε / 3,
      { field_simp [this], simp [bit0, bit1, mul_add] },
      rw this,
      apply add_lt_add,
      { suffices : padic_norm_e ((↑(lim_seq f j) - f j) + (f j - f (max N N2))) < ε / 3 + ε / 3,
          by simpa [sub_add_sub_cancel],
        apply lt_of_le_of_lt,
        { apply padic_norm_e.add },
        { apply add_lt_add,
          { rw [padic_norm_e.sub_rev],
            apply_mod_cast hN,
            exact le_of_max_le_left hj },
          { apply hN2,
            exact le_of_max_le_right hj,
            apply le_max_right }}},
      { apply_mod_cast hN,
        apply le_max_left }}}
end

private def lim' : padic_seq p := ⟨_, exi_rat_seq_conv_cauchy f⟩

private def lim : ℚ_[p] := ⟦lim' f⟧

theorem complete' : ∃ q : ℚ_[p], ∀ ε > 0, ∃ N, ∀ i ≥ N, padic_norm_e (q - f i) < ε :=
⟨ lim f,
  λ ε hε,
  let ⟨N, hN⟩ := exi_rat_seq_conv f (show ε / 2 > 0, from div_pos hε (by norm_num)),
      ⟨N2, hN2⟩ := padic_norm_e.defn (lim' f) (show ε / 2 > 0, from div_pos hε (by norm_num)) in
  begin
    existsi max N N2,
    intros i hi,
    suffices : padic_norm_e ((lim f - lim' f i) + (lim' f i - f i)) < ε,
    { ring at this; exact this },
    { apply lt_of_le_of_lt,
      { apply padic_norm_e.add },
      { have : ε = ε / 2 + ε / 2, by rw ←(add_self_div_two ε); simp,
        rw this,
        apply add_lt_add,
        { apply hN2, exact le_of_max_le_right hi },
        { rw_mod_cast [padic_norm_e.sub_rev],
          apply hN,
          exact le_of_max_le_left hi }}}
  end ⟩

end complete

section normed_space
variables (p : ℕ) [fact p.prime]

instance : has_dist ℚ_[p] := ⟨λ x y, padic_norm_e (x - y)⟩

instance : metric_space ℚ_[p] :=
{ dist_self := by simp [dist],
  dist_comm := λ x y, by unfold dist; rw ←padic_norm_e.neg (x - y); simp,
  dist_triangle :=
    begin
      intros, unfold dist,
      exact_mod_cast padic_norm_e.triangle_ineq _ _ _,
    end,
  eq_of_dist_eq_zero :=
    begin
      unfold dist, intros _ _ h,
      apply eq_of_sub_eq_zero,
      apply (padic_norm_e.zero_iff _).1,
      exact_mod_cast h
    end }

instance : has_norm ℚ_[p] := ⟨λ x, padic_norm_e x⟩

instance : normed_field ℚ_[p] :=
{ dist_eq := λ _ _, rfl,
  norm_mul' := by simp [has_norm.norm, padic_norm_e.mul'] }

instance : is_absolute_value (λ a : ℚ_[p], ∥a∥) :=
{ abv_nonneg := norm_nonneg,
  abv_eq_zero := λ _, norm_eq_zero,
  abv_add := norm_add_le,
  abv_mul := by simp [has_norm.norm, padic_norm_e.mul'] }

theorem rat_dense {p : ℕ} {hp : fact p.prime} (q : ℚ_[p]) {ε : ℝ} (hε : ε > 0) :
        ∃ r : ℚ, ∥q - r∥ < ε :=
let ⟨ε', hε'l, hε'r⟩ := exists_rat_btwn hε,
    ⟨r, hr⟩ := rat_dense' q (by simpa using hε'l)  in
⟨r, lt.trans (by simpa [has_norm.norm] using hr) hε'r⟩

end normed_space
end padic

namespace padic_norm_e
section normed_space
variables {p : ℕ} [hp : fact p.prime]
include hp

@[simp] protected lemma mul (q r : ℚ_[p]) : ∥q * r∥ = ∥q∥ * ∥r∥ :=
by simp [has_norm.norm, padic_norm_e.mul']

protected lemma is_norm (q : ℚ_[p]) : ↑(padic_norm_e q) = ∥q∥ := rfl

theorem nonarchimedean (q r : ℚ_[p]) : ∥q + r∥ ≤ max (∥q∥) (∥r∥) :=
begin
  unfold has_norm.norm,
  exact_mod_cast nonarchimedean' _ _
end

theorem add_eq_max_of_ne {q r : ℚ_[p]} (h : ∥q∥ ≠ ∥r∥) : ∥q+r∥ = max (∥q∥) (∥r∥) :=
begin
  unfold has_norm.norm,
  apply_mod_cast add_eq_max_of_ne',
  intro h',
  apply h,
  unfold has_norm.norm,
  exact_mod_cast h'
end

@[simp] lemma eq_padic_norm (q : ℚ) : ∥(↑q : ℚ_[p])∥ = padic_norm p q :=
begin
  unfold has_norm.norm,
  rw [← padic_norm_e.eq_padic_norm', ← padic.cast_eq_of_rat]
end

instance : nondiscrete_normed_field ℚ_[p] :=
{ non_trivial := ⟨padic.of_rat p (p⁻¹), begin
    have h0 : p ≠ 0 := ne_of_gt (hp.pos),
    have h1 : 1 < p := hp.one_lt,
    rw [← padic.cast_eq_of_rat, eq_padic_norm],
    simp only [padic_norm, inv_eq_zero],
    simp only [if_neg] {discharger := `[exact_mod_cast h0]},
    norm_cast,
    simp only [padic_val_rat.inv] {discharger := `[exact_mod_cast h0]},
    rw [neg_neg, padic_val_rat.padic_val_rat_self h1],
    erw _root_.pow_one,
    exact_mod_cast h1,
  end⟩ }


protected theorem image {q : ℚ_[p]} : q ≠ 0 → ∃ n : ℤ, ∥q∥ = ↑((↑p : ℚ) ^ (-n)) :=
quotient.induction_on q $ λ f hf,
  have ¬ f ≈ 0, from (padic_seq.ne_zero_iff_nequiv_zero f).1 hf,
  let ⟨n, hn⟩ := padic_seq.norm_image f this in
  ⟨n, congr_arg coe hn⟩

protected lemma is_rat (q : ℚ_[p]) : ∃ q' : ℚ, ∥q∥ = ↑q' :=
if h : q = 0 then ⟨0, by simp [h]⟩
else let ⟨n, hn⟩ := padic_norm_e.image h in ⟨_, hn⟩

def rat_norm (q : ℚ_[p]) : ℚ := classical.some (padic_norm_e.is_rat q)

lemma eq_rat_norm (q : ℚ_[p]) : ∥q∥ = rat_norm q := classical.some_spec (padic_norm_e.is_rat q)

theorem norm_rat_le_one : ∀ {q : ℚ} (hq : ¬ p ∣ q.denom), ∥(q : ℚ_[p])∥ ≤ 1
| ⟨n, d, hn, hd⟩ := λ hq : ¬ p ∣ d,
  if hnz : n = 0 then
    have (⟨n, d, hn, hd⟩ : ℚ) = 0,
    from rat.zero_iff_num_zero.mpr hnz,
    by norm_num [this]
  else
    begin
      have hnz' : {rat . num := n, denom := d, pos := hn, cop := hd} ≠ 0, from mt rat.zero_iff_num_zero.1 hnz,
      rw [padic_norm_e.eq_padic_norm],
      norm_cast,
      rw [padic_norm.eq_fpow_of_nonzero p hnz', padic_val_rat_def p hnz'],
      have h : (multiplicity p d).get _ = 0, by simp [multiplicity_eq_zero_of_not_dvd, hq],
      simp only, norm_cast,
      rw_mod_cast [h, sub_zero],
      apply fpow_le_one_of_nonpos,
      { exact_mod_cast le_of_lt hp.one_lt, },
      { apply neg_nonpos_of_nonneg, norm_cast, simp, }
    end

lemma eq_of_norm_add_lt_right {p : ℕ} {hp : fact p.prime} {z1 z2 : ℚ_[p]}
  (h : ∥z1 + z2∥ < ∥z2∥) : ∥z1∥ = ∥z2∥ :=
by_contradiction $ λ hne,
  not_lt_of_ge (by rw padic_norm_e.add_eq_max_of_ne hne; apply le_max_right) h

lemma eq_of_norm_add_lt_left {p : ℕ} {hp : fact p.prime} {z1 z2 : ℚ_[p]}
  (h : ∥z1 + z2∥ < ∥z1∥) : ∥z1∥ = ∥z2∥ :=
by_contradiction $ λ hne,
  not_lt_of_ge (by rw padic_norm_e.add_eq_max_of_ne hne; apply le_max_left) h

end normed_space
end padic_norm_e

namespace padic
variables {p : ℕ} [fact p.prime]

set_option eqn_compiler.zeta true
instance complete : cau_seq.is_complete ℚ_[p] norm :=
begin
  split, intro f,
  have cau_seq_norm_e : is_cau_seq padic_norm_e f,
  { intros ε hε,
    let h := is_cau f ε (by exact_mod_cast hε),
    unfold norm at h,
    apply_mod_cast h },
  cases padic.complete' ⟨f, cau_seq_norm_e⟩ with q hq,
  existsi q,
  intros ε hε,
  cases exists_rat_btwn hε with ε' hε',
  norm_cast at hε',
  cases hq ε' hε'.1 with N hN, existsi N,
  intros i hi, let h := hN i hi,
  unfold norm,
  rw_mod_cast [cau_seq.sub_apply, padic_norm_e.sub_rev],
  refine lt.trans _ hε'.2,
  exact_mod_cast hN i hi
end

lemma padic_norm_e_lim_le {f : cau_seq ℚ_[p] norm} {a : ℝ} (ha : a > 0)
      (hf : ∀ i, ∥f i∥ ≤ a) : ∥f.lim∥ ≤ a :=
let ⟨N, hN⟩ := setoid.symm (cau_seq.equiv_lim f) _ ha in
calc ∥f.lim∥ = ∥f.lim - f N + f N∥ : by simp
                ... ≤ max (∥f.lim - f N∥) (∥f N∥) : padic_norm_e.nonarchimedean _ _
                ... ≤ a : max_le (le_of_lt (hN _ (le_refl _))) (hf _)

end padic
