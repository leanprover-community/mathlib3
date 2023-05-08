/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge
-/
import group_theory.monoid_localization
import ring_theory.non_zero_divisors
import ring_theory.ore_localization.ore_set
import tactic.noncomm_ring

/-!

# Localization over right Ore sets.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the localization of a monoid over a right Ore set and proves its universal
mapping property. It then extends the definition and its properties first to semirings and then
to rings. We show that in the case of a commutative monoid this definition coincides with the
common monoid localization. Finally we show that in a ring without zero divisors, taking the Ore
localization at `R - {0}` results in a division ring.

## Notations

Introduces the notation `R[S⁻¹]` for the Ore localization of a monoid `R` at a right Ore
subset `S`. Also defines a new heterogeneos division notation `r /ₒ s` for a numerator `r : R` and
a denominator `s : S`.

## References

* <https://ncatlab.org/nlab/show/Ore+localization>
* [Zoran Škoda, *Noncommutative localization in noncommutative geometry*][skoda2006]


## Tags
localization, Ore, non-commutative

-/

universe u

open ore_localization

namespace ore_localization

variables (R : Type*) [monoid R] (S : submonoid R) [ore_set S]

/-- The setoid on `R × S` used for the Ore localization. -/
def ore_eqv : setoid (R × S) :=
{ r := λ rs rs', ∃ (u : S) (v : R), rs'.1 * u = rs.1 * v
                            ∧ (rs'.2 : R) * u = rs.2 * v,
  iseqv :=
  begin
    refine ⟨_, _, _⟩,
    { rintro ⟨r,s⟩, use 1, use 1, simp [submonoid.one_mem] },
    { rintros ⟨r, s⟩ ⟨r', s'⟩ ⟨u, v, hru, hsu⟩,
      rcases ore_condition (s : R) s' with ⟨r₂, s₂, h₁⟩,
      rcases ore_condition r₂ u with ⟨r₃, s₃, h₂⟩,
      have : (s : R) * ((v : R) * r₃) = (s : R) * (s₂ * s₃),
      { assoc_rw [h₁, h₂, hsu], symmetry, apply mul_assoc },
      rcases ore_left_cancel (v * r₃) (s₂ * s₃) s this with ⟨w, hw⟩,
      use s₂ * s₃ * w, use u * r₃ * w, split; simp only [submonoid.coe_mul],
      { assoc_rw [hru, ←hw], simp [mul_assoc] },
      { assoc_rw [hsu, ←hw], simp [mul_assoc] } },
    { rintros ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨r₃, s₃⟩ ⟨u, v, hur₁, hs₁u⟩ ⟨u', v', hur₂, hs₂u⟩,
      rcases ore_condition v' u with ⟨r', s', h⟩,
      use u' * s', use v * r', split; simp only [submonoid.coe_mul],
      { assoc_rw [hur₂, h, hur₁, mul_assoc] },
      { assoc_rw [hs₂u, h, hs₁u, mul_assoc] } }
  end }

end ore_localization

/-- The ore localization of a monoid and a submonoid fulfilling the ore condition. -/
def ore_localization (R : Type*) [monoid R] (S : submonoid R) [ore_set S] :=
quotient (ore_localization.ore_eqv R S)

namespace ore_localization

section monoid

variables {R : Type*} [monoid R] {S : submonoid R}

variables (R S) [ore_set S]

notation R `[`:1075 S `⁻¹]`:1075 := ore_localization R S

local attribute [instance] ore_eqv

variables {R S}

/-- The division in the ore localization `R[S⁻¹]`, as a fraction of an element of `R` and `S`. -/
def ore_div (r : R) (s : S) : R[S⁻¹] := quotient.mk (r, s)

infixl ` /ₒ `:70 := ore_div

@[elab_as_eliminator]
protected lemma ind {β : R [S ⁻¹] → Prop} (c : ∀ (r : R) (s : S), β (r /ₒ s)) : ∀ q, β q :=
by { apply quotient.ind, rintro ⟨r, s⟩, exact c r s }

lemma ore_div_eq_iff {r₁ r₂ : R} {s₁ s₂ : S} :
  r₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ (∃ (u : S) (v : R), r₂ * u = r₁ * v ∧ (s₂ : R) * u = s₁ * v) :=
quotient.eq'

/-- A fraction `r /ₒ s` is equal to its expansion by an arbitrary factor `t` if `s * t ∈ S`. -/
protected lemma expand (r : R) (s : S) (t : R) (hst : (s : R) * t ∈ S) :
  r /ₒ s = (r * t) /ₒ (⟨s * t, hst⟩) :=
by { apply quotient.sound, refine ⟨s, t * s, _, _⟩; dsimp; rw [mul_assoc]; refl }

/-- A fraction is equal to its expansion by an factor from s. -/
protected lemma expand' (r : R) (s s' : S) : r /ₒ s = (r * s') /ₒ (s * s') :=
ore_localization.expand r s s' (by norm_cast; apply set_like.coe_mem)

/-- Fractions which differ by a factor of the numerator can be proven equal if
those factors expand to equal elements of `R`. -/
protected lemma eq_of_num_factor_eq {r r' r₁ r₂ : R} {s t : S}
  (h : r * t = r' * t) : (r₁ * r * r₂) /ₒ s = (r₁ * r' * r₂) /ₒ s :=
begin
  rcases ore_condition r₂ t with ⟨r₂',t', hr₂⟩,
  calc (r₁ * r * r₂) /ₒ s = (r₁ * r * r₂ * t') /ₒ (s * t') : ore_localization.expand _ _ t' _
  ...                     = ((r₁ * r) * (r₂ * t')) /ₒ (s * t') : by simp [←mul_assoc]
  ...                     = ((r₁ * r) * (t * r₂')) /ₒ (s * t') : by rw hr₂
  ...                     = (r₁ * (r * t) * r₂') /ₒ (s * t') : by simp [←mul_assoc]
  ...                     = (r₁ * (r' * t) * r₂') /ₒ (s * t') : by rw h
  ...                     = (r₁ * r' * (t * r₂')) /ₒ (s * t') : by simp [←mul_assoc]
  ...                     = (r₁ * r' * (r₂ * t')) /ₒ (s * t') : by rw hr₂
  ...                     = (r₁ * r' * r₂ * t') /ₒ (s * t') : by simp [←mul_assoc]
  ...                     = (r₁ * r' * r₂) /ₒ s : by symmetry; apply ore_localization.expand
end

/-- A function or predicate over `R` and `S` can be lifted to `R[S⁻¹]` if it is invariant
under expansion on the right. -/
def lift_expand {C : Sort*} (P : R → S → C)
  (hP : ∀ (r t : R) (s : S) (ht : ((s : R) * t) ∈ S), P r s = P (r * t) ⟨s * t, ht⟩) :
  R[S⁻¹] → C :=
quotient.lift (λ (p : R × S), P p.1 p.2) $ λ p q pq,
begin
  cases p with r₁ s₁, cases q with r₂ s₂, rcases pq with ⟨u, v, hr₂, hs₂⟩,
  dsimp at *,
  have s₁vS : (s₁ : R) * v ∈ S,
  { rw [←hs₂, ←S.coe_mul], exact set_like.coe_mem (s₂ * u) },
  replace hs₂ : s₂ * u = ⟨(s₁ : R) * v, s₁vS⟩, { ext, simp [hs₂] },
  rw [hP r₁ v s₁ s₁vS, hP r₂ u s₂ (by { norm_cast, rw hs₂, assumption }), hr₂],
  simpa [← hs₂]
end

@[simp]
lemma lift_expand_of {C : Sort*} {P : R → S → C}
  {hP : ∀ (r t : R) (s : S) (ht : ((s : R) * t) ∈ S), P r s = P (r * t) ⟨s * t, ht⟩}
  (r : R) (s : S) :
  lift_expand P hP (r /ₒ s) = P r s := rfl

/-- A version of `lift_expand` used to simultaneously lift functions with two arguments
in ``R[S⁻¹]`.-/
def lift₂_expand {C : Sort*} (P : R → S → R → S → C)
  (hP : ∀ (r₁ t₁ : R) (s₁ : S) (ht₁ : (s₁ : R) * t₁ ∈ S)
          (r₂ t₂ : R) (s₂ : S) (ht₂ : (s₂ : R) * t₂ ∈ S),
    P r₁ s₁ r₂ s₂ = P (r₁ * t₁) ⟨s₁ * t₁, ht₁⟩ (r₂ * t₂) ⟨s₂ * t₂, ht₂⟩) : R[S⁻¹] → R[S⁻¹] → C :=
lift_expand
  (λ r₁ s₁, lift_expand (P r₁ s₁) $ λ r₂ t₂ s₂ ht₂, by simp [hP r₁ 1 s₁ (by simp) r₂ t₂ s₂ ht₂]) $
   λ r₁ t₁ s₁ ht₁,
   begin
     ext x, induction x using ore_localization.ind with r₂ s₂,
     rw [lift_expand_of, lift_expand_of, hP r₁ t₁ s₁ ht₁ r₂ 1 s₂ (by simp)], simp,
   end

@[simp]
lemma lift₂_expand_of {C : Sort*} {P : R → S → R → S → C}
  {hP : ∀ (r₁ t₁ : R) (s₁ : S) (ht₁ : (s₁ : R) * t₁ ∈ S)
          (r₂ t₂ : R) (s₂ : S) (ht₂ : (s₂ : R) * t₂ ∈ S),
    P r₁ s₁ r₂ s₂ = P (r₁ * t₁) ⟨s₁ * t₁, ht₁⟩ (r₂ * t₂) ⟨s₂ * t₂, ht₂⟩}
  (r₁ : R) (s₁ : S) (r₂ : R) (s₂ : S) :
  lift₂_expand P hP (r₁ /ₒ s₁) (r₂ /ₒ s₂) = P r₁ s₁ r₂ s₂ :=
rfl

private def mul' (r₁ : R) (s₁ : S) (r₂ : R) (s₂ : S) : R[S⁻¹] :=
  (r₁ * ore_num r₂ s₁) /ₒ (s₂ * ore_denom r₂ s₁)

private lemma mul'_char (r₁ r₂ : R) (s₁ s₂ : S) (u : S) (v : R) (huv : r₂ * (u : R) = s₁ * v) :
  mul' r₁ s₁ r₂ s₂ = (r₁ * v) /ₒ (s₂ * u) :=
begin
  simp only [mul'],
  have h₀ := ore_eq r₂ s₁, set v₀ := ore_num r₂ s₁, set u₀ := ore_denom r₂ s₁,
  rcases ore_condition (u₀ : R) u with ⟨r₃, s₃, h₃⟩,
  have :=
  calc (s₁ : R) * (v * r₃) = r₂ * u * r₃ : by assoc_rw ←huv; symmetry; apply mul_assoc
  ...                      = r₂ * u₀ * s₃ : by assoc_rw ←h₃; refl
  ...                      = s₁ * (v₀ * s₃) : by assoc_rw h₀; apply mul_assoc,
  rcases ore_left_cancel _ _ _ this with ⟨s₄, hs₄⟩,
  symmetry, rw ore_div_eq_iff,
  use s₃ * s₄, use r₃ * s₄, simp only [submonoid.coe_mul], split,
  { assoc_rw ←hs₄, simp only [mul_assoc] },
  { assoc_rw h₃, simp only [mul_assoc] }
end

/-- The multiplication on the Ore localization of monoids. -/
protected def mul : R[S⁻¹] → R[S⁻¹] → R[S⁻¹] :=
lift₂_expand mul' $ λ r₂ p s₂ hp r₁ r s₁ hr,
begin
  have h₁ := ore_eq r₁ s₂, set r₁' := ore_num r₁ s₂, set s₂' := ore_denom r₁ s₂,
  rcases ore_condition (↑s₂ * r₁') ⟨s₂ * p, hp⟩ with ⟨p', s_star, h₂⟩, dsimp at h₂,
  rcases ore_condition r (s₂' * s_star) with ⟨p_flat, s_flat, h₃⟩, simp only [S.coe_mul] at h₃,
  have : r₁ * r * s_flat = s₂ * p * (p' * p_flat),
  { rw [←mul_assoc, ←h₂, ←h₁, mul_assoc, h₃], simp only [mul_assoc] },
  rw mul'_char (r₂ * p) (r₁ * r) ⟨↑s₂ * p, hp⟩ ⟨↑s₁ * r, hr⟩ _ _ this, clear this,
  have hsssp : ↑s₁ * ↑s₂' * ↑s_star * p_flat ∈ S,
  { rw [mul_assoc, mul_assoc, ←mul_assoc ↑s₂', ←h₃, ←mul_assoc],
    exact S.mul_mem hr (set_like.coe_mem s_flat) },
  have : (⟨↑s₁ * r, hr⟩ : S) * s_flat = ⟨s₁ * s₂' * s_star * p_flat, hsssp⟩,
  { ext, simp only [set_like.coe_mk, submonoid.coe_mul],
    rw [mul_assoc, h₃, ←mul_assoc, ←mul_assoc] },
  rw this, clear this,
  rcases ore_left_cancel (p * p') (r₁' * ↑s_star) s₂ (by simp [←mul_assoc, h₂]) with ⟨s₂'', h₂''⟩,
  rw [←mul_assoc, mul_assoc r₂, ore_localization.eq_of_num_factor_eq h₂''],
  norm_cast at ⊢ hsssp, rw [←ore_localization.expand _ _ _ hsssp, ←mul_assoc],
  apply ore_localization.expand
end

instance : has_mul R[S⁻¹] := ⟨ore_localization.mul⟩

lemma ore_div_mul_ore_div {r₁ r₂ : R} {s₁ s₂ : S} :
  (r₁ /ₒ s₁) * (r₂ /ₒ s₂) = (r₁ * ore_num r₂ s₁) /ₒ (s₂ * ore_denom r₂ s₁) := rfl

/-- A characterization lemma for the multiplication on the Ore localization, allowing for a choice
of Ore numerator and Ore denominator. -/
lemma ore_div_mul_char (r₁ r₂ : R) (s₁ s₂ : S) (r' : R) (s' : S)
  (huv : r₂ * (s' : R) = s₁ * r') : (r₁ /ₒ s₁) * (r₂ /ₒ s₂) = (r₁ * r') /ₒ (s₂ * s') :=
mul'_char r₁ r₂ s₁ s₂ s' r' huv

/-- Another characterization lemma for the multiplication on the Ore localizaion delivering
Ore witnesses and conditions bundled in a sigma type. -/
def ore_div_mul_char' (r₁ r₂ : R) (s₁ s₂ : S) :
  Σ' r' : R, Σ' s' : S, r₂ * (s' : R) = s₁ * r'
                        ∧  (r₁ /ₒ s₁) * (r₂ /ₒ s₂) = (r₁ * r') /ₒ (s₂ * s') :=
⟨ore_num r₂ s₁, ore_denom r₂ s₁, ore_eq r₂ s₁, ore_div_mul_ore_div⟩

instance : has_one R[S⁻¹] := ⟨1 /ₒ 1⟩

protected lemma one_def : (1 : R[S⁻¹]) = 1 /ₒ 1 := rfl

instance : inhabited R[S⁻¹] := ⟨1⟩

@[simp]
protected lemma div_eq_one' {r : R} (hr : r ∈ S) : r /ₒ ⟨r, hr⟩ = 1 :=
by { rw [ore_localization.one_def, ore_div_eq_iff], exact ⟨⟨r, hr⟩, 1, by simp, by simp⟩ }

@[simp]
protected lemma div_eq_one {s : S} : (s : R) /ₒ s = 1 :=
by { cases s; apply ore_localization.div_eq_one' }

protected lemma one_mul (x : R[S⁻¹]) : 1 * x = x :=
begin
  induction x using ore_localization.ind with r s,
  simp [ore_localization.one_def, ore_div_mul_char (1 : R) r (1 : S) s r 1 (by simp)]
end

protected lemma mul_one (x : R[S⁻¹]) : x * 1 = x :=
begin
  induction x using ore_localization.ind with r s,
  simp [ore_localization.one_def, ore_div_mul_char r 1 s 1 1 s (by simp)]
end

protected lemma mul_assoc (x y z : R[S⁻¹]) : x * y * z = x * (y * z) :=
begin
  induction x using ore_localization.ind with r₁ s₁,
  induction y using ore_localization.ind with r₂ s₂,
  induction z using ore_localization.ind with r₃ s₃,
  rcases ore_div_mul_char' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩, rw ha', clear ha',
  rcases ore_div_mul_char' r₂ r₃ s₂ s₃ with ⟨rb, sb, hb, hb'⟩, rw hb', clear hb',
  rcases ore_condition rb sa with ⟨rc, sc, hc⟩,
  rw ore_div_mul_char (r₁ * ra) r₃ (s₂ * sa) s₃ rc (sb * sc)
    (by { simp only [submonoid.coe_mul], assoc_rw [hb, hc] }),
  rw [mul_assoc, ←mul_assoc s₃],
  symmetry, apply ore_div_mul_char,
  assoc_rw [hc, ←ha], apply mul_assoc
end

instance : monoid R[S⁻¹] :=
{ one_mul := ore_localization.one_mul,
  mul_one := ore_localization.mul_one,
  mul_assoc := ore_localization.mul_assoc,
  .. ore_localization.has_mul,
  .. ore_localization.has_one }

protected lemma mul_inv (s s' : S) : ((s : R) /ₒ s') * (s' /ₒ s) = 1 :=
by simp [ore_div_mul_char (s :R) s' s' s 1 1 (by simp)]

@[simp]
protected lemma mul_one_div {r : R} {s t : S} : (r /ₒ s) * (1 /ₒ t) = r /ₒ (t * s) :=
by simp [ore_div_mul_char r 1 s t 1 s (by simp)]

@[simp]
protected lemma mul_cancel {r : R} {s t : S} : (r /ₒ s) * (s /ₒ t) = r /ₒ t :=
by simp [ore_div_mul_char r s s t 1 1 (by simp)]

@[simp]
protected lemma mul_cancel' {r₁ r₂ : R} {s t : S} : (r₁ /ₒ s) * ((s * r₂) /ₒ t) = (r₁ * r₂) /ₒ t :=
by simp [ore_div_mul_char r₁ (s * r₂) s t r₂ 1 (by simp)]

@[simp]
lemma div_one_mul {p r : R} {s : S} :
  (r /ₒ 1) * (p /ₒ s) = (r * p) /ₒ s := --TODO use coercion r ↦ r /ₒ 1
by simp [ore_div_mul_char r p 1 s p 1 (by simp)]

/-- The fraction `s /ₒ 1` as a unit in `R[S⁻¹]`, where `s : S`. -/
def numerator_unit (s : S) : units R[S⁻¹] :=
{ val := (s : R) /ₒ 1,
  inv := (1 : R) /ₒ s,
  val_inv := ore_localization.mul_inv s 1,
  inv_val := ore_localization.mul_inv 1 s }

/-- The multiplicative homomorphism from `R` to `R[S⁻¹]`, mapping `r : R` to the
fraction `r /ₒ 1`. -/
def numerator_hom : R →* R[S⁻¹] :=
{ to_fun := λ r, r /ₒ 1,
  map_one' := rfl,
  map_mul' := λ r₁ r₂, div_one_mul.symm }

lemma numerator_hom_apply {r : R} : numerator_hom r = r /ₒ (1 : S) := rfl

lemma numerator_is_unit (s : S) : is_unit ((numerator_hom (s : R)) : R[S⁻¹]) :=
⟨numerator_unit s, rfl⟩

section UMP

variables {T : Type*} [monoid T]
variables (f : R →* T) (fS : S →* units T)
variables (hf : ∀ (s : S), f s = fS s)

include f fS hf

/-- The universal lift from a morphism `R →* T`, which maps elements of `S` to units of `T`,
to a morphism `R[S⁻¹] →* T`. -/
def universal_mul_hom : R[S⁻¹] →* T :=
{ to_fun := λ x, x.lift_expand (λ r s, (f r) * ((fS s)⁻¹ : units T)) $ λ r t s ht,
  begin
    have : ((fS ⟨s * t, ht⟩) : T) = fS s * f t,
    { simp only [←hf, set_like.coe_mk, monoid_hom.map_mul] },
    conv_rhs { rw [monoid_hom.map_mul, ←mul_one (f r), ←units.coe_one, ←mul_left_inv (fS s)],
      rw [units.coe_mul, ←mul_assoc, mul_assoc _ ↑(fS s), ←this, mul_assoc] },
    simp only [mul_one, units.mul_inv]
  end,
  map_one' := by rw [ore_localization.one_def, lift_expand_of]; simp,
  map_mul' := λ x y,
  begin
    induction x using ore_localization.ind with r₁ s₁,
    induction y using ore_localization.ind with r₂ s₂,
    rcases ore_div_mul_char' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩, rw ha', clear ha',
    rw [lift_expand_of, lift_expand_of, lift_expand_of],
    conv_rhs { congr, skip, congr,
      rw [←mul_one (f r₂), ←(fS sa).mul_inv, ←mul_assoc, ←hf, ←f.map_mul, ha, f.map_mul] },
    rw [mul_assoc, mul_assoc, mul_assoc, ←mul_assoc _ (f s₁), hf s₁, (fS s₁).inv_mul, one_mul,
      f.map_mul, mul_assoc, fS.map_mul, ←units.coe_mul], refl
  end }

lemma universal_mul_hom_apply {r : R} {s : S} :
  universal_mul_hom f fS hf (r /ₒ s) = (f r) * ((fS s)⁻¹ : units T) :=
rfl

lemma universal_mul_hom_commutes {r : R} : universal_mul_hom f fS hf (numerator_hom r) = f r :=
by simp [numerator_hom_apply, universal_mul_hom_apply]

/-- The universal morphism `universal_mul_hom` is unique. -/
lemma universal_mul_hom_unique (φ : R[S⁻¹] →* T) (huniv : ∀ (r : R), φ (numerator_hom r) = f r) :
  φ = universal_mul_hom f fS hf :=
begin
  ext, induction x using ore_localization.ind with r s,
  rw [universal_mul_hom_apply, ←huniv r, numerator_hom_apply, ←mul_one (φ (r /ₒ s)),
    ←units.coe_one, ←mul_right_inv (fS s), units.coe_mul, ←mul_assoc,
    ←hf, ←huniv, ←φ.map_mul, numerator_hom_apply, ore_localization.mul_cancel],
end

end UMP

end monoid

section comm_monoid

variables {R : Type*} [comm_monoid R] {S : submonoid R} [ore_set S]

lemma ore_div_mul_ore_div_comm {r₁ r₂ : R} {s₁ s₂ : S} :
  (r₁ /ₒ s₁) * (r₂ /ₒ s₂) = (r₁ * r₂) /ₒ (s₁ * s₂) :=
by rw [ore_div_mul_char r₁ r₂ s₁ s₂ r₂ s₁ (by simp [mul_comm]), mul_comm s₂]

instance : comm_monoid R[S⁻¹] :=
{ mul_comm := λ x y,
  begin
    induction x using ore_localization.ind with r₁ s₁,
    induction y using ore_localization.ind with r₂ s₂,
    rw [ore_div_mul_ore_div_comm, ore_div_mul_ore_div_comm, mul_comm r₁, mul_comm s₁],
  end,
  ..ore_localization.monoid }

variables (R S)

/-- The morphism `numerator_hom` is a monoid localization map in the case of commutative `R`. -/
protected def localization_map : S.localization_map R[S⁻¹] :=
{ to_fun := numerator_hom,
  map_one' := rfl,
  map_mul' := λ r₁ r₂, by simp,
  map_units' := numerator_is_unit,
  surj' := λ z,
  begin
    induction z using ore_localization.ind with r s,
    use (r, s), dsimp,
    rw [numerator_hom_apply, numerator_hom_apply], simp
  end,
  eq_iff_exists' := λ r₁ r₂,
  begin
    dsimp, split,
    { intro h,
      rw [numerator_hom_apply, numerator_hom_apply, ore_div_eq_iff] at h,
      rcases h with ⟨u, v, h₁, h₂⟩, dsimp at h₂,
      rw [one_mul, one_mul] at h₂,
      subst h₂,
      use u,
      simpa only [mul_comm] using h₁.symm },
    { rintro ⟨s, h⟩,
      rw [numerator_hom_apply, numerator_hom_apply, ore_div_eq_iff],
      refine ⟨s, s, _, _⟩,
      { simpa [mul_comm] using h.symm },
      { simp [one_mul]} }
  end }

/-- If `R` is commutative, Ore localization and monoid localization are isomorphic. -/
protected noncomputable def equiv_monoid_localization : localization S ≃* R[S⁻¹] :=
localization.mul_equiv_of_quotient (ore_localization.localization_map R S)

end comm_monoid

section semiring

variables {R : Type*} [semiring R] {S : submonoid R} [ore_set S]

private def add'' (r₁ : R) (s₁ : S) (r₂ : R) (s₂ : S) : R[S⁻¹] :=
(r₁ * ore_denom (s₁ : R) s₂ + r₂ * ore_num s₁ s₂) /ₒ (s₁ * ore_denom s₁ s₂)

private lemma add''_char
  (r₁ : R) (s₁ : S) (r₂ : R) (s₂ : S)
  (rb : R) (sb : S) (hb : (s₁ : R) * sb = (s₂ : R) * rb) :
add'' r₁ s₁ r₂ s₂ = (r₁ * sb + r₂ * rb) /ₒ (s₁ * sb) :=
begin
  simp only [add''],
  have ha := ore_eq (s₁ : R) s₂,
  set! ra := ore_num (s₁ : R) s₂ with h, rw ←h at *, clear h, -- r tilde
  set! sa := ore_denom (s₁ : R) s₂ with h, rw ←h at *, clear h, -- s tilde
  rcases ore_condition (sa : R) sb with ⟨rc, sc, hc⟩, -- s*, r*
  have : (s₂ : R) * (rb * rc) = s₂ * (ra * sc),
  { rw [←mul_assoc, ←hb, mul_assoc, ←hc, ←mul_assoc, ←mul_assoc, ha] },
  rcases ore_left_cancel _ _ s₂ this with ⟨sd, hd⟩, -- s#
  symmetry, rw ore_div_eq_iff,
  use sc * sd, use rc * sd,
  split; simp only [submonoid.coe_mul],
  { noncomm_ring, assoc_rw [hd, hc], noncomm_ring },
  { assoc_rewrite [hc], noncomm_ring }
end

local attribute [instance] ore_localization.ore_eqv

private def add' (r₂ : R) (s₂ : S) : R[S⁻¹] → R[S⁻¹] := --plus tilde
quotient.lift (λ (r₁s₁ : R × S), add'' r₁s₁.1 r₁s₁.2 r₂ s₂) $
begin
  rintros ⟨r₁', s₁'⟩ ⟨r₁, s₁⟩ ⟨sb, rb, hb, hb'⟩, -- s*, r*
  rcases ore_condition (s₁' : R) s₂ with ⟨rc, sc, hc⟩, --s~~, r~~
  rcases ore_condition rb sc with ⟨rd, sd, hd⟩, -- s#, r#
  dsimp at *, rw add''_char _ _ _ _ rc sc hc,
  have : ↑s₁ * ↑(sb * sd) = ↑s₂ * (rc * rd),
  { simp only [submonoid.coe_mul], assoc_rewrite [hb', hd, hc], noncomm_ring },
  rw add''_char _ _ _ _ (rc * rd : R) (sb * sd : S) this,
  simp only [submonoid.coe_mul], assoc_rw [hb, hd],
  rw [←mul_assoc, ←add_mul, ore_div_eq_iff],
  use 1, use rd, split,
  { simp },
  { simp only [mul_one, submonoid.coe_one, submonoid.coe_mul] at ⊢ this, assoc_rw [hc, this] },
end

private lemma add'_comm (r₁ r₂ : R) (s₁ s₂ : S) : add' r₁ s₁ (r₂ /ₒ s₂) = add' r₂ s₂ (r₁ /ₒ s₁) :=
begin
  simp only [add', ore_div, add'', quotient.lift_mk, quotient.eq],
  have hb := ore_eq ↑s₂ s₁, set rb := ore_num ↑s₂ s₁ with h, -- r~~
    rw ←h, clear h, set sb := ore_denom ↑s₂ s₁ with h, rw ←h, clear h, -- s~~
  have ha := ore_eq ↑s₁ s₂, set ra := ore_num ↑s₁ s₂ with h, -- r~
    rw ←h, clear h, set sa := ore_denom ↑s₁ s₂ with h, rw ←h, clear h, -- s~
  rcases ore_condition ra sb with ⟨rc, sc, hc⟩, -- r#, s#
  have : (s₁ : R) * (rb * rc) = s₁ * (sa * sc),
  { rw [←mul_assoc, ←hb, mul_assoc, ←hc, ←mul_assoc, ←ha, mul_assoc] },
  rcases ore_left_cancel _ _ s₁ this with ⟨sd, hd⟩, -- s+
  use sc * sd, use rc * sd,
  dsimp, split,
  { rw [add_mul, add_mul, add_comm], assoc_rw [←hd, hc], noncomm_ring },
  { rw [mul_assoc, ←mul_assoc ↑sa, ←hd, hb], noncomm_ring }
end

/-- The addition on the Ore localization. -/
private def add : R[S⁻¹] → R[S⁻¹] → R[S⁻¹] :=
λ x,
quotient.lift (λ rs : R × S, add' rs.1 rs.2 x)
begin
  rintros ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ hyz,
  induction x using ore_localization.ind with r₃ s₃,
  dsimp, rw [add'_comm, add'_comm r₂],
  simp [(/ₒ), quotient.sound hyz],
end

instance : has_add R[S⁻¹] := ⟨add⟩

lemma ore_div_add_ore_div {r r' : R} {s s' : S} :
  r /ₒ s + r' /ₒ s' = (r * ore_denom (s : R) s' + r' * ore_num s s') /ₒ (s * ore_denom s s') :=
rfl

/-- A characterization of the addition on the Ore localizaion, allowing for arbitrary Ore
numerator and Ore denominator. -/
lemma ore_div_add_char {r r' : R} (s s' : S) (rb : R) (sb : S)
  (h : (s : R) * sb = s' * rb) :
  r /ₒ s + r' /ₒ s' = (r * sb + r' * rb) /ₒ (s * sb) :=
add''_char r s r' s' rb sb h

/-- Another characterization of the addition on the Ore localization, bundling up all witnesses
and conditions into a sigma type. -/
def ore_div_add_char' (r r' : R) (s s' : S) :
  Σ' r'' : R, Σ' s'' : S, (s : R) * s'' = s' * r'' ∧
                  r /ₒ s + r' /ₒs' = (r * s'' + r' * r'') /ₒ (s * s'') :=
⟨ore_num s s', ore_denom s s', ore_eq s s', ore_div_add_ore_div⟩

@[simp] lemma add_ore_div {r r' : R} {s : S} : (r /ₒ s) + (r' /ₒ s) = (r + r') /ₒ s :=
by simp [ore_div_add_char s s 1 1 (by simp)]

protected lemma add_assoc (x y z : R[S⁻¹]) :
  (x + y) + z = x + (y + z) :=
begin
  induction x using ore_localization.ind with r₁ s₁,
  induction y using ore_localization.ind with r₂ s₂,
  induction z using ore_localization.ind with r₃ s₃,
  rcases ore_div_add_char' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩, rw ha', clear ha',
  rcases ore_div_add_char' r₂ r₃ s₂ s₃ with ⟨rb, sb, hb, hb'⟩, rw hb', clear hb',
  rcases ore_div_add_char' (r₁ * sa + r₂ * ra) r₃ (s₁ * sa) s₃ with ⟨rc, sc, hc, q⟩, rw q, clear q,
  rcases ore_div_add_char' r₁ (r₂ * sb + r₃ * rb) s₁ (s₂ * sb) with ⟨rd, sd, hd, q⟩, rw q, clear q,
  noncomm_ring, rw add_comm (r₂ * _),
  repeat { rw ←add_ore_div },
  congr' 1,
  { rcases ore_condition (sd : R) (sa * sc) with ⟨re, se, he⟩,
    { simp_rw ←submonoid.coe_mul at hb hc hd,
      assoc_rw [subtype.coe_eq_of_eq_mk hc],
      rw [←ore_localization.expand, subtype.coe_eq_of_eq_mk hd, ←mul_assoc,
        ←ore_localization.expand, subtype.coe_eq_of_eq_mk hb],
      apply ore_localization.expand } },
  congr' 1,
  { rw [←ore_localization.expand', ←mul_assoc, ←mul_assoc,
      ←ore_localization.expand', ←ore_localization.expand'] },
  { simp_rw [←submonoid.coe_mul] at ha hd,
    rw [subtype.coe_eq_of_eq_mk hd, ←mul_assoc, ←mul_assoc,
      ←mul_assoc, ←ore_localization.expand, ←ore_localization.expand',
      subtype.coe_eq_of_eq_mk ha, ←ore_localization.expand],
    apply ore_localization.expand' }
end

private def zero : R[S⁻¹] := 0 /ₒ 1

instance : has_zero R[S⁻¹] := ⟨zero⟩

protected lemma zero_def : (0 : R[S⁻¹]) = 0 /ₒ 1 := rfl

@[simp]
lemma zero_div_eq_zero (s : S) : 0 /ₒ s = 0 :=
by { rw [ore_localization.zero_def, ore_div_eq_iff], exact ⟨s, 1, by simp⟩ }

protected lemma zero_add (x : R[S⁻¹]) : 0 + x = x :=
begin
  induction x using ore_localization.ind,
  rw [←zero_div_eq_zero, add_ore_div], simp
end

protected lemma add_comm (x y : R[S⁻¹]) : x + y = y + x :=
begin
  induction x using ore_localization.ind,
  induction y using ore_localization.ind,
  change add' _ _ (_ /ₒ _) = _, apply add'_comm
end

instance : add_comm_monoid R[S⁻¹] :=
{ add_comm := ore_localization.add_comm,
  add_assoc := ore_localization.add_assoc,
  zero := zero,
  zero_add := ore_localization.zero_add,
  add_zero := λ x, by rw [ore_localization.add_comm, ore_localization.zero_add],
  .. ore_localization.has_add }

protected lemma zero_mul (x : R[S⁻¹]) : 0 * x = 0 :=
begin
  induction x using ore_localization.ind with r s,
  rw [ore_localization.zero_def, ore_div_mul_char 0 r 1 s r 1 (by simp)], simp
end

protected lemma mul_zero (x : R[S⁻¹]) : x * 0 = 0 :=
begin
  induction x using ore_localization.ind with r s,
  rw [ore_localization.zero_def, ore_div_mul_char r 0 s 1 0 1 (by simp)], simp
end

protected lemma left_distrib (x y z : R[S⁻¹]) : x * (y + z) = x * y + x * z :=
begin
  induction x using ore_localization.ind with r₁ s₁,
  induction y using ore_localization.ind with r₂ s₂,
  induction z using ore_localization.ind with r₃ s₃,
  rcases ore_div_add_char' r₂ r₃ s₂ s₃ with ⟨ra, sa, ha, q⟩, rw q, clear q,
  rw ore_localization.expand' r₂ s₂ sa,
  rcases ore_div_mul_char' r₁ (r₂ * sa) s₁ (s₂ * sa) with ⟨rb, sb, hb, q⟩, rw q, clear q,
  have hs₃rasb : ↑s₃ * (ra * sb) ∈ S, { rw [←mul_assoc, ←ha], norm_cast, apply set_like.coe_mem },
  rw ore_localization.expand _ _ _ hs₃rasb,
  have ha' : (↑(s₂ * sa * sb)) = ↑s₃ * (ra * sb), { simp [ha, ←mul_assoc] },
  rw ←subtype.coe_eq_of_eq_mk ha',
  rcases ore_div_mul_char' r₁ (r₃ * (ra * sb)) s₁ (s₂ * sa * sb) with ⟨rc, sc, hc, hc'⟩, rw hc',
  rw ore_div_add_char (s₂ * sa * sb) (s₂ * sa * sb * sc) 1 sc (by simp),
  rw ore_localization.expand' (r₂ * ↑sa + r₃ * ra) (s₂ * sa) (sb * sc),
  conv_lhs { congr, skip, congr,
    rw [add_mul, S.coe_mul, ←mul_assoc, hb, ←mul_assoc, mul_assoc r₃, hc, mul_assoc, ←mul_add] },
  rw ore_localization.mul_cancel', simp only [mul_one, submonoid.coe_mul, mul_add, ←mul_assoc],
end

lemma right_distrib (x y z : R[S⁻¹]) : (x + y) * z = x * z + y * z :=
begin
  induction x using ore_localization.ind with r₁ s₁,
  induction y using ore_localization.ind with r₂ s₂,
  induction z using ore_localization.ind with r₃ s₃,
  rcases ore_div_add_char' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩, rw ha', clear ha', norm_cast at ha,
  rw ore_localization.expand' r₁ s₁ sa,
  rw ore_localization.expand r₂ s₂ ra (by rw ←ha; apply set_like.coe_mem),
  rw ←subtype.coe_eq_of_eq_mk ha,
  repeat { rw ore_div_mul_ore_div }, simp only [add_mul, add_ore_div]
end

instance : semiring R[S⁻¹] :=
{ zero_mul := ore_localization.zero_mul,
  mul_zero := ore_localization.mul_zero,
  left_distrib := ore_localization.left_distrib,
  right_distrib := right_distrib,
  .. ore_localization.add_comm_monoid,
  .. ore_localization.monoid }

section UMP
variables {T : Type*} [semiring T]
variables (f : R →+* T) (fS : S →* units T)
variables (hf : ∀ (s : S), f s = fS s)

include f fS hf

/-- The universal lift from a ring homomorphism `f : R →+* T`, which maps elements in `S` to
units of `T`, to a ring homomorphism `R[S⁻¹] →+* T`. This extends the construction on
monoids. -/
def universal_hom : R[S⁻¹] →+* T :=
{ map_zero' :=
  begin
    rw [monoid_hom.to_fun_eq_coe, ore_localization.zero_def, universal_mul_hom_apply],
    simp
  end,
  map_add' := λ x y,
  begin
    induction x using ore_localization.ind with r₁ s₁,
    induction y using ore_localization.ind with r₂ s₂,
    rcases ore_div_add_char' r₁ r₂ s₁ s₂ with ⟨r₃, s₃, h₃, h₃'⟩, rw h₃', clear h₃',
    simp only [universal_mul_hom_apply, ring_hom.coe_monoid_hom,
      ring_hom.to_monoid_hom_eq_coe, monoid_hom.to_fun_eq_coe],
    simp only [mul_inv_rev, monoid_hom.map_mul, ring_hom.map_add, ring_hom.map_mul, units.coe_mul],
    rw [add_mul, ←mul_assoc, mul_assoc (f r₁), hf, ←units.coe_mul],
    simp only [mul_one, mul_right_inv, units.coe_one],
    congr' 1, rw [mul_assoc], congr' 1,
    norm_cast at h₃, have h₃' := subtype.coe_eq_of_eq_mk h₃,
    rw [←units.coe_mul, ←mul_inv_rev, ←fS.map_mul, h₃'],
    have hs₂r₃ : ↑s₂ * r₃ ∈ S, { rw ←h₃, exact set_like.coe_mem (s₁ * s₃)},
    apply (units.inv_mul_cancel_left (fS s₂) _).symm.trans,
    conv_lhs { congr, skip,
      rw [←units.mul_inv_cancel_left (fS ⟨s₂ * r₃, hs₂r₃⟩) (fS s₂), mul_assoc, mul_assoc],
      congr, skip, rw [←hf, ←mul_assoc (f s₂), ←f.map_mul],
      conv { congr, skip, congr, rw [←h₃] },
      rw [hf, ←mul_assoc, ←h₃', units.inv_mul] },
    rw [one_mul, ←h₃', units.mul_inv, mul_one],
  end,
  .. universal_mul_hom f.to_monoid_hom fS hf }

lemma universal_hom_apply {r : R} {s : S} :
  universal_hom f fS hf (r /ₒ s) = (f r) * ((fS s)⁻¹ : units T) := rfl

lemma universal_hom_commutes {r : R} : universal_hom f fS hf (numerator_hom r) = f r :=
by simp [numerator_hom_apply, universal_hom_apply]

lemma universal_hom_unique (φ : R[S⁻¹] →+* T) (huniv : ∀ (r : R), φ (numerator_hom r) = f r) :
  φ = universal_hom f fS hf :=
ring_hom.coe_monoid_hom_injective $
universal_mul_hom_unique (ring_hom.to_monoid_hom f) fS hf ↑φ huniv

end UMP

end semiring

section ring
variables {R : Type*} [ring R] {S : submonoid R} [ore_set S]

/-- Negation on the Ore localization is defined via negation on the numerator. -/
protected def neg : R[S⁻¹] → R[S⁻¹] :=
lift_expand (λ (r : R) (s : S), (- r) /ₒ s) $
  λ r t s ht, by rw [neg_mul_eq_neg_mul, ←ore_localization.expand]

instance : has_neg R[S⁻¹] := ⟨ore_localization.neg⟩

@[simp] protected lemma neg_def (r : R) (s : S) : - (r /ₒ s) = (- r) /ₒ s := rfl

protected lemma add_left_neg (x : R[S⁻¹]) : (- x) + x = 0 :=
by induction x using ore_localization.ind with r s; simp

instance : ring R[S⁻¹] :=
{ add_left_neg := ore_localization.add_left_neg,
  .. ore_localization.semiring,
  .. ore_localization.has_neg }

open_locale non_zero_divisors

lemma numerator_hom_inj (hS : S ≤ R⁰) : function.injective (numerator_hom : R → R[S⁻¹]) :=
λ r₁ r₂ h,
begin
  rw [numerator_hom_apply, numerator_hom_apply, ore_div_eq_iff] at h,
  rcases h with ⟨u, v, h₁, h₂⟩,
  simp only [S.coe_one, one_mul] at h₂,
  rwa [←h₂, mul_cancel_right_mem_non_zero_divisor (hS (set_like.coe_mem u)), eq_comm] at h₁,
end

lemma nontrivial_of_non_zero_divisors [nontrivial R] (hS : S ≤ R⁰) : nontrivial R[S⁻¹] :=
⟨⟨0, 1, λ h,
  begin
    rw [ore_localization.one_def, ore_localization.zero_def] at h,
    apply non_zero_divisors.coe_ne_zero 1 (numerator_hom_inj hS h).symm
  end⟩⟩

end ring

section division_ring

open_locale non_zero_divisors
open_locale classical

variables {R : Type*} [ring R] [nontrivial R] [ore_set R⁰]

instance : nontrivial R[R⁰⁻¹] := nontrivial_of_non_zero_divisors (refl R⁰)

variables [no_zero_divisors R]

noncomputable theory

/-- The inversion of Ore fractions for a ring without zero divisors, satisying `0⁻¹ = 0` and
`(r /ₒ r')⁻¹ = r' /ₒ r` for `r ≠ 0`. -/
protected def inv : R[R⁰⁻¹] → R[R⁰⁻¹] :=
lift_expand (λ r s, if hr: r = (0 : R) then (0 : R[R⁰⁻¹])
  else (s /ₒ ⟨r, λ _, eq_zero_of_ne_zero_of_mul_right_eq_zero hr⟩))
begin
  intros r t s hst,
  by_cases hr : r = 0,
  { simp [hr] },
  { by_cases ht : t = 0,
    { exfalso, apply non_zero_divisors.coe_ne_zero ⟨_, hst⟩, simp [ht, mul_zero] },
    { simp only [hr, ht, set_like.coe_mk, dif_neg, not_false_iff, or_self, mul_eq_zero],
      apply ore_localization.expand } }
end

instance : has_inv R[R⁰⁻¹] := ⟨ore_localization.inv⟩

protected lemma inv_def {r : R} {s : R⁰} :
  (r /ₒ s)⁻¹ = if hr: r = (0 : R) then (0 : R[R⁰⁻¹])
  else (s /ₒ ⟨r, λ _, eq_zero_of_ne_zero_of_mul_right_eq_zero hr⟩) := rfl

protected lemma mul_inv_cancel (x : R[R⁰⁻¹]) (h : x ≠ 0) : x * x⁻¹ = 1 :=
begin
  induction x using ore_localization.ind with r s,
  rw [ore_localization.inv_def, ore_localization.one_def],
  by_cases hr : r = 0,
  { exfalso, apply h, simp [hr] },
  { simp [hr], apply ore_localization.div_eq_one' }
end

protected lemma inv_zero : (0 : R[R⁰⁻¹])⁻¹ = 0 :=
by { rw [ore_localization.zero_def, ore_localization.inv_def], simp }

instance : division_ring R[(R⁰)⁻¹] :=
{ mul_inv_cancel := ore_localization.mul_inv_cancel,
  inv_zero := ore_localization.inv_zero,
  .. ore_localization.nontrivial,
  .. ore_localization.has_inv,
  .. ore_localization.ring }

end division_ring

end ore_localization
