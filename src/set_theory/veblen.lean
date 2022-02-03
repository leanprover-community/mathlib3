/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Violeta Hernández Palacios
-/
import set_theory.fixed_points

/-!
# Veblen's function

In this file, we build Veblen's two argument function.

TODO:
- prove the existence of a Veblen normal form.
- prove that `veblen f (a + 1) b` is always `principal` with respect to `f a`.

## Main definitions

- `veblen`: The two argument Veblen function from a given starting normal function.
- `veblen'`: Equal to `veblen (λ a, ω^a)`.

## Main results

-/

noncomputable theory

universes u v
variable {ι : Type u}

namespace ordinal


theorem le_nfp_family [hι : nonempty ι] {f : ι → ordinal → ordinal} (Hf : ∀ i, is_normal (f i))
{a b} : (∀ i, f i b ≤ nfp_family f a) ↔ b ≤ nfp_family f a :=
begin
  refine ⟨λ h, _, λ h i, _⟩,
  { unfreezingI { cases hι with i },
    exact ((Hf i).le_self b).trans (h i) },
  rw ←nfp_family_fp Hf i,
  exact (Hf i).strict_mono.monotone h
end

theorem nfp_family_limit {f : ι → ordinal.{max u v} → ordinal.{max u v}} (Hf : ∀ i, is_normal (f i))
{o : ordinal.{max u v}} (ho : is_limit o) :
  nfp_family.{u v} f o = bsup.{(max u v) u} o (λ a ha, nfp_family f a) :=
begin

end

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
has an unbounded set of common fixed points. -/
theorem nfp_family_unbounded {f : ι → ordinal.{max u v} → ordinal} (Hf : ∀ i, is_normal (f i)) :
  unbounded (<) (⋂ i, function.fixed_points (f i)) :=
λ a, ⟨_, begin
  rintros S ⟨i, hi⟩,
  rw ←hi,
  exact nfp_family_fp Hf a i
end, not_lt_of_ge (le_nfp_family_self f a)⟩

theorem nfp_family_is_normal {f : ι → ordinal.{max u v} → ordinal} (Hf : ∀ i, is_normal (f i)) :
  is_normal (enum_ord _ (nfp_family_unbounded Hf)) :=
begin
  rw ←is_normal_iff_strict_mono_limit,
  use enum_ord.strict_mono _,
  intros a ha c b,
  sorry,
end

/-- The next common fixed point above `a` for a family of normal functions indexed by ordinals. -/
def nfp_bfamily (o : ordinal.{u}) (f : Π b < o, ordinal.{max u v} → ordinal.{max u v}) :
  ordinal.{max u v} → ordinal.{max u v} :=
nfp_family (family_of_bfamily o f)

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
has an unbounded set of common fixed points. -/
-- Big thanks to Bhavik for this.
theorem nfp_bfamily_unbounded {o : ordinal.{u}} {f : Π i < o, ordinal.{max u v} → ordinal}
  (Hf : ∀ i hi, is_normal (f i hi)) :
  unbounded (<) (λ b, ∀ i hi, f i hi b = b) :=
begin
  induction o using ordinal.induction_on with α r hr,
  introI a,
  obtain ⟨b, hb₁, hb₂⟩ := nfp_family_unbounded (λ i, Hf _ (typein_lt_type r i)) a,
  refine ⟨b, λ i hi, _, hb₂⟩,
  convert hb₁ (ordinal.enum r i hi),
  simp
end

theorem nfp_bfamily_is_normal {o : ordinal.{u}} {f : Π i < o, ordinal.{max u v} → ordinal}
  (Hf : ∀ i hi, is_normal (f i hi)) : is_normal (enum_ord (nfp_bfamily_unbounded Hf)) := sorry

private def veblen_aux {f : ordinal.{u} → ordinal.{u}} (Hf : is_normal f) :
  ordinal.{u} → {φ // is_normal φ} :=
wf.fix (λ a φ, if a = 0 then ⟨f, Hf⟩ else ⟨_, nfp_bfamily_is_normal.{u u} (λ i hi, (φ i hi).prop)⟩)

end ordinal
