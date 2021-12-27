/-
Copyright (c) 2021 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Violeta Hernández Palacios
-/
import set_theory.ordinal_arithmetic

/-!
# Veblen's lemma

In this file, we build Veblen's two argument function, and prove the existence of a Veblen normal
form.

## Main definitions

- `veblen`: The two argument Veblen function from a given starting normal function.
- `veblen'`: Equal to `veblen (λ a, ω^a)`.

## Main results

-/

noncomputable theory

open ordinal

universes u v
variable {ι : Type u}

private def nfp_family_iterate (f : ι → ordinal.{max u v} → ordinal.{max u v}) (a) :
  list ι → ordinal.{max u v}
| []       := a
| (i :: l) := f i (nfp_family_iterate l)

/-- The next common fixed point above `a` for a family of normal functions. -/
-- Todo: prove it's actually the next
def nfp_family (f : ι → ordinal → ordinal) (a) : ordinal := sup (nfp_family_iterate f a)

theorem le_nfp_family_self (f : ι → ordinal → ordinal) (a) : a ≤ nfp_family f a := le_sup _ []

theorem nfp_family_fp {f : ι → ordinal → ordinal} (Hf : ∀ i, is_normal (f i)) (a i) :
  f i (nfp_family f a) = (nfp_family f a) :=
begin
  unfold nfp_family,
  rw (Hf i).sup ⟨[]⟩,
  apply le_antisymm;
  rw ordinal.sup_le,
  exact λ l, le_sup _ (i :: l),
  exact λ l, le_trans ((Hf i).le_self _) (le_sup _ _)
end

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
has an unbounded set of common fixed points. -/
theorem nfp_family_unbounded {f : ι → ordinal.{max u v} → ordinal} (Hf : ∀ i, is_normal (f i)) :
  ∀ a, ∃ b, (∀ i, f i b = b) ∧ a ≤ b :=
λ a, ⟨nfp_family f a, nfp_family_fp Hf a, le_nfp_family_self f a⟩

/-- The next common fixed point above `a` for a family of normal functions indexed by ordinals. -/
def nfp_bfamily (a o : ordinal.{u}) (f : Π b < o, ordinal.{max u v} → ordinal.{max u v}) : ordinal :=
sorry

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
has an unbounded set of common fixed points. -/
-- Big thanks to Bhavik for this.
theorem nfp_bfamily_unbounded {o : ordinal.{u}} {f : Π i < o, ordinal.{max u v} → ordinal}
  (Hf : ∀ i hi, is_normal (f i hi)) :
  ∀ a, ∃ b, (∀ i hi, f i hi b = b) ∧ a ≤ b :=
begin
  induction o using ordinal.induction_on with α r hr,
  introI a,
  obtain ⟨b, hb₁, hb₂⟩ := nfp_family_unbounded (λ i, Hf _ (typein_lt_type r i)) a,
  refine ⟨b, λ i hi, _, hb₂⟩,
  convert hb₁ (ordinal.enum r i hi),
  simp,
end
