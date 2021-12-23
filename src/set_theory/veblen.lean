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

private theorem aux {o : ordinal} (ho : 2 ≤ o) : o ≠ 0 :=
by { intro h, rw [h, ordinal.le_zero] at ho, exact (succ_ne_zero 1) ho }

private theorem aux₂ {o b : ordinal.{u}} (ho : 2 ≤ o) (hb : b ≠ 0)
(hb' : b < o ^ ordinal.omega.{u}) : b / o < b :=
begin
  rw div_lt (aux ho),
  apply lt_of_le_of_ne, {
    nth_rewrite 0 ←one_mul b,
    apply ordinal.mul_le_mul_right,
    have h : (1:ordinal)≤ 2:= sorry,
    exact le_trans h ho,
  },
  sorry
end

-- We implicitly assume `f 0 _ = id` and `f 1 _ = id`.
private def nfp_bfamily_iterate {o : ordinal.{u}} (ho : 2 ≤ o)
  (f : Π b < o, ordinal.{max u v} → ordinal.{max u v}) (a : ordinal.{u}) :
  Π b, b < o ^ ordinal.omega.{u} → ordinal.{max u v} :=
λ b, @well_founded.recursion _ _ wf (λ c, c < o ^ ordinal.omega.{u} → ordinal.{max u v}) b
(λ b h hb',
  if hb : b = 0
  then a.lift
  else f (b % o) (mod_lt _ (aux ho)) (h (b / o) (aux₂ ho hb hb') (lt_trans (aux₂ ho hb hb') hb')))


/-- The next common fixed point above `a` for a family of normal functions indexed by ordinals. -/
def nfp_bfamily (a o : ordinal.{u}) (f : Π b < o, ordinal.{max u v} → ordinal.{max u v}) : ordinal :=
bsup (o ^ ordinal.omega.{u}) begin
  intros b hb,
  sorry
end

/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
has an unbounded set of common fixed points. -/
theorem nfp_bfamily_unbounded (o : ordinal.{u}) {f : Π a < o, ordinal → ordinal}
(Hf : ∀ i hi, is_normal (f i hi)) :
  ∀ a, ∃ b, (∀ i hi, f i hi b = b) ∧ a ≤ b := sorry
