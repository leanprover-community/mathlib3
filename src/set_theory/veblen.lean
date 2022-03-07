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

universe u

namespace ordinal

/-- The Veblen hierarchy from a function. `veblen f 0` equals the original function, and for any
    `o > 0`, `veblen f o` enumerates the common fixed points of all `veblen f a` for `a < o`. -/
def veblen (f : ordinal → ordinal) : ordinal → ordinal → ordinal :=
wf.fix (λ o φ, if o = 0 then f else deriv_bfamily.{u u} o φ)

private theorem veblen_def (f : ordinal → ordinal) (o) :
  veblen f o = if o = 0 then f else deriv_bfamily.{u u} o (λ a _, veblen f a) :=
wf.fix_eq _ o

theorem veblen_zero (f : ordinal → ordinal) : veblen f 0 = f :=
by { rw veblen_def, exact if_pos rfl }

theorem veblen_pos (f : ordinal → ordinal) {o : ordinal} (ho : o ≠ 0) :
  veblen f o = deriv_bfamily.{u u} o (λ a _, veblen f a) :=
by { rw veblen_def, exact if_neg ho }

theorem veblen_is_normal' (f : ordinal → ordinal) {o : ordinal.{u}} (ho : o ≠ 0) :
  is_normal (veblen f o) :=
by { rw veblen_pos f ho, apply deriv_bfamily_is_normal }

theorem veblen_is_normal {f : ordinal → ordinal} (hf : is_normal f) (o : ordinal.{u}) :
  is_normal (veblen f o) :=
begin
  rcases eq_or_ne o 0 with rfl | ho,
  { rwa veblen_zero },
  { exact veblen_is_normal' f ho }
end

theorem veblen_id (o : ordinal.{u}) : veblen id o = id :=
begin
  apply wf.induction o,
  intros a H,
  rcases eq_or_ne a 0 with rfl | ho,
  { rw veblen_zero },
  { rw veblen_pos id ho,
  suffices : (λ (i : a.out.α), veblen id (typein a.out.r i)) = λ i, id,
  { change deriv_family (λ (i : a.out.α), _) = _,
    rw [this, ←@deriv_eq_deriv_family'.{u u} a.out.α (by rwa out_nonempty_iff_ne_zero), deriv_id] },
  funext,
  rw H _ (typein_lt_self i) }
end

theorem veblen_fp_lt_of_fp {f : ordinal → ordinal} {o o' a : ordinal.{u}} (hf : is_normal f)
  (ho : veblen f o a = a) (ho' : o' ≤ o) : veblen f o' a = a :=
begin
  rcases lt_or_eq_of_le ho' with ho' | rfl,
  { rw veblen_pos f ((ordinal.zero_le o').trans_lt ho').ne' at ho,
    have := deriv_bfamily_fp.{u u} (λ i _, @veblen_is_normal f hf i) a _ ho',
    rwa ho at this },
  { exact ho }
end

theorem veblen_succ {f : ordinal → ordinal} (hf : is_normal f) (o : ordinal.{u}) :
  veblen f o.succ = deriv (veblen f o) :=
begin
  rw veblen_pos f (@succ_ne_zero o),
  refine deriv_family_eq_of_fp_eq.{u 0 0}
    (λ i, veblen_is_normal hf _)
    (λ _, veblen_is_normal hf o)
    (λ a, ⟨λ H _, _, λ H i, veblen_fp_lt_of_fp hf (H unit.star) (lt_succ.1 (typein_lt_self i))⟩),
  have := H (enum o.succ.out.r o (by { rw type_out, exact lt_succ_self o })),
  rwa family_of_bfamily_enum at this
end

set_option pp.universes true

theorem veblen_monotone {f : ordinal.{u} → ordinal} (hf : is_normal f) (o) :
  monotone (λ a, veblen f a o) :=
λ b c hbc, begin
  dsimp,
  rcases eq_zero_or_pos b with rfl | hb,
  { rcases lt_or_eq_of_le hbc with hc | rfl,
    { rw [veblen_zero, veblen_pos f hc.ne'],
      apply (self_le_deriv hf o).trans,
      rw deriv_eq_deriv_bfamily.{0 u} f,
      refine deriv_bfamily_le_of_fp_subset.{u 0 0} (λ a _, veblen_is_normal hf a) (λ _ _, hf)
        (λ a H _ _, _) o,
      rw ←veblen_zero f,
      exact H 0 hc },
    { refl } },
  { rw [veblen_pos f hb.ne', veblen_pos f (hb.trans_le hbc).ne'],
    exact deriv_bfamily_le_of_fp_subset.{u u u} (λ a _, veblen_is_normal hf a)
      (λ a _, veblen_is_normal hf a) (λ a H i hib, H i (hib.trans_le hbc)) o }
end

theorem veblen_zero_is_normal {f : ordinal → ordinal} (hf : is_normal f) (hf₀ : f 0 ≠ 0) :
  is_normal (λ a, veblen f a 0) :=
begin
  split,{
    dsimp,
    intro o,
    have ho := veblen_is_normal hf o,
    rw [veblen_succ hf, deriv_zero, ←ho.nfp_fp],
    apply ho.strict_mono ((ordinal.pos_iff_ne_zero.2 (λ h, hf₀ _)).trans_le (iterate_le_nfp _ 0 1)),
    have := veblen_fp_lt_of_fp hf h (ordinal.zero_le o),
    rwa veblen_zero at this
  },
  {
intros o ho a,dsimp,split,{
  intros ha b hb,sorry,
}
  }
end

end ordinal
