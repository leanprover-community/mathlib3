import set_theory.cardinal
import control.ulift

import .group_theory.ad_to_ulift
open_locale cardinal

lemma gimme_more {α : Type} (m : ℕ) (x : fin m → α) (hα : ↑m < #α) :
  ∃ (a : α), a ∉ set.range x :=
begin
  apply not_forall.mp,
  change ¬ (function.surjective x),
  intro h,
  apply (lt_iff_not_ge _ _).mp  hα,
  rw ← cardinal.mk_fin,
  exact cardinal.mk_le_of_surjective h
end

lemma gimme_more' {α : Type*} (m : ℕ) (x : fin m → α) (hα : ↑m < #α) :
  ∃ (a : α), a ∉ set.range x :=
begin
  apply not_forall.mp,
  -- change ¬ (function.surjective x),
  intro h,
  apply (lt_iff_not_ge _ _).mp  hα,
  --   rw ge_iff_le,
  let hx := cardinal.mk_le_of_surjective (ulift.surjective_iff_surjective.mpr h),
  simp only [cardinal.mk_ulift] at hx,
  simp only [cardinal.mk_fin, cardinal.lift_nat_cast] at hx,
  rw  cardinal.lift_id at hx,
  exact hx,
end

lemma gimme_encore {α : Type*} (m : ℕ) (x : fin m → α) (hα : ↑m < #α) :
  ∃ (a : α), a ∉ set.range x :=
begin
  apply not_forall.mp,
  -- change ¬ (function.surjective x),
  intro h,
  apply (lt_iff_not_ge _ _).mp  hα,
  --   rw ge_iff_le,
  let hx := cardinal.mk_le_of_surjective (ulift.surjective_iff_surjective.mpr h),
  simp only [cardinal.mk_ulift, cardinal.mk_fintype, fintype.card_ulift, fintype.card_fin] at hx,
  rw  cardinal.lift_id at hx,
  exact hx,
end
