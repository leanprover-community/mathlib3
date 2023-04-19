/-
Copyright (c) 2022 Dagur Tómas Ásgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Tómas Ásgeirsson, Leonardo de Moura
-/

import data.set.image

/-!
# Indicator function valued in bool

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

See also `set.indicator` and `set.piecewise`.
-/

open bool

namespace set
variables {α : Type*} (s : set α)

/-- `bool_indicator` maps `x` to `tt` if `x ∈ s`, else to `ff` -/
noncomputable def bool_indicator (x : α) :=
@ite _ (x ∈ s) (classical.prop_decidable _) tt ff

lemma mem_iff_bool_indicator (x : α) : x ∈ s ↔ s.bool_indicator x = tt :=
by { unfold bool_indicator, split_ifs ; tauto }

lemma not_mem_iff_bool_indicator (x : α) : x ∉ s ↔ s.bool_indicator x = ff :=
by { unfold bool_indicator, split_ifs ; tauto }

lemma preimage_bool_indicator_tt : s.bool_indicator ⁻¹' {tt} = s :=
ext (λ x, (s.mem_iff_bool_indicator x).symm)

lemma preimage_bool_indicator_ff : s.bool_indicator ⁻¹' {ff} = sᶜ :=
ext (λ x, (s.not_mem_iff_bool_indicator x).symm)

open_locale classical

lemma preimage_bool_indicator_eq_union (t : set bool) :
  s.bool_indicator ⁻¹' t = (if tt ∈ t then s else ∅) ∪ (if ff ∈ t then sᶜ else ∅) :=
begin
  ext x,
  dsimp [bool_indicator],
  split_ifs ; tauto
end

lemma preimage_bool_indicator (t : set bool) :
  s.bool_indicator ⁻¹' t = univ ∨ s.bool_indicator ⁻¹' t = s ∨
  s.bool_indicator ⁻¹' t = sᶜ ∨ s.bool_indicator ⁻¹' t = ∅ :=
begin
  simp only [preimage_bool_indicator_eq_union],
  split_ifs ; simp [s.union_compl_self]
end

end set
