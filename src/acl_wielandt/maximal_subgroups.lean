/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

-- import algebra.group.defs
import group_theory.subgroup.basic

/-! # Maximal subgroups

A subgroup `is_maximal` if it is maximal in the collection of
proper subgroups.

We prove a few basic results which are essentially copied from
those about maximal ideals.

Besides them, we have :
* `is_maximal_iff` proves that a subgroup K of G is maximal
if and only  if it is not ⊤ and if for all g ∈ G such that g ∉ K,
every subgroup containing K and g is ⊤.

## TODO

Is it useful to write it in a greater generality?
Will we need to write this for all `sub`-structures ?

-/
variables {G : Type*} [group G]

namespace subgroup

/-- A subgroup is maximal if it is maximal in the collection of proper subgroups. -/
class is_maximal (K : subgroup G) : Prop :=
(out : is_coatom K)

theorem is_maximal_def {K : subgroup G} : K.is_maximal ↔ is_coatom K := ⟨λ h, h.1, λ h, ⟨h⟩⟩

theorem is_maximal.ne_top {K : subgroup G} (h : K.is_maximal) : K ≠ ⊤ := (is_maximal_def.1 h).1

theorem is_maximal_iff {K: subgroup G} : K.is_maximal ↔
  K ≠ ⊤ ∧ ∀ (H: subgroup G) g, K ≤ H → g ∉ K → g ∈ H → H = ⊤ :=
begin
  split,
  { intro hK, split, exact is_maximal.ne_top hK,
  intros H g hKH hgK hgH,
  suffices : K < H,
    apply (is_maximal_def.1 hK).2, assumption,
  have zKH : K ≠ H, { rw ne.def, intro z, rw z at hgK, exact hgK hgH },
  exact (ne.le_iff_lt zKH).mp hKH,},
  { rintros ⟨ hG, hmax ⟩,
  split, split, assumption,
  introsI H hKH,
  obtain ⟨ g, hgH, hgK ⟩ := (set.exists_of_ssubset hKH),
  exact hmax H g (le_of_lt hKH) hgK hgH },
end

theorem is_maximal.eq_of_le {K H: subgroup G} (hK : K.is_maximal) (hH : H ≠ ⊤) (KH : K ≤ H) :
  K = H :=
eq_iff_le_not_lt.2 ⟨KH, λ h, hH (hK.1.2 _ h)⟩

end subgroup
#lint
