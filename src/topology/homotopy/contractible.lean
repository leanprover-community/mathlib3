/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/

import topology.homotopy.path
import topology.homotopy.equiv

/-!
# Contractible spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we define `contractible_space`, a space that is homotopy equivalent to `unit`.
-/

noncomputable theory

namespace continuous_map
variables {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]

/-- A map is nullhomotopic if it is homotopic to a constant map. -/
def nullhomotopic (f : C(X, Y)) : Prop :=
∃ y : Y, homotopic f (continuous_map.const _ y)

lemma nullhomotopic_of_constant (y : Y) : nullhomotopic (continuous_map.const X y) :=
⟨y, by refl⟩

lemma nullhomotopic.comp_right {f : C(X, Y)} (hf : f.nullhomotopic) (g : C(Y, Z)) :
  (g.comp f).nullhomotopic :=
by { cases hf with y hy, use g y, exact homotopic.hcomp hy (homotopic.refl g), }

lemma nullhomotopic.comp_left {f : C(Y, Z)} (hf : f.nullhomotopic) (g : C(X, Y)) :
  (f.comp g).nullhomotopic :=
by { cases hf with y hy, use y, exact homotopic.hcomp (homotopic.refl g) hy, }

end continuous_map

open continuous_map
open_locale continuous_map

/-- A contractible space is one that is homotopy equivalent to `unit`. -/
class contractible_space (X : Type*) [topological_space X] : Prop :=
(hequiv_unit [] : nonempty (X ≃ₕ unit))

lemma id_nullhomotopic (X : Type*) [topological_space X] [contractible_space X] :
  (continuous_map.id X).nullhomotopic :=
begin
  obtain ⟨hv⟩ := contractible_space.hequiv_unit X,
  use hv.inv_fun (),
  convert hv.left_inv.symm,
  ext, simp, congr,
end

lemma contractible_iff_id_nullhomotopic (Y : Type*) [topological_space Y] :
  contractible_space Y ↔ (continuous_map.id Y).nullhomotopic :=
begin
  split, { introI, apply id_nullhomotopic, },
  rintro ⟨p, h⟩,
  refine_struct { hequiv_unit := ⟨
  { to_fun := continuous_map.const _ (),
    inv_fun := continuous_map.const _ p }⟩ },
  { exact h.symm, }, { convert homotopic.refl (continuous_map.id unit), ext, },
end

variables {X Y : Type*} [topological_space X] [topological_space Y]

protected lemma continuous_map.homotopy_equiv.contractible_space [contractible_space Y]
  (e : X ≃ₕ Y) :
  contractible_space X :=
⟨(contractible_space.hequiv_unit Y).map e.trans⟩

protected lemma continuous_map.homotopy_equiv.contractible_space_iff (e : X ≃ₕ Y) :
  contractible_space X ↔ contractible_space Y :=
⟨by { introI h, exact e.symm.contractible_space }, by { introI h, exact e.contractible_space }⟩

protected lemma homeomorph.contractible_space [contractible_space Y] (e : X ≃ₜ Y) :
  contractible_space X :=
e.to_homotopy_equiv.contractible_space

protected lemma homeomorph.contractible_space_iff (e : X ≃ₜ Y) :
  contractible_space X ↔ contractible_space Y :=
e.to_homotopy_equiv.contractible_space_iff

namespace contractible_space

@[priority 100]
instance [contractible_space X] : path_connected_space X :=
begin
  obtain ⟨p, ⟨h⟩⟩ := id_nullhomotopic X,
  have : ∀ x, joined p x := λ x, ⟨(h.eval_at x).symm⟩,
  rw path_connected_space_iff_eq, use p, ext, tauto,
end

end contractible_space
