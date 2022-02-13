/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import group_theory.quotient_group

/-!
# Group theory lemmas
-/

noncomputable theory

universe u

variables {G H : Type u}

----------------------------------------------------------------------------------------------------
/-! ## Group theory -/

/-- If `ker(G →* H)` and `H` are finite, then `G` is finite. -/
@[to_additive "If `ker(G →+ H)` and `H` are finite, then `G` is finite."]
def group.fintype_of_ker_codom [group G] [group H] {f : G →* H} :
  fintype f.ker → fintype H → fintype G :=
λ hK hH, @fintype.of_equiv _ _
  (@prod.fintype _ _ (@fintype.of_injective _ _ hH _ $ quotient_group.ker_lift_injective f) hK)
  subgroup.group_equiv_quotient_times_subgroup.symm

local notation n`⬝`G := (zpow_group_hom n : G →* G).range

/-- If `G ≃* H`, then `G / Gⁿ ≃* H / Hⁿ`. -/
@[to_additive "If `G ≃+ H`, then `G / nG ≃+ H / nH`."]
def quotient_group.quotient_equiv_of_equiv [comm_group G] [comm_group H] (hGH : G ≃* H) (n : ℤ) :
  G ⧸ (n⬝G) ≃* H ⧸ (n⬝H) :=
begin
  have ker_eq_range : (n⬝G) = ((quotient_group.mk' (n⬝H)).comp hGH.to_monoid_hom).ker :=
  begin
    ext g,
    change (∃ h : G, h ^ n = g) ↔ ↑(hGH.to_monoid_hom g) = _,
    rw [quotient_group.eq_one_iff],
    change _ ↔ ∃ h : H, h ^ n = hGH.to_monoid_hom g,
    exact ⟨λ hg, ⟨hGH.to_monoid_hom hg.some, by rw [← map_zpow, hg.some_spec]⟩,
           λ hg, ⟨hGH.symm.to_monoid_hom hg.some, by simpa only [← map_zpow, hg.some_spec]
                                                  using hGH.left_inv g⟩⟩
  end,
  rw [ker_eq_range],
  apply quotient_group.quotient_ker_equiv_of_surjective,
  intro g,
  existsi [hGH.inv_fun $ quot.out g],
  change ↑(hGH.to_fun $ hGH.inv_fun $ quot.out g) = g,
  rw [hGH.right_inv],
  exact quot.out_eq g
end

----------------------------------------------------------------------------------------------------
