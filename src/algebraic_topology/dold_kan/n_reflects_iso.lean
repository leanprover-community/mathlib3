/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.functor_n
import algebraic_topology.dold_kan.decomposition
import category_theory.idempotents.homological_complex

/-!

# N₁ and N₂ reflects isomorphisms

In this file, it is shown that the functor
`N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)`
reflects isomorphisms for any preadditive category `C`.

TODO @joelriou: deduce that `N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)`
also reflects isomorphisms.

-/

open category_theory
open category_theory.category
open category_theory.idempotents
open opposite
open_locale simplicial

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]

open morph_components

instance : reflects_isomorphisms (N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)) :=
⟨λ X Y f, begin
  introI,
  /- restating the result in a way that allows induction on the degree n -/
  suffices : ∀ (n : ℕ), is_iso (f.app (op [n])),
  { haveI : ∀ (Δ : simplex_categoryᵒᵖ), is_iso (f.app Δ) := λ Δ, this Δ.unop.len,
    apply nat_iso.is_iso_of_is_iso_app, },
  /- restating the assumption in a more practical form -/
  have h₁ := homological_complex.congr_hom (karoubi.hom_ext.mp (is_iso.hom_inv_id (N₁.map f))),
  have h₂ := homological_complex.congr_hom (karoubi.hom_ext.mp (is_iso.inv_hom_id (N₁.map f))),
  have h₃ := λ n, karoubi.homological_complex.p_comm_f_assoc (inv (N₁.map f)) (n) (f.app (op [n])),
  simp only [N₁_map_f, karoubi.comp_f, homological_complex.comp_f,
    alternating_face_map_complex.map_f, N₁_obj_p, karoubi.id_eq, assoc] at h₁ h₂ h₃,
  /- we have to construct an inverse to f in degree n, by induction on n -/
  intro n,
  induction n with n hn,
  /- degree 0 -/
  { use (inv (N₁.map f)).f.f 0,
    have h₁₀ := h₁ 0,
    have h₂₀ := h₂ 0,
    dsimp at h₁₀ h₂₀,
    simp only [id_comp, comp_id] at h₁₀ h₂₀,
    tauto, },
  /- induction step -/
  { haveI := hn,
    use φ
      { a := P_infty.f (n+1) ≫ (inv (N₁.map f)).f.f (n+1),
        b := λ i, inv (f.app (op [n])) ≫ X.σ i, },
    simp only [morph_components.id, ← id_φ, ← pre_comp_φ, pre_comp, ← post_comp_φ,
      post_comp, P_infty_f_naturality_assoc, is_iso.hom_inv_id_assoc, assoc,
      is_iso.inv_hom_id_assoc, simplicial_object.σ_naturality, h₁, h₂, h₃],
    tauto, },
end⟩

end dold_kan

end algebraic_topology
