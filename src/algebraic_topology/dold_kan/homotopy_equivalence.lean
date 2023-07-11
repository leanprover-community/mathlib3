/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.normalized

/-!

# The normalized Moore complex and the alternating face map complex are homotopy equivalent

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, when the category `A` is abelian, we obtain the homotopy equivalence
`homotopy_equiv_normalized_Moore_complex_alternating_face_map_complex` between the
normalized Moore complex and the alternating face map complex of a simplicial object in `A`.

-/

open category_theory category_theory.category category_theory.limits
  category_theory.preadditive
open_locale simplicial dold_kan

noncomputable theory

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C] (X : simplicial_object C)

/-- Inductive construction of homotopies from `P q` to `𝟙 _` -/
noncomputable def homotopy_P_to_id : Π (q : ℕ),
  homotopy (P q : K[X] ⟶ _) (𝟙 _)
| 0     := homotopy.refl _
| (q+1) := begin
    refine homotopy.trans (homotopy.of_eq _)
      (homotopy.trans
        (homotopy.add (homotopy_P_to_id q) (homotopy.comp_left (homotopy_Hσ_to_zero q) (P q)))
        (homotopy.of_eq _)),
    { unfold P, simp only [comp_add, comp_id], },
    { simp only [add_zero, comp_zero], },
  end

/-- The complement projection `Q q` to `P q` is homotopic to zero. -/
def homotopy_Q_to_zero (q : ℕ) : homotopy (Q q : K[X] ⟶ _) 0 :=
homotopy.equiv_sub_zero.to_fun (homotopy_P_to_id X q).symm

lemma homotopy_P_to_id_eventually_constant {q n : ℕ} (hqn : n<q):
  ((homotopy_P_to_id X (q+1)).hom n (n+1) : X _[n] ⟶ X _[n+1]) =
  (homotopy_P_to_id X q).hom n (n+1) :=
begin
  unfold homotopy_P_to_id,
  simp only [homotopy_Hσ_to_zero, hσ'_eq_zero hqn (c_mk (n+1) n rfl), homotopy.trans_hom,
    pi.add_apply, homotopy.of_eq_hom, pi.zero_apply, homotopy.add_hom, homotopy.comp_left_hom,
    homotopy.null_homotopy'_hom, complex_shape.down_rel, eq_self_iff_true, dite_eq_ite,
    if_true, comp_zero, add_zero, zero_add],
end

variable (X)

/-- Construction of the homotopy from `P_infty` to the identity using eventually
(termwise) constant homotopies from `P q` to the identity for all `q` -/
@[simps]
def homotopy_P_infty_to_id :
  homotopy (P_infty : K[X] ⟶ _) (𝟙 _) :=
{ hom := λ i j, (homotopy_P_to_id X (j+1)).hom i j,
  zero' := λ i j hij, homotopy.zero _ i j hij,
  comm := λ n, begin
    cases n,
    { simpa only [homotopy.d_next_zero_chain_complex, homotopy.prev_d_chain_complex,  P_f_0_eq,
        zero_add, homological_complex.id_f, P_infty_f] using (homotopy_P_to_id X 2).comm 0, },
    { simpa only [homotopy.d_next_succ_chain_complex, homotopy.prev_d_chain_complex,
        homological_complex.id_f, P_infty_f, ← P_is_eventually_constant (rfl.le : n+1 ≤ n+1),
        homotopy_P_to_id_eventually_constant X (lt_add_one (n+1))]
        using (homotopy_P_to_id X (n+2)).comm (n+1), },
  end }

/-- The inclusion of the Moore complex in the alternating face map complex
is an homotopy equivalence -/
@[simps]
def homotopy_equiv_normalized_Moore_complex_alternating_face_map_complex {A : Type*}
  [category A] [abelian A] {Y : simplicial_object A} :
  homotopy_equiv ((normalized_Moore_complex A).obj Y) ((alternating_face_map_complex A).obj Y) :=
{ hom := inclusion_of_Moore_complex_map Y,
  inv := P_infty_to_normalized_Moore_complex Y,
  homotopy_hom_inv_id := homotopy.of_eq (split_mono_inclusion_of_Moore_complex_map Y).id,
  homotopy_inv_hom_id := homotopy.trans
    (homotopy.of_eq (P_infty_to_normalized_Moore_complex_comp_inclusion_of_Moore_complex_map Y))
    (homotopy_P_infty_to_id Y), }

end dold_kan

end algebraic_topology
