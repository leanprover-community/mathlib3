import combinatorics.quiver.basic
import combinatorics.quiver.single_obj
import group_theory.group_action.basic
import group_theory.group_action.group
import combinatorics.quiver.covering
import group_theory.subgroup.basic
import group_theory.coset
import group_theory.quotient_group
import group_theory.group_action.quotient

universes u v w

namespace quiver

section basic

/--
Alias for the Schreier graph vertex type.
-/
def schreier_graph (V : Type*) {M : Type*} [has_smul M V] {S : Type*} (ι : S → M) := V

/--
Converting between the original vertex type and the alias.
-/
@[simps] def equiv_schreier_graph {V : Type*} {M : Type*} [has_smul M V] {S : Type*} {ι : S → M} :
  V ≃ schreier_graph V ι := equiv.refl V

variables (V : Type*) {M : Type*} [has_smul M V] {S : Type*} (ι : S → M)

instance : has_smul M (schreier_graph V ι) :=
{ smul := λ x y, equiv_schreier_graph $ x • (equiv_schreier_graph.symm y)}

/--
The `quiver` instance on `schreier_graph V ι`.
The set of arrow from `x` to `y` is the subset of `S` such that `(ι s) x = y`.
-/
instance schreier_graph.quiver : quiver (schreier_graph V ι) :=
{ hom := λ x y, {s : S // (ι s) • x = y} }

/--
Any arrow in `schreier_graph V ι` is labelled by an element of `S`.
This is encoded as mapping to the `single_obj S` quiver.
-/
@[simps] def schreier_graph_labelling : (schreier_graph V ι) ⥤q single_obj S :=
{ obj := λ (x : schreier_graph V ι), single_obj.star S,
  map := λ x y e, subtype.rec_on e (λ s h, s), }

end basic

section group_action

variables (V : Type*) {M : Type*} [group M] [mul_action M V] {S : Type*} (ι : S → M)

instance : mul_action M (schreier_graph V ι) :=
{ smul := has_smul.smul,
  one_smul := mul_action.one_smul,
  mul_smul := mul_action.mul_smul }

instance path_action : mul_action (subgroup.closure (set.range ι)) (schreier_graph V ι) :=
{ smul := by { rintro ⟨x,xι⟩, simp at xι, },
  one_smul := mul_action.one_smul,
  mul_smul := mul_action.mul_smul }

lemma schreier_graph_labelling_is_covering : (schreier_graph_labelling V ι).is_covering :=
begin
  refine ⟨λ u, ⟨_, _⟩, λ u, ⟨_, _⟩⟩,
  { rintro ⟨v,⟨x,hx⟩⟩ ⟨w,⟨y,hy⟩⟩ h,
    simp only [prefunctor.star_apply, schreier_graph_labelling_map, single_obj.to_hom_apply,
               eq_iff_true_of_subsingleton, heq_iff_eq, true_and] at h,
    subst_vars, },
  { rintro ⟨⟨⟩,x⟩, exact ⟨⟨(ι x) • u, ⟨x, rfl⟩⟩, rfl⟩, },
  { rintro ⟨v,⟨x,hx⟩⟩ ⟨w,⟨y,hy⟩⟩ h,
    simp only [prefunctor.costar_apply, schreier_graph_labelling_map, single_obj.to_hom_apply,
               eq_iff_true_of_subsingleton, heq_iff_eq, true_and] at h,
    subst_vars,
    simp only [smul_left_cancel_iff] at hy,
    subst hy, },
  { rintro ⟨⟨⟩,x⟩,
    exact ⟨⟨(ι x) ⁻¹ • u, ⟨x, by simp⟩⟩, by simp⟩, },
end

section schreier_coset_graph

/--
A Schreier coset graph is the Schreier graph of the action of a group `M` on the cosets `M ⧸ H`.
-/
abbreviation schreier_coset_graph (H : subgroup M) := schreier_graph (M ⧸ H) ι
abbreviation schreier_coset_graph_labelling (H : subgroup M) := schreier_graph_labelling (M ⧸ H) ι

notation `𝑺` := schreier_coset_graph
notation `𝑺l` := schreier_coset_graph_labelling

@[simps] noncomputable def from_coset_graph (v₀ : V) :
  schreier_coset_graph ι (mul_action.stabilizer M v₀) ⥤q schreier_graph (mul_action.orbit M v₀) ι :=
{ obj := (mul_action.orbit_equiv_quotient_stabilizer M v₀).symm,
  map := λ X Y e, ⟨e.val, by obtain ⟨e,rfl⟩ := e;
                          simp only [mul_action.smul_orbit_equiv_quotient_stabilizer_symm_apply]⟩ }

lemma from_coset_graph_labelling (v₀ : V) :
  (from_coset_graph V ι v₀) ⋙q schreier_graph_labelling (mul_action.orbit M v₀) ι =
  schreier_graph_labelling (M ⧸ mul_action.stabilizer M v₀) ι :=
begin
  dsimp only [from_coset_graph, schreier_graph_labelling],
  fapply prefunctor.ext,
  { simp only [eq_iff_true_of_subsingleton, implies_true_iff], },
  { rintros _ _ ⟨e, he⟩,
    simp only [prefunctor.comp_map, eq_rec_constant], },
end

@[simps] noncomputable def to_coset_graph (v₀ : V) :
  schreier_graph (mul_action.orbit M v₀) ι ⥤q schreier_coset_graph ι (mul_action.stabilizer M v₀) :=
{ obj := (mul_action.orbit_equiv_quotient_stabilizer M v₀),
  map := λ X Y e, ⟨e.val, by obtain ⟨e,rfl⟩ := e;
                          simp only [mul_action.smul_orbit_equiv_quotient_stabilizer_apply]⟩ }

lemma to_coset_graph_labelling (v₀ : V) :
  (to_coset_graph V ι v₀) ⋙q schreier_graph_labelling (M ⧸ mul_action.stabilizer M v₀) ι =
  schreier_graph_labelling (mul_action.orbit M v₀) ι:=
begin
  dsimp only [to_coset_graph, schreier_graph_labelling],
  fapply prefunctor.ext,
  { simp only [eq_iff_true_of_subsingleton, implies_true_iff], },
  { rintros _ _ ⟨_,_⟩,
    simp only [prefunctor.comp_map, eq_rec_constant], },
end

lemma from_coset_graph_to_coset_graph (v₀ : V) :
  from_coset_graph V ι v₀ ⋙q to_coset_graph V ι v₀ = 𝟭q _ :=
begin
  have obj : ∀ x, (from_coset_graph V ι v₀ ⋙q to_coset_graph V ι v₀).obj x = (𝟭q _).obj x, by
  { rintro _,
    simp only [to_coset_graph, from_coset_graph, prefunctor.comp_obj, equiv.apply_symm_apply,
               prefunctor.id_obj, id.def], },
  apply prefunctor.ext obj,
  rintro u v e,
  let hu := obj u,
  let hv := obj v,
  change (from_coset_graph V ι v₀ ⋙q to_coset_graph V ι v₀).map e =
         eq.rec_on hv.symm (eq.rec_on hu.symm ((𝟭q _).map e)),
  sorry,
end

lemma to_coset_graph_from_coset_graph (v₀ : V) :
  to_coset_graph V ι v₀ ⋙q from_coset_graph V ι v₀ = 𝟭q _ :=
begin
  dsimp only [to_coset_graph, from_coset_graph],
  fapply prefunctor.ext,
  { rintro ⟨_,_⟩,
    simp, },
  { rintro ⟨_,⟨m,rfl⟩⟩ ⟨_,⟨n,rfl⟩⟩ ⟨x,h⟩,
    simp,
    simp at h,
    sorry, }
end

section action

variables {N : subgroup M} [Nn : N.normal]
include Nn

@[simps] def as_autom (g : M) : schreier_coset_graph ι N ⥤q schreier_coset_graph ι N :=
{ obj := λ x, equiv_schreier_graph ((equiv_schreier_graph.symm x) * (g⁻¹)),
  map := λ x y a, ⟨a.val, by
    begin
      obtain ⟨a,rfl⟩ := a,
      obtain ⟨x⟩ := x,
      change ι a • ((↑x : M ⧸ N) * (↑g)⁻¹) = ι a • (↑x : M ⧸ N) * (↑g)⁻¹,
      simpa only [mul_action.quotient.smul_coe, smul_eq_mul, quotient_group.coe_mul, mul_assoc],
    end⟩ }

lemma as_autom_labelling (g : M) :
  as_autom ι g ⋙q schreier_coset_graph_labelling ι N = schreier_coset_graph_labelling ι N :=
begin
  dsimp only [as_autom, schreier_graph_labelling],
  fapply prefunctor.ext,
  { simp only [eq_iff_true_of_subsingleton, implies_true_iff], },
  { rintro _ _ ⟨_, rfl⟩,
    simp [subtype.coe_mk, prefunctor.comp_map, schreier_graph_labelling_map,
    eq_rec_constant], },
end

lemma as_autom_one : as_autom ι 1 = 𝟭q (𝑺 ι N) :=
begin
  dsimp only [as_autom],
  fapply prefunctor.ext,
  { simp only [equiv_schreier_graph_symm_apply, quotient_group.coe_one, inv_one, mul_one,
               equiv_schreier_graph_apply, prefunctor.id_obj, id.def, eq_self_iff_true,
               implies_true_iff], },
  { rintro _ _ ⟨_, rfl⟩,
    simp only [prefunctor.id_map],
    sorry, },
end

lemma as_autom_mul (g h : M) :
  (as_autom ι (g * h) : 𝑺 ι N ⥤q  𝑺 ι N) = (as_autom ι h) ⋙q (as_autom ι g) :=
begin
  dsimp only [as_autom],
  fapply prefunctor.ext,
  { simp only [mul_assoc, equiv_schreier_graph_symm_apply, quotient_group.coe_mul, mul_inv_rev,
               equiv_schreier_graph_apply, prefunctor.comp_obj, eq_self_iff_true,
               implies_true_iff], },
  { rintro _ _ ⟨_, rfl⟩,
    simp only [prefunctor.comp_map],
    sorry, },
end

end action

end schreier_coset_graph

/--
The Cayley graph of `M` w.r.t. `ι : S → M` is the Schreier coset graph where `H` is the trivial
subgroup of `M`.
-/
abbreviation cayley_graph := schreier_coset_graph ι (⊥ : subgroup M)
abbreviation cayley_graph_labelling := schreier_graph_labelling (M ⧸ (⊥ : subgroup M)) ι

notation `𝑪` := cayley_graph
notation `𝑪l` := cayley_graph_labelling

namespace cayley_graph

/-
@[simps] def as_autom (g : M) : cayley_graph ι ⥤q cayley_graph ι :=
{ obj := ,--equiv_schreier_graph ((equiv_schreier_graph.symm x) * (g⁻¹)),
  map := λ x y a,
    ⟨a.val, by
      { obtain ⟨a,rfl⟩ := a,
        simp only [equiv_schreier_graph_symm_apply, equiv_schreier_graph_apply],


        let := rw mul_action.quotient.smul_mk,
        sorry, }⟩ }
/--
Any automorphism of the cayley graph (preserving the labelling) comes from an element of the group.
not true actually
-/
lemma as_autom_surjective {φ ψ : cayley_graph ι ⥤q cayley_graph ι}
  (φψ : φ ⋙q ψ = 𝟭q _) (ψφ : ψ ⋙q φ = 𝟭q _)
  (φc : φ ⋙q cayley_graph_labelling ι = cayley_graph_labelling ι) :
  ∃ g : M, φ = as_autom ι g :=
begin

end
-/
end cayley_graph

end group_action

end quiver
