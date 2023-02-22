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

abbreviation schreier_coset_graph (H : subgroup M) := schreier_graph (M ⧸ H) ι

@[simps] noncomputable def from_coset_graph (v₀ : V) :
  schreier_coset_graph ι (mul_action.stabilizer M v₀) ⥤q schreier_graph (mul_action.orbit M v₀) ι :=
{ obj := (mul_action.orbit_equiv_quotient_stabilizer M v₀).symm,
  map := λ X Y e, ⟨e.val, by obtain ⟨e,rfl⟩ := e;
                          simp only [mul_action.smul_orbit_equiv_quotient_stabilizer_symm_apply]⟩ }

set_option profiler true

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
  { rintros _ _ ⟨e,he⟩,
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
  { rintro ⟨_,_⟩ ⟨_,_⟩ ⟨_,h⟩, sorry, }
end

abbreviation cayley_graph := schreier_coset_graph ι (⊥ : subgroup M)

end group_action

end quiver
