import category_theory.action
  combinatorics.quiver
  group_theory.free_group

universes v u

open category_theory

class is_free_group (G) [group.{u} G] :=
(generators : Type u)
(of : generators → G)
(unique_lift : ∀ {X} [group.{u} X] (f : generators → X),
                ∃! F : G →* X, ∀ a, F (of a) = f a)

instance {A} : is_free_group (free_group A) :=
{ generators := A,
  of := free_group.of,
  unique_lift := by { introsI X _ f, exact ⟨free_group.lift f, λ _, free_group.lift.of,
      λ g hg, monoid_hom.ext (λ _, free_group.lift.unique g hg)⟩ } }

namespace is_free_group

lemma end_is_id {G} [group G] [is_free_group G] (f : G →* G)
  (h : ∀ a, f (of a) = of a) : ∀ g, f g = g :=
begin
  suffices : f = monoid_hom.id G,
  { intro, rw [this, monoid_hom.id_apply] },
  rcases unique_lift (f ∘ of) with ⟨_, _, u⟩,
  exact (u _ (λ _, rfl)).trans (u _ (by simp [h])).symm,
end

noncomputable def iso_free_group_of_is_free_group (G) [group G] [is_free_group G] :
  G ≃* free_group (generators G) :=
let ⟨F, hF, uF⟩ := classical.indefinite_description _ (unique_lift free_group.of) in
{ to_fun := F,
  inv_fun := free_group.lift of,
  left_inv := end_is_id ((free_group.lift of).comp F) (by simp [hF]),
  right_inv := by { suffices : F.comp (free_group.lift of) = monoid_hom.id _,
    { rwa monoid_hom.ext_iff at this }, apply free_group.ext_hom, simp [hF] },
  map_mul' := F.map_mul }

def of_mul_equiv {G H} [group G] [group H] (h : G ≃* H) [is_free_group G] : is_free_group H :=
{ generators := generators G,
  of := h ∘ of,
  unique_lift := begin
    introsI X _ f,
    rcases unique_lift f with ⟨F, hF, uF⟩,
    refine ⟨F.comp h.symm.to_monoid_hom, by simp [hF], _⟩,
    intros F' hF',
    suffices : F'.comp h.to_monoid_hom = F,
    { rw ←this, ext, simp },
    apply uF,
    simp [hF'],
  end }

end is_free_group

class is_free_groupoid (G) [groupoid.{v} G] :=
(generators : quiver.{v} G)
(of : Π ⦃a b⦄, generators.arrow a b → (a ⟶ b))
(unique_lift : ∀ X [group.{v} X] (f : generators.labelling X),
                ∃! F : G ⥤ single_obj X, ∀ a b (g : generators.arrow a b),
                  F.map (of g) = f g)

instance {G A X : Type*} [monoid G] [mul_action G A] : mul_action Gᵒᵖ (A → X) :=
{ smul := λ g' F a, F (g'.unop • a),
  one_smul := by simp,
  mul_smul := by simp [mul_smul] }

@[simp] lemma arrow_action_apply {G A X : Type*} [monoid G] [mul_action G A]
  (g : Gᵒᵖ) (F : A → X) (a : A) : (g • F) a = F (g.unop • a) := rfl

def foo {G A X} [group G] [mul_action G A] [has_mul X] :
  Gᵒᵖ →* mul_aut (A → X) :=
{ to_fun := λ g, {
    to_fun := λ F, g • F,
    inv_fun := λ F, g⁻¹ • F,
    left_inv := λ F, inv_smul_smul g F,
    right_inv := λ F, smul_inv_smul g F,
    map_mul' := by { intros, funext, simp only [arrow_action_apply, pi.mul_apply]} },
  map_one' := by { ext, simp only [mul_aut.one_apply, mul_equiv.coe_mk, one_smul]},
  map_mul' := by {intros, ext, simp only [mul_smul, mul_equiv.coe_mk, mul_aut.mul_apply]} }
