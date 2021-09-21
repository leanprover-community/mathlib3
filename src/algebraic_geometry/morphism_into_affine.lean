/- Quite an ugly proof. Mostly because of the `eq_to_hom` stuff. -/
import algebraic_geometry.global_section_of_spec

universe u

noncomputable theory
open category_theory
open opposite
open algebraic_geometry.LocallyRingedSpace
open topological_space

namespace algebraic_geometry

namespace Spec

/- Basically just `Top.presheaf.section_ext`. However, it is defined only for Type-valued presheaves.-/
lemma hom_eq_iff_stalk_eq {X Y : LocallyRingedSpace} (f g : X ⟶ Y)
  (h1 : f.val.base = g.val.base) (h2 : ∀ (x : X), stalk_map f x = (eq_to_hom (by rwa h1)) ≫ stalk_map g x) : f = g
  := sorry

/- Basically just `Top.presheaf.germ_exist` then `structure_sheaf.exists_const`. -/
lemma germ_locally_fraction (R : CommRing) (x : Top_obj R) (s : (structure_sheaf R).presheaf.stalk x)
  : ∃ (U : opens (Top_obj R)) (f g : R) (hx1) (hx2),
    (structure_sheaf R).presheaf.germ ⟨x, hx1⟩ (structure_sheaf.const R f g U hx2) = s := sorry

local attribute [reassoc] structure_sheaf.to_open_res

/- For a constant section `a/1` on `U`, `φ(a/1)` is equal to `φ(a)` restricted onto `U`. -/
lemma hom_app_const {R : CommRing} {X : LocallyRingedSpace}
  (f : X⟶ Spec.to_LocallyRingedSpace.obj (op R))
  (U : opens (Top_obj R)) (a : R) (φ) (H : φ = f.val.c.app (op ⊤))
  : (f.val.c.app (op (by dsimp[to_LocallyRingedSpace]; exact U))
      (structure_sheaf.const R a 1 U (λ x _, submonoid.one_mem _))) =
        ((f.val.base _* X.presheaf).map (opens.le_top U).op (φ (to_Spec_Γ R a)))
  := by {
    have : to_Spec_Γ R ≫ φ ≫ (f.val.base _* X.presheaf).map (opens.le_top U).op
    = structure_sheaf.to_open R U ≫ f.val.c.app (op U) := by {
      rw H, unfold to_Spec_Γ,
      rw ← f.val.c.naturality,
      erw structure_sheaf.to_open_res_assoc,
    },
    erw congr_hom this,
    simp only [comp_apply, structure_sheaf.to_open_eq_const],
    refl
  }

variables {R : CommRing.{u}} {X : LocallyRingedSpace.{u}}
  {f g : X ⟶ Spec.to_LocallyRingedSpace.obj (op R)}
  (h1 : f.val.base = g.val.base) (h2 : Γ.map f.op = Γ.map g.op) {U: opens (Top_obj R)}
  (a b : R) (hb : ∀ x ∈ U, b ∈ (x : prime_spectrum.Top R).as_ideal.prime_compl)


/- The `eq_to_hom`. -/
include h1
private def coerce : (g.val.base _* X.presheaf).obj (op U) ⟶ (f.val.base _* X.presheaf).obj (op U)
    := X.presheaf.map (eq_to_hom (by rw h1) :
      (opens.map f.val.base).obj U ⟶ (opens.map g.val.base).obj U).op
omit h1

include h2
/- Turns out that `Γ.map` is a little different from `_.val.c.app (op ⊤)`. -/
private lemma global_eq : f.val.c.app (op ⊤) = g.val.c.app (op ⊤) := by {
  simp only [Γ_map] at h2,
  change f.val.c.app (op ⊤) ≫ X.presheaf.map (𝟙 _ : op ((opens.map f.val.base).obj ⊤) ⟶ op ⊤) =
    g.val.c.app (op ⊤) ≫ X.presheaf.map (𝟙 _ : op ((opens.map g.val.base).obj ⊤) ⟶ op ⊤) at h2,
  erw [X.presheaf.map_id, category.comp_id, category.comp_id] at h2,
  exact h2,
}

/- `f(a/1) = g(a/1)` -/
private lemma const_eq_1 :
  (f.val.c.app (op U) (structure_sheaf.const R a 1 U (λ x _, submonoid.one_mem _))) =
      coerce h1 (g.val.c.app (op U) (structure_sheaf.const R a 1 U (λ x _, submonoid.one_mem _)))
:= by {
  erw hom_app_const g _ _ (f.val.c.app (op ⊤)) (global_eq h2),
  erw hom_app_const _ _ _ _ rfl,
  change (to_Spec_Γ R ≫ _ ≫ X.presheaf.map _) a =
    (to_Spec_Γ R ≫ _ ≫ X.presheaf.map _ ≫ X.presheaf.map _) a,
  rw ← X.presheaf.map_comp,
  congr,
}

/- `f(1/b) = g(1/b)` -/
private lemma const_eq_2 :
  (f.val.c.app (op U) (structure_sheaf.const R 1 b U hb)) =
      coerce h1 (g.val.c.app (op U) (structure_sheaf.const R 1 b U hb))
:= by {
  apply @inv_unique _ _
      (f.val.c.app (op U) (structure_sheaf.const R b 1 U (λ _ _, submonoid.one_mem _))), {
      rw ← ring_hom.map_mul,
      rw structure_sheaf.const_mul_rev, simp only [eq_self_iff_true, ring_hom.map_one],
    }, {
      simp only [const_eq_1 h1 h2 b, ← ring_hom.map_mul,
        structure_sheaf.const_mul_rev, ring_hom.map_one],
    }
}

variables (f g)
include h1

lemma hom_to_affine_eq_if_global_eq : f = g := by {
  apply hom_eq_iff_stalk_eq, swap, exact h1,
  intro x,
  apply ring_hom.ext,
  intro s,
  rcases germ_locally_fraction _ _ s with ⟨U, a, b, hx1, hb, eq⟩,
  have := congr (congr_arg has_mul.mul (const_eq_1 h1 h2 a)) (const_eq_2 h1 h2 b hb),
  simp only [← ring_hom.map_mul, structure_sheaf.const_mul, mul_one, one_mul] at this,
  rw ← eq,

  /- Basically `eq_to_hom` juggling from this point forward. -/
  erw PresheafedSpace.stalk_map_germ_apply f.val U ⟨x, hx1⟩,
  erw this,
  rw ← comp_apply, rw ← comp_apply, rw ← comp_apply,
  refine congr_fun _ (structure_sheaf.const R a b U hb),
  unfold coerce,
  rw Top.presheaf.germ_res X.presheaf (eq_to_hom _) ⟨x, _⟩,
  rw ← PresheafedSpace.stalk_map_germ g.val U,
  rw ← category.assoc,
  congr' 2,
  /- Yuck! -/
  let F := λ (x : U), (structure_sheaf R).presheaf.germ x,
  have : ∀ (a b) (H : a = b), F a = F b ≫ eq_to_hom (by rw H) := λ _ _ H, by subst H; simp,
  apply this,
  congr' 2,
  rw h1,
}

end Spec
end algebraic_geometry
