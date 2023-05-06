import algebra.category.Group.adjunctions
import algebra.category.Group.equivalence_Group_AddGroup
import algebraic_geometry.GroupObject.basic
import algebraic_geometry.Gamma_Spec_adjunction
import algebraic_geometry.Scheme
import data.polynomial.laurent

open category_theory algebraic_geometry
universes v u w

local attribute [instance] over.over_has_terminal
  over.construct_products.over_binary_product_of_pullback

abbreviation GroupScheme (S : Scheme) := RepresentableGroupFunctor (over S)

section

variables (S : AffineScheme)

instance : has_forget₂ CommRing Mon :=
{ forget₂ :=
  { obj := λ X, Mon.of X,
    map := λ X Y f, f.to_monoid_hom },
  forget_comp := rfl }

instance : has_forget₂ CommRing AddGroup :=
{ forget₂ :=
  { obj := λ X, AddGroup.of X,
    map := λ X Y f, f.to_add_monoid_hom },
  forget_comp := rfl }

-- where's this?
@[simps] noncomputable def Ring.polynomial : Ring ⥤ Ring :=
{ obj := λ R, Ring.of (polynomial R),
  map := λ R S f, polynomial.map_ring_hom f ,
  map_id' := λ R, polynomial.map_ring_hom_id,
  map_comp' := λ R S T f g, (polynomial.map_ring_hom_comp g f).symm }

@[simps] noncomputable def CommRing.polynomial : CommRing ⥤ CommRing :=
{ obj := λ R, CommRing.of (polynomial R),
  map := λ R S f, polynomial.map_ring_hom f ,
  map_id' := λ R, polynomial.map_ring_hom_id,
  map_comp' := λ R S T f g, (polynomial.map_ring_hom_comp g f).symm }

-- well this is more general than the next defn but whatever.
/-noncomputable def add_monoid_algebra.map_range
  (α : Type*) [add_comm_monoid α] (R S : Type*) [comm_semiring R] [semiring S] [algebra R S] :
  add_monoid_algebra R α →+* add_monoid_algebra S α :=
{ map_one' :=
  begin
    simp only [ring_hom.coe_add_monoid_hom, ring_hom.to_add_monoid_hom_eq_coe,
      add_monoid_hom.to_fun_eq_coe, finsupp.map_range.add_monoid_hom_apply,
      add_monoid_algebra.one_def, finsupp.map_range_single, map_one],
  end,
  map_mul' := λ x y,
  begin
    simp only [ring_hom.coe_add_monoid_hom, ring_hom.to_add_monoid_hom_eq_coe,
      add_monoid_hom.to_fun_eq_coe, finsupp.map_range.add_monoid_hom_apply],
    induction y using add_monoid_algebra.induction_on,
    { induction x using add_monoid_algebra.induction_on,
      { simp only [add_monoid_algebra.of_apply,
          add_monoid_algebra.single_mul_single, one_mul, finsupp.map_range_single, map_one]},
      { rw [add_mul, finsupp.map_range_add, finsupp.map_range_add, add_mul, x_ᾰ, x_ᾰ_1],
        all_goals { exact map_add _ }},
      { rw [smul_mul_assoc, finsupp.map_range_smul, finsupp.map_range_smul, x_ᾰ, smul_mul_assoc],
        all_goals { intro r, rw [smul_eq_mul, map_mul, algebra.smul_def] }}},
    { rw [mul_add, finsupp.map_range_add, finsupp.map_range_add, mul_add, y_ᾰ, y_ᾰ_1],
      all_goals { exact map_add _ }},
    { rw [mul_smul_comm, finsupp.map_range_smul, finsupp.map_range_smul, mul_smul_comm, y_ᾰ],
      all_goals { intro r, rw [smul_eq_mul, map_mul, algebra.smul_def], } }
  end, ..finsupp.map_range.add_monoid_hom (algebra_map R S).to_add_monoid_hom }-/

noncomputable def laurent_polynomial.T_as_unit (R : Type*) [semiring R] :
  units (laurent_polynomial R) :=
{ val := laurent_polynomial.T 1,
  inv := laurent_polynomial.T (-1 : ℤ),
  val_inv := sorry,
  inv_val := sorry }

noncomputable def laurent_polynomial.map_ring_hom {R S : Type*} [comm_semiring R]
  [comm_semiring S] (f : R →+* S) :
  laurent_polynomial R →+* laurent_polynomial S :=
@is_localization.map _ _ _ _ _ _ _ _ laurent_polynomial.is_localization _ _ _ _
  laurent_polynomial.is_localization (polynomial.map_ring_hom f) $
by simp only [submonoid.closure_singleton_le_iff_mem, submonoid.mem_comap,
  polynomial.coe_map_ring_hom, polynomial.map_X, submonoid.mem_closure_singleton_self]

lemma laurent_polynomial.map_ring_hom_id (R : Type*) [comm_semiring R] :
  laurent_polynomial.map_ring_hom (ring_hom.id R) = ring_hom.id _ :=
begin
  ext,
  all_goals
  { dsimp [laurent_polynomial.map_ring_hom],
    simp only [polynomial.map_ring_hom_id, is_localization.map_id] },
end

lemma laurent_polynomial.map_ring_hom_comp {R S T : Type*} [comm_semiring R]
  [comm_semiring S] [comm_semiring T] (f : R →+* S) (g : S →+* T) :
  laurent_polynomial.map_ring_hom (g.comp f)
  = (laurent_polynomial.map_ring_hom g).comp (laurent_polynomial.map_ring_hom f) :=
sorry

-- again I don't think we need `R` commutative but I want to use `is_localization.lift`.
noncomputable def laurent_polynomial.eval₂_ring_hom {R S : Type*}
  [comm_semiring R] [comm_semiring S] (f : R →+* S) (x : units S) :
  laurent_polynomial R →+* S :=
@is_localization.lift (polynomial R) _ _ _ _ _ _ _ laurent_polynomial.is_localization
(polynomial.eval₂_ring_hom f x) $
begin
  suffices : submonoid.closure {@polynomial.X R _} ≤ (is_unit.submonoid S).comap
    (polynomial.eval₂_ring_hom f x).to_monoid_hom,
  { intro y, exact this y.2},
  rw submonoid.closure_le,
  simpa only [ring_hom.to_monoid_hom_eq_coe, submonoid.coe_comap, ring_hom.coe_monoid_hom,
    polynomial.coe_eval₂_ring_hom, set.singleton_subset_iff, set.mem_preimage,
    polynomial.eval₂_X] using units.is_unit x,
end

@[simps] noncomputable def CommRing.laurent_polynomial : CommRing ⥤ CommRing :=
{ obj := λ R, CommRing.of (laurent_polynomial R),
  map := λ R S f, laurent_polynomial.map_ring_hom f,
  map_id' := λ R, laurent_polynomial.map_ring_hom_id R,
  map_comp' := sorry }

noncomputable def 𝔸_1 : CommRingᵒᵖ ⥤ Scheme :=
CommRing.polynomial.op ⋙ Scheme.Spec

noncomputable def 𝔸_1' : CommRingᵒᵖ ⥤ AffineScheme :=
CommRing.polynomial.op ⋙ AffineScheme.Spec

noncomputable def 𝔸_1_projection (R : CommRingᵒᵖ) :
  𝔸_1.obj R ⟶ Scheme.Spec.obj R :=
Scheme.Spec_map (CommRing.of_hom polynomial.C)

noncomputable def polynomial_C (R : CommRingᵒᵖ) :
  opposite.unop R ⟶ (CommRing.of (polynomial $ (opposite.unop R).α)) :=
CommRing.of_hom polynomial.C

noncomputable def 𝔸_1_over (R : CommRingᵒᵖ) : over (Scheme.Spec.obj R) :=
over.mk (𝔸_1_projection R)

noncomputable def 𝔾_a_functor (R : CommRingᵒᵖ) : (over (Scheme.Spec.obj R))ᵒᵖ ⥤ Group :=
(over.forget _ ⋙ Scheme.Γ.right_op ⋙ (forget₂ CommRing AddGroup ⋙ AddGroup.to_Group).op).left_op

variables (R : CommRingᵒᵖ)

noncomputable def yoneda_𝔸_1_over_iso_aux {R : CommRingᵒᵖ} {X : (over (Scheme.Spec.obj R))ᵒᵖ}
  (f : (𝔾_a_functor R ⋙ forget Group).obj X) :
  (opposite.unop X).left ⟶ 𝔸_1.obj R :=
Γ_Spec.adjunction.hom_equiv _ _ (by dsimp; exact quiver.hom.op
  (CommRing.of_hom (polynomial.eval₂_ring_hom ((Γ_Spec.adjunction.hom_equiv
        (opposite.unop X).left R).symm (opposite.unop X).hom).unop f)))

noncomputable def yoneda_𝔸_1_over_iso (R : CommRingᵒᵖ) :
  yoneda.obj (𝔸_1_over R) ≅ 𝔾_a_functor R ⋙ forget _ :=
{ hom :=
  { app := λ X f, Scheme.Γ.map (quiver.hom.op f.1) ((Γ_Spec.adjunction.counit.app
        (CommRing.polynomial.op.obj R)).unop polynomial.X),
    naturality' := λ X Y g, by ext; refl },
  inv :=
  { app := λ X f, over.hom_mk (yoneda_𝔸_1_over_iso_aux f) sorry,
    naturality' := λ X Y g, sorry },
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

noncomputable def 𝔾_a (R : CommRingᵒᵖ) : GroupScheme (Scheme.Spec.obj R) :=
{ obj := 𝔾_a_functor R,
  property := ⟨⟨𝔸_1_over R, (yoneda_𝔸_1_over_iso R).hom, infer_instance⟩⟩ }

noncomputable def 𝔸_1_star : CommRingᵒᵖ ⥤ Scheme :=
CommRing.laurent_polynomial.op ⋙ Scheme.Spec

noncomputable def 𝔸_1_star' : CommRingᵒᵖ ⥤ AffineScheme :=
CommRing.laurent_polynomial.op ⋙ AffineScheme.Spec

noncomputable def 𝔸_1_star_projection (R : CommRingᵒᵖ) :
  𝔸_1_star.obj R ⟶ Scheme.Spec.obj R :=
Scheme.Spec_map (CommRing.of_hom laurent_polynomial.C)

noncomputable def 𝔸_1_star_over (R : CommRingᵒᵖ) : over (Scheme.Spec.obj R) :=
over.mk (𝔸_1_star_projection R)

noncomputable def 𝔾_m_functor (R : CommRingᵒᵖ) : (over (Scheme.Spec.obj R))ᵒᵖ ⥤ Group :=
(over.forget _ ⋙ Scheme.Γ.right_op ⋙ (forget₂ (CommRing) Mon ⋙ Mon.units).op).left_op

noncomputable def yoneda_𝔸_1_star_over_iso_aux {R : CommRingᵒᵖ} {X : (over (Scheme.Spec.obj R))ᵒᵖ}
  (f : (𝔾_m_functor R ⋙ forget Group).obj X) :
  (opposite.unop X).left ⟶ 𝔸_1_star.obj R :=
Γ_Spec.adjunction.hom_equiv _ _ (by dsimp; exact quiver.hom.op
  (CommRing.of_hom (laurent_polynomial.eval₂_ring_hom ((Γ_Spec.adjunction.hom_equiv
        (opposite.unop X).left R).symm (opposite.unop X).hom).unop f)))

noncomputable def yoneda_𝔸_1_star_over_iso (R : CommRingᵒᵖ) :
  yoneda.obj (𝔸_1_star_over R) ≅ 𝔾_m_functor R ⋙ forget _ :=
{ hom :=
  { app := λ X f, units.map ((Γ_Spec.adjunction.counit.app
      (CommRing.laurent_polynomial.op.obj R)).unop
      ≫ Scheme.Γ.map (quiver.hom.op f.1)).to_monoid_hom
      (laurent_polynomial.T_as_unit $ (opposite.unop R).α) },
  inv :=
  { app := λ X f, over.hom_mk (yoneda_𝔸_1_star_over_iso_aux f) sorry,
    naturality' := λ X Y g, sorry },
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

noncomputable def 𝔾_m (R : CommRingᵒᵖ) : GroupScheme (Scheme.Spec.obj R) :=
{ obj := 𝔾_m_functor R,
  property := ⟨⟨𝔸_1_star_over R, (yoneda_𝔸_1_star_over_iso R).hom, infer_instance⟩⟩ }

end
