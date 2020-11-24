import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.constructions.preserve_binary_products
import category_theory.limits.preserves.basic
import category_theory.adjunction
import category_theory.monad.limits
import category_theory.adjunction.fully_faithful
import category_theory.closed.cartesian

universes v₁ v₂ u₁ u₂

noncomputable theory

namespace category_theory

open limits category

section subcat

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] {i : D ⥤ C}

/--
-- Given a subcategory `D` of `C` expressed as an (inclusion) functor `i : D ⥤ C`, the object `A : C`
-- is said to be "in" the subcategory if there is a witness in `D`, such that `i.obj witness` is
-- isomorphic to `A`.
-/
def ess_range (i : D ⥤ C) : set C := λ A, ∃ (B : D), nonempty (i.obj B ≅ A)

/-- Get the witnessing object that `A` is in the subcategory given by `i`. -/
def ess_range.witness {A : C} (h : A ∈ ess_range i) : D := h.some

/-- Extract the isomorphism between `i.obj h.witness` and `A` itself. -/
def ess_range.get_iso {A : C} (h : A ∈ ess_range i) : i.obj h.witness ≅ A :=
classical.choice h.some_spec

lemma ess_surjective (i : D ⥤ C) : Prop := ess_range i = set.univ

/-- Being in the subcategory is a "hygenic" property: it is preserved under isomorphism. -/
lemma in_subcategory_of_iso {A A' : C} (h' : A ≅ A') (hA : A ∈ ess_range i) :
  A' ∈ ess_range i :=
hA.imp (λ B, nonempty.map (≪≫ h'))

lemma inclusion_is_in (i : D ⥤ C) (B : D) : i.obj B ∈ ess_range i := ⟨B, ⟨iso.refl _⟩⟩

lemma hom_comp_eq_id {X Y : C} (g : X ⟶ Y) [is_iso g] {f : Y ⟶ X} : g ≫ f = 𝟙 X ↔ f = inv g :=
iso.hom_comp_eq_id (as_iso g)

lemma comp_hom_eq_id {X Y : C} (g : X ⟶ Y) [is_iso g] {f : Y ⟶ X} : f ≫ g = 𝟙 Y ↔ f = inv g :=
iso.comp_hom_eq_id (as_iso g)

/-- Auxiliary definition for `unit_comp_partial_bijective`. -/
def unit_comp_partial_bijective_aux [reflective i] (A : C) (B : D) :
  (A ⟶ i.obj B) ≃ (i.obj ((left_adjoint i).obj A) ⟶ i.obj B) :=
((adjunction.of_right_adjoint i).hom_equiv _ _).symm.trans (equiv_of_fully_faithful i)

/-- The description of the inverse of the bijection. -/
lemma unit_comp_partial_bijective_aux_symm_apply [reflective i] {A : C} {B : D}
  (f : i.obj ((left_adjoint i).obj A) ⟶ i.obj B) :
  (unit_comp_partial_bijective_aux _ _).symm f = (adjunction.of_right_adjoint i).unit.app A ≫ f :=
by simp [unit_comp_partial_bijective_aux]

/--
If `i` has a reflector `L`, then the function `(i L A ⟶ B) → (A ⟶ B)` given by precomposing with
`η.app A` is a bijection provided `B` is in the subcategory given by `i`.

This establishes there is a natural bijection `(A ⟶ B) ≃ (i L A ⟶ B)`. In other words, from the
point of view of objects in `D`, `A` and `i L A` look the same: specifically that `η.app A` is
an isomorphism.
-/
def unit_comp_partial_bijective [reflective i] (A : C) {B : C} (hB : B ∈ ess_range i) :
  (A ⟶ B) ≃ (i.obj ((left_adjoint i).obj A) ⟶ B) :=
calc (A ⟶ B) ≃ (A ⟶ i.obj hB.witness) : iso.hom_congr (iso.refl _) hB.get_iso.symm
     ...     ≃ (i.obj _ ⟶ i.obj hB.witness) : unit_comp_partial_bijective_aux _ _
     ...     ≃ (i.obj ((left_adjoint i).obj A) ⟶ B) : iso.hom_congr (iso.refl _) hB.get_iso

@[simp]
lemma unit_comp_partial_bijective_symm_apply [reflective i] (A : C) {B : C}
  (hB : B ∈ ess_range i) (f) :
  (unit_comp_partial_bijective A hB).symm f = (adjunction.of_right_adjoint i).unit.app A ≫ f :=
by simp [unit_comp_partial_bijective, unit_comp_partial_bijective_aux_symm_apply]

lemma unit_comp_partial_bijective_symm_natural [reflective i] (A : C) {B B' : C} (h : B ⟶ B')
  (hB : B ∈ ess_range i) (hB' : B' ∈ ess_range i) (f : i.obj ((left_adjoint i).obj A) ⟶ B) :
  (unit_comp_partial_bijective A hB').symm (f ≫ h) = (unit_comp_partial_bijective A hB).symm f ≫ h :=
by simp

lemma unit_comp_partial_bijective_natural [reflective i] (A : C) {B B' : C} (h : B ⟶ B')
  (hB : B ∈ ess_range i) (hB' : B' ∈ ess_range i) (f : A ⟶ B) :
  (unit_comp_partial_bijective A hB') (f ≫ h) = unit_comp_partial_bijective A hB f ≫ h :=
by rw [←equiv.eq_symm_apply, unit_comp_partial_bijective_symm_natural A h, equiv.symm_apply_apply]

/--
If `A` is in the reflective subcategory, then `η_A` is an isomorphism.
This gives that the "witness" for `A` being in the subcategory can instead be given as the
reflection of `A`, with the isomorphism as `η_A`.

(For any `B` in the reflective subcategory, we automatically have that `ε_B` is an iso.)
-/
def ess_range.unit_iso [reflective i] {A : C} (h : A ∈ ess_range i) :
  is_iso ((adjunction.of_right_adjoint i).unit.app A) :=
begin
  have : ∀ (B : D), is_iso ((adjunction.of_right_adjoint i).unit.app (i.obj B)),
  { intro B,
    have : (adjunction.of_right_adjoint i).unit.app (i.obj B) =
             inv (i.map ((adjunction.of_right_adjoint i).counit.app B)),
    { rw ← comp_hom_eq_id,
      apply (adjunction.of_right_adjoint i).right_triangle_components },
    rw this,
    apply_instance },
  resetI,
  suffices :
    (adjunction.of_right_adjoint i).unit.app A =
      h.get_iso.inv ≫
        (adjunction.of_right_adjoint i).unit.app (i.obj h.witness) ≫
          (left_adjoint i ⋙ i).map h.get_iso.hom,
  { rw this,
    apply_instance },
  rw ← nat_trans.naturality,
  simp only [functor.id_map, iso.inv_hom_id_assoc],
end

/--  If `η_A` is an isomorphism, then `A` is in the subcategory. -/
lemma in_subcategory_of_unit_is_iso [is_right_adjoint i] (A : C)
  [is_iso ((adjunction.of_right_adjoint i).unit.app A)] : ess_range i A :=
⟨(left_adjoint i).obj A, ⟨(as_iso ((adjunction.of_right_adjoint i).unit.app A)).symm⟩⟩

/-- If `η_A` is a split monomorphism, then `A` is in the reflective subcategory. -/
lemma in_subcategory_of_unit_split_mono [reflective i] {A : C}
  [split_mono ((adjunction.of_right_adjoint i).unit.app A)] : A ∈ ess_range i :=
begin
  let η : 𝟭 C ⟶ left_adjoint i ⋙ i := (adjunction.of_right_adjoint i).unit,
  haveI : is_iso (η.app (i.obj ((left_adjoint i).obj A))) := (inclusion_is_in _ _).unit_iso,
  have : epi (η.app A),
  { apply epi_of_epi (retraction (η.app A)) _,
    rw (show retraction _ ≫ η.app A = _, from η.naturality (retraction (η.app A))),
    apply epi_comp (η.app (i.obj ((left_adjoint i).obj A))) },
  resetI,
  haveI := is_iso_of_epi_of_split_mono (η.app A),
  exact in_subcategory_of_unit_is_iso A,
end

end subcat

section ideal

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₁} D] {i : D ⥤ C}

/--
The category of subterminals in `C` is the subcategory of objects for which the unique morphism to
the terminal object is a monomorphism.
TODO: If `C` is the category of sheaves on a topological space `X`, this category is equivalent
to the lattice of open subsets of `X`.
-/
@[derive category]
def subterminals (C : Type u₁) [category.{v₁} C] :=
{A : C // ∀ {Z : C} (f g : Z ⟶ A), f = g}

/-- The inclusion of the subterminal objects into the original category. -/
@[derive [full, faithful]]
def subterminal_inclusion : subterminals C ⥤ C := full_subcategory_inclusion _

variables (i) [has_finite_products C] [cartesian_closed C]

/--
The subcategory `D` of `C` expressed as an inclusion functor is an *exponential ideal* if
`B ∈ D` implies `B^A ∈ D` for all `A`.
-/
class exponential_ideal : Prop :=
(exp_closed : ∀ {B}, B ∈ ess_range i → ∀ A, (A ⟹ B) ∈ ess_range i)

/--
To show `i` is an exponential ideal it suffices to show that `(iB)^A` is `in` `D` for any `A` in `C`
and `B` in `D`.
-/
lemma exponential_ideal.mk' (h : ∀ (B : D) (A : C), (A ⟹ i.obj B) ∈ ess_range i) :
  exponential_ideal i :=
⟨λ B hB A,
begin
  rcases hB with ⟨B', ⟨iB'⟩⟩,
  apply in_subcategory_of_iso _ (h B' A),
  apply (exp A).map_iso iB',
end⟩

/--
If `D` is a reflective subcategory, the property of being an exponential ideal is equivalent to
the presence of a natural isomorphism `i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A`, that is:
`(iB)^A ≅ i L (iB)^A`, naturally in `B`.
The converse is given in `exponential_ideal.mk_of_iso`.
-/
def exponential_ideal_reflective (A : C) [reflective i] [exponential_ideal i] :
  i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A :=
begin
  symmetry,
  apply nat_iso.of_components _ _,
  { intro X,
    haveI := (exponential_ideal.exp_closed (inclusion_is_in i X) A).unit_iso,
    apply as_iso ((adjunction.of_right_adjoint i).unit.app (i.obj X ^^ A)) },
  { simp }
end

/--
Given a natural isomorphism `i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A`, we can show `i`
is an exponential ideal.
-/
lemma exponential_ideal.mk_of_iso [reflective i]
  (h : Π (A : C), i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A) :
  exponential_ideal i :=
begin
  apply exponential_ideal.mk',
  intros B A,
  exact ⟨_, ⟨(h A).app B⟩⟩,
end

/-- The subcategory of subterminal objects is an exponential ideal. -/
instance : exponential_ideal (subterminal_inclusion : _ ⥤ C) :=
begin
  apply exponential_ideal.mk',
  rintros B A,
  refine ⟨⟨B.1 ^^ A, λ Z g h, _⟩, ⟨iso.refl _⟩⟩,
  exact uncurry_injective (B.2 (cartesian_closed.uncurry g) (cartesian_closed.uncurry h))
end

end ideal

section

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₁} D]
variables (i : D ⥤ C) [has_finite_products C]

lemma reflective_products [reflective i] : has_finite_products D :=
λ J 𝒥₁ 𝒥₂, by exactI has_limits_of_shape_of_reflective i

local attribute [instance] reflective_products

variables [cartesian_closed C]

/--
If `i` witnesses that `D` is a reflective subcategory and an exponential ideal, then `D` is
itself cartesian closed.
-/
def reflective_cc [reflective i] [exponential_ideal i] : cartesian_closed D :=
{ closed := λ B,
  { is_adj :=
    { right := i ⋙ exp (i.obj B) ⋙ left_adjoint i,
      adj :=
      begin
        apply adjunction.restrict_fully_faithful i i (exp.adjunction (i.obj B)),
        { symmetry,
          apply nat_iso.of_components _ _,
          { intro X,
            haveI := adjunction.right_adjoint_preserves_limits (adjunction.of_right_adjoint i),
            apply as_iso (prod_comparison i B X) },
          { intros X Y f,
            dsimp,
            rw prod_comparison_natural,
            simp, } },
        { apply (exponential_ideal_reflective i _).symm }
      end } } }

/-- If the reflector preserves binary products, the subcategory is an exponential ideal. -/
lemma ideal_of_preserves_binary_products [reflective i]
  [preserves_limits_of_shape (discrete walking_pair) (left_adjoint i)] :
  exponential_ideal i :=
begin
  let ir := adjunction.of_right_adjoint i,
  let L : C ⥤ D := left_adjoint i,
  let η : 𝟭 C ⟶ L ⋙ i := ir.unit,
  let ε : i ⋙ L ⟶ 𝟭 D := ir.counit,
  apply exponential_ideal.mk',
  intros B A,
  let q : i.obj (L.obj (i.obj B ^^ A)) ⟶ i.obj B ^^ A,
    apply cartesian_closed.curry (ir.hom_equiv _ _ _),
    apply _ ≫ (ir.hom_equiv _ _).symm ((ev A).app (i.obj B)),
    refine prod_comparison L A _ ≫ limits.prod.map (𝟙 _) (ε.app _) ≫ inv (prod_comparison _ _ _),
  have : η.app (i.obj B ^^ A) ≫ q = 𝟙 (i.obj B ^^ A),
  { rw [← curry_natural_left, curry_eq_iff, uncurry_id_eq_ev],
    erw ← ir.hom_equiv_naturality_left,
    rw ir.hom_equiv_apply_eq,
    change L.map _ ≫ _ ≫ _ = _,
    rw [assoc, assoc],
    erw prod_comparison_natural_assoc,
    rw [limits.prod.map_map_assoc, L.map_id, id_comp, ir.left_triangle_components],
    erw prod.map_id_id,
    rw id_comp,
    apply is_iso.hom_inv_id_assoc },
  haveI : split_mono (η.app (i.obj B ^^ A)) := ⟨_, this⟩,
  apply in_subcategory_of_unit_split_mono,
end

noncomputable def bijection (A B : C) (C' : D) [reflective i] [exponential_ideal i] :
  ((left_adjoint i).obj (A ⨯ B) ⟶ C') ≃ ((left_adjoint i).obj A ⨯ (left_adjoint i).obj B ⟶ C') :=
calc _ ≃ (A ⨯ B ⟶ i.obj C') :
              (adjunction.of_right_adjoint i).hom_equiv _ _
   ... ≃ (B ⨯ A ⟶ i.obj C') :
              (limits.prod.braiding _ _).hom_congr (iso.refl _)
   ... ≃ (A ⟶ B ⟹ i.obj C') :
              (exp.adjunction _).hom_equiv _ _
   ... ≃ (i.obj ((left_adjoint i).obj A) ⟶ B ⟹ i.obj C') :
              unit_comp_partial_bijective _ (exponential_ideal.exp_closed (inclusion_is_in i _) _)
   ... ≃ (B ⨯ i.obj ((left_adjoint i).obj A) ⟶ i.obj C') :
              ((exp.adjunction _).hom_equiv _ _).symm
   ... ≃ (i.obj ((left_adjoint i).obj A) ⨯ B ⟶ i.obj C') :
              (limits.prod.braiding _ _).hom_congr (iso.refl _)
   ... ≃ (B ⟶ i.obj ((left_adjoint i).obj A) ⟹ i.obj C') :
              (exp.adjunction _).hom_equiv _ _
   ... ≃ (i.obj ((left_adjoint i).obj B) ⟶ i.obj ((left_adjoint i).obj A) ⟹ i.obj C') :
              unit_comp_partial_bijective _ (exponential_ideal.exp_closed (inclusion_is_in i _) _)
   ... ≃ (i.obj ((left_adjoint i).obj A) ⨯ i.obj ((left_adjoint i).obj B) ⟶ i.obj C') :
              ((exp.adjunction _).hom_equiv _ _).symm
   ... ≃ (i.obj ((left_adjoint i).obj A ⨯ (left_adjoint i).obj B) ⟶ i.obj C') :
     begin
       apply iso.hom_congr _ (iso.refl _),
       apply (as_iso (prod_comparison _ _ _)).symm,
       haveI : preserves_limits i := (adjunction.of_right_adjoint i).right_adjoint_preserves_limits,
       apply_instance,
     end
   ... ≃ ((left_adjoint i).obj A ⨯ (left_adjoint i).obj B ⟶ C') :
              (equiv_of_fully_faithful _).symm

lemma bijection_symm_apply_id (A B : C) [reflective i] [exponential_ideal i] :
  (bijection i A B _).symm (𝟙 _) = prod_comparison _ _ _ :=
begin
  let L := left_adjoint i,
  let adj : L ⊣ i := adjunction.of_right_adjoint i,
  let η : _ ⟶ L ⋙ i := adj.unit,
  dsimp [bijection],
  rw [equiv.symm_symm, equiv.symm_symm, equiv.symm_symm, comp_id, comp_id, comp_id,
      equiv_of_fully_faithful_apply, i.map_id, comp_id, unit_comp_partial_bijective_symm_apply,
      unit_comp_partial_bijective_symm_apply],
  change (adj.hom_equiv _ _).symm
    ((limits.prod.braiding A B).hom ≫
      cartesian_closed.uncurry (η.app _ ≫
        cartesian_closed.curry ((limits.prod.braiding _ B).inv ≫
          cartesian_closed.uncurry (η.app _ ≫
            cartesian_closed.curry _)))) =
    prod_comparison L _ _,
  rw [uncurry_natural_left, uncurry_curry, uncurry_natural_left, uncurry_curry,
      ←braid_natural_assoc, iso.hom_inv_id_assoc, limits.prod.map_map_assoc, comp_id, id_comp,
      ← adjunction.eq_hom_equiv_apply, adjunction.hom_equiv_unit, is_iso.comp_inv_eq, assoc],
  apply prod.hom_ext,
  { rw [limits.prod.map_fst, assoc, assoc, prod_comparison, prod_comparison, prod.lift_fst,
        ←i.map_comp, prod.lift_fst],
    apply η.naturality },
  { rw [limits.prod.map_snd, assoc, assoc, prod_comparison, prod_comparison, prod.lift_snd,
        ←i.map_comp, prod.lift_snd],
    apply η.naturality },
end.

lemma bijection_natural [reflective i] [exponential_ideal i]
  (A B : C) (C' C'' : D) (f : ((left_adjoint i).obj (A ⨯ B) ⟶ C')) (g : C' ⟶ C'') :
  bijection i _ _ _ (f ≫ g) = bijection i _ _ _ f ≫ g :=
begin
  apply i.map_injective,
  dsimp [bijection],
  rw [i.image_preimage, i.map_comp, i.image_preimage, comp_id, comp_id, comp_id, comp_id, comp_id,
      comp_id],
  change prod_comparison _ _ _ ≫
    cartesian_closed.uncurry
      (unit_comp_partial_bijective _ _
        (cartesian_closed.curry ((limits.prod.braiding _ _).hom ≫
          cartesian_closed.uncurry
            (unit_comp_partial_bijective _ _
              (cartesian_closed.curry
                ((limits.prod.braiding _ _).hom ≫ _)))))) = _,
  rw [adjunction.hom_equiv_naturality_right, ← assoc, curry_natural_right _ (i.map g),
      unit_comp_partial_bijective_natural, uncurry_natural_right, ← assoc, curry_natural_right,
      unit_comp_partial_bijective_natural, uncurry_natural_right, assoc],
  refl,
end

noncomputable def preserves_pair_of_exponential_ideal [reflective i] [exponential_ideal i]
  (A B : C) : preserves_limit (pair A B) (left_adjoint i) :=
begin
  let ir : is_right_adjoint i := by apply_instance,
  let L := ir.left,
  let adj : L ⊣ i := ir.adj,
  let η : _ ⟶ L ⋙ i := adj.unit,
  apply preserves_binary_prod_of_prod_comparison_iso L _ _,
  refine is_iso.of_iso ⟨prod_comparison _ _ _, bijection i _ _ _ (𝟙 _), _, _⟩,
  { dsimp,
    rw [←(bijection i _ _ _).injective.eq_iff, bijection_natural, ← bijection_symm_apply_id,
        equiv.apply_symm_apply, id_comp] },
  { dsimp,
    rw [←bijection_natural, id_comp, ←bijection_symm_apply_id, equiv.apply_symm_apply] }
end

noncomputable def preserves_binary_products_of_exponential_ideal
  [reflective i] [exponential_ideal i] :
  preserves_limits_of_shape (discrete walking_pair) (left_adjoint i) :=
{ preserves_limit := λ K,
  begin
    apply limits.preserves_limit_of_iso_diagram _ (diagram_iso_pair K).symm,
    apply preserves_pair_of_exponential_ideal,
  end }
end

#lint

end category_theory
