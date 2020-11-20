import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.constructions.preserve_binary_products
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

def coyoneda.ext {X Y : C} (p : Π {Z : C}, (X ⟶ Z) ≃ (Y ⟶ Z))
  (n : Π {Z Z' : C} (f : Z ⟶ Z') (g : X ⟶ Z), p (g ≫ f) = p g ≫ f) : X ≅ Y :=
{ hom := p.symm (𝟙 Y),
  inv := p (𝟙 X),
  hom_inv_id' := by rw [← p.injective.eq_iff, n, p.apply_symm_apply, id_comp],
  inv_hom_id' := by rw [← n, id_comp, equiv.apply_symm_apply] }

/--
Given a subcategory `D` of `C` expressed as an (inclusion) functor `i : D ⥤ C`, the object `A : C`
is said to be "in" the subcategory if there is a witness in `D`, such that `i.obj witness` is
isomorphic to `A`.
This notion is useful primarily when `i` is faithful.
-/
def in_subcategory (i : D ⥤ C) (A : C) : Prop := ∃ (B : D), nonempty (i.obj B ≅ A)

def in_subcategory.witness {A : C} (h : in_subcategory i A) : D := h.some

def in_subcategory.get_iso {A : C} (h : in_subcategory i A) : i.obj h.witness ≅ A :=
classical.choice h.some_spec

/-- Being in the subcategory is a "hygenic" property: it is preserved under isomorphism. -/
lemma in_subcategory_of_iso {A A' : C} (h' : A ≅ A') (hA : in_subcategory i A) :
  in_subcategory i A' :=
hA.imp (λ B, nonempty.map (≪≫ h'))

lemma inclusion_is_in (i : D ⥤ C) (B : D) : in_subcategory i (i.obj B) := ⟨B, ⟨iso.refl _⟩⟩

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
point of view of objects in `i`, `A` and `i L A` look the same.
-/
def unit_comp_partial_bijective [reflective i] (A : C) {B : C} (hB : in_subcategory i B) :
  (A ⟶ B) ≃ (i.obj ((left_adjoint i).obj A) ⟶ B) :=
calc (A ⟶ B) ≃ (A ⟶ i.obj hB.witness) : iso.hom_congr (iso.refl _) hB.get_iso.symm
     ...     ≃ (i.obj _ ⟶ i.obj hB.witness) : unit_comp_partial_bijective_aux _ _
     ...     ≃ (i.obj ((left_adjoint i).obj A) ⟶ B) : iso.hom_congr (iso.refl _) hB.get_iso

@[simp]
lemma unit_comp_partial_bijective_symm_apply [reflective i] (A : C) {B : C}
  (hB : in_subcategory i B) (f) :
  (unit_comp_partial_bijective A hB).symm f = (adjunction.of_right_adjoint i).unit.app A ≫ f :=
by simp [unit_comp_partial_bijective, unit_comp_partial_bijective_aux_symm_apply]

lemma unit_comp_partial_bijective_symm_natural [reflective i] (A : C) {B B' : C} (h : B ⟶ B')
  (hB : in_subcategory i B) (hB' : in_subcategory i B') (f : i.obj ((left_adjoint i).obj A) ⟶ B) :
  (unit_comp_partial_bijective A hB').symm (f ≫ h) = (unit_comp_partial_bijective A hB).symm f ≫ h :=
by simp

lemma unit_comp_partial_bijective_natural [reflective i] (A : C) {B B' : C} (h : B ⟶ B')
  (hB : in_subcategory i B) (hB' : in_subcategory i B') (f : A ⟶ B) :
  (unit_comp_partial_bijective A hB') (f ≫ h) = unit_comp_partial_bijective A hB f ≫ h :=
by rw [← equiv.eq_symm_apply, unit_comp_partial_bijective_symm_natural A h hB, equiv.symm_apply_apply]

/--
If `A` is in the reflective subcategory, then `η_A` is an isomorphism.
This gives that the "witness" for `A` being in the subcategory can instead be given as the
reflection of `A`, with the isomorphism as `η_A`.

(For any `B` in the reflective subcategory, we automatically have that `ε_B` is an iso.)
-/
def in_subcategory.unit_iso [reflective i] {A : C} (h : in_subcategory i A) :
  is_iso ((adjunction.of_right_adjoint i).unit.app A) :=
begin
  let ir := adjunction.of_right_adjoint i,
  let L : C ⥤ D := left_adjoint i,
  let η : 𝟭 C ⟶ L ⋙ i := ir.unit,
  let ε : i ⋙ L ⟶ 𝟭 D := ir.counit,
  have : ∀ (B : D), is_iso (η.app (i.obj B)),
  { intro B,
    have : η.app (i.obj B) = inv (i.map (ε.app B)),
    { rw ← comp_hom_eq_id,
      apply ir.right_triangle_components },
    rw this,
    apply_instance },
  resetI,
  change is_iso (η.app A),
  suffices : η.app A = h.get_iso.inv ≫ η.app (i.obj h.witness) ≫ (L ⋙ i).map h.get_iso.hom,
  { rw this,
    apply_instance },
  rw ← η.naturality,
  simp only [functor.id_map, iso.inv_hom_id_assoc],
end

def in_subcategory_of_unit_is_iso [reflective i] (A : C)
  [is_iso ((adjunction.of_right_adjoint i).unit.app A)] : in_subcategory i A :=
begin
  refine ⟨(left_adjoint i).obj A, ⟨_⟩⟩,
  apply (as_iso ((adjunction.of_right_adjoint i).unit.app A)).symm,
end

def in_subcategory_of_unit_split_mono [reflective i] {A : C}
  [split_mono ((adjunction.of_right_adjoint i).unit.app A)] : in_subcategory i A :=
begin
  let ir := adjunction.of_right_adjoint i,
  let η : 𝟭 C ⟶ left_adjoint i ⋙ i := ir.unit,
  haveI : is_iso (η.app (i.obj ((left_adjoint i).obj A))) := (inclusion_is_in _ _).unit_iso,
  have : epi (η.app A),
    apply epi_of_epi (retraction (η.app A)) _,
    have : retraction _ ≫ η.app A = _ := η.naturality (retraction (η.app A)),
    rw this,
    apply epi_comp (η.app (i.obj ((left_adjoint i).obj A))) _,
    apply split_epi.epi _,
    apply_instance,
  resetI,
  haveI := is_iso_of_epi_of_split_mono (η.app A),
  exact in_subcategory_of_unit_is_iso A,
end

end subcat

section ideal

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₁} D] {i : D ⥤ C}
variables (i) [has_finite_products C] [cartesian_closed C]

/--
The subcategory `D` of `C` expressed as an inclusion functor is an *exponential ideal* if
`B ∈ D` implies `B^A ∈ D` for all `A`.
-/
class exponential_ideal : Prop :=
(exp_closed : ∀ {B}, in_subcategory i B → ∀ A, in_subcategory i (A ⟹ B))

def exponential_ideal_reflective (A : C) [reflective i] [exponential_ideal i] :
  i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A :=
begin
  symmetry,
  apply nat_iso.of_components _ _,
  { intro X,
    haveI : is_iso ((adjunction.of_right_adjoint i).unit.app (i.obj X ^^ A)) :=
      in_subcategory.unit_iso
        (exponential_ideal.exp_closed (inclusion_is_in i X) A),
    apply as_iso ((adjunction.of_right_adjoint i).unit.app (i.obj X ^^ A)) },
  { simp }
end

def exponential_ideal.mk' (h : ∀ (B : D) (A : C), in_subcategory i (A ⟹ i.obj B)) :
  exponential_ideal i :=
⟨λ B hB A,
begin
  rcases hB with ⟨B', ⟨iB'⟩⟩,
  apply in_subcategory_of_iso _ (h B' A),
  apply (exp A).map_iso iB',
end⟩

def exponential_ideal.mk_of_iso [reflective i]
  (h : Π (A : C), i ⋙ exp A ⋙ left_adjoint i ⋙ i ≅ i ⋙ exp A) :
  exponential_ideal i :=
begin
  apply exponential_ideal.mk',
  intros B A,
  exact ⟨_, ⟨(h A).app B⟩⟩,
end

@[derive category]
def subterminals (C : Type u₁) [category.{v₁} C] [has_terminal C] :=
{A : C // mono (terminal.from A)}

def subterminal_inclusion : subterminals C ⥤ C := full_subcategory_inclusion _

instance : exponential_ideal (subterminal_inclusion : _ ⥤ C) :=
begin
  apply exponential_ideal.mk',
  rintros ⟨B, hB'⟩ A,
  refine ⟨⟨B ^^ A, ⟨_⟩⟩, ⟨iso.refl _⟩⟩,
  introsI Z g h eq,
  apply uncurry_injective,
  rw [← cancel_mono (terminal.from B)],
  apply subsingleton.elim,
end

end ideal

section

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₁} D]
variables (i : D ⥤ C) [has_finite_products C] [cartesian_closed C]

def reflective_products [reflective i] : has_finite_products D :=
λ J 𝒥₁ 𝒥₂,
{ has_limit := λ F, by { have := monadic_creates_limits i, exactI has_limit_of_created F i } }

local attribute [instance] reflective_products

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
def ideal_of_preserves_binary_products [reflective i]
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
    apply cartesian_closed.curry,
    apply ir.hom_equiv _ _ _,
    apply _ ≫ (ir.hom_equiv _ _).symm ((ev A).app (i.obj B)),
    refine prod_comparison L A _ ≫ limits.prod.map (𝟙 _) (ε.app _) ≫ inv (prod_comparison _ _ _),
  have : η.app (i.obj B ^^ A) ≫ q = 𝟙 (i.obj B ^^ A),
    rw ← curry_natural_left,
    rw curry_eq_iff,
    rw uncurry_id_eq_ev,
    erw ← ir.hom_equiv_naturality_left,
    rw ir.hom_equiv_apply_eq,
    change L.map _ ≫ _ ≫ _ = _,
    rw [assoc, assoc],
    erw prod_comparison_natural_assoc,
    rw [limits.prod.map_map_assoc, L.map_id, id_comp],
    rw ir.left_triangle_components,
    erw prod.map_id_id,
    rw id_comp,
    erw is_iso.hom_inv_id_assoc,
    refl,
  haveI : split_mono (η.app (i.obj B ^^ A)) := ⟨_, this⟩,
  apply in_subcategory_of_unit_split_mono,
end

def hom_equiv_aux1 [reflective i] (A B : C) (X : D) :
  ((left_adjoint i).obj (A ⨯ B) ⟶ X) ≃ (B ⟶ (i.obj X) ^^ A) :=
(adjunction.comp _ _ (exp.adjunction A) (adjunction.of_right_adjoint i)).hom_equiv _ _

lemma pre_natural {A A' : C} (B : C) (X : D) (f : A' ⟶ A) (k) :
  cartesian_closed.curry k ≫ pre (i.obj X) f = cartesian_closed.curry (limits.prod.map f (𝟙 B) ≫ k) :=
begin
  rw [pre, eq_curry_iff, uncurry_natural_left, uncurry_curry, prod.map_swap_assoc, curry_eq,
      prod.map_id_comp, assoc, ev_naturality],
  dsimp,
  rw ev_coev_assoc,
end

lemma hom_equiv_aux1_naturality_A [reflective i] {A A' : C} (B : C) (X : D)
  (f : A' ⟶ A) (k) :
  hom_equiv_aux1 i A B X k ≫ pre _ f = hom_equiv_aux1 i A' B X ((left_adjoint i).map (limits.prod.map f (𝟙 _)) ≫ k) :=
begin
  dsimp [hom_equiv_aux1, adjunction.comp],
  change cartesian_closed.curry _ ≫ _ = cartesian_closed.curry _,
  rw (adjunction.of_right_adjoint i).hom_equiv_naturality_left,
  rw pre_natural,
end

def hom_equiv_aux2 [reflective i] [exponential_ideal i] (A B : C) (X : D) :
  ((left_adjoint i).obj (A ⨯ B) ⟶ X) ≃ ((left_adjoint i).obj (A ⨯ i.obj ((left_adjoint i).obj B)) ⟶ X) :=
calc ((left_adjoint i).obj (A ⨯ B) ⟶ X) ≃ (B ⟶ (i.obj X) ^^ A) : hom_equiv_aux1 i _ _ _
    ... ≃ (i.obj ((left_adjoint i).obj B) ⟶ (i.obj X) ^^ A) : unit_comp_partial_bijective _ (exponential_ideal.exp_closed (inclusion_is_in _ _) _)
    ... ≃ _ : (hom_equiv_aux1 i _ _ _).symm

@[reassoc]
lemma hom_equiv_aux2_naturality_A [reflective i] [exponential_ideal i] {A A' : C} (B : C) (X : D)
  (f : A' ⟶ A) (k) :
    (left_adjoint i).map (limits.prod.map f (𝟙 _)) ≫ hom_equiv_aux2 i A B X k
  = hom_equiv_aux2 i A' B X ((left_adjoint i).map (limits.prod.map f (𝟙 _)) ≫ k) :=
begin
  dsimp [hom_equiv_aux2],
  rw ← hom_equiv_aux1_naturality_A,
  rw equiv.eq_symm_apply,
  rw ← hom_equiv_aux1_naturality_A,
  rw equiv.apply_symm_apply,
  rw unit_comp_partial_bijective_natural,
end

lemma hom_equiv_aux2_naturality_B [reflective i] [exponential_ideal i] (A : C) {B B' : C} (X : D)
  (f : B' ⟶ B) (k) :
    (left_adjoint i).map (limits.prod.map (𝟙 _) (i.map ((left_adjoint i).map f))) ≫ hom_equiv_aux2 i A B X k
  = hom_equiv_aux2 i A B' X ((left_adjoint i).map (limits.prod.map (𝟙 _) f) ≫ k) :=
begin
  dsimp [hom_equiv_aux2, hom_equiv_aux1],
  erw (adjunction.comp _ i (exp.adjunction A) (adjunction.of_right_adjoint i)).hom_equiv_naturality_left,
  erw ← (adjunction.comp _ i (exp.adjunction A) (adjunction.of_right_adjoint i)).hom_equiv_naturality_left_symm,
  congr' 1,
  rw ← equiv.symm_apply_eq,
  rw unit_comp_partial_bijective_symm_apply,
  erw ← (adjunction.of_right_adjoint i).unit.naturality_assoc,
  rw ← unit_comp_partial_bijective_symm_apply B,
  rw equiv.symm_apply_apply,
  refl,
end

lemma hom_equiv_aux2_naturality_X [reflective i] [exponential_ideal i] (A : C) (B : C) {X X' : D}
  (f : X ⟶ X') (k) :
  hom_equiv_aux2 i A B X k ≫ f = hom_equiv_aux2 i A B X' (k ≫ f) :=
begin
  dsimp [hom_equiv_aux2, hom_equiv_aux1],
  rw (adjunction.comp _ i (exp.adjunction A) (adjunction.of_right_adjoint i)).hom_equiv_naturality_right,
  rw unit_comp_partial_bijective_natural,
  rw ← (adjunction.comp _ i (exp.adjunction A) (adjunction.of_right_adjoint i)).hom_equiv_naturality_right_symm,
end

lemma hom_equiv_aux2_naturality_symm_X [reflective i] [exponential_ideal i] (A : C) (B : C) {X X' : D}
  (f : X ⟶ X') (k) :
  (hom_equiv_aux2 i A B X).symm k ≫ f = (hom_equiv_aux2 i A B X').symm (k ≫ f) :=
begin
  rw equiv.eq_symm_apply,
  rw ← hom_equiv_aux2_naturality_X,
  rw equiv.apply_symm_apply,
end

def inner_mul_unit_iso [reflective i] [exponential_ideal i] (A B : C) :
  (left_adjoint i).obj (A ⨯ B) ≅ (left_adjoint i).obj (A ⨯ i.obj ((left_adjoint i).obj B)) :=
{ hom := (hom_equiv_aux2 _ _ _ _).symm (𝟙 _),
  inv := (hom_equiv_aux2 _ _ _ _) (𝟙 _),
  hom_inv_id' := by rw [hom_equiv_aux2_naturality_symm_X, id_comp, equiv.symm_apply_apply],
  inv_hom_id' := by rw [hom_equiv_aux2_naturality_X, id_comp, equiv.apply_symm_apply] }

lemma inner_mul_natural [reflective i] [exponential_ideal i] {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') :
  (inner_mul_unit_iso i A B).hom ≫ (left_adjoint i).map (limits.prod.map f (i.map ((left_adjoint i).map g))) = (left_adjoint i).map (limits.prod.map f g) ≫ (inner_mul_unit_iso i A' B').hom :=
begin
  rw ← iso.comp_inv_eq,
  rw assoc,
  rw ← iso.eq_inv_comp,
  change _ ≫ hom_equiv_aux2 _ _ _ _ _ = hom_equiv_aux2 _ _ _ _ _ ≫ _,
  have : limits.prod.map f (i.map ((left_adjoint i).map g)) = limits.prod.map f (𝟙 _) ≫ limits.prod.map (𝟙 _) (i.map ((left_adjoint i).map g)),
    simp,
  rw this,
  rw (left_adjoint i).map_comp,
  rw assoc,
  rw hom_equiv_aux2_naturality_B,
  rw comp_id,
  rw hom_equiv_aux2_naturality_A,
  rw hom_equiv_aux2_naturality_X,
  rw id_comp,
  rw ← (left_adjoint i).map_comp,
  simp,
end

-- def preserves_binary_products_of_ideal [reflective i] [exponential_ideal i] :
--   preserves_limits_of_shape (discrete walking_pair) (left_adjoint i) :=
-- begin

-- end

end

-- def witness_in (A : C) [in_subcategory i A] : D := in_subcategory.witness.{v₁} i A
-- def witness_iso (A : C) [in_subcategory i A] : i.obj (witness_in i A) ≅ A := in_subcategory.iso.

-- class in_subcategory' [ir : is_right_adjoint i] (A : C) :=
-- ( returning : is_iso (ir.adj.unit.app A) )

-- def containment_iso (A : C) [ir : is_right_adjoint i] [h : in_subcategory' i A] : A ≅ i.obj ((left_adjoint i).obj A) :=
-- begin
--   haveI := h.returning,
--   exact as_iso (ir.adj.unit.app A),
-- end
-- variable {i}

-- instance inclusion_is_in (B : D) : in_subcategory i (i.obj B) :=
-- { witness := B,
--   iso := iso.refl _ }

-- instance inclusion_is_in' (B : D) [ir : reflective i] : in_subcategory' i (i.obj B) :=
-- { returning :=
--   begin
--     haveI := nat_iso.is_iso_app_of_is_iso ir.adj.counit B,
--     have : ir.adj.unit.app (i.obj B) ≫ i.map (ir.adj.counit.app B) = 𝟙 (i.obj B) := ir.adj.right_triangle_components,
--     refine ⟨i.map (ir.adj.counit.app B), ir.adj.right_triangle_components, _⟩,
--     dsimp,
--     rw [← cancel_mono (i.map (is_right_adjoint.adj.counit.app B)), assoc, this, comp_id, id_comp],
--     apply is_iso.mono_of_iso,
--   end }

-- def unit_iso_of_split_mono [ir : reflective i] (A : C) [split_mono (ir.adj.unit.app A)] : is_iso (ir.adj.unit.app A) :=
-- begin
--   let h : i.obj (ir.left.obj A) ⟶ A := retraction (ir.adj.unit.app A),
--   haveI : is_iso (ir.adj.unit.app (i.obj (ir.left.obj A))) := in_subcategory'.returning,
--   haveI : split_epi h := ⟨ir.adj.unit.app A, split_mono.id (ir.adj.unit.app A)⟩,
--   suffices : epi (ir.adj.unit.app A),
--     refine ⟨h, split_mono.id (ir.adj.unit.app A), _⟩,
--     resetI,
--     dsimp,
--     erw [← cancel_epi (ir.adj.unit.app A), split_mono.id_assoc (ir.adj.unit.app A), comp_id],
--   suffices : epi (ir.adj.unit.app _ ≫ i.map (ir.left.map h)),
--     erw [← ir.adj.unit.naturality h, functor.id_map] at this,
--     resetI,
--     apply epi_of_epi h,
--   apply epi_comp,
-- end

-- -- Some of the stuff here doesn't need reflectiveness, need to untangle what assumptions are actually used
-- def in_subcategory_of_has_iso [ir : reflective i] (A : C) (B : D) (h : i.obj B ≅ A) : in_subcategory' i A :=
-- { returning :=
--   begin
--     apply unit_iso_of_split_mono _,
--     refine ⟨i.map ((ir.adj.hom_equiv _ _).symm h.inv) ≫ h.hom, _⟩,
--     simp,
--   end }

-- @[reducible]
-- def equiv_homset_left_of_iso
--   {X X' : C} (Y : C) (i : X ≅ X') :
--   (X ⟶ Y) ≃ (X' ⟶ Y) :=
-- { to_fun := λ f, i.inv ≫ f,
--   inv_fun := λ f, i.hom ≫ f,
--   left_inv := λ f, by simp,
--   right_inv := λ f, by simp }.

-- @[reducible]
-- def equiv_homset_right_of_iso
--   (X : C) {Y Y' : C} (i : Y ≅ Y') :
--   (X ⟶ Y) ≃ (X ⟶ Y') :=
-- { to_fun := λ f, f ≫ i.hom,
--   inv_fun := λ f, f ≫ i.inv,
--   left_inv := λ f, by simp,
--   right_inv := λ f, by simp }.

-- variable (i)
-- def biject_inclusion [ir : reflective i] {A B : C} [in_subcategory' i B] : (A ⟶ B) ≃ (i.obj ((left_adjoint i).obj A) ⟶ B) :=
-- calc (A ⟶ B) ≃ (A ⟶ i.obj ((left_adjoint i).obj B)) : equiv_homset_right_of_iso _ (containment_iso _ _)
--     ... ≃ ((left_adjoint i).obj A ⟶ (left_adjoint i).obj B) : (ir.adj.hom_equiv _ _).symm
--     ... ≃ (i.obj ((left_adjoint i).obj A) ⟶ i.obj ((left_adjoint i).obj B)) : equiv_of_fully_faithful i
--     ... ≃ (i.obj ((left_adjoint i).obj A) ⟶ B) : equiv_homset_right_of_iso _ (containment_iso _ _).symm
-- variable {i}

-- lemma biject_inclusion_natural [ir : reflective i] {A B B' : C} [h : in_subcategory' i B] [h' : in_subcategory' i B'] (f : A ⟶ B) (g : B ⟶ B') :
--   biject_inclusion i (f ≫ g) = biject_inclusion i f ≫ g :=
-- begin
--   dsimp [biject_inclusion, containment_iso],
--   haveI := h'.returning,
--   haveI := h.returning,
--   have : i.map
--         (((is_right_adjoint.adj.hom_equiv A ((left_adjoint i).obj B')).symm)
--            ((f ≫ g) ≫ is_right_adjoint.adj.unit.app B')) ≫
--       inv (is_right_adjoint.adj.unit.app B') = (i.map
--            (((is_right_adjoint.adj.hom_equiv A ((left_adjoint i).obj B)).symm)
--               (f ≫ is_right_adjoint.adj.unit.app B)) ≫
--          inv (is_right_adjoint.adj.unit.app B)) ≫
--       g ↔ _ = _ := (as_iso (ir.adj.unit.app B')).comp_inv_eq,
--   convert this.2 _, -- this should not be necessary
--   clear this,
--   dsimp [as_iso_hom],
--   erw [assoc, assoc, ir.adj.unit.naturality, assoc, (as_iso _).inv_hom_id_assoc, functor.comp_map, ← functor.map_comp],
--   rw [← ir.adj.hom_equiv_naturality_right_symm, assoc], refl,
-- end .

-- lemma biject_inclusion_natural_left [ir : reflective i] {A A' B : C} [h : in_subcategory' i B] (f : A ⟶ A') (g : A' ⟶ B) :
--   biject_inclusion i (f ≫ g) = i.map ((left_adjoint i).map f) ≫ biject_inclusion i g :=
-- begin
--   dsimp [biject_inclusion],
--   erw [← i.map_comp_assoc, ← ir.adj.hom_equiv_naturality_left_symm, assoc],
-- end

-- lemma biject_inclusion_symm_id_eq [ir : reflective i] (A : C) :
--   (biject_inclusion i).symm (𝟙 (i.obj ((left_adjoint i).obj A))) = ir.adj.unit.app A :=
-- begin
--   rw equiv.symm_apply_eq,
--   dsimp [biject_inclusion, containment_iso],
--   rw [ir.adj.hom_equiv_counit],
--   let η := ir.adj.unit,
--   let ε := ir.adj.counit,
--   let L := left_adjoint i,
--   have : 𝟙 (i.obj ((left_adjoint i).obj A)) = _ ≫ inv (is_right_adjoint.adj.unit.app (i.obj ((left_adjoint i).obj A))) ↔ _ = _ := (as_iso (is_right_adjoint.adj.unit.app (i.obj ((left_adjoint i).obj A)))).eq_comp_inv,
--   rw this, clear this,
--   rw [id_comp, as_iso_hom],
--   change η.app (i.obj (L.obj A)) = i.map (L.map (η.app A ≫ η.app (i.obj (L.obj A))) ≫ ε.app (L.obj (i.obj (L.obj A)))),
--   rw [L.map_comp, assoc],
--   haveI := nat_iso.is_iso_app_of_is_iso ε (L.obj A),
--   erw [ir.adj.left_triangle_components, comp_id, ← cancel_mono (i.map (ε.app (L.obj A))), ir.adj.right_triangle_components,
--        ← i.map_comp, ir.adj.left_triangle_components, i.map_id],
-- end

-- lemma biject_inclusion_is_comp_unit [ir : reflective i] {A B : C} [h : in_subcategory' i B] (f : i.obj ((left_adjoint i).obj A) ⟶ B) :
--   (biject_inclusion i).symm f = ir.adj.unit.app _ ≫ f :=
-- by rw [← biject_inclusion_symm_id_eq A, (biject_inclusion i).symm_apply_eq,
--        biject_inclusion_natural _ _, equiv.apply_symm_apply, id_comp]

-- variables [has_finite_products.{v₁} C] [has_finite_products.{v₁} D] [cartesian_closed C] (i)

-- class exponential_ideal extends reflective i :=
-- [ strength (A) {B} [in_subcategory' i B] : in_subcategory' i (A ⟹ B) ]

-- noncomputable def exponential_ideal_of [z : reflective i]
--   (h : ∀ (A : C) (B : D), in_subcategory' i (A ⟹ i.obj B)) : exponential_ideal i :=
-- { strength := λ A B inst,
--   begin
--     resetI,
--     let ir : is_right_adjoint i := by apply_instance,
--     let L := ir.left,
--     let η := ir.adj.unit,
--     haveI := h A (L.obj B),
--     let i₁ : B ≅ i.obj (L.obj B) := containment_iso i B,
--     let i₂ : A ⟹ i.obj (L.obj B) ≅ i.obj (L.obj (A ⟹ (i.obj (L.obj B)))) := containment_iso i (A ⟹ i.obj (L.obj B)),
--     let : A ⟹ B ≅ i.obj (L.obj (A ⟹ B)),
--       apply (exp A).map_iso i₁ ≪≫ i₂ ≪≫ (exp A ⋙ L ⋙ i).map_iso i₁.symm,
--     refine ⟨_⟩,
--     convert is_iso.of_iso this,
--     change η.app (A ⟹ B) =
--       (exp _).map (containment_iso _ _).hom ≫ η.app _ ≫ i.map (L.map ((exp _).map (containment_iso _ _).inv)),
--     erw η.naturality_assoc,
--     change η.app (A ⟹ B) = η.app (A ⟹ B) ≫ (exp A ⋙ L ⋙ _).map _ ≫ (exp A ⋙ L ⋙ _).map _,
--     rw [← (exp A ⋙ L ⋙ _).map_comp, iso.hom_inv_id, functor.map_id],
--     erw comp_id,
--   end,
--   ..z }

-- variables [exponential_ideal i]

-- noncomputable
-- def bijection (A B : C) (C' : D) : ((left_adjoint i).obj (A ⨯ B) ⟶ C') ≃ ((left_adjoint i).obj A ⨯ (left_adjoint i).obj B ⟶ C') :=
-- calc _ ≃ (A ⨯ B ⟶ i.obj C') : _inst_6.to_reflective.adj.hom_equiv _ _
-- ... ≃ (B ⨯ A ⟶ i.obj C') : equiv_homset_left_of_iso _ (limits.prod.braiding _ _)
-- ... ≃ (A ⟶ B ⟹ i.obj C') : (exp.adjunction _).hom_equiv _ _
-- ... ≃ (i.obj ((left_adjoint i).obj A) ⟶ B ⟹ i.obj C') :
--   begin
--     apply biject_inclusion i,
--     apply exponential_ideal.strength,
--   end
-- ... ≃ (B ⨯ i.obj ((left_adjoint i).obj A) ⟶ i.obj C') : ((exp.adjunction _).hom_equiv _ _).symm
-- ... ≃ (i.obj ((left_adjoint i).obj A) ⨯ B ⟶ i.obj C') : equiv_homset_left_of_iso _ (limits.prod.braiding _ _)
-- ... ≃ (B ⟶ i.obj ((left_adjoint i).obj A) ⟹ i.obj C') : (exp.adjunction _).hom_equiv _ _
-- ... ≃ (i.obj ((left_adjoint i).obj B) ⟶ i.obj ((left_adjoint i).obj A) ⟹ i.obj C') :
--   begin
--     apply biject_inclusion _,
--     apply exponential_ideal.strength,
--   end
-- ... ≃ (i.obj ((left_adjoint i).obj A) ⨯ i.obj ((left_adjoint i).obj B) ⟶ i.obj C') : ((exp.adjunction _).hom_equiv _ _).symm
-- ... ≃ (i.obj ((left_adjoint i).obj A ⨯ (left_adjoint i).obj B) ⟶ i.obj C') : equiv_homset_left_of_iso _
--   begin
--     apply (as_iso (prod_comparison _ _ _)).symm,
--     haveI : preserves_limits i := _inst_6.to_reflective.adj.right_adjoint_preserves_limits,
--     apply_instance,
--   end
-- ... ≃ ((left_adjoint i).obj A ⨯ (left_adjoint i).obj B ⟶ C') : (equiv_of_fully_faithful _).symm

-- variables {i}

-- lemma comp_inv_eq {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) (h : Z ⟶ X) [is_iso f] :
--   g ≫ inv f = h ↔ g = h ≫ f :=
-- (as_iso f).comp_inv_eq.

-- -- @[reassoc] lemma prod_comparison_natural (F : C ⥤ D) {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') :
-- --   F.map (prod.map f g) ≫ prod_comparison F A' B' = prod_comparison F A B ≫ prod.map (F.map f) (F.map g) :=

-- lemma bijection_id (A B : C) : (bijection i A B _).symm (𝟙 _) = prod_comparison _ _ _ :=
-- begin
--   dsimp [bijection],
--   rw [equiv.symm_symm, equiv.symm_symm, equiv.symm_symm],
--   dsimp [equiv_of_fully_faithful],
--   rw [i.map_id, comp_id, biject_inclusion_is_comp_unit, biject_inclusion_is_comp_unit],
--   let ir : is_right_adjoint i := by apply_instance,
--   let L := ir.left,
--   let adj : L ⊣ i := ir.adj,
--   let η : _ ⟶ L ⋙ i := adj.unit,
--   let ε : i ⋙ L ⟶ _ := adj.counit,
--   change ((adj.hom_equiv (A ⨯ B) (L.obj A ⨯ L.obj B)).symm)
--       (prod.lift limits.prod.snd limits.prod.fst ≫
--          cartesian_closed.uncurry (η.app A ≫
--               cartesian_closed.curry (prod.lift limits.prod.snd limits.prod.fst ≫
--                    cartesian_closed.uncurry (η.app B ≫ cartesian_closed.curry _)))) =
--     prod_comparison L A B,
--   rw [uncurry_natural_left, uncurry_curry, uncurry_natural_left, uncurry_curry,
--       ← adjunction.eq_hom_equiv_apply, prod.lift_map_assoc, prod.lift_map_assoc,
--       comp_id, comp_id, ← assoc, comp_inv_eq, adjunction.hom_equiv_unit, assoc],
--   apply prod.hom_ext,
--   rw [assoc, prod.lift_fst, prod.lift_snd, assoc, assoc, prod_comparison, prod_comparison,
--       prod.lift_fst, ← i.map_comp, prod.lift_fst],
--   apply η.naturality,
--   rw [assoc, prod.lift_snd, prod.lift_fst_assoc, assoc, assoc, prod_comparison,
--       prod_comparison, prod.lift_snd, ← i.map_comp, prod.lift_snd],
--   apply η.naturality,
-- end .

-- lemma bijection_natural (A B : C) (C' C'' : D) (f : ((left_adjoint i).obj (A ⨯ B) ⟶ C')) (g : C' ⟶ C'') : bijection i _ _ _ (f ≫ g) = bijection i _ _ _ f ≫ g :=
-- begin
--   have : i.preimage (i.map g) = g := preimage_map g,
--   conv_rhs {congr, skip, rw ← this},
--   dsimp [bijection],
--   rw [← preimage_comp, assoc, ← adjunction.hom_equiv_naturality_right_symm,
--       is_right_adjoint.adj.hom_equiv_naturality_right, ← assoc,
--       (exp.adjunction B).hom_equiv_naturality_right, ← biject_inclusion_natural _ _,
--       ← (exp.adjunction (i.obj _)).hom_equiv_naturality_right, assoc,
--       ← (exp.adjunction B).hom_equiv_naturality_right_symm, ← biject_inclusion_natural _ _],
-- end

-- open limits.prod

-- noncomputable
-- def preserves_pair_of_exponential_ideal (A B : C) : preserves_limit (pair.{v₁} A B) (is_right_adjoint.left i) :=
-- begin
--   let ir : is_right_adjoint i := by apply_instance,
--   let L := ir.left,
--   let adj : L ⊣ i := ir.adj,
--   let η : _ ⟶ L ⋙ i := adj.unit,
--   let ε : i ⋙ L ⟶ _ := adj.counit,
--   apply preserves_binary_prod_of_prod_comparison_iso L _ _,
--   let : L.obj (A ⨯ B) ≅ L.obj A ⨯ L.obj B := coyoneda.ext (λ Z, bijection i A B _) (λ _ _ _ _, bijection_natural _ _ _ _ _ _),
--   have equate : prod_comparison L A B = this.hom := (bijection_id A B).symm,
--   convert is_iso.of_iso this,
-- end

-- variable (i)
-- noncomputable
-- def preserves_binary_products_of_exponential_ideal : preserves_limits_of_shape (discrete walking_pair) (is_right_adjoint.left i) :=
-- { preserves_limit := λ K,
--   begin
--     apply preserves_limit_of_iso _ (diagram_iso_pair K).symm,
--     apply preserves_pair_of_exponential_ideal,
--   end }
end category_theory
