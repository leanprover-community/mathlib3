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
point of view of objects in `D`, `A` and `i L A` look the same.
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
  erw ev_coev_assoc,
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
  ((left_adjoint i).obj (A ⨯ B) ⟶ X) ≃
  ((left_adjoint i).obj (A ⨯ i.obj ((left_adjoint i).obj B)) ⟶ X) :=
(hom_equiv_aux1 i _ _ _).trans
  ((unit_comp_partial_bijective _ (exponential_ideal.exp_closed (inclusion_is_in _ _) _)).trans
    (hom_equiv_aux1 i _ _ _).symm)

@[reassoc]
lemma hom_equiv_aux2_naturality_A [reflective i] [exponential_ideal i] {A A' : C} (B : C) (X : D)
  (f : A' ⟶ A) (k) :
    (left_adjoint i).map (limits.prod.map f (𝟙 _)) ≫ hom_equiv_aux2 i A B X k
  = hom_equiv_aux2 i A' B X ((left_adjoint i).map (limits.prod.map f (𝟙 _)) ≫ k) :=
begin
  dsimp [hom_equiv_aux2],
  rw [← hom_equiv_aux1_naturality_A, equiv.eq_symm_apply, ← hom_equiv_aux1_naturality_A,
      equiv.apply_symm_apply, unit_comp_partial_bijective_natural],
end

lemma hom_equiv_aux2_naturality_B [reflective i] [exponential_ideal i] (A : C) {B B' : C} (X : D)
  (f : B' ⟶ B) (k) :
    (left_adjoint i).map (limits.prod.map (𝟙 _) (i.map ((left_adjoint i).map f))) ≫ hom_equiv_aux2 i A B X k
  = hom_equiv_aux2 i A B' X ((left_adjoint i).map (limits.prod.map (𝟙 _) f) ≫ k) :=
begin
  dsimp [hom_equiv_aux2, hom_equiv_aux1],
  erw adjunction.hom_equiv_naturality_left,
  erw ← (adjunction.comp _ i (exp.adjunction A) _).hom_equiv_naturality_left_symm,
  congr' 1,
  rw [← equiv.symm_apply_eq, unit_comp_partial_bijective_symm_apply],
  erw ← (adjunction.of_right_adjoint i).unit.naturality_assoc,
  rw [← unit_comp_partial_bijective_symm_apply B, equiv.symm_apply_apply],
  refl,
end

lemma hom_equiv_aux2_naturality_X [reflective i] [exponential_ideal i] (A : C) (B : C) {X X' : D}
  (f : X ⟶ X') (k) :
  hom_equiv_aux2 i A B X k ≫ f = hom_equiv_aux2 i A B X' (k ≫ f) :=
begin
  dsimp [hom_equiv_aux2, hom_equiv_aux1],
  rw [adjunction.hom_equiv_naturality_right, unit_comp_partial_bijective_natural,
      ←adjunction.hom_equiv_naturality_right_symm],
end

lemma hom_equiv_aux2_naturality_symm_X [reflective i] [exponential_ideal i] (A : C) (B : C) {X X' : D}
  (f : X ⟶ X') (k) :
  (hom_equiv_aux2 i A B X).symm k ≫ f = (hom_equiv_aux2 i A B X').symm (k ≫ f) :=
by rw [equiv.eq_symm_apply, ← hom_equiv_aux2_naturality_X, equiv.apply_symm_apply]

def inner_mul_unit_iso [reflective i] [exponential_ideal i] (A B : C) :
  (left_adjoint i).obj (A ⨯ B) ≅ (left_adjoint i).obj (A ⨯ i.obj ((left_adjoint i).obj B)) :=
{ hom := (hom_equiv_aux2 _ _ _ _).symm (𝟙 _),
  inv := (hom_equiv_aux2 _ _ _ _) (𝟙 _),
  hom_inv_id' := by rw [hom_equiv_aux2_naturality_symm_X, id_comp, equiv.symm_apply_apply],
  inv_hom_id' := by rw [hom_equiv_aux2_naturality_X, id_comp, equiv.apply_symm_apply] }

@[reassoc]
lemma inner_mul_natural [reflective i] [exponential_ideal i] {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') :
  (inner_mul_unit_iso i A B).hom ≫ (left_adjoint i).map (limits.prod.map f (i.map ((left_adjoint i).map g))) = (left_adjoint i).map (limits.prod.map f g) ≫ (inner_mul_unit_iso i A' B').hom :=
begin
  rw [← iso.comp_inv_eq, assoc, ← iso.eq_inv_comp],
  change _ ≫ hom_equiv_aux2 _ _ _ _ _ = hom_equiv_aux2 _ _ _ _ _ ≫ _,
  have : limits.prod.map f (i.map ((left_adjoint i).map g)) = limits.prod.map f (𝟙 _) ≫ limits.prod.map (𝟙 _) (i.map ((left_adjoint i).map g)),
    simp,
  rw [this, (left_adjoint i).map_comp, assoc, hom_equiv_aux2_naturality_B, comp_id,
      hom_equiv_aux2_naturality_A, hom_equiv_aux2_naturality_X, id_comp,
      ← (left_adjoint i).map_comp],
  simp,
end

def inner_mul_unit_iso_right [reflective i] [exponential_ideal i] (A B : C) :
  (left_adjoint i).obj (A ⨯ B) ≅ (left_adjoint i).obj (i.obj ((left_adjoint i).obj A) ⨯ B) :=
(left_adjoint i).map_iso (limits.prod.braiding A B) ≪≫
inner_mul_unit_iso _ _ _ ≪≫
(left_adjoint i).map_iso (limits.prod.braiding _ _)

@[reassoc]
lemma inner_mul_right_natural [reflective i] [exponential_ideal i] {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') :
  (inner_mul_unit_iso_right i A B).hom ≫ (left_adjoint i).map (limits.prod.map (i.map ((left_adjoint i).map f)) g) = (left_adjoint i).map (limits.prod.map f g) ≫ (inner_mul_unit_iso_right i A' B').hom :=
begin
  change ((left_adjoint i).map _ ≫ _ ≫ (left_adjoint i).map _) ≫ _ = _ ≫ _ ≫ _ ≫ _,
  rw [assoc, assoc, ← (left_adjoint i).map_comp, ← limits.braid_natural, (left_adjoint i).map_comp,
      inner_mul_natural_assoc, ← (left_adjoint i).map_comp_assoc, ← limits.braid_natural,
      (left_adjoint i).map_comp, assoc],
  refl,
end

def main_iso [reflective i] [exponential_ideal i] (A B : C) :
  (left_adjoint i).obj (A ⨯ B) ≅ (left_adjoint i).obj A ⨯ (left_adjoint i).obj B :=
begin
  refine
    inner_mul_unit_iso _ _ _ ≪≫
    inner_mul_unit_iso_right _ _ _ ≪≫
    (left_adjoint i).map_iso _ ≪≫
    as_iso ((adjunction.of_right_adjoint i).counit.app _),
  haveI := adjunction.right_adjoint_preserves_limits (adjunction.of_right_adjoint i),
  exact (as_iso (prod_comparison i _ _)).symm,
end

lemma main_iso_natural [reflective i] [exponential_ideal i] {A A' B B' : C}
  (f : A ⟶ A') (g : B ⟶ B') :
  (main_iso i A B).hom ≫ limits.prod.map ((left_adjoint i).map f) ((left_adjoint i).map g) =
  (left_adjoint i).map (limits.prod.map f g) ≫ (main_iso i A' B').hom :=
begin
  change (_ ≫ _ ≫ _ ≫ (adjunction.of_right_adjoint i).counit.app _) ≫ _ = _ ≫ _ ≫ _ ≫ _ ≫ (adjunction.of_right_adjoint i).counit.app _,
  rw [assoc, assoc, assoc, ← inner_mul_natural_assoc, ← inner_mul_right_natural_assoc],
  congr' 2,
  rw ← iso.eq_inv_comp,
  change _ = (left_adjoint i).map (prod_comparison _ _ _) ≫ (left_adjoint i).map _ ≫ (left_adjoint i).map _ ≫ _,
  rw [← (left_adjoint i).map_comp_assoc, ← (left_adjoint i).map_comp_assoc,
      ← prod_comparison_natural, assoc],
  dsimp,
  rw [is_iso.hom_inv_id, comp_id],
  apply ((adjunction.of_right_adjoint i).counit.naturality _).symm,
end

end

end category_theory
