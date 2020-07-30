import data.equiv.basic
import algebra.category.Mon.limits
import category_theory.monoidal.category
--import category_theory.limits.shapes.finite_products

open category_theory category_theory.limits category_theory.iso
open Mon

namespace category_theory.monoidal

def assoc (X Y Z : Mon) : Mon.of (↥(Mon.of (↥X × ↥Y)) × ↥Z) ≅ Mon.of (↥X × ↥(Mon.of (↥Y × ↥Z))) :=
begin
  apply mul_equiv.to_Mon_iso,
  exact { to_fun := by rintro ⟨⟨x, y⟩, z⟩; exact (x, (y, z)),
  inv_fun := by rintro ⟨x, ⟨y, z⟩⟩; exact ((x, y), z),
  left_inv := by rintro ⟨⟨x, y⟩, z⟩; refl,
  right_inv := by rintro ⟨x, ⟨y, z⟩⟩; refl,
  map_mul' := by rintros ⟨⟨x, y⟩,_⟩ ⟨⟨x, y⟩, _⟩; refl, }
end

def of_self_iso (M : Mon) : Mon.of M ≅ M :=
{ hom := 𝟙 M, inv := 𝟙 M }

lemma product.lid (M : Mon) : of (punit × M) ≃* M :=
{to_fun := λ p, p.2,
 inv_fun := λ p, (1, p),
 left_inv := by intros x; cases x; cases x_fst; refl,
 right_inv := by intros x; refl,
 map_mul' := by intros x y; refl}

lemma product.rid (M : Mon) : of (M × punit) ≃* M :=
{to_fun := λ p, p.1,
 inv_fun := λ p, (p, 1),
 left_inv := by intros x; cases x; cases x_snd; refl,
 right_inv := by intros x; refl,
 map_mul' := by intros x y; refl}

lemma left_unitor (M : Mon) : Mon.of (↥(of punit) × ↥M) ≅ M :=
(mul_equiv.to_Mon_iso (product.lid M)).trans (of_self_iso M)

lemma right_unitor (M : Mon) : Mon.of (↥M × ↥(of punit)) ≅ M :=
(mul_equiv.to_Mon_iso (product.rid M)).trans (of_self_iso M)

instance Mon_monoidal : monoidal_category Mon := {
  tensor_obj := λ M N, Mon.of (↥M × ↥N),
  tensor_hom := λ _ _ _  _ f g,
  { to_fun := (λ p, (f p.1, g p.2)),
    map_one' := by tidy,
    map_mul' := by tidy },
  tensor_unit := of punit,
  associator := assoc,
  left_unitor := left_unitor,
  right_unitor := right_unitor
}


/-instance : has_terminal Mon :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    { cone :=
      { X := default Mon,
        π := by tidy },
      is_limit := by tidy } } }-/

--open category_theory.limits.walking_pair

--local attribute [instance] monoidal_of_has_finite_products

--instance : has_binary_products Mon := infer_instance
--instance : has_terminal Mon := infer_instance
--instance : monoidal_category Mon := monoidal_of_has_finite_products Mon

/-instance : has_binary_products Mon :=
{ has_limits_of_shape :=
  { has_limit := λ F,
    { cone :=
      { X := Mon.of (F.obj left × F.obj right),
        π := { app := begin
                        rintro ⟨_|_⟩,
                        exact { to_fun := λ x, x.fst, map_one' := prod.fst_one, map_mul' := prod.fst_mul },
                        exact { to_fun := λ x, x.snd, map_one' := prod.snd_one, map_mul' := prod.snd_mul },
                      end } },
      is_limit := { lift :=  λ s, { to_fun := λ x, ⟨s.π.app left x, s.π.app right x⟩,
      map_one' := prod.mk_eq_one.mpr ⟨monoid_hom.map_one (s.π.app left), monoid_hom.map_one (s.π.app right)⟩,
      map_mul' :=
      begin
        intros,
        rw (monoid_hom.map_mul (s.π.app left) x y),
        rw (monoid_hom.map_mul (s.π.app right) x y),
        refl,
      end },
  uniq' := sorry /- begin
    intros,
    ext,
    have := (m x),
    have q := (w left),
    have := ( s.π.app left) x,
    --simp at *,

    --have := congr_fun to_fun q,
    --convert @congr_fun _ _ (λ x, (m x).fst) ( s.π.app left) q,
  end-/
  } } } }-/

 /-        π :=
        { app := by { rintro ⟨_|_⟩, exact prod.fst, exact prod.snd, } }, },
      is_limit :=
      { lift := λ s x, (s.π.app left x, s.π.app right x),
        uniq' := λ s m w,
        begin
          ext,
          exact congr_fun (w left) x,
          exact congr_fun (w right) x,
        end }, } } }


-/


--monoidal_of_has_finite_products Mon

/- @[simp] lemma tensor_apply {W X Y Z : Mon} (f : W ⟶ X) (g : Y ⟶ Z) (p : W ⊗ Y) :
(f ⊗ g) p = (f p.1, g p.2) := rfl

@[simp] lemma left_unitor_hom_apply {X : Mon} {x : X} {p : punit} :
  ((λ_ X).hom : (𝟙_ (Mon)) ⊗ X → X) (p, x) = x := rfl
@[simp] lemma left_unitor_inv_apply {X : Mon} {x : X} :
  ((λ_ X).inv : X ⟶ (𝟙_ (Mon)) ⊗ X) x = (punit.star, x) := rfl

@[simp] lemma right_unitor_hom_apply {X : Mon} {x : X} {p : punit} :
  ((ρ_ X).hom : X ⊗ (𝟙_ (Mon)) → X) (x, p) = x := rfl
@[simp] lemma right_unitor_inv_apply {X : Mon} {x : X} :
  ((ρ_ X).inv : X ⟶ X ⊗ (𝟙_ (Mon))) x = (x, punit.star) := rfl

@[simp] lemma associator_hom_apply {X Y Z : Mon} {x : X} {y : Y} {z : Z} :
  ((α_ X Y Z).hom : (X ⊗ Y) ⊗ Z → X ⊗ (Y ⊗ Z)) ((x, y), z) = (x, (y, z)) := rfl
@[simp] lemma associator_inv_apply {X Y Z : Mon} {x : X} {y : Y} {z : Z} :
  ((α_ X Y Z).inv : X ⊗ (Y ⊗ Z) → (X ⊗ Y) ⊗ Z) (x, (y, z)) = ((x, y), z) := rfl -/

end category_theory.monoidal
