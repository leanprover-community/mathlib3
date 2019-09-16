import category_theory.types
import category_theory.core
import category_theory.concrete_category
import category_theory.elements
import category_theory.functorial

universes w₁ v₁ v₂ u₁ u₂

open category_theory

set_option pp.universes true

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]

section

class iso_functorial (f : C → D) :=
(map : Π {X Y : C}, (X ≅ Y) → (f X ≅ f Y))
(map_id'   : ∀ (X : C), map (iso.refl X) = iso.refl (f X) . obviously)
(map_comp' : ∀ {X Y Z : C} (f : X ≅ Y) (g : Y ≅ Z), map (f ≪≫ g) = (map f) ≪≫ (map g) . obviously)

restate_axiom iso_functorial.map_id'
attribute [simp] iso_functorial.map_id
restate_axiom iso_functorial.map_comp'
attribute [simp] iso_functorial.map_comp

@[simp] lemma iso_functorial.map_id_core (f : C → D) [iso_functorial.{v₁ v₂} f] (X : core C) :
  iso_functorial.map.{v₁} f (𝟙 X) = iso.refl _ :=
iso_functorial.map_id.{v₁ v₂} f (of_core X)
@[simp] lemma iso_functorial.map_comp_core (f : C → D) [iso_functorial.{v₁ v₂} f]
  (X Y Z : core C) (g : X ⟶ Y) (h : Y ⟶ Z) :
  iso_functorial.map.{v₁} f (g ≫ h) = iso_functorial.map.{v₁} f g ≪≫ iso_functorial.map.{v₁} f h :=
iso_functorial.map_comp.{v₁ v₂} f g h

def as_core_functor (f : C → D) [I : iso_functorial.{v₁ v₂} f] : core C ⥤ D :=
{ obj := λ X, f (of_core X),
  map := λ X Y g, iso.hom (iso_functorial.map.{v₁} f g) }

@[simp] lemma as_core_functor_obj  (f : C → D) [iso_functorial.{v₁ v₂} f] (X : core C) :
  (as_core_functor f).obj X = f (of_core X) := rfl

instance functor_obj_iso_functorial (F : C ⥤ D) : iso_functorial.{v₁ v₂} F.obj :=
{ map := λ X Y f, F.map_iso f }

-- TODO specialise some universe variables?
instance iso_functorial_elements_1 (F : C ⥤ Type w₁) (g : C → D) [iso_functorial.{v₁ v₂} g] :
  iso_functorial.{v₁ v₂} (λ (X : F.elements), g (X.1)) :=
{ map := λ X Y f,  iso_functorial.map.{v₁ v₂} g (of_element_iso f) }

omit 𝒟
instance (p : C → Prop) : subsingleton (functorial.{v₁ 0} (plift ∘ p)) :=
⟨by { rintros ⟨a⟩ ⟨b⟩, congr, ext, apply proof_irrel_heq, apply proof_irrel_heq, }⟩

end

section
include 𝒞
class hygienic (p : C → Prop) : Prop :=
(map : Π {X Y : C}, (X ≅ Y) → (p X ↔ p Y))

instance (p : C → Prop) : subsingleton (hygienic.{v₁} p) :=
⟨by { rintros ⟨a⟩ ⟨b⟩, congr }⟩

def hygienic_of_hygieinic_core (p : C → Prop) [hygienic.{v₁} (p ∘ of_core)] : hygienic.{v₁} p :=
{ map := λ X Y f,
  begin
    have t := hygienic.map.{v₁} (p ∘ of_core) (core.lift_iso f),
    exact t,
  end }

def hygienic_equiv_functorial (p : C → Prop) : hygienic.{v₁} p ≃ functorial.{v₁ 0} (plift ∘ p ∘ (core.inclusion C).obj) :=
{ to_fun := λ H, by exactI
  { map := λ X Y f x, ⟨(hygienic.map p f).mp x.down⟩ },
  inv_fun := λ F, by exactI
  { map := λ X Y f,
  begin
    split,
    intro h,
    have f' := functorial.map.{v₁ 0} (plift ∘ p ∘ (core.inclusion C).obj) f,
    exact (f' ⟨h⟩).down,
    intro h,
    have f' := functorial.map.{v₁ 0} (plift ∘ p ∘ (core.inclusion C).obj) f.symm,
    exact (f' ⟨h⟩).down,
  end },
  left_inv := by tidy,
  right_inv := by tidy }

def hygienic_not (p : C → Prop) [hygienic.{v₁} p] : hygienic.{v₁} (λ X, ¬ p X) :=
{ map := λ X Y f,
  begin
    have ph := hygienic.map p f,
    finish,
  end }
def hygienic_and (p q : C → Prop) [hygienic.{v₁} p] [hygienic.{v₁} q] : hygienic.{v₁} (λ X, p X ∧ q X) :=
{ map := λ X Y f,
  begin
    have ph := hygienic.map p f,
    have qh := hygienic.map q f,
    finish,
  end }
def hygienic_or (p q : C → Prop) [hygienic.{v₁} p] [hygienic.{v₁} q] : hygienic.{v₁} (λ X, p X ∨ q X) :=
{ map := λ X Y f,
  begin
    have ph := hygienic.map p f,
    have qh := hygienic.map q f,
    finish,
  end }

def hygienic_forall (F : C ⥤ Type w₁) (q : F.elements → Prop) [hygienic.{v₁} q] :
  hygienic.{v₁} (λ X : C, ∀ a : F.obj X, q (as_element a)) :=
begin
  fsplit,
  intros X Y f,
  fsplit,
  { intros h a,
    have qh := hygienic.map.{v₁ (max u₁ w₁)} q,
    have t := qh (as_element_iso f.symm a),
    apply t.2,
    apply h, },
  { intros h a,
    have qh := hygienic.map.{v₁ (max u₁ w₁)} q,
    have t := qh (as_element_iso f a),
    apply t.2,
    apply h, },
end


def hygienic_exists (F : C ⥤ Type w₁) (q : F.elements → Prop) [hygienic.{v₁} q] :
  hygienic.{v₁} (λ X : C, ∃ a : F.obj X, q (as_element a)) :=
begin
  fsplit,
  intros X Y f,
  fsplit,
  { rintros ⟨a, h⟩,
    have qh := hygienic.map.{v₁ (max u₁ w₁)} q,
    have t := qh (as_element_iso f a),
    use F.map f.hom a,
    apply t.1,
    apply h, },
  { rintros ⟨a, h⟩,
    have qh := hygienic.map.{v₁ (max u₁ w₁)} q,
    have t := qh (as_element_iso f.symm a),
    use F.map f.inv a,
    apply t.1,
    apply h, },
end

end

def bundled_hygienic {m : Type u₁ → Type u₁} [category.{u₁} (bundled m)] (p : Π (α : Type u₁), m α → Prop) : Prop :=
hygienic.{u₁ u₁+1} (λ (A : bundled m), p A.α A.str)

attribute [class] bundled_hygienic

def hygienic_forall_forget (C : Type (u₁+1)) [concrete_category C]
  (q : Π (X : C), (forget C).obj X → Prop) [hygienic.{u₁} (λ X : (forget C).elements, q X.1 X.2)] :
    hygienic.{u₁} (λ X : C, ∀ a : (forget C).obj X, q X a) :=
hygienic_forall (forget C) (λ e, q e.1 e.2)

instance hygienic_exists_functorial [category.{v₁} C] (f : C → Type w₁) [functorial.{v₁ w₁} f] (p : Π X : C, f X → Prop)
  [hygienic.{v₁} (λ e : (as_functor f).elements, p e.1 e.2)]:
    hygienic.{v₁} (λ X : C, ∃ a : f X, p X a) :=
hygienic_exists (as_functor f) (λ e, p e.1 e.2)

instance hygienic_exists_iso_functorial' [category.{v₁} C] (f : C → Type w₁) [iso_functorial.{v₁ w₁} f] (p : Π X : C, f X → Prop)
  [hygienic.{v₁} (λ e : (as_core_functor f).elements, p (of_core e.1) e.2)]:
    hygienic.{v₁} (λ X : core C, ∃ a : f (of_core X), p (of_core X) a) :=
(hygienic_exists (as_core_functor f) (λ e, p (of_core e.1) e.2))

def hygienic_exists_iso_functorial [category.{v₁} C] (f : C → Type w₁) [iso_functorial.{v₁ w₁} f] (p : Π X : C, f X → Prop)
  [hygienic.{v₁} (λ e : (as_core_functor f).elements, p (of_core e.1) e.2)]:
    hygienic.{v₁} (λ X : C, ∃ a : f X, p X a) :=
hygienic_of_hygieinic_core (λ X : C, ∃ a : f X, p X a)
