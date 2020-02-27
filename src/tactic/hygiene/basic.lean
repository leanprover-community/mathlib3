import tactic.hygiene.iso_functorial

universes w₁ v₁ v₂ u₁ u₂

open category_theory

set_option pp.universes true

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]

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
  [hygienic.{v₁} (λ e : (functor.of f).elements, p e.1 e.2)] :
    hygienic.{v₁} (λ X : C, ∃ a : f X, p X a) :=
hygienic_exists (functor.of f) (λ e, p e.1 e.2)

instance hygienic_exists_iso_functorial' [category.{v₁} C] (f : C → Type w₁) [iso_functorial.{v₁ w₁} f] (p : Π X : C, f X → Prop)
  [hygienic.{v₁} (λ e : (as_core_functor f).elements, p (of_core e.1) e.2)] :
    hygienic.{v₁} (λ X : core C, ∃ a : f (of_core X), p (of_core X) a) :=
(hygienic_exists (as_core_functor f) (λ e, p (of_core e.1) e.2))

def hygienic_exists_iso_functorial [category.{v₁} C] (f : C → Type w₁) [iso_functorial.{v₁ w₁} f] (p : Π X : C, f X → Prop)
  [hygienic.{v₁} (λ e : (as_core_functor f).elements, p (of_core e.1) e.2)] :
    hygienic.{v₁} (λ X : C, ∃ a : f X, p X a) :=
hygienic_of_hygieinic_core (λ X : C, ∃ a : f X, p X a)
