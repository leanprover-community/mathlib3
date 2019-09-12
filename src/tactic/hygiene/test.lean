import category_theory.types
import category_theory.core
import category_theory.concrete_category
import category_theory.elements
import algebra.category.CommRing.basic
import ring_theory.ideals

universes w₁ v₁ v₂ u₁ u₂

open category_theory

set_option pp.universes true

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]

section
include 𝒞 𝒟
class functorial (f : C → D) :=
(map : Π {X Y : C}, (X ⟶ Y) → (f X ⟶ f Y))
(map_id'   : ∀ (X : C), map (𝟙 X) = 𝟙 (f X) . obviously)
(map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = (map f) ≫ (map g) . obviously)

restate_axiom functorial.map_id'
attribute [simp] functorial.map_id
restate_axiom functorial.map_comp'
attribute [simp] functorial.map_comp

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

def hygienic_equiv_functorial (p : C → Prop) : hygienic.{v₁} p ≃ functorial.{v₁ 0} (plift ∘ p ∘ core.inclusion.obj) :=
{ to_fun := λ H, by exactI
  { map := λ X Y f x, ⟨(hygienic.map p f).mp x.down⟩ },
  inv_fun := λ F, by exactI
  { map := λ X Y f,
  begin
    split,
    intro h,
    have f' := functorial.map.{v₁ 0} (plift ∘ p ∘ core.inclusion.obj) f,
    exact (f' ⟨h⟩).down,
    intro h,
    have f' := functorial.map.{v₁ 0} (plift ∘ p ∘ core.inclusion.obj) f.symm,
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

def hygienic_bundled_forall {m : Type u₁ → Type u₁} (q : Π (α : Type u₁) (i : m α), α → Prop) [hygienic.{v₁} (λ X : functor.elements (@forget m _ _), q X.1.1 X.1.2 X.2)] :
  hygienic.{u₁} (λ X : bundled m, ∀ a : X.α, q X.α X.str a) :=
sorry


instance hygienic_zero_eq_one : bundled_hygienic.{u₁} (λ (α : Type u₁) [comm_ring α], by exactI (0 : α) = (1 : α)) :=
begin
  dsimp [bundled_hygienic],
  fsplit,
  intros X Y f,
  fsplit,
  { intro h,
    haveI := f.hom.property,
    have t := congr_arg f.hom.val h,
    rw [is_ring_hom.map_zero f.hom.val] at t,
    rw [is_ring_hom.map_one f.hom.val] at t,
    exact t },
  { intro h,
    haveI := f.inv.property,
    have t := congr_arg f.inv.val h,
    rw [is_ring_hom.map_zero f.inv.val] at t,
    rw [is_ring_hom.map_one f.inv.val] at t,
    exact t },
end

instance hygienic_is_unit :
  hygienic.{u₁ u₁+1}
  (λ (X : bundled.{u₁ u₁} comm_ring.{u₁}), ∀ (a : X.α), is_unit.{u₁} a ∨ is_unit.{u₁} (1 + -a)) :=
begin
  apply hygienic_forall,
end

instance : bundled_hygienic.{u₁} is_local_ring.{u₁} :=
begin
  have t : (is_local_ring = λ (x : Type u₁) [comm_ring x], by exactI is_local_ring x), funext, refl,
  rw t,
  clear t,
  conv {
    congr, funext, dsimp [is_local_ring],
  },
  dsimp [bundled_hygienic],
  apply @hygienic_and _ _ _ _ _ _,
  apply @hygienic_not _ _ _ _,
  apply hygienic_zero_eq_one,
  extract_goal,
  apply @hygienic_forall _ _ (forget) (λ (a : forget.elements.{u₁}), by {haveI : comm_ring.{u₁} (forget.obj a.1) := a.1.2, exact is_unit a.2 ∨ is_unit (1 + - a.2)}) _,
  funext,
  dsimp [forget],
  funext,
  sorry,
end


-- instance : functorial.{u₁ u₁} local_ring.{u₁} :=
-- begin
--
-- end
