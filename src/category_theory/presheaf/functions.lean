import category_theory.presheaf
import category_theory.instances.TopCommRing
import group_theory.submonoid
import ring_theory.subring

universes v u

open category_theory
open category_theory.instances
open topological_space

open category_theory
open category_theory.instances
open topological_space

namespace category_theory.presheaf_on_space

variables (X : Top.{v})

def presheaf_of_functions_to (T : Top.{v}) : presheaf_on_space (Type v) X :=
(opens.to_Top X).op ⋙ (yoneda.obj T)

instance continuous_submonoid (α : Type u) (β : Type v) [topological_space α] [topological_space β]
  [monoid β] [topological_monoid β] : is_submonoid { f : α → β | continuous f } :=
{ one_mem :=
  begin
    dsimp [has_one.one, monoid.one],
    exact continuous_const,
  end,
  mul_mem := λ f g fc gc,
  begin
    have q := continuous.comp (continuous.prod_mk fc gc) (topological_monoid.continuous_mul β),
    exact q,
  end }.

instance continuous_subring (α : Type u) (β : Type v) [topological_space α] [topological_space β]
  [ring β] [topological_ring β] : is_subring { f : α → β | continuous f } :=
{ zero_mem :=
  begin
    dsimp [has_zero.zero, add_group.zero, add_monoid.zero, add_comm_group.zero, ring.zero],
    exact continuous_const,
  end,
  add_mem := λ f g fc gc,
  begin
    have q := continuous.comp (continuous.prod_mk fc gc) (topological_add_monoid.continuous_add β),
    exact q,
  end,
  neg_mem := λ f fc,
  begin
    have q := continuous.comp fc (topological_ring.continuous_neg β),
    exact q,
  end,
  ..presheaf_on_space.continuous_submonoid α β }.

instance continuous_monoid {α : Type u} {β : Type v} [topological_space α] [topological_space β]
  [monoid β] [topological_monoid β] : monoid { f : α → β | continuous f } :=
subtype.monoid

instance continuous_comm_ring {α : Type u} {β : Type v} [topological_space α] [topological_space β]
  [comm_ring β] [topological_ring β] : comm_ring { f : α → β | continuous f } :=
@subtype.comm_ring _ _ _ (presheaf_on_space.continuous_subring α β) -- infer_instance doesn't work?!

def continuous_functions (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) : CommRing.{v} :=
{ α := (unop X) ⟶ (TopCommRing.forget_to_Top.obj R),
  str := presheaf_on_space.continuous_comm_ring } -- but infer_instance doesn't work?

-- FIXME why do we have to state these about monoid.one and comm_ring.add, instead
-- of using notation
@[simp] def continuous_functions_one (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) (x) :
  (monoid.one ↥(continuous_functions X R)).val x = 1 :=
rfl
@[simp] def continuous_functions_add (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) (f g : continuous_functions X R) (x) :
  (comm_ring.add f g).val x = f.1 x + g.1 x :=
rfl
@[simp] def continuous_functions_mul (X : Top.{v}ᵒᵖ) (R : TopCommRing.{v}) (f g : continuous_functions X R) (x) :
  (ring.mul f g).val x = f.1 x * g.1 x :=
rfl

def continuous_functions.pullback {X Y : Topᵒᵖ} (f : X ⟶ Y) (R : TopCommRing) : continuous_functions X R ⟶ continuous_functions Y R :=
{ val := λ g, f.unop ≫ g,
  property :=
  { map_one := rfl,
    map_add := by tidy,
    map_mul := by tidy } }

local attribute [extensionality] subtype.eq

def continuous_functions.map (X : Topᵒᵖ) {R S : TopCommRing} (φ : R ⟶ S) : continuous_functions X R ⟶ continuous_functions X S :=
{ val := λ g, g ≫ (TopCommRing.forget_to_Top.map φ),
  property :=
  { map_one := begin ext1, ext1, dsimp, simp, exact φ.2.1.map_one end,
    map_add := λ x y, begin ext1, ext1, dsimp, simp, apply φ.2.1.map_add end,
    map_mul := λ x y, begin ext1, ext1, dsimp, simp, apply φ.2.1.map_mul end } }

def CommRing_yoneda : TopCommRing ⥤ (Topᵒᵖ ⥤ CommRing) :=
{ obj := λ R,
  { obj := λ X, continuous_functions X R,
    map := λ X Y f, continuous_functions.pullback f R },
  map := λ R S φ,
  { app := λ X, continuous_functions.map X φ } }

def presheaf_of_functions_to_TopCommRing (T : TopCommRing.{v}) :
  presheaf_on_space CommRing.{v} X :=
(opens.to_Top X).op ⋙ (CommRing_yoneda.obj T)


noncomputable def presheaf_of_rational_functions (Y : Top.{0}) : presheaf_on_space CommRing Y :=
presheaf_of_functions_to_TopCommRing Y TopCommRing.rational

noncomputable def presheaf_of_real_functions (Y : Top) : presheaf_on_space CommRing Y :=
presheaf_of_functions_to_TopCommRing Y TopCommRing.real

noncomputable def presheaf_of_complex_functions (Y : Top) : presheaf_on_space CommRing Y :=
presheaf_of_functions_to_TopCommRing Y TopCommRing.complex

end category_theory.presheaf_on_space
