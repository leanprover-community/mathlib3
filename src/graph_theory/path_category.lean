import graph_theory.paths
import category_theory.functor
import category_theory.eq_to_hom

open category_theory

namespace multigraph

open path

universes v u v₁ u₁
/--
We define a type synonym for `V`,
thought of as a vertex in the particular graph G.
-/
-- This is perhaps badly named, as `a : paths G` actually says
-- "`a` is an object of the path category of `G`, i.e. a vertex of `G`"!

-- Possibly it will be safer to make this irreducible,
-- or possibly even an inductive type wrapping `V`.
def paths {V : Type u} (G : multigraph.{v} V) := V

variables {V : Type u} (G : multigraph.{v} V)

instance path_category : category (paths G) :=
{ hom := G.path,
  id := @path.nil _ _,
  comp := @comp _ _, }

@[simp]
lemma comp_as_comp {a b c : paths G} (p : a ⟶ b) (q : b ⟶ c) :
  comp p q = p ≫ q := rfl
@[simp]
lemma nil_as_id (a : paths G) : path.nil G a = 𝟙 a := rfl

variables {G} {C : Type u₁} [𝒞 : category.{v₁} C]
  (f_obj : V → C)
  (f_edge : Π {a b}, G.edge a b → (f_obj a ⟶ f_obj b))
include G 𝒞

namespace functor_of_edge_map

def to_hom : Π {a b} (p : G.path a b), (f_obj a ⟶ f_obj b)
| _ _ (path.nil _ _) := 𝟙 _
| _ _ (path.app p e) := to_hom p ≫ f_edge e

@[simp]
lemma to_hom.nil {a : paths G} : to_hom f_obj @f_edge (𝟙 a) = 𝟙 _ := rfl

@[simp]
lemma to_hom.app {a b c} (p : G.path a b) (e : G.edge b c) :
  to_hom f_obj @f_edge (path.app p e) = to_hom f_obj @f_edge p ≫ f_edge e := rfl

@[simp]
lemma to_hom.of {a b} (e : G.edge a b) : to_hom f_obj @f_edge (of e) = f_edge e :=
by { simp [of], }

@[simp]
lemma to_hom.comp : Π {a b c} (p : G.path a b) (q : G.path b c),
  to_hom f_obj @f_edge (comp p q) = to_hom f_obj @f_edge p ≫ to_hom f_obj @f_edge q
| _ _ _ p (path.nil _ _) := by simp
| _ _ _ _ (path.app _ _) := by {rw [comp_app, to_hom.app, to_hom.app, to_hom.comp], simp}

end functor_of_edge_map

open functor_of_edge_map

def functor_of_edge_map : (paths G) ⥤ C :=
{ obj := f_obj,
  map := λ a b p, to_hom f_obj @f_edge p,
  map_comp' := λ _ _ _ _ _, to_hom.comp _ _ _ _ }

-- We shouldn't really need this lemma. :-(
lemma functor_of_edge_map.map {a b} (p : G.path a b) :
  (functor_of_edge_map f_obj @f_edge).map p = to_hom f_obj @f_edge p := rfl

lemma functor_of_edge_map.unique {F : (paths G) ⥤ C}
  (h_obj : ∀ a, F.obj a = f_obj a)
  (h_edge : ∀ {a b} (e : G.edge a b),
    F.map (of e) = eq_to_hom (h_obj a) ≫ f_edge e ≫ eq_to_hom (h_obj b).symm) :
  F = functor_of_edge_map f_obj @f_edge :=
category_theory.functor.ext h_obj $ begin
  apply comp_induction,
  { intro a,
    simp [h_obj], },
  { intros, rw [h_edge, functor_of_edge_map.map, to_hom.of], },
  { intros a b c p q hp hq,
    simp [hp, hq], }
end

-- An alternative would be to finish this proof, which is less evil.
def functor_of_edge_map.iso_ext {F F' : (paths G) ⥤ C}
  (h_obj : ∀ a, F.obj a = F'.obj a)
  (h_edge : ∀ {a b} (e : G.edge a b),
    F.map (of e) = eq_to_hom (h_obj a) ≫ F'.map (of e) ≫ eq_to_hom (h_obj b).symm): F ≅ F' :=
nat_iso.of_components
  (λ a, eq_to_iso (h_obj a))
  (λ X Y f,
  begin
    induction f,
    { simp, },
    { simp, sorry }
  end)

end multigraph
