import category_theory.functor
import category_theory.eq_to_hom
import graph_theory.paths

open category_theory

namespace directed_multigraph

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
def paths {V : Type u} (G : directed_multigraph.{v} V) := V

variables {V : Type u} (G : directed_multigraph.{v} V)

instance path_category : category (paths G) :=
{ hom := G.path,
  id := @path.nil _ _,
  comp := @concat _ _, }

lemma concat_as_comp {a b c : paths G} (p : a ⟶ b) (q : b ⟶ c) :
  concat p q = p ≫ q := rfl
-- lemma cons_as_comp {a b c : paths G} (p : G.edge a b) (q : b ⟶ c) :
--   p :: q = concat p[p] q := rfl
lemma nil_as_id (a : paths G) : p[] = 𝟙 a := rfl

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

lemma functor_map_cons (F : paths G ⥤ C) {a b c : paths G} (p : G.edge a b) (q : b ⟶ c) :
  F.map (p :: q) = F.map p[p] ≫ F.map q :=
by convert F.map_comp p[p] q

variables {G} (F : graph_hom G (as_graph C))
include G

namespace functor_of_edge_map

@[simp]
def to_hom : Π {a b} (p : G.path a b), (F.obj a ⟶ F.obj b)
| _ _ p[] := 𝟙 _
| _ _ (e :: p) := F.edge e ≫ to_hom p

@[simp]
lemma to_hom.comp : Π {a b c} (p : G.path a b) (q : G.path b c),
  to_hom F (concat p q) = to_hom F p ≫ to_hom F q
| _ _ _ p[] _ := begin simp, end
| _ _ _ (_ :: _) _ := begin simp [to_hom.comp], end

end functor_of_edge_map

open functor_of_edge_map

def functor_of_edge_map : (paths G) ⥤ C :=
{ obj := F.obj,
  map := λ a b p, to_hom F p,
  map_comp' := @to_hom.comp _ _ _ _ _ }

@[simp]
lemma functor_of_edge_map.map_edge {a b} (e : G.edge a b) :
  (functor_of_edge_map F).map p[e] = F.edge e ≫ 𝟙 _ := rfl

-- This is a less evil alternative, perhaps
def functor_of_edge_map.iso_ext {F F' : (paths G) ⥤ C}
  (h_obj : ∀ a, F.obj a = F'.obj a)
  (h_edge : ∀ {a b} (e : G.edge a b),
    F.map (p[e]) = eq_to_hom (h_obj a) ≫ F'.map (p[e]) ≫ eq_to_hom (h_obj b).symm) :
    F ≅ F' :=
nat_iso.of_components
  (λ a, eq_to_iso (h_obj a))
  (λ X Y f,
  begin
    induction f,
    { simp [nil_as_id], },
    { rw [functor_map_cons _ _ f_e f_l, functor_map_cons _ _ f_e f_l],
      dsimp at f_ih,
      simp [f_ih, h_edge], }
  end)

end directed_multigraph
