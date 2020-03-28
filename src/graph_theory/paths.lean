import category_theory.category
  category_theory.functor
  category_theory.eq_to_hom
  category_theory.single_obj
  graph_theory.hedetniemi
open category_theory

universes v u v₁ u₁

variables {V : Type u} (G : multigraph.{v} V)

namespace multigraph

inductive path : V → V → Type (max u v)
| nil (a : V) : path a a
| app {a b c : V} (p : path a b) (e : G.edge b c) : path a c

end multigraph
open multigraph

namespace path
variable {G}

def of {a b : V} : G.edge a b → G.path a b := path.app (path.nil _ _)

def comp : Π {a b c : V}, G.path a b → G.path b c → G.path a c
| _ _ _ p (path.nil _ _) := p
| _ _ _ p (path.app q e) := path.app (comp p q) e

lemma comp_app {a b c d : V} {p : G.path a b} {q : G.path b c} {e : G.edge c d} :
  comp p (path.app q e) = path.app (comp p q) e := rfl

@[simp]
lemma comp_nil {a b : V} {p : G.path a b} : comp p (path.nil _ _) = p := rfl

@[simp]
lemma nil_comp : ∀ {a b : V} {p : G.path a b}, comp (path.nil _ _) p = p
| _ _ (path.nil _ _) := rfl
| _ _ (path.app p e) := by rw [comp_app, nil_comp]

@[simp]
lemma comp_assoc : ∀ {a b c d : V} {p : G.path a b} {q : G.path b c} {r : G.path c d},
  comp (comp p q) r = comp p (comp q r)
| _ _ _ _ _ _ (path.nil _ _) := rfl
| _ _ _ _ _ _ (path.app _ _) := by {rw [comp_app, comp_app, comp_app, comp_assoc]}

lemma app_eq_comp_of {a b c} (p : G.path a b) (e : G.edge b c) :
  path.app p e = comp p (of e) := rfl

lemma comp_induction {C : Π {a b} (p : G.path a b), Sort*}
  (h_nil : ∀ a, C (@path.nil _ _ a))
  (h_of : ∀ {a b} (e : G.edge a b), C (of e))
  (h_comp : ∀ {a b c} {p : G.path a b} {q : G.path b c}, C p → C q → C (comp p q)) :
  ∀ {a b} (p : G.path a b), C p
| _ _ (path.nil _ _) := h_nil _
| _ _ (path.app p e) := by {rw app_eq_comp_of, exact h_comp (comp_induction p) (h_of e)}

end path
open path

/--
We define a type synonym for `V`,
thought of as a vertex in the particular graph G.
-/
-- This is perhaps badly named, as `a : paths G` actually says
-- "`a` is an object of the path category of `G`, i.e. a vertex of `G`"!

-- Possibly it will be safer to make this irreducible,
-- or possibly even an inductive type wrapping `V`.
def paths {V : Type u} (G : multigraph.{v} V) := V

instance path_category : category (paths G) :=
{ hom := G.path,
  id := @path.nil _ _,
  comp := @comp _ _, }

@[simp]
lemma comp_as_comp {a b c : paths G} (p : a ⟶ b) (q : b ⟶ c) :
  comp p q = p ≫ q := rfl
@[simp]
lemma nil_as_id (a : paths G) : path.nil G a = 𝟙 a := rfl

section to_category

variables {G} {C : Type u₁} [category.{v₁} C]
  (f_obj : V → C)
  (f_edge : Π {a b}, G.edge a b → (f_obj a ⟶ f_obj b))
include G

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

def to_category : (paths G) ⥤ C :=
{ obj := f_obj,
  map := λ a b p, to_hom f_obj @f_edge p,
  map_comp' := λ _ _ _ _ _, to_hom.comp _ _ _ _ }

lemma to_category.obj : (to_category f_obj @f_edge).obj = f_obj := rfl
lemma to_category.map {a b} (p : G.path a b) :
  (to_category f_obj @f_edge).map p = to_hom f_obj @f_edge p := rfl

lemma to_category.unique {F : (paths G) ⥤ C}
  (h_obj : ∀ a, F.obj a = f_obj a)
  (h_edge : ∀ {a b} (e : G.edge a b),
    F.map (of e) = eq_to_hom (h_obj a) ≫ f_edge e ≫ eq_to_hom (h_obj b).symm) :
  F = to_category f_obj @f_edge :=
category_theory.functor.ext h_obj $ begin
  apply comp_induction,
  { intro a,
    simp },
  { intros, rw [h_edge, to_category.map, to_hom.of] },
  { intros a b c p q hp hq,
    simp [hp, hq], }
end

end to_category

namespace path

variable {G}

-- Would probably be more sensible to define length directly
def length {a b} (p : G.path a b) : ℕ :=
@to_hom _ _ (single_obj $ multiplicative ℕ) _ (λ _, single_obj.star _)
  (λ _ _ _, (1:ℕ)) _ _ p

lemma length_def {a b} (p : G.path a b) : length p =
@to_hom _ _ (single_obj $ multiplicative ℕ) _ (λ _, single_obj.star _)
  (λ _ _ _, (1:ℕ)) _ _ p := rfl

lemma length_comp {a b c} (p : G.path a b) (q : G.path b c) :
  length (comp p q) = length p + length q :=
by { rw [length_def, to_hom.comp, add_comm], refl }

-- Why is this not rfl when #reduce lenth (@path.nil _ G a) gives 0?
lemma length_nil {a : V} : length (@path.nil _ G a) = (0 : ℕ) :=
by {rw [←add_left_inj (length $ path.nil _ _), ←length_comp], refl }

lemma length_of {a b} (e : G.edge a b) : length (of e) = 1 := rfl

lemma length_app {a b c} (p : G.path a b) (e : G.edge b c) :
  length (path.app p e) = length p + 1 := add_comm _ _

end path

-- TODO: define "reversible" multigraphs and the free groupoid
