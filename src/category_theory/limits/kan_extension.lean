import category_theory.punit
import category_theory.comma
import category_theory.limits.functor_category

noncomputable theory

namespace category_theory

open limits

universes v u₁ u₂ u₃

variables {S : Type v} {L : Type u₂} {D : Type u₃}
variables [category.{v} S] [category.{v} L] [category.{v} D]

namespace Ran

local attribute [simp] comma.snd comma.map_left

variables (ι : S ⥤ L)

@[simp, derive category]
def index (l : L) := comma (functor.from_punit l) ι

variable {ι}

@[simp]
def index.mk {x : L} {y : S} (f : x ⟶ ι.obj y) : index ι x := ⟨⟨⟩, y, f⟩

@[simp]
def index_map {x y : L} (f : x ⟶ y) : index ι y ⥤ index ι x :=
comma.map_left _ ((functor.const _).map f)

@[simps]
def index.mk_hom {x : L} {y z : S} (f : x ⟶ ι.obj y) (g : y ⟶ z) :
  index.mk f ⟶ index.mk (f ≫ ι.map g) :=
{ left := 𝟙 _,
  right := g,
  w' := by simpa }

@[simp]
lemma index_map_mk {x y : L} {z : S} (f : x ⟶ ι.obj z) (g : y ⟶ x) :
  (index_map g).obj (index.mk f) = index.mk (g ≫ f) := rfl

@[simp]
lemma index_map_id {x : L} {j : index ι x} :
  (index_map (𝟙 x)).obj j = j := by {cases j, tidy}

@[simp]
lemma index_map_comp {x y z : L} (f : z ⟶ y) (g : y ⟶ x) (j : index ι x) :
  (index_map (f ≫ g)).obj j = (index_map f).obj ((index_map g).obj j) :=
by {cases j, tidy}

variable (ι)
@[simp]
def diagram (F : S ⥤ D) (x : L) : index ι x ⥤ D :=
  comma.snd (functor.from_punit x) ι ⋙ F
variable {ι}

def cone {F : S ⥤ D} {G : L ⥤ D} (x : L) (f : ι ⋙ G ⟶ F) :
  cone (diagram ι F x) :=
{ X := G.obj x,
  π :=
  { app := λ i, G.map i.hom ≫ f.app i.right,
    naturality' := begin
      rintro ⟨⟨il⟩,ir,i⟩ ⟨⟨jl⟩,jr,j⟩ ⟨⟨⟨fl⟩⟩,fr,ff⟩,
      dsimp at *,
      simp only [category.id_comp, category.assoc, eq_iff_true_of_subsingleton] at *,
      rw [ff],
      have := f.naturality,
      tidy,
    end } }

variable (ι)

@[simps]
def obj_aux (F : S ⥤ D) [∀ x, has_limits_of_shape (index ι x) D] : L ⥤ D :=
{ obj := λ x, limit (diagram ι F x),
  map := λ x y f, limit.pre (diagram _ _ _) (index_map f),
  map_id' := begin
    intro l,
    ext j,
    simp only [category.id_comp, limit.pre_π],
    congr' 1,
    rw [index_map_id],
  end,
  map_comp' := begin
    intros x y z f g,
    ext j,
    erw [limit.pre_pre, limit.pre_π, limit.pre_π],
    congr' 1,
    tidy,
  end }

end Ran

end category_theory
