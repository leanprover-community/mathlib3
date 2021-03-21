import category_theory.punit
import category_theory.comma
import category_theory.limits.functor_category

noncomputable theory

namespace category_theory

open limits

universes v u₁ u₂ u₃

variables {S : Type v} {L : Type u₂} {D : Type u₃}
variables [category.{v} S] [category.{v} L] [category.{v} D]
variables (ι : S ⥤ L)

namespace Ran

local attribute [simp] comma.snd comma.map_left


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

@[simp]
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

@[simps]
def equiv [∀ x, has_limits_of_shape (index ι x) D] (F : S ⥤ D) (G : L ⥤ D) :
  (G ⟶ obj_aux ι F) ≃ (ι ⋙ G ⟶ F) :=
{ to_fun := λ f,
  { app := λ x, f.app _ ≫ limit.π (diagram ι F (ι.obj x)) (index.mk (𝟙 _)),
  naturality' := begin
    intros x y ff,
    simp only [functor.comp_map, nat_trans.naturality_assoc, obj_aux_map, category.assoc],
    congr' 1,
    erw [limit.pre_π, limit.w (diagram ι F _) (index.mk_hom (𝟙 _) ff)],
    congr,
    tidy,
  end },
  inv_fun := λ f,
  { app := λ x, limit.lift (diagram ι F x) (cone _ f),
    naturality' := begin
      intros x y ff,
      ext j,
      erw [limit.lift_pre, limit.lift_π, category.assoc, limit.lift_π (cone _ f) j],
      delta cone index_map,
      tidy,
    end },
  left_inv := begin
    intro x,
    ext k j,
    dsimp only [cone, diagram],
    rw limit.lift_π,
    simp only [nat_trans.naturality_assoc, obj_aux_map],
    congr' 1,
    erw limit.pre_π,
    congr,
    cases j,
    tidy,
  end,
  right_inv := by tidy }

@[simps]
def equiv' [∀ x, has_limits_of_shape (index ι x) D] (F : S ⥤ D) (G : L ⥤ D) :
  (G ⟶ obj_aux ι F) ≃ (((whiskering_left _ _ _).obj ι).obj G ⟶ F) := equiv _ _ _

end Ran

def Ran [∀ X, has_limits_of_shape (Ran.index ι X) D] : (S ⥤ D) ⥤ L ⥤ D :=
adjunction.right_adjoint_of_equiv (λ F G, (Ran.equiv' ι G F).symm)
begin
  intros x y z f g,
  ext _ ⟨jl, jr, j⟩,
  dsimp [Ran.equiv'],
  tidy,
end

namespace Ran

variable (D)
def adjunction [∀ X, has_limits_of_shape (Ran.index ι X) D] :
  (whiskering_left _ _ D).obj ι ⊣ Ran ι :=
adjunction.adjunction_of_equiv_right _ _

end Ran

end category_theory
