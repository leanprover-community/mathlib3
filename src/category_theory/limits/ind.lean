import category_theory.fintype
import category_theory.limits.flat
import data.finset.lattice

universe u

namespace category_theory
open limits

-- Every type is a filtered colimit of finite sets: namely the (directed) union of its finite
-- subsets, which is a directed union

@[simps]
def finite_subsets_diagram (X : Type u) : finset X ⥤ Type u :=
{ obj := λ x, ((x : set X) : Type u),
  map := λ x y f t, ⟨_, le_of_hom f t.2⟩ }

@[simps]
def finite_subsets_cocone (X : Type u) : cocone (finite_subsets_diagram X) :=
{ X := X, ι := { app := λ Y y, y.1 } }

def finite_subsets_colimit (X : Type u) : is_colimit (finite_subsets_cocone X) :=
{ desc := λ s x, s.ι.app {x} ⟨x, by simp⟩,
  fac' := λ s j,
  begin
    ext ⟨x, hx⟩,
    dsimp,
    have x_le_j : {x} ≤ j,
    { simpa using hx },
    rw ← s.w (hom_of_le x_le_j),

  end,
  uniq' := sorry

}

instance {X : Type u} [decidable_eq X] : is_filtered (finset X) := {}.

def type_to_ind_fintype : Type u ⥤ ind.{u} Fintype.{u} :=
{ obj := λ X, ⟨_, _⟩,

}

-- def ind_fintype_to_type : ind.{u} Fintype.{u} ⥤ Type u :=
-- ind_extension _

def ind_fintype_equiv_type : ind Fintype.{u} ≌ Type u :=
begin

end

end category_theory
