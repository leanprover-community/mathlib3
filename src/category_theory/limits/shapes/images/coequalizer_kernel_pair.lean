import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.regular_mono

open category_theory.limits

namespace category_theory

universes v u -- declare the `v`s first; see `category_theory.category` for an explanation

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

variables [has_pullbacks.{v} C] [has_coequalizers.{v} C]

variables {X Y : C} (f : X ⟶ Y)

def coequalizer_kernel_pair : C :=
coequalizer (pullback.fst : pullback f f ⟶ X) (pullback.snd : pullback f f ⟶ X)

namespace coequalizer_kernel_pair

def π : X ⟶ coequalizer_kernel_pair f := coequalizer.π _ _
def ι : coequalizer_kernel_pair f ⟶ Y := coequalizer.desc f (pullback.condition)

instance : regular_epi (π f) :=
by { dsimp [π], apply_instance, }

-- We can't prove yet that `ι f` is a mono.
-- For this we need that the ambient category is regular.
-- There's a detailed proof at Proposition 4.2, p.29 of
-- http://www.staff.science.uu.nl/~ooste110/syllabi/catsmoeder.pdf

@[simp]
lemma fac : π f ≫ ι f = f :=
by { dsimp [π, ι], simp only [cofork.of_π_app_one, colimit.ι_desc] }

section
variables {f} {f' : X ⟶ Y}

def map_eq (h : f = f') : coequalizer_kernel_pair f ⟶ coequalizer_kernel_pair f' :=
begin
-- TODO golf
  apply coequalizer.desc,
  swap,
  apply π f',
  dsimp [π],
  convert coequalizer.condition _ _; exact h.symm,
end

variables {f'' : X ⟶ Y}

@[simp]
lemma map_eq_refl : map_eq (rfl) = 𝟙 (coequalizer_kernel_pair f) :=
begin
  dsimp [map_eq, π],
  ext,
  erw [colimit.ι_desc, cofork.of_π_app_one, category.comp_id],
end

@[simp, reassoc]
lemma map_eq_trans (h : f = f') (h' : f' = f'') : map_eq h ≫ map_eq h' = map_eq (h.trans h') :=
begin
  dsimp [map_eq, π],
  ext,
  simp,
end
end


section
-- In this section we assume that `ι f` is always a mono, and deduce the mapping properties.
variables [Π {X Y : C} (f : X ⟶ Y), mono (ι f)]

variables {Z : C} (g : Y ⟶ Z)
def pre_comp : coequalizer_kernel_pair (f ≫ g) ⟶ coequalizer_kernel_pair g :=
begin
  apply coequalizer.desc (f ≫ π g),
  apply @mono.right_cancellation _ _ _ _ (ι g),
  simp only [fac, category.assoc],
  apply pullback.condition,
end

section
variables {f g} {g' : Y ⟶ Z} (w : g = g') (w' : f ≫ g = f ≫ g')

lemma pre_comp_map_eq : pre_comp f g ≫ map_eq w = map_eq w' ≫ pre_comp f g' :=
begin
  dsimp [pre_comp, map_eq, π],
  ext,
  simp only [cofork.of_π_app_one, colimit.ι_desc, colimit.ι_desc_assoc, category.assoc],
end
end

section
variables {W : C} (h : Z ⟶ W)
@[simp]
lemma pre_comp_pre_comp : pre_comp f (g ≫ h) ≫ pre_comp g h = map_eq (by simp) ≫ pre_comp (f ≫ g) h :=
begin
  dsimp [pre_comp, map_eq, π],
  ext,
  simp only [cofork.of_π_app_one, colimit.ι_desc, colimit.ι_desc_assoc, category.assoc],
end
end

def post_comp : coequalizer_kernel_pair f ⟶ coequalizer_kernel_pair (f ≫ g) :=
begin
  -- TODO golf
  apply coequalizer.desc,
  swap,
  exact π (f ≫ g),
  apply @mono.right_cancellation _ _ _ _ (ι (f ≫ g)),
  simp only [fac, category.assoc],
  apply pullback.condition_assoc,
end

section
variables {f g} {f' : X ⟶ Y} (w : f = f') (w' : f ≫ g = f' ≫ g)

lemma map_eq_post_comp : map_eq w ≫ post_comp f' g = post_comp f g ≫ map_eq w' :=
begin
  dsimp [post_comp, map_eq, π],
  ext,
  simp only [cofork.of_π_app_one, colimit.ι_desc, colimit.ι_desc_assoc],
end

end

section
variables {W : C} (e : W ⟶ X)
@[simp]
lemma post_comp_post_comp :
  post_comp e f ≫ post_comp (e ≫ f) g = post_comp e (f ≫ g) ≫ map_eq (by simp) :=
begin
  dsimp [post_comp, map_eq, π],
  ext,
  simp only [cofork.of_π_app_one, colimit.ι_desc, colimit.ι_desc_assoc, category.assoc],
end

lemma pre_comp_post_comp :
  pre_comp e f ≫ post_comp f g = post_comp (e ≫ f) g ≫ map_eq (by simp) ≫ pre_comp e (f ≫ g) :=
begin
  dsimp [pre_comp, post_comp, map_eq, π],
  ext,
  simp only [cofork.of_π_app_one, colimit.ι_desc, colimit.ι_desc_assoc, category.assoc],
end

end

variables {f} {X' Y' : C} {f' : X' ⟶ Y'} {dX : X ⟶ X'} {dY : Y ⟶ Y'}

def map (w : f ≫ dY = dX ≫ f') : coequalizer_kernel_pair f ⟶ coequalizer_kernel_pair f' :=
post_comp f dY ≫ map_eq w ≫ pre_comp dX f'

lemma map_id (w : f ≫ 𝟙 Y = 𝟙 X ≫ f) : map w = 𝟙 (coequalizer_kernel_pair f) :=
begin
  dsimp [map, pre_comp, post_comp, map_eq, π],
  ext,
  simp only [colimit.ι_desc, colimit.ι_desc_assoc, category.id_comp, cofork.of_π_app_one],
  erw category.comp_id,
end

variables {X'' Y'' : C} (f'' : X'' ⟶ Y'') (dX' : X' ⟶ X'') (dY' : Y' ⟶ Y'')

lemma map_comp (w : f ≫ dY = dX ≫ f') (w' : f' ≫ dY' = dX' ≫ f'') (w'' : f ≫ (dY ≫ dY') = (dX ≫ dX') ≫ f'') :
  map w ≫ map w' = map w'' :=
begin
  dsimp [map],
  conv { to_lhs, slice 3 4, rw pre_comp_post_comp, },
  conv { to_lhs, slice 2 3, rw map_eq_post_comp w (w =≫ dY'), },
  conv { to_lhs, slice 1 2, rw post_comp_post_comp, },
  conv { to_lhs, slice 5 6,
    -- FIXME slice isn't working properly here
    rw ← category.assoc,
    rw pre_comp_map_eq w' (dX ≫= w'),
   },
   conv { to_lhs, slice 5 6, rw pre_comp_pre_comp, },
   simp only [map_eq_trans_assoc],
end

end

end coequalizer_kernel_pair

end category_theory
