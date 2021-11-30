import algebraic_geometry.Scheme
import category_theory.limits.functor_category
import algebraic_geometry.open_immersion
import algebraic_geometry.presheafed_space.gluing
import category_theory.limits.yoneda

universes v u

open category_theory category_theory.limits algebraic_geometry
namespace algebraic_geometry.Scheme

variables {C : Type u} [category.{v} C]

section

variables {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

variables [mono g]

def pullback_cone_of_left_factors : pullback_cone g (f ≫ g) :=
pullback_cone.mk f (𝟙 _) $ by simp

@[simp] lemma pullback_cone_of_left_factors_X :
  (pullback_cone_of_left_factors f g).X = X := rfl

@[simp] lemma pullback_cone_of_left_factors_fst :
  (pullback_cone_of_left_factors f g).fst = f := rfl

@[simp] lemma pullback_cone_of_left_factors_snd :
  (pullback_cone_of_left_factors f g).snd = 𝟙 _ := rfl

@[simp] lemma pullback_cone_of_left_factors_π_app_none :
  (pullback_cone_of_left_factors f g).π.app none = f ≫ g := rfl

@[simp] lemma pullback_cone_of_left_factors_π_app_left :
  (pullback_cone_of_left_factors f g).π.app walking_cospan.left = f := rfl

@[simp] lemma pullback_cone_of_left_factors_π_app_right :
  (pullback_cone_of_left_factors f g).π.app walking_cospan.right = 𝟙 _ := rfl

/-- Verify that the constructed cocone is indeed a colimit. -/
def pullback_cone_of_left_factors_is_limit :
  is_limit (pullback_cone_of_left_factors f g) :=
pullback_cone.is_limit_aux' _ (λ s, ⟨s.snd, by simpa [← cancel_mono g] using s.condition.symm⟩)

instance has_pullback_of_left_factors : has_pullback g (f ≫ g) :=
⟨⟨⟨_, pullback_cone_of_left_factors_is_limit f g⟩⟩⟩

instance pullback_fst_iso_of_left_factors : is_iso (pullback.snd : pullback g (f ≫ g) ⟶ _) :=
begin
  have : _ ≫ 𝟙 _ = pullback.snd := limit.iso_limit_cone_hom_π
    ⟨_, pullback_cone_of_left_factors_is_limit f g⟩ walking_cospan.right,
  rw ← this,
  apply_instance
end

def pullback_cone_of_right_factors : pullback_cone (f ≫ g) g :=
pullback_cone.mk (𝟙 _) f $ by simp

@[simp] lemma pullback_cone_of_right_factors_X :
  (pullback_cone_of_right_factors f g).X = X := rfl

@[simp] lemma pullback_cone_of_right_factors_fst :
  (pullback_cone_of_right_factors f g).fst = 𝟙 _ := rfl

@[simp] lemma pullback_cone_of_right_factors_snd :
  (pullback_cone_of_right_factors f g).snd = f := rfl

@[simp] lemma pullback_cone_of_right_factors_π_app_none :
  (pullback_cone_of_right_factors f g).π.app none = f ≫ g := category.id_comp _

@[simp] lemma pullback_cone_of_right_factors_π_app_left :
  (pullback_cone_of_right_factors f g).π.app walking_cospan.left = 𝟙 _ := rfl

@[simp] lemma pullback_cone_of_right_factors_π_app_right :
  (pullback_cone_of_right_factors f g).π.app walking_cospan.right = f := rfl

/-- Verify that the constructed cocone is indeed a colimit. -/
def pullback_cone_of_right_factors_is_limit :
  is_limit (pullback_cone_of_right_factors f g) :=
pullback_cone.is_limit_aux' _ (λ s, ⟨s.fst, by simpa [← cancel_mono g] using s.condition⟩)

instance has_pullback_of_right_factors : has_pullback (f ≫ g) g :=
⟨⟨⟨_, pullback_cone_of_right_factors_is_limit f g⟩⟩⟩

instance pullback_fst_iso_of_right_factors : is_iso (pullback.fst : pullback (f ≫ g) g ⟶ _) :=
begin
  have : _ ≫ 𝟙 _ = pullback.fst := limit.iso_limit_cone_hom_π
    ⟨_, pullback_cone_of_right_factors_is_limit f g⟩ walking_cospan.left,
  rw ← this,
  apply_instance
end

section

variables {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ X₂) (g₁ : X₂ ⟶ X₃) (f₂ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃)
variables (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (i₃ : X₃ ⟶ Y₃)
variables (h₁ : i₁ ≫ f₂ = f₁ ≫ i₂) (h₂ : i₂ ≫ g₂ = g₁ ≫ i₃)

def comp_square_is_limit_of_is_limit (H : is_limit (pullback_cone.mk _ _ h₂))
  (H' : is_limit (pullback_cone.mk _ _ h₁)) :
  is_limit (pullback_cone.mk _ _ (show i₁ ≫ f₂ ≫ g₂ = (f₁ ≫ g₁) ≫ i₃,
      by rw [← category.assoc, h₁, category.assoc, h₂, category.assoc])) :=
begin
  fapply pullback_cone.is_limit_aux',
  intro s,
  have : (s.fst ≫ f₂) ≫ g₂ = s.snd ≫ i₃ := by rw [← s.condition, category.assoc],
  rcases pullback_cone.is_limit.lift' H (s.fst ≫ f₂) s.snd this with ⟨l₁, hl₁, hl₁'⟩,
  rcases pullback_cone.is_limit.lift' H' s.fst l₁ hl₁.symm with ⟨l₂, hl₂, hl₂'⟩,
  use l₂,
  use hl₂,
  use show l₂ ≫ f₁ ≫ g₁ = s.snd, by { rw [← hl₁', ← hl₂', category.assoc], refl },
  intros m hm₁ hm₂,
  apply pullback_cone.is_limit.hom_ext H',
  { erw [hm₁, hl₂] },
  { apply pullback_cone.is_limit.hom_ext H,
    { erw [category.assoc, ← h₁, ← category.assoc, hm₁, ← hl₂,
      category.assoc, category.assoc, h₁], refl },
    { erw [category.assoc, hm₂, ← hl₁', ← hl₂'] } }
end

def is_limit_of_comp_square_is_limit (H : is_limit (pullback_cone.mk _ _ h₂))
  (H' : is_limit (pullback_cone.mk _ _ (show i₁ ≫ f₂ ≫ g₂ = (f₁ ≫ g₁) ≫ i₃,
      by rw [← category.assoc, h₁, category.assoc, h₂, category.assoc]))) :
  is_limit (pullback_cone.mk _ _ h₁) :=
begin
  fapply pullback_cone.is_limit_aux',
  intro s,
  have : s.fst ≫ f₂ ≫ g₂ = (s.snd ≫ g₁) ≫ i₃ :=
  by { rw [← category.assoc, s.condition, category.assoc, category.assoc, h₂] },
  rcases pullback_cone.is_limit.lift' H' s.fst (s.snd ≫ g₁) this with ⟨l₁, hl₁, hl₁'⟩,
  dsimp at *,
  use l₁,
  use hl₁,
  split,
  { apply pullback_cone.is_limit.hom_ext H,
    { erw [category.assoc, ← h₁, ← category.assoc, hl₁, s.condition], refl },
    { erw [category.assoc, hl₁'], refl } },
  intros m hm₁ hm₂,
  apply pullback_cone.is_limit.hom_ext H',
  { erw [hm₁, hl₁] },
  { erw [hl₁', ← hm₂], exact (category.assoc _ _ _).symm }
end

def comp_square_is_limit_iff_is_limit (H : is_limit (pullback_cone.mk _ _ h₂)) :
  is_limit (pullback_cone.mk _ _ (show i₁ ≫ f₂ ≫ g₂ = (f₁ ≫ g₁) ≫ i₃,
    by rw [← category.assoc, h₁, category.assoc, h₂, category.assoc])) ≃
  is_limit (pullback_cone.mk _ _ h₁) :=
{ to_fun := is_limit_of_comp_square_is_limit _ _ _ _ _ _ _ h₁ h₂ H,
  inv_fun := comp_square_is_limit_of_is_limit _ _ _ _ _ _ _ h₁ h₂ H,
  left_inv := by tidy,
  right_inv := by tidy }

end
end
section
variables {X Y Z X' : C} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ X)
  [has_pullback f g]
  [has_pullback f' (pullback.fst : pullback f g ⟶ _)] [has_pullback (f' ≫ f) g]

noncomputable
def pullback_left_pullback_fst_iso :
  pullback f' (pullback.fst : pullback f g ⟶ _) ≅ pullback (f' ≫ f) g :=
begin
  let := comp_square_is_limit_of_is_limit
    (pullback.snd : pullback f' (pullback.fst : pullback f g ⟶ _) ⟶ _) pullback.snd
    f' f pullback.fst pullback.fst g pullback.condition pullback.condition
    (pullback_is_pullback _ _) (pullback_is_pullback _ _),
  exact (this.cone_point_unique_up_to_iso (pullback_is_pullback _ _) : _)
end

@[simp, reassoc]
lemma pullback_left_pullback_fst_iso_hom_fst :
  (pullback_left_pullback_fst_iso f g f').hom ≫ pullback.fst = pullback.fst :=
is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.left

@[simp, reassoc]
lemma pullback_left_pullback_fst_iso_hom_snd :
  (pullback_left_pullback_fst_iso f g f').hom ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right

@[simp, reassoc]
lemma pullback_left_pullback_fst_iso_inv_fst :
  (pullback_left_pullback_fst_iso f g f').inv ≫ pullback.fst = pullback.fst :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ _ walking_cospan.left

@[simp, reassoc]
lemma pullback_left_pullback_fst_iso_inv_snd_snd :
  (pullback_left_pullback_fst_iso f g f').inv ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ _ walking_cospan.right

@[simp, reassoc]
lemma pullback_left_pullback_fst_iso_inv_snd_fst :
  (pullback_left_pullback_fst_iso f g f').inv ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ f' :=
begin
  rw ← pullback.condition,
  exact pullback_left_pullback_fst_iso_inv_fst_assoc _ _ _ _
end

section pullback_assoc

noncomputable theory
/-

X₁



-/

variables {X₁ X₂ X₃ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₁) (f₃ : X₂ ⟶ Y₂)
variables (f₄ : X₃ ⟶ Y₂) [has_pullback f₁ f₂] [has_pullback f₃ f₄]

include f₁ f₂ f₃ f₄

local notation `Z₁` := pullback f₁ f₂
local notation `Z₂` := pullback f₃ f₄
local notation `g₁` := (pullback.fst : Z₁ ⟶ X₁)
local notation `g₂` := (pullback.snd : Z₁ ⟶ X₂)
local notation `g₃` := (pullback.fst : Z₂ ⟶ X₂)
local notation `g₄` := (pullback.snd : Z₂ ⟶ X₃)
local notation `W`  := pullback (g₂ ≫ f₃) f₄
local notation `W'` := pullback f₁ (g₃ ≫ f₂)
local notation `l₁` := (pullback.fst : W ⟶ Z₁)
local notation `l₂` := (pullback.lift (pullback.fst ≫ g₂) pullback.snd
    ((category.assoc _ _ _).trans pullback.condition) : W ⟶ Z₂)
local notation `l₁'`:= (pullback.lift pullback.fst (pullback.snd ≫ g₃)
    (pullback.condition.trans (category.assoc _ _ _).symm) : W' ⟶ Z₁)
local notation `l₂'`:= (pullback.snd : W' ⟶ Z₂)

/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
def pullback_pullback_left_is_pullback [has_pullback (g₂ ≫ f₃) f₄] :
is_limit (pullback_cone.mk l₁ l₂ (show l₁ ≫ g₂ = l₂ ≫ g₃, from (pullback.lift_fst _ _ _).symm)) :=
begin
  apply is_limit_of_comp_square_is_limit,
  exact pullback_is_pullback f₃ f₄,
  convert pullback_is_pullback (g₂ ≫ f₃) f₄,
  rw pullback.lift_snd
end

/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
def pullback_assoc_is_pullback [has_pullback (g₂ ≫ f₃) f₄] :
is_limit (pullback_cone.mk (l₁ ≫ g₁) l₂ (show (l₁ ≫ g₁) ≫ f₁ = l₂ ≫ (g₃ ≫ f₂),
  by rw [pullback.lift_fst_assoc, category.assoc, category.assoc, pullback.condition])) :=
begin
  apply pullback_cone.flip_is_limit,
  apply comp_square_is_limit_of_is_limit,
  apply pullback_cone.flip_is_limit,
  exact pullback_is_pullback f₁ f₂,
  apply pullback_cone.flip_is_limit,
  apply pullback_pullback_left_is_pullback,
  exact pullback.lift_fst _ _ _,
  exact pullback.condition.symm
end

lemma has_pullback_assoc [has_pullback (g₂ ≫ f₃) f₄] :
has_pullback f₁ (g₃ ≫ f₂) :=
⟨⟨⟨_, pullback_assoc_is_pullback f₁ f₂ f₃ f₄⟩⟩⟩

/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
def pullback_pullback_right_is_pullback [has_pullback f₁ (g₃ ≫ f₂)] :
is_limit (pullback_cone.mk l₁' l₂' (show l₁' ≫ g₂ = l₂' ≫ g₃, from pullback.lift_snd _ _ _)) :=
begin
  apply pullback_cone.flip_is_limit,
  apply is_limit_of_comp_square_is_limit,
  apply pullback_cone.flip_is_limit,
  exact pullback_is_pullback f₁ f₂,
  apply pullback_cone.flip_is_limit,
  convert pullback_is_pullback f₁ (g₃ ≫ f₂),
  rw pullback.lift_fst,
  exact pullback.condition.symm
end

/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[Y₂] X₃`. -/
def pullback_assoc_symm_is_pullback [has_pullback f₁ (g₃ ≫ f₂)] :
is_limit (pullback_cone.mk l₁' (l₂' ≫ g₄) (show l₁' ≫ (g₂ ≫ f₃) = (l₂' ≫ g₄) ≫ f₄,
  by rw [pullback.lift_snd_assoc, category.assoc, category.assoc, pullback.condition])) :=
begin
  apply comp_square_is_limit_of_is_limit,
  exact pullback_is_pullback f₃ f₄,
  apply pullback_pullback_right_is_pullback
end

lemma has_pullback_assoc_symm [has_pullback f₁ (g₃ ≫ f₂)] :
has_pullback (g₂ ≫ f₃) f₄ :=
⟨⟨⟨_, pullback_assoc_symm_is_pullback f₁ f₂ f₃ f₄⟩⟩⟩

variables [has_pullback (g₂ ≫ f₃) f₄] [has_pullback f₁ (g₃ ≫ f₂)]

noncomputable
def pullback_assoc :
  pullback (pullback.snd ≫ f₃ : pullback f₁ f₂ ⟶ _) f₄ ≅
    pullback f₁ (pullback.fst ≫ f₂ : pullback f₃ f₄ ⟶ _) :=
(pullback_pullback_left_is_pullback f₁ f₂ f₃ f₄).cone_point_unique_up_to_iso
(pullback_pullback_right_is_pullback f₁ f₂ f₃ f₄)

@[simp, reassoc]
lemma pullback_assoc_inv_fst_fst :
  (pullback_assoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.fst = pullback.fst :=
begin
  transitivity l₁' ≫ pullback.fst,
  rw ← category.assoc,
  congr' 1,
  exact is_limit.cone_point_unique_up_to_iso_inv_comp _ _ walking_cospan.left,
  exact pullback.lift_fst _ _ _,
end

@[simp, reassoc]
lemma pullback_assoc_hom_fst :
  (pullback_assoc f₁ f₂ f₃ f₄).hom ≫ pullback.fst = pullback.fst ≫ pullback.fst :=
by rw [← iso.eq_inv_comp, pullback_assoc_inv_fst_fst]

@[simp, reassoc]
lemma pullback_assoc_hom_snd_fst :
  (pullback_assoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
begin
  transitivity l₂ ≫ pullback.fst,
  rw ← category.assoc,
  congr' 1,
  exact is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right,
  exact pullback.lift_fst _ _ _,
end

@[simp, reassoc]
lemma pullback_assoc_hom_snd_snd :
  (pullback_assoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd ≫ pullback.snd = pullback.snd :=
begin
  transitivity l₂ ≫ pullback.snd,
  rw ← category.assoc,
  congr' 1,
  exact is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right,
  exact pullback.lift_snd _ _ _,
end

@[simp, reassoc]
lemma pullback_assoc_inv_fst_snd :
  (pullback_assoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.fst :=
by rw [iso.inv_comp_eq, pullback_assoc_hom_snd_fst]

@[simp, reassoc]
lemma pullback_assoc_inv_snd :
  (pullback_assoc f₁ f₂ f₃ f₄).inv ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by rw [iso.inv_comp_eq, pullback_assoc_hom_snd_snd]

end pullback_assoc
-- instance pullback.map_is_iso {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S) [has_pullback f₁ f₂]
--   (g₁ : Y ⟶ T) (g₂ : Z ⟶ T) [has_pullback g₁ g₂] (i₁ : W ⟶ Y) (i₂ : X ⟶ Z) (i₃ : S ⟶ T)
--   (eq₁ : f₁ ≫ i₃ = i₁ ≫ g₁) (eq₂ : f₂ ≫ i₃ = i₂ ≫ g₂) [is_iso i₁] [is_iso i₂] [is_iso i₃] :
--   is_iso (pullback.map f₁ f₂ g₁ g₂ i₁ i₂ i₃ eq₁ eq₂) :=
-- begin
--   constructor,
--   fconstructor,
--   refine pullback.map _ _ _ _ (inv i₁) (inv i₂) (inv i₃) _ _,
--   { rw [is_iso.comp_inv_eq, category.assoc, eq₁, is_iso.inv_hom_id_assoc] },
--   { rw [is_iso.comp_inv_eq, category.assoc, eq₂, is_iso.inv_hom_id_assoc] },
--   tidy
-- end

-- instance lem : has_pullbacks (Scheme.{u}ᵒᵖ ⥤ Type u) := sorry
-- instance coyoneda_functor_preserves_limits :

-- class open_subfunctor {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G) :=
-- (subfunctor : mono f)
-- (res : ∀ {S : Scheme.{u}} (g : yoneda.obj S ⟶ G), functor.representable (pullback f g))
-- (res_open : ∀ {S : Scheme.{u}} (g : yoneda.obj S ⟶ G),
--   is_open_immersion (yoneda.preimage (functor.repr_f (pullback f g) ≫ pullback.snd)).val)

-- attribute[instance] open_subfunctor.subfunctor open_subfunctor.res open_subfunctor.res_open

-- noncomputable
-- def res_repr_X {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G) [open_subfunctor f]
--   {S : Scheme.{u}} (g : yoneda.obj S ⟶ G) : Scheme := functor.repr_X (pullback f g)

-- noncomputable
-- def res_repr_f {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G) [open_subfunctor f]
--   {S : Scheme.{u}} (g : yoneda.obj S ⟶ G) : res_repr_X f g ⟶ S :=
-- yoneda.preimage (functor.repr_f (pullback f g) ≫ pullback.snd)

-- instance res_repr_f_is_open_immersion {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G) [open_subfunctor f]
--   {S : Scheme.{u}} (g : yoneda.obj S ⟶ G) : is_open_immersion (res_repr_f f g) :=
-- open_subfunctor.res_open g

-- @[simp]
-- lemma yoneda_map_res_repr_f {F G : Scheme.{u}ᵒᵖ ⥤ Type u} (f : F ⟶ G) [open_subfunctor f]
--   {S : Scheme.{u}} (g : yoneda.obj S ⟶ G) : yoneda.map (res_repr_f f g) =
--     (pullback f g).repr_f ≫ pullback.snd := functor.image_preimage _ _


-- structure open_subfunctor_cover (F : Scheme.{u}ᵒᵖ ⥤ Type u) :=
-- (ι : Type u)
-- (F' : ι → Scheme.{u}ᵒᵖ ⥤ Type u)
-- (f : Π (i : ι), F' i ⟶ F)
-- (f_open_subfunctor : ∀ i, open_subfunctor (f i))
-- (covers : ∀ (T : Scheme.{u}) (g : yoneda.obj T ⟶ F) (x : T.carrier),
--   ∃ (i : ι), (x ∈ set.range (res_repr_f (f i) g).1.base))

-- attribute[instance] open_subfunctor_cover.f_open_subfunctor


-- variables {F : Scheme.{u}ᵒᵖ ⥤ Type u}
--   (D : open_subfunctor_cover F) [H : ∀ i : D.ι, functor.representable (D.F' i)]

-- include H

-- noncomputable
-- def open_subfunctor_cover.functor_t (i j : D.ι) : pullback (D.f j) ((D.F' i).repr_f ≫ D.f i) ⟶
--   pullback (D.f i) ((D.F' j).repr_f ≫ D.f j) :=
-- pullback.map _ _ _ _ (𝟙 _) (D.F' i).repr_f (𝟙 _) (by simp) (by simp) ≫
--   (pullback_symmetry _ _).hom ≫
--   inv (pullback.map _ _ _ _ (𝟙 _) (D.F' j).repr_f (𝟙 _) (by simp) (by simp))

-- -- set_option pp.universes true

-- noncomputable
-- lemma open_subfunctor_cover.glue_data : Scheme.glue_data.{u} :=
-- { ι := D.ι,
--   U := λ i, functor.repr_X (D.F' i),
--   V := λ ⟨i, j⟩, res_repr_X (D.f j) ((D.F' i).repr_f ≫ D.f i),
--   f := λ i j, res_repr_f _ _,
--   -- f_id := λ i, by { apply is_iso_of_reflects_iso _ yoneda,
--   --   rw yoneda_map_res_repr_f, apply_instance },
--   f_open := λ i, by {   },
--   t := λ i j, yoneda.preimage (functor.repr_f _ ≫ D.functor_t i j ≫ inv (functor.repr_f _)),
--   -- t_id := λ i, by simp [open_subfunctor_cover.functor_t],
--   t' := λ i j k, yoneda.preimage (by {
--     have : yoneda.obj (pullback (res_repr_f (D.f j) ((D.F' i).repr_f ≫ D.f i)) (res_repr_f (D.f k) ((D.F' i).repr_f ≫ D.f i)))
--     ⟶ pullback (yoneda.map $ res_repr_f (D.f j) ((D.F' i).repr_f ≫ D.f i)) (yoneda)
--     let := @preserves_pullback.iso.{u+1 u+1} (Scheme.{u}ᵒᵖ ⥤ Type u) _,
--     -- have := (preserves_pullback.iso.{u u+1 u+1} yoneda.{u u+1} (res_repr_f.{u} (D.f j) ((D.F' i).repr_f ≫ D.f i))
--     --   (res_repr_f.{u} (D.f k) ((D.F' i).repr_f ≫ D.f i))).hom, })
--   })

-- }

-- section end

-- lemma open_subfunctor_cover.representable (F : Scheme.{u}ᵒᵖ ⥤ Type u)
--   (D : open_subfunctor_cover F) (H : ∀ i : D.ι, functor.representable (D.F' i)) :
--     functor.representable F :=
-- begin




end

variables {X Y Z : Scheme.{u}} (c : Π (x : X.carrier), over X) (f : X ⟶ Z) (g : Y ⟶ Z)
variables (hc : ∀ x, x ∈ set.range (c x).hom.1.base) [∀ x, has_pullback ((c x).hom ≫ f) g]
variables [∀ x, is_open_immersion (c x).hom]

/-- (Xᵢ ×[Z] Y) ×[X] Xⱼ -/
def V (x y : X.carrier) : Scheme :=
pullback ((pullback.fst : pullback ((c x).hom ≫ f) g ⟶ _) ≫ (c x).hom) (c y).hom

def t (x y : X.carrier) : V c f g x y ⟶ V c f g y x :=
begin
  haveI : has_pullback (pullback.snd ≫ (c x).hom ≫ f) g :=
    has_pullback_assoc_symm (c y).hom (c x).hom ((c x).hom ≫ f) g,
  haveI : has_pullback (pullback.snd ≫ (c y).hom ≫ f) g :=
    has_pullback_assoc_symm (c x).hom (c y).hom ((c y).hom ≫ f) g,
  refine (pullback_symmetry _ _).hom ≫ _,
  refine (pullback_assoc _ _ _ _).inv ≫ _,
  change pullback _ _ ⟶ pullback _ _,
  refine _ ≫ (pullback_symmetry _ _).hom,
  refine _ ≫ (pullback_assoc _ _ _ _).hom,
  refine pullback.map _ _ _ _ (pullback_symmetry _ _).hom (𝟙 _) (𝟙 _) _ _,
  rw [pullback_symmetry_hom_comp_snd_assoc, pullback.condition_assoc, category.comp_id],
  rw [category.comp_id, category.id_comp]
end

@[simp, reassoc]
lemma t_fst_fst (x y : X.carrier) : t c f g x y ≫ pullback.fst ≫ pullback.fst = pullback.snd :=
by { delta t, simp }

@[simp, reassoc]
lemma t_fst_snd (x y : X.carrier) :
  t c f g x y ≫ pullback.fst ≫ pullback.snd = pullback.fst ≫ pullback.snd :=
by { delta t, simp }

@[simp, reassoc]
lemma t_snd (x y : X.carrier) :
  t c f g x y ≫ pullback.snd = pullback.fst ≫ pullback.fst :=
by { delta t, simp }

lemma t_id (x : X.carrier) : t c f g x x = 𝟙 _ :=
begin
  apply pullback.hom_ext; rw category.id_comp,
  apply pullback.hom_ext,
  { rw ← cancel_mono (c x).hom,
    simp [pullback.condition] },
  { simp },
  { rw ← cancel_mono (c x).hom,
    simp [pullback.condition] }
end

abbreviation fV (x y : X.carrier) : V c f g x y ⟶ pullback ((c x).hom ≫ f) g := pullback.fst

/-- (Xᵢ ×[Z] Y) ×[X] Xⱼ ×[Xᵢ ×[Z] Y] (Xᵢ ×[Z] Y) ×[X] Xₖ  -/
def t' (x y z : X.carrier) :
  pullback (fV c f g x y) (fV c f g x z) ⟶ pullback (fV c f g y z) (fV c f g y x) :=
begin
  refine (pullback_left_pullback_fst_iso _ _ _).hom ≫ _,
  refine _ ≫ (pullback_symmetry _ _).hom,
  refine _ ≫ (pullback_left_pullback_fst_iso _ _ _).inv,
  refine pullback.map _ _ _ _ (t c f g x y) (𝟙 _) (𝟙 _) _ _,
  { simp [← pullback.condition] },
  { simp }
end

section end

@[simp, reassoc]
lemma t'_fst_fst_fst (x y z : X.carrier) :
  t' c f g x y z ≫ pullback.fst ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_fst_fst_snd (x y z : X.carrier) :
  t' c f g x y z ≫ pullback.fst ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_fst_snd (x y z : X.carrier) :
  t' c f g x y z ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_fst_fst (x y z : X.carrier) :
  t' c f g x y z ≫ pullback.snd ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_fst_snd (x y z : X.carrier) :
  t' c f g x y z ≫ pullback.snd ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_snd (x y z : X.carrier) :
  t' c f g x y z ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.fst :=
by { delta t', simp, }

lemma cocycle_fst_fst_fst (x y z : X.carrier) :
  t' c f g x y z ≫ t' c f g y z x ≫ t' c f g z x y ≫ pullback.fst ≫ pullback.fst ≫
  pullback.fst = pullback.fst ≫ pullback.fst ≫ pullback.fst :=
by simp

lemma cocycle_fst_fst_snd (x y z : X.carrier) :
  t' c f g x y z ≫ t' c f g y z x ≫ t' c f g z x y ≫ pullback.fst ≫ pullback.fst ≫
  pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by simp

lemma cocycle_fst_snd (x y z : X.carrier) :
  t' c f g x y z ≫ t' c f g y z x ≫ t' c f g z x y ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.snd :=
by simp

lemma cocycle_snd_fst_fst (x y z : X.carrier) :
  t' c f g x y z ≫ t' c f g y z x ≫ t' c f g z x y ≫ pullback.snd ≫ pullback.fst ≫
  pullback.fst = pullback.snd ≫ pullback.fst ≫ pullback.fst :=
by { rw ← cancel_mono (c x).hom, simp [pullback.condition_assoc, pullback.condition] }

lemma cocycle_snd_fst_snd (x y z : X.carrier) :
  t' c f g x y z ≫ t' c f g y z x ≫ t' c f g z x y ≫ pullback.snd ≫ pullback.fst ≫
  pullback.snd = pullback.snd ≫ pullback.fst ≫ pullback.snd :=
by { simp [pullback.condition_assoc, pullback.condition] }

lemma cocycle_snd_snd (x y z : X.carrier) :
  t' c f g x y z ≫ t' c f g y z x ≫ t' c f g z x y ≫ pullback.snd ≫ pullback.snd =
    pullback.snd ≫ pullback.snd :=
by simp

lemma cocycle (x y z : X.carrier) :
  t' c f g x y z ≫ t' c f g y z x ≫ t' c f g z x y = 𝟙 _ :=
begin
  apply pullback.hom_ext; rw category.id_comp,
  apply pullback.hom_ext,
  apply pullback.hom_ext,
  simp_rw category.assoc,
  exact cocycle_fst_fst_fst c f g x y z,
  simp_rw category.assoc,
  exact cocycle_fst_fst_snd c f g x y z,
  simp_rw category.assoc,
  exact cocycle_fst_snd c f g x y z,
  apply pullback.hom_ext,
  apply pullback.hom_ext,
  simp_rw category.assoc,
  exact cocycle_snd_fst_fst c f g x y z,
  simp_rw category.assoc,
  exact cocycle_snd_fst_snd c f g x y z,
  simp_rw category.assoc,
  exact cocycle_snd_snd c f g x y z
end

def gluing : Scheme.glue_data.{u} :=
{ ι := X.carrier,
  U := λ x, pullback ((c x).hom ≫ f) g,
  V := λ ⟨x, y⟩, V c f g x y, -- p⁻¹(Xᵢ ∩ Xⱼ)
  f := λ x y, pullback.fst,
  f_id := λ x, infer_instance,
  f_open := infer_instance,
  t := λ x y, t c f g x y,
  t_id := λ x, t_id c f g x,
  t' := λ x y z, t' c f g x y z,
  t_fac := λ x y z, begin
    apply pullback.hom_ext,
    apply pullback.hom_ext,
    all_goals { simp }
  end,
  cocycle := λ x y z, cocycle c f g x y z }

section end

example := (gluing c f g).glued

def p1 : (gluing c f g).glued ⟶ X :=
begin
  fapply multicoequalizer.desc,
  exact λ x, pullback.fst ≫ (c x).hom,
  rintro ⟨x,y⟩,
  change pullback.fst ≫ _ ≫ (c x).hom = (_ ≫ _) ≫ _ ≫ (c y).hom,
  rw pullback.condition,
  rw ← category.assoc,
  congr' 1,
  rw category.assoc,
  exact (t_fst_fst _ _ _ _ _).symm
end

def p2 : (gluing c f g).glued ⟶ Y :=
begin
  fapply multicoequalizer.desc,
  exact λ x, pullback.snd,
  rintro ⟨x,y⟩,
  change pullback.fst ≫ _ = (_ ≫ _) ≫ _,
  rw category.assoc,
  exact (t_fst_snd _ _ _ _ _).symm
end

section end

lemma p_comm : p1 c f g ≫ f = p2 c f g ≫ g :=
begin
  apply multicoequalizer.hom_ext,
  intro x,
  erw [multicoequalizer.π_desc_assoc, multicoequalizer.π_desc_assoc],
  rw [category.assoc, pullback.condition]
end

section end

def glued_cover_t' (x y z : X.carrier) :
  pullback (pullback.fst : pullback (c x).hom (c y).hom ⟶ _)
    (pullback.fst : pullback (c x).hom (c z).hom ⟶ _) ⟶
  pullback (pullback.fst : pullback (c y).hom (c z).hom ⟶ _)
    (pullback.fst : pullback (c y).hom (c x).hom ⟶ _) :=
begin
  refine (pullback_left_pullback_fst_iso _ _ _).hom ≫ _,
  refine _ ≫ (pullback_symmetry _ _).hom,
  refine _ ≫ (pullback_left_pullback_fst_iso _ _ _).inv,
  refine pullback.map _ _ _ _ (pullback_symmetry _ _).hom (𝟙 _) (𝟙 _) _ _,
  { simp [pullback.condition] },
  { simp }
end

@[simp, reassoc]
lemma glued_cover_t'_fst_fst (x y z : X.carrier) :
  glued_cover_t' c x y z ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta glued_cover_t', simp }

@[simp, reassoc]
lemma glued_cover_t'_fst_snd (x y z : X.carrier) :
  glued_cover_t' c x y z ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by { delta glued_cover_t', simp }

@[simp, reassoc]
lemma glued_cover_t'_snd_fst (x y z : X.carrier) :
  glued_cover_t' c x y z ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta glued_cover_t', simp }

@[simp, reassoc]
lemma glued_cover_t'_snd_snd (x y z : X.carrier) :
  glued_cover_t' c x y z ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst :=
by { delta glued_cover_t', simp }

lemma glued_cover_cocycle_fst (x y z : X.carrier) :
  glued_cover_t' c x y z ≫ glued_cover_t' c y z x ≫ glued_cover_t' c z x y ≫ pullback.fst =
    pullback.fst :=
by apply pullback.hom_ext; simp

lemma glued_cover_cocycle_snd (x y z : X.carrier) :
  glued_cover_t' c x y z ≫ glued_cover_t' c y z x ≫ glued_cover_t' c z x y ≫ pullback.snd =
    pullback.snd :=
by apply pullback.hom_ext; simp [pullback.condition]

lemma glued_cover_cocycle (x y z : X.carrier) :
  glued_cover_t' c x y z ≫ glued_cover_t' c y z x ≫ glued_cover_t' c z x y = 𝟙 _ :=
begin
  apply pullback.hom_ext; simp_rw [category.id_comp, category.assoc],
  apply glued_cover_cocycle_fst,
  apply glued_cover_cocycle_snd,
end

def glued_cover : Scheme.glue_data.{u} :=
{ ι := X.carrier,
  U := λ x, (c x).left,
  V := λ ⟨x, y⟩, pullback (c x).hom (c y).hom,
  f := λ x y, pullback.fst,
  f_id := λ x, infer_instance,
  t := λ x y, (pullback_symmetry _ _).hom,
  t_id := λ x, by simpa,
  t' := λ x y z, glued_cover_t' c x y z,
  t_fac := λ x y z, by apply pullback.hom_ext; simp,
  cocycle := λ x y z, glued_cover_cocycle c x y z,
  f_open := λ x, infer_instance }

section end

def to_glued_cover : (glued_cover c).glued ⟶ X :=
begin
  fapply multicoequalizer.desc,
  exact λ x, (c x).hom,
  rintro ⟨x, y⟩,
  change pullback.fst ≫ _ = ((pullback_symmetry _ _).hom ≫ pullback.fst) ≫ _,
  simpa using pullback.condition
end

include hc

lemma to_glued_cover_bijective : is_iso (to_glued_cover c).1.base :=
begin
  let e : (glued_cover c).glued.carrier ≅
    (glued_cover c).to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
      .to_PresheafedSpace_glue_data.to_Top_glue_data.to_glue_data.glued,
  { refine (PresheafedSpace.forget _).map_iso _ ≪≫
      glue_data.glued_iso _ (PresheafedSpace.forget _),
    refine SheafedSpace.forget_to_PresheafedSpace.map_iso _ ≪≫
    SheafedSpace.glue_data.iso_PresheafedSpace _,
    refine LocallyRingedSpace.forget_to_SheafedSpace.map_iso _ ≪≫
    LocallyRingedSpace.glue_data.iso_SheafedSpace _,
    exact Scheme.glue_data.iso_LocallyRingedSpace _ },
  rw ← e.hom_inv_id_assoc (to_glued_cover c).1.base,
  apply_with is_iso.comp_is_iso { instances := ff },
--   simp only [functor.map_iso_inv, iso.trans_inv, functor.map_iso_trans, category.assoc,
--     PresheafedSpace.forget_map,
--  subtype.val_eq_coe],
end

def iso_glued_cover := @@as_iso _ (to_glued_cover c) (is_iso_glued_cover c hc)

variable (s : pullback_cone f g)

def glued_lift : s.X ⟶ (glued_cover c).glued :=
begin

end

end algebraic_geometry.Scheme
