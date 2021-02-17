/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.opposites
-- import category_theory.limits.lattice
-- import category_theory.limits.shapes.finite_products
-- import category_theory.limits.shapes.terminal
import category_theory.full_subcategory
-- import category_theory.limits.shapes.regular_mono
import category_theory.closed.cartesian
import category_theory.limits.shapes.pullbacks
-- import category_theory.limits.over
import category_theory.currying
-- import category_theory.adjunction.fully_faithful
import category_theory.skeletal
import category_theory.limits.shapes.images
import category_theory.monad.adjunction

universes v₁ v₂ u₁ u₂

noncomputable theory
namespace category_theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v₁} C] {X Y Z : C}
variables {D : Type u₂} [category.{v₂} D]

/--
The category of monomorphisms into `X` as a full subcategory of the over category.
This isn't skeletal, so it's not a partial order.

Later we define `subobject X` as the quotient of this by isomorphisms.
-/
@[derive [category, λ t, has_coe t (over X)]]
def mono_over (X : C) := {f : over X // mono f.hom}

namespace mono_over

@[simps]
def mk' {X A : C} (f : A ⟶ X) [hf : mono f] : mono_over X := { val := over.mk f, property := hf }

/-- The inclusion from monomorphisms over X to morphisms over X. -/
def forget (X : C) : mono_over X ⥤ over X := full_subcategory_inclusion _

@[simp]
lemma forget_obj_left {f} : ((forget X).obj f).left = f.val.left := rfl

/-- Convenience notation for the underlying arrow of a monomorphism over X. -/
abbreviation arrow (f : mono_over X) : _ ⟶ X := ((forget X).obj f).hom

@[simp] lemma mk'_arrow {X A : C} (f : A ⟶ X) [hf : mono f] : (mk' f).arrow = f := rfl

@[simp]
lemma forget_obj_hom {f} : ((forget X).obj f).hom = f.arrow := rfl

instance : full (forget X) := full_subcategory.full _
instance : faithful (forget X) := full_subcategory.faithful _

instance mono (f : mono_over X) : mono f.arrow := f.property

/-- The category of monomorphisms over X is a thin category,
which makes defining its skeleton easy. -/
instance is_thin {X : C} (f g : mono_over X) : subsingleton (f ⟶ g) :=
⟨begin
  intros h₁ h₂,
  ext1,
  erw [← cancel_mono g.arrow, over.w h₁, over.w h₂],
end⟩

@[reassoc] lemma w {f g : mono_over X} (k : f ⟶ g) : k.left ≫ g.arrow = f.arrow := over.w _

/-- Convenience constructor for a morphism in monomorphisms over `X`. -/
abbreviation hom_mk {f g : mono_over X} (h : f.val.left ⟶ g.val.left) (w : h ≫ g.arrow = f.arrow) :
  f ⟶ g :=
over.hom_mk h w

/-- Convenience constructor for an isomorphism in monomorphisms over `X`. -/
@[simps]
def iso_mk {f g : mono_over X} (h : f.val.left ≅ g.val.left) (w : h.hom ≫ g.arrow = f.arrow) :
  f ≅ g :=
{ hom := hom_mk h.hom w,
  inv := hom_mk h.inv (by rw [h.inv_comp_eq, w]) }

/--
Lift a functor between over categories to a functor between `mono_over` categories,
given suitable evidence that morphisms are taken to monomorphisms.
-/
@[simps]
def lift {Y : D} (F : over Y ⥤ over X)
  (h : ∀ (f : mono_over Y), mono (F.obj ((mono_over.forget Y).obj f)).hom) :
  mono_over Y ⥤ mono_over X :=
{ obj := λ f, ⟨_, h f⟩,
  map := λ _ _ k, (mono_over.forget X).preimage ((mono_over.forget Y ⋙ F).map k), }

def lift_iso {Y : D} {F₁ F₂ : over Y ⥤ over X} (h₁ h₂) (i : F₁ ≅ F₂) :
  lift F₁ h₁ ≅ lift F₂ h₂ :=
fully_faithful_cancel_right (mono_over.forget X) (iso_whisker_left (mono_over.forget Y) i)

def lift_comp {X Z : C} {Y : D} (F : over X ⥤ over Y) (G : over Y ⥤ over Z) (h₁ h₂) :
  lift F h₁ ⋙ lift G h₂ ≅ lift (F ⋙ G) (λ f, h₂ ⟨_, h₁ f⟩) :=
fully_faithful_cancel_right (mono_over.forget _) (iso.refl _)

def lift_id :
  lift (𝟭 (over X)) (λ f, f.2) ≅ 𝟭 _ :=
fully_faithful_cancel_right (mono_over.forget _) (iso.refl _)

@[simp]
lemma lift_comm (F : over Y ⥤ over X)
  (h : ∀ (f : mono_over Y), mono (F.obj ((mono_over.forget Y).obj f)).hom) :
  lift F h ⋙ mono_over.forget X = mono_over.forget Y ⋙ F :=
rfl

section pullback
variables [has_pullbacks C]

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `mono_over Y ⥤ mono_over X`,
by pulling back a monomorphism along `f`. -/
def pullback [has_pullbacks C] (f : X ⟶ Y) : mono_over Y ⥤ mono_over X :=
mono_over.lift (over.pullback f)
begin
  intro g,
  apply @pullback.snd_of_mono _ _ _ _ _ _ _ _ _,
  change mono g.arrow,
  apply_instance,
end

def pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) : pullback (f ≫ g) ≅ pullback g ⋙ pullback f :=
lift_iso _ _ (over.pullback_comp _ _) ≪≫ (lift_comp _ _ _ _).symm

def pullback_id : pullback (𝟙 X) ≅ 𝟭 _ :=
lift_iso _ _ over.pullback_id ≪≫ lift_id

@[simp] lemma pullback_obj_left (f : X ⟶ Y) (g : mono_over Y) :
(↑((pullback f).obj g) : over X).left = limits.pullback g.arrow f :=
rfl

@[simp] lemma pullback_obj_arrow (f : X ⟶ Y) (g : mono_over Y) :
((pullback f).obj g).arrow = pullback.snd :=
rfl

end pullback

section map

attribute [instance] mono_comp

def map (f : X ⟶ Y) [mono f] : mono_over X ⥤ mono_over Y :=
lift (over.map f)
(λ g, by apply mono_comp g.arrow f)

def map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] :
  map (f ≫ g) ≅ map f ⋙ map g :=
lift_iso _ _ (over.map_comp _ _) ≪≫ (lift_comp _ _ _ _).symm

def map_id : map (𝟙 X) ≅ 𝟭 _ :=
lift_iso _ _ over.map_id ≪≫ lift_id

@[simp] lemma map_obj_left (f : X ⟶ Y) [mono f] (g : mono_over X) :
(↑((map f).obj g) : over Y).left = g.val.left :=
rfl

@[simp]
lemma map_obj_arrow (f : X ⟶ Y) [mono f] (g : mono_over X) :
((map f).obj g).arrow = g.arrow ≫ f := rfl

instance full_map (f : X ⟶ Y) [mono f] : full (map f) :=
{ preimage := λ g h e,
  begin
    refine hom_mk e.left _,
    rw [← cancel_mono f, assoc],
    apply w e,
  end }

instance faithful_map (f : X ⟶ Y) [mono f] : faithful (map f) := {}.

/-- `map f` is left adjoint to `pullback f` when `f` is a monomorphism -/
def map_pullback_adj (f : X ⟶ Y) [mono f] [has_pullbacks C] : map f ⊣ pullback f :=
adjunction.restrict_fully_faithful
  (forget X) (forget Y) (over.map_pullback_adj f) (iso.refl _) (iso.refl _)

end map

section image

variables [has_images C]

@[simps]
def image : over X ⥤ mono_over X :=
{ obj := λ f, mk' (image.ι f.hom),
  map := λ f g k,
  begin
    apply (forget X).preimage _,
    apply over.hom_mk _ _,
    refine image.lift {I := image _, m := image.ι g.hom, e := k.left ≫ factor_thru_image g.hom},
    apply image.lift_fac,
  end }

def image_forget_adj : image ⊣ forget X :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ f g,
  { to_fun := λ k,
    begin
      apply over.hom_mk (factor_thru_image f.hom ≫ k.left) _,
      change (factor_thru_image f.hom ≫ k.left) ≫ _ = f.hom,
      rw [assoc, over.w k],
      apply image.fac
    end,
    inv_fun := λ k,
    begin
      refine over.hom_mk _ _,
      refine image.lift {I := g.val.left, m := g.arrow, e := k.left, fac' := over.w k},
      apply image.lift_fac,
    end,
    left_inv := λ k, subsingleton.elim _ _,
    right_inv := λ k,
    begin
      ext1,
      change factor_thru_image _ ≫ image.lift _ = _,
      rw [← cancel_mono g.arrow, assoc, image.lift_fac, image.fac f.hom],
      exact (over.w k).symm,
    end } }

instance : is_right_adjoint (forget X) :=
{ left := image, adj := image_forget_adj }

instance reflective : reflective (forget X) := {}.

def forget_image : forget X ⋙ image ≅ 𝟭 (mono_over X) :=
as_iso (adjunction.counit image_forget_adj)

end image

section «exists»
variables [has_images C]

def «exists» (f : X ⟶ Y) : mono_over X ⥤ mono_over Y :=
forget _ ⋙ over.map f ⋙ image

instance sub.faithful_exists (f : X ⟶ Y) : faithful («exists» f) := {}.

def exists_iso_map (f : X ⟶ Y) [mono f] : «exists» f ≅ map f :=
nat_iso.of_components
begin
  intro Z,
  suffices : (forget _).obj ((«exists» f).obj Z) ≅ (forget _).obj ((map f).obj Z),
    apply preimage_iso this,
  apply over.iso_mk _ _,
  apply image_mono_iso_source (Z.arrow ≫ f),
  apply image_mono_iso_source_hom_self,
end
begin
  intros Z₁ Z₂ g,
  ext1,
  change image.lift ⟨_, _, _, _⟩ ≫ (image_mono_iso_source (Z₂.arrow ≫ f)).hom =
         (image_mono_iso_source (Z₁.arrow ≫ f)).hom ≫ g.left,
  rw [← cancel_mono (Z₂.arrow ≫ f), assoc, assoc, w_assoc g, image_mono_iso_source_hom_self,
      image_mono_iso_source_hom_self],
  apply image.lift_fac,
end


/-- exists is adjoint to pullback when images exist -/
-- I really think there should be a high-level proof of this but not sure what it is...
def exists_pullback_adj (f : X ⟶ Y) [has_pullbacks C] : «exists» f ⊣ pullback f :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ g h,
  { to_fun := λ k,
    hom_mk
      (begin
        refine pullback.lift (factor_thru_image _ ≫ k.1) g.arrow _,
        rw [assoc, w k],
        apply image.fac,
       end)
      (pullback.lift_snd _ _ _),
    inv_fun := λ k, hom_mk (image.lift ⟨_, h.arrow, k.left ≫ pullback.fst,
      by { rw [assoc, pullback.condition], apply w_assoc, }⟩) (image.lift_fac _),
    left_inv := λ k, subsingleton.elim _ _,
    right_inv := λ k, subsingleton.elim _ _ } }

end «exists»

section has_top

instance {X : C} : has_top (mono_over X) :=
{ top := mk' (𝟙 _) }

def to_top (f : mono_over X) : f ⟶ ⊤ :=
hom_mk f.arrow (comp_id _)

@[simp] lemma top_left (X : C) : (⊤ : mono_over X).val.left = X := rfl
@[simp] lemma top_arrow (X : C) : (⊤ : mono_over X).arrow = 𝟙 X := rfl

def map_top (f : X ⟶ Y) [mono f] : (map f).obj ⊤ ≅ mk' f :=
iso_of_both_ways (hom_mk (𝟙 _) rfl) (hom_mk (𝟙 _) (by simp [id_comp f]))

def pullback_top (f : X ⟶ Y) [has_pullbacks C] : (pullback f).obj ⊤ ≅ ⊤ :=
iso_of_both_ways (to_top _) (hom_mk (pullback.lift f (𝟙 _) (by tidy)) (pullback.lift_snd _ _ _))

end has_top

section inf
variables [has_pullbacks C]

@[simps]
def inf {A : C} : mono_over A ⥤ mono_over A ⥤ mono_over A :=
{ obj := λ f, pullback f.arrow ⋙ map f.arrow,
  map := λ f₁ f₂ k,
  { app := λ g,
    begin
      apply hom_mk _ _,
      apply pullback.lift pullback.fst (pullback.snd ≫ k.left) _,
      rw [pullback.condition, assoc, w k],
      dsimp,
      rw [pullback.lift_snd_assoc, assoc, w k],
    end } }.

def inf_le_left {A : C} (f g : mono_over A) :
  (inf.obj f).obj g ⟶ f :=
hom_mk _ rfl

def inf_le_right {A : C} (f g : mono_over A) :
  (inf.obj f).obj g ⟶ g :=
hom_mk _ pullback.condition

def le_inf {A : C} (f g h : mono_over A) :
  (h ⟶ f) → (h ⟶ g) → (h ⟶ (inf.obj f).obj g) :=
begin
  intros k₁ k₂,
  refine hom_mk (pullback.lift k₂.left k₁.left _) _,
  rw [w k₁, w k₂],
  erw [pullback.lift_snd_assoc, w k₁],
end

end inf

section sup
variables [has_images C] [has_finite_coproducts C]

def sup  {A : C} : mono_over A ⥤ mono_over A ⥤ mono_over A :=
curry_obj ((forget A).prod (forget A) ⋙ uncurry.obj (over.coprod _) ⋙ image)

def le_sup_left {A : C} (f g : mono_over A) :
  f ⟶ (sup.obj f).obj g :=
begin
  refine hom_mk (coprod.inl ≫ factor_thru_image _) _,
  erw [category.assoc, image.fac, coprod.inl_desc],
  refl,
end

def le_sup_right {A : C} (f g : mono_over A) :
  g ⟶ (sup.obj f).obj g :=
begin
  refine hom_mk (coprod.inr ≫ factor_thru_image _) _,
  erw [category.assoc, image.fac, coprod.inr_desc],
  refl,
end

def sup_le {A : C} (f g h : mono_over A) :
  (f ⟶ h) → (g ⟶ h) → ((sup.obj f).obj g ⟶ h) :=
begin
  intros k₁ k₂,
  refine hom_mk _ _,
  apply image.lift ⟨_, h.arrow, coprod.desc k₁.left k₂.left, _⟩,
  { dsimp,
    ext1,
    { simp [w k₁] },
    { simp [w k₂] } },
  { apply image.lift_fac }
end

end sup

end mono_over

@[derive [partial_order, category]]
def subobject (X : C) := thin_skeleton (mono_over X)

namespace subobject

abbreviation mk {X A : C} (f : A ⟶ X) [mono f] : subobject X :=
(to_thin_skeleton _).obj (mono_over.mk' f)

-- FIXME rename?
def lower {Y : D} (F : mono_over Y ⥤ mono_over X) : subobject Y ⥤ subobject X :=
thin_skeleton.map F

lemma lower_iso (F₁ F₂ : mono_over X ⥤ mono_over Y) (h : F₁ ≅ F₂) :
  lower F₁ = lower F₂ :=
thin_skeleton.map_iso_eq h

-- FIXME rename?
def lower₂ (F : mono_over X ⥤ mono_over Y ⥤ mono_over Z) :
  subobject X ⥤ subobject Y ⥤ subobject Z :=
thin_skeleton.map₂ F

@[simp]
lemma lower_comm (F : mono_over Y ⥤ mono_over X) :
  to_thin_skeleton _ ⋙ lower F = F ⋙ to_thin_skeleton _ :=
rfl

def lower_adjunction {A : C} {B : D}
  {R : mono_over B ⥤ mono_over A} {L : mono_over A ⥤ mono_over B} (h : L ⊣ R) :
  lower L ⊣ lower R :=
thin_skeleton.lower_adjunction _ _ h

section pullback
variables [has_pullbacks C]

def pullback (f : X ⟶ Y) : subobject Y ⥤ subobject X :=
lower (mono_over.pullback f)

lemma pullback_id (x : subobject X) : (pullback (𝟙 X)).obj x = x :=
begin
  apply quotient.induction_on' x,
  intro f,
  apply quotient.sound,
  exact ⟨mono_over.pullback_id.app f⟩,
end

lemma pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : subobject Z) :
  (pullback (f ≫ g)).obj x = (pullback f).obj ((pullback g).obj x) :=
begin
  apply quotient.induction_on' x,
  intro t,
  apply quotient.sound,
  refine ⟨(mono_over.pullback_comp _ _).app t⟩,
end

instance (f : X ⟶ Y) : faithful (pullback f) := {}

end pullback

section map

def map (f : X ⟶ Y) [mono f] : subobject X ⥤ subobject Y :=
lower (mono_over.map f)

lemma map_id (x : subobject X) : (map (𝟙 X)).obj x = x :=
begin
  apply quotient.induction_on' x,
  intro f,
  apply quotient.sound,
  exact ⟨mono_over.map_id.app f⟩,
end
lemma map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] (x : subobject X) :
  (map (f ≫ g)).obj x = (map g).obj ((map f).obj x) :=
begin
  apply quotient.induction_on' x,
  intro t,
  apply quotient.sound,
  refine ⟨(mono_over.map_comp _ _).app t⟩,
end

def map_pullback_adj (f : X ⟶ Y) [mono f] [has_pullbacks C] : map f ⊣ pullback f :=
lower_adjunction (mono_over.map_pullback_adj f)

end map

section «exists»
variables [has_images C]

def «exists» (f : X ⟶ Y) : subobject X ⥤ subobject Y :=
lower (mono_over.exists f)

def exists_pullback_adj (f : X ⟶ Y) [has_pullbacks C] : «exists» f ⊣ pullback f :=
lower_adjunction (mono_over.exists_pullback_adj f)

end  «exists»

section order_top

instance order_top {X : C} : order_top (subobject X) :=
{ top := quotient.mk' ⊤,
  le_top :=
  begin
    refine quotient.ind' (λ f, _),
    exact ⟨mono_over.to_top f⟩,
  end,
  ..category_theory.subobject.partial_order X}

def map_top (f : X ⟶ Y) [mono f] : (map f).obj ⊤ = quotient.mk' (mono_over.mk' f) :=
quotient.sound' ⟨mono_over.map_top f⟩

def pullback_top (f : X ⟶ Y) [has_pullbacks C] : (pullback f).obj ⊤ = ⊤ :=
quotient.sound' ⟨mono_over.pullback_top f⟩

end order_top

section functor
variable (C)

@[simps]
def functor [has_pullbacks C] : Cᵒᵖ ⥤ Type (max u₁ v₁) :=
{ obj := λ X, subobject X.unop,
  map := λ X Y f, (pullback f.unop).obj,
  map_id' := λ X, funext pullback_id,
  map_comp' := λ X Y Z f g, funext (pullback_comp _ _) }

end functor

section semilattice_inf_top
variables [has_pullbacks C]

def inf {A : C} : subobject A ⥤ subobject A ⥤ subobject A :=
thin_skeleton.map₂ mono_over.inf

lemma inf_le_left  {A : C} (f g : subobject A) :
  (inf.obj f).obj g ≤ f :=
quotient.induction_on₂' f g (λ a b, ⟨mono_over.inf_le_left _ _⟩)

lemma inf_le_right {A : C} (f g : subobject A) :
  (inf.obj f).obj g ≤ g :=
quotient.induction_on₂' f g (λ a b, ⟨mono_over.inf_le_right _ _⟩)

lemma le_inf {A : C} (h f g : subobject A) :
  h ≤ f → h ≤ g → h ≤ (inf.obj f).obj g :=
quotient.induction_on₃' h f g
begin
  rintros f g h ⟨k⟩ ⟨l⟩,
  exact ⟨mono_over.le_inf _ _ _ k l⟩,
end

instance {B : C} : semilattice_inf_top (subobject B) :=
{ inf := λ m n, (inf.obj m).obj n,
  inf_le_left := inf_le_left,
  inf_le_right := inf_le_right,
  le_inf := le_inf,
  ..category_theory.subobject.order_top }

lemma inf_eq_map_pullback {A : C} (f₁ : mono_over A) (f₂ : subobject A) :
  (quotient.mk' f₁ ⊓ f₂ : subobject A) = (map f₁.arrow).obj ((pullback f₁.arrow).obj f₂) :=
begin
  apply quotient.induction_on' f₂,
  intro f₂,
  refl,
end

end semilattice_inf_top

section semilattice_sup
variables [has_images C] [has_finite_coproducts C]

def sup {A : C} : subobject A ⥤ subobject A ⥤ subobject A :=
thin_skeleton.map₂ mono_over.sup

instance {B : C} : semilattice_sup (subobject B) :=
{ sup := λ m n, (sup.obj m).obj n,
  le_sup_left := λ m n, quotient.induction_on₂' m n (λ a b, ⟨mono_over.le_sup_left _ _⟩),
  le_sup_right := λ m n, quotient.induction_on₂' m n (λ a b, ⟨mono_over.le_sup_right _ _⟩),
  sup_le := λ m n k, quotient.induction_on₃' m n k (λ a b c ⟨i⟩ ⟨j⟩, ⟨mono_over.sup_le _ _ _ i j⟩),
  ..category_theory.subobject.partial_order B }

end semilattice_sup

end subobject





-- -- Is this actually necessary?
-- def factors_through {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : Prop := nonempty (over.mk f ⟶ over.mk g)
-- lemma factors_through_iff_le {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [mono f] [mono g] :
--   factors_through f g ↔ subq.mk f ≤ subq.mk g :=
-- iff.rfl


@[simps]
def postcompose_subobject_equiv_of_iso (e : X ≅ Y) : subobject X ≃ subobject Y :=
{ to_fun := (subobject.map e.hom).obj,
  inv_fun := (subobject.map e.inv).obj,
  left_inv := λ g, by simp_rw [← subobject.map_comp, e.hom_inv_id, subobject.map_id],
  right_inv := λ g, by simp_rw [← subobject.map_comp, e.inv_hom_id, subobject.map_id] }

-- lemma postcompose_pullback_comm' [has_pullbacks.{v} C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} [mono h] [mono g]
--   {comm : f ≫ h = g ≫ k} (t : is_limit (pullback_cone.mk f g comm)) (a) :
--   (sub.post g).obj ((sub.pullback f).obj a) ≈ (sub.pullback k).obj ((sub.post h).obj a) :=
-- begin
--   apply equiv_of_both_ways,
--   { refine sub.hom_mk (pullback.lift pullback.fst _ _) (pullback.lift_snd _ _ _),
--     change _ ≫ a.arrow ≫ h = (pullback.snd ≫ g) ≫ _,
--     rw [assoc, ← comm, pullback.condition_assoc] },
--   { refine sub.hom_mk (pullback.lift pullback.fst
--                        (pullback_cone.is_limit.lift' t (pullback.fst ≫ a.arrow) pullback.snd _).1
--                        (pullback_cone.is_limit.lift' _ _ _ _).2.1.symm) _,
--     { rw [← pullback.condition, assoc], refl },
--     { erw [pullback.lift_snd_assoc], apply (pullback_cone.is_limit.lift' _ _ _ _).2.2 } }
-- end

lemma postcompose_pullback_comm [has_pullbacks C] {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} [mono h] [mono g]
  (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk f g comm)) :
  ∀ p, (subobject.map g).obj ((subobject.pullback f).obj p) = (subobject.pullback k).obj ((subobject.map h).obj p) :=
begin
  apply quotient.ind',
  intro a,
  apply quotient.sound,
  apply thin_skeleton.equiv_of_both_ways,
  { refine mono_over.hom_mk (pullback.lift pullback.fst _ _) (pullback.lift_snd _ _ _),
    change _ ≫ a.arrow ≫ h = (pullback.snd ≫ g) ≫ _,
    rw [assoc, ← comm, pullback.condition_assoc] },
  { refine mono_over.hom_mk (pullback.lift pullback.fst
                        (pullback_cone.is_limit.lift' t (pullback.fst ≫ a.arrow) pullback.snd _).1
                        (pullback_cone.is_limit.lift' _ _ _ _).2.1.symm) _,
    { rw [← pullback.condition, assoc], refl },
    { dsimp, rw [pullback.lift_snd_assoc],
      apply (pullback_cone.is_limit.lift' _ _ _ _).2.2 } }
end

lemma mono_over.pullback_map_self [has_pullbacks C] (f : X ⟶ Y) [mono f] (g₁ : mono_over X) :
  mono_over.map f ⋙ mono_over.pullback f ≅ 𝟭 _ :=
(as_iso (mono_over.map_pullback_adj f).unit).symm

lemma subobject.pullback_map_self [has_pullbacks C] (f : X ⟶ Y) [mono f] :
  ∀ g₁, (subobject.pullback f).obj ((subobject.map f).obj g₁) = g₁ :=
begin
  apply quotient.ind,
  intro g,
  apply quotient.sound,
  exact ⟨(mono_over.pullback_map_self f g).app _⟩,
end

instance over_mono {B : C} {f g : over B} (m : f ⟶ g) [mono m] : mono m.left :=
⟨λ A h k e,
begin
  let A' : over B := over.mk (k ≫ f.hom),
  have: h ≫ f.hom = k ≫ f.hom,
    rw ← over.w m, rw reassoc_of e,
  let h' : A' ⟶ f := over.hom_mk h,
  let k' : A' ⟶ f := over.hom_mk k,
  have : h' ≫ m = k' ≫ m := over.over_morphism.ext e,
  rw cancel_mono m at this,
  injection this
end⟩

def over_mono' {B : C} {f g : over B} (m : f ⟶ g) [mono m.left] : mono m :=
{right_cancellation := λ A h k e, over.over_morphism.ext ((cancel_mono m.left).1 (congr_arg comma_morphism.left e))}

@[simps]
def preorder_functor {α β : Type*} [preorder α] [preorder β] (f : α → β) (hf : monotone f) : α ⥤ β :=
{ obj := f,
  map := λ X Y ⟨⟨h⟩⟩, ⟨⟨hf h⟩⟩ }

@[simps]
def preorder_equivalence {α β : Type*} [preorder α] [preorder β] (f : α ≃o β) : α ≌ β :=
{ functor := preorder_functor f (λ x y h, by rwa [← rel_iso.map_rel_iff f]),
  inverse := preorder_functor f.symm (λ x y h, by rwa [← rel_iso.map_rel_iff f.symm]),
  unit_iso := nat_iso.of_components (λ X, eq_to_iso (f.left_inv _).symm) (λ X Y f, rfl),
  counit_iso := nat_iso.of_components (λ X, eq_to_iso (f.right_inv _)) (λ X Y f, rfl) }

instance iso_term (A : C) [has_terminal (over A)] : is_iso (⊤_ over A).hom :=
begin
  let := (⊤_ over A).hom,
  dsimp at this,
  let ident : over A := over.mk (𝟙 A),
  let k : ident ⟶ (⊤_ over A) := default _,
  haveI : split_epi (⊤_ over A).hom := ⟨k.left, over.w k⟩,
  let l : (⊤_ over A) ⟶ ident := over.hom_mk (⊤_ over A).hom (comp_id _),
  haveI : mono l := ⟨λ _ _ _ _, subsingleton.elim _ _⟩,
  haveI : mono (⊤_ over A).hom := category_theory.over_mono l,
  apply is_iso_of_mono_of_split_epi,
end

def mono_over_iso {A B : C} (e : A ≅ B) : mono_over A ≌ mono_over B :=
{ functor := mono_over.map e.hom,
  inverse := mono_over.map e.inv,
  unit_iso := ((mono_over.map_comp _ _).symm ≪≫ eq_to_iso (by simp) ≪≫ mono_over.map_id).symm,
  counit_iso := ((mono_over.map_comp _ _).symm ≪≫ eq_to_iso (by simp) ≪≫ mono_over.map_id) }

def sub_slice {A : C} {f : over A} (h₁ h₂) : mono_over f ≌ mono_over f.left :=
{ functor := mono_over.lift f.iterated_slice_equiv.functor h₁,
  inverse := mono_over.lift f.iterated_slice_equiv.inverse h₂,
  unit_iso := mono_over.lift_id.symm ≪≫ mono_over.lift_iso _ _ f.iterated_slice_equiv.unit_iso ≪≫ (mono_over.lift_comp _ _ _ _).symm,
  counit_iso := mono_over.lift_comp _ _ _ _ ≪≫ mono_over.lift_iso _ _ f.iterated_slice_equiv.counit_iso ≪≫ mono_over.lift_id }

@[simps]
def subq.equiv {A : C} {B : D} (e : mono_over A ≌ mono_over B) : subobject A ≌ subobject B :=
{ functor := subobject.lower e.functor,
  inverse := subobject.lower e.inverse,
  unit_iso :=
  begin
    apply eq_to_iso,
    convert thin_skeleton.map_iso_eq e.unit_iso,
    { exact thin_skeleton.map_id_eq.symm },
    { exact (thin_skeleton.map_comp_eq _ _).symm },
  end,
  counit_iso :=
  begin
    apply eq_to_iso,
    convert thin_skeleton.map_iso_eq e.counit_iso,
    { exact (thin_skeleton.map_comp_eq _ _).symm },
    { exact thin_skeleton.map_id_eq.symm },
  end }

def sub_one_over (A : C) [has_terminal (over A)] : subobject A ≌ subobject (⊤_ (over A)) :=
begin
  refine subq.equiv ((mono_over_iso (as_iso (⊤_ over A).hom).symm).trans (sub_slice _ _).symm),
  intro f, dsimp, apply_instance,
  intro f,
  apply over_mono' _,
  dsimp,
  apply_instance,
end




lemma prod_eq_inter {A : C} [has_pullbacks C] {f₁ f₂ : subobject A} [has_binary_product f₁ f₂] :
  (f₁ ⨯ f₂) = f₁ ⊓ f₂ :=
le_antisymm
  (le_inf
    (le_of_hom limits.prod.fst)
    (le_of_hom limits.prod.snd))
  (le_of_hom
    (prod.lift
      (hom_of_le inf_le_left)
      (hom_of_le inf_le_right)))

lemma inf_eq_intersection {B : C} (m m' : subobject B) [has_pullbacks C] :
  m ⊓ m' = (subobject.inf.obj m).obj m' := rfl

lemma top_eq_id {B : C} : (⊤ : subobject B) = subobject.mk (𝟙 B) := rfl

/-- Intersection plays well with pullback. -/
lemma inf_pullback [has_pullbacks.{v} C] {X Y : C} (g : X ⟶ Y) (f₂) :
  ∀ f₁, (subobject.pullback g).obj (f₁ ⊓ f₂) = (subobject.pullback g).obj f₁ ⊓ (subobject.pullback g).obj f₂ :=
quotient.ind' begin
  intro f₁,
  erw [inf_eq_intersection, inf_eq_intersection, subq.intersection_eq_post_pull,
       subq.intersection_eq_post_pull, ← subq.pullback_comp,
       ← postcompose_pullback_comm pullback.condition (cone_is_pullback f₁.arrow g),
       ← subq.pullback_comp, pullback.condition],
  refl,
end

lemma inf_post [has_pullbacks.{v} C] {X Y : C} (g : Y ⟶ X) [mono g] (f₂) :
  ∀ f₁, (subobject.map g).obj (f₁ ⊓ f₂) = (subobject.map g).obj f₁ ⊓ (subobject.map g).obj f₂ :=
quotient.ind' begin
  intro f₁,
  erw [inf_eq_intersection, inf_eq_intersection, subq.intersection_eq_post_pull,
       subq.intersection_eq_post_pull, ← subq.post_comp],
  dsimp,
  rw [subq.pullback_comp, subq.pull_post_self],
end

def sub.top_le_pullback_self {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks C] :
  (⊤ : mono_over A) ⟶ (mono_over.pullback f).obj (mono_over.mk' f) :=
mono_over.hom_mk _ (pullback.lift_snd _ _ rfl)

def mono_over.pullback_self {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks C] :
  (mono_over.pullback f).obj (mono_over.mk' f) ≅ ⊤ :=
iso_of_both_ways (mono_over.to_top _) (sub.top_le_pullback_self _)

lemma subobject.pullback_self {A B : C} (f : A ⟶ B) [mono f] [has_pullbacks C] :
  (subobject.pullback f).obj (subobject.mk f) = ⊤ :=
quotient.sound' ⟨mono_over.pullback_self f⟩

section
variable [has_binary_products C]

instance mono_prod_lift_of_left {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [mono f] : mono (limits.prod.lift f g) :=
begin
  split, intros W h k l,
  have := l =≫ limits.prod.fst,
  simp at this,
  rwa cancel_mono at this,
end

instance mono_prod_lift_of_right {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [mono g] : mono (limits.prod.lift f g) :=
begin
  split, intros W h k l,
  have := l =≫ limits.prod.snd,
  simp at this,
  rwa cancel_mono at this,
end
end

section
variable [has_finite_products C]
instance subterminal_ideal {A B : C} [exponentiable B] [mono (default (A ⟶ ⊤_ C))] :
  mono (default (A^^B ⟶ ⊤_ C)) :=
⟨λ Z f g eq, begin
  apply uncurry_injective,
  rw ← cancel_mono (default (A ⟶ ⊤_ C)),
  apply subsingleton.elim,
end⟩

/-- Auxiliary def for the exponential in the subobject category `sub 1`. -/
def sub.exp_aux (A : C) [exponentiable A] : mono_over (⊤_ C) ⥤ mono_over (⊤_ C) :=
{ obj := λ f,
  { val := over.mk (default (f.val.left^^A ⟶ ⊤_ C)),
    property :=
    ⟨λ Z g h eq, uncurry_injective (by { rw ← cancel_mono f.arrow, apply subsingleton.elim })⟩ },
  map := λ f₁ f₂ h, mono_over.hom_mk ((exp A).map h.left) (subsingleton.elim _ _) }

@[simps]
def sub.exp_aux_left {A₁ A₂ : C} [exponentiable A₁] [exponentiable A₂] (f : A₁ ⟶ A₂) :
  sub.exp_aux A₂ ⟶ sub.exp_aux A₁ :=
{ app := λ g, mono_over.hom_mk (pre _ f) (subsingleton.elim _ _) }

lemma sub_exp_aux_left_comp {A₁ A₂ A₃ : C} [cartesian_closed C] (f : A₁ ⟶ A₂) (g : A₂ ⟶ A₃) :
  sub.exp_aux_left (f ≫ g) = sub.exp_aux_left g ≫ sub.exp_aux_left f :=
begin
  ext : 3,
  apply pre_map,
end
lemma sub_exp_aux_left_id {A₁ : C} [cartesian_closed C] :
  sub.exp_aux_left (𝟙 A₁) = 𝟙 _ :=
begin
  ext : 3,
  apply pre_id,
end

/-- Candidate for the exponential functor in sub 1. -/
def sub.exp (f : mono_over (⊤_ C)) [cartesian_closed C] : mono_over (⊤_ C) ⥤ mono_over (⊤_ C) :=
sub.exp_aux f.val.left
end

variable [has_finite_limits C]
local attribute [instance] has_finite_products_of_has_finite_limits

def sub.exp_equiv [cartesian_closed C] (f₁ f₂ f₃ : mono_over (⊤_ C)) :
  ((mono_over.inf.obj f₂).obj f₁ ⟶ f₃) ≃ (f₁ ⟶ (sub.exp f₂).obj f₃) :=
{ to_fun := λ k,
  begin
    refine mono_over.hom_mk (cartesian_closed.curry _) (subsingleton.elim _ _),
    apply (pullback.lift limits.prod.snd limits.prod.fst _) ≫ k.left,
    dsimp,
    apply subsingleton.elim,
  end,
  inv_fun := λ k, mono_over.hom_mk (prod.lift pullback.snd pullback.fst ≫ cartesian_closed.uncurry k.left) (subsingleton.elim _ _),
  left_inv := λ x, subsingleton.elim _ _,
  right_inv := λ x, subsingleton.elim _ _ }

def subq.exp_aux [cartesian_closed C] (f : mono_over (⊤_ C)) : subobject (⊤_ C) ⥤ subobject (⊤_ C) :=
subobject.lower (sub.exp f)

def subq.exp (f : subobject (⊤_ C)) [cartesian_closed C] : subobject (⊤_ C) ⥤ subobject (⊤_ C) :=
begin
  apply quotient.lift_on' f subq.exp_aux _,
  rintros f₁ f₂ ⟨h⟩,
  apply subobject.lower_iso,
  have hi : h.hom.left ≫ h.inv.left = 𝟙 _,
    change (h.hom ≫ h.inv).left = _,
    rw h.hom_inv_id, refl,
  have ih : h.inv.left ≫ h.hom.left = 𝟙 _,
    change (h.inv ≫ h.hom).left = _,
    rw h.inv_hom_id, refl,
  refine ⟨sub.exp_aux_left h.inv.left, sub.exp_aux_left h.hom.left, _, _⟩,
  rw [← sub_exp_aux_left_comp, hi, sub_exp_aux_left_id], exact rfl,
  rw [← sub_exp_aux_left_comp, ih, sub_exp_aux_left_id], exact rfl,
end

variable (C)
def top_cc [cartesian_closed C] : cartesian_closed (subobject (⊤_ C)) :=
{ closed := λ f₁,
  { is_adj :=
    { right := subq.exp f₁,
      adj := adjunction.mk_of_hom_equiv
      { hom_equiv := λ f₂ f₃,
        begin
          change (_ ⨯ _ ⟶ _) ≃ (_ ⟶ _),
          rw prod_eq_inter,
          apply @@quotient.rec_on_subsingleton₂ (is_isomorphic_setoid _) (is_isomorphic_setoid _) _ _ f₁ f₂,
          intros f₁ f₂,
          apply @@quotient.rec_on_subsingleton (is_isomorphic_setoid _) _ _ f₃,
          intro f₃,
          refine ⟨_, _, _, _⟩,
          { rintro k,
            refine ⟨⟨_⟩⟩,
            rcases k with ⟨⟨⟨k⟩⟩⟩,
            refine ⟨sub.exp_equiv _ _ _ k⟩ },
          { rintro k,
            refine ⟨⟨_⟩⟩,
            rcases k with ⟨⟨⟨k⟩⟩⟩,
            refine ⟨(sub.exp_equiv _ _ _).symm k⟩ },
          { tidy },
          { tidy },
          { tidy },
          { tidy }
        end } } } }

end category_theory
