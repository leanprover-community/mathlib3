import category_theory.limits.preserves
import category_theory.whiskering
import data.equiv.basic

namespace category_theory
open category
open category_theory.limits

universes u₁ v₁ u₂ v₂ u₃ v₃

local attribute [elab_simple] whisker_left whisker_right

variables {C : Type u₁} [𝒞 : category.{u₁ v₁} C] {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒞 𝒟

/--
`adjunction F G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

The adjunction is represented by a pair of natural transformations satisfying
the triangle equations.
-/
structure adjunction (F : C ⥤ D) (G : D ⥤ C) :=
(unit : functor.id C ⟹ F.comp G)
(counit : G.comp F ⟹ functor.id D)
(left_triangle : (whisker_right unit F).vcomp (whisker_left F counit) = nat_trans.id _)
(right_triangle : (whisker_left G unit).vcomp (whisker_right counit G) = nat_trans.id _)

attribute [simp] adjunction.left_triangle adjunction.right_triangle

namespace adjunction

section
variables {F : C ⥤ D} {G : D ⥤ C} (adj : adjunction F G)

lemma left_triangle_components {c : C} :
  F.map (adj.unit.app c) ≫ adj.counit.app (F.obj c) = 𝟙 _ :=
congr_arg (λ (t : _ ⟹ functor.id C ⋙ F), nat_trans.app t c) adj.left_triangle

lemma right_triangle_components {d : D} :
  adj.unit.app (G.obj d) ≫ G.map (adj.counit.app d) = 𝟙 _ :=
congr_arg (λ (t : _ ⟹ G ⋙ functor.id C), nat_trans.app t d) adj.right_triangle

def hom_equiv {X Y} : (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y) :=
{ to_fun := λ f, adj.unit.app X ≫ G.map f,
  inv_fun := λ g, F.map g ≫ adj.counit.app Y,
  left_inv := λ f, begin
    change F.map (_ ≫ _) ≫ _ = _,
    rw [F.map_comp, assoc, ←functor.comp_map, adj.counit.naturality, ←assoc],
    convert id_comp _ f,
    apply left_triangle_components
  end,
  right_inv := λ g, begin
    change _ ≫ G.map (_ ≫ _) = _,
    rw [G.map_comp, ←assoc, ←functor.comp_map, ←adj.unit.naturality, assoc],
    convert comp_id _ g,
    apply right_triangle_components
  end }

@[simp] lemma hom_equiv_naturality {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
  adj.hom_equiv.to_fun (f ≫ g) = adj.hom_equiv.to_fun f ≫ G.map g :=
show adj.unit.app X ≫ G.map (f ≫ g) = (adj.unit.app X ≫ G.map f) ≫ G.map g,
by simp

@[simp] lemma hom_equiv_symm_naturality {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
  adj.hom_equiv.inv_fun (f ≫ g) = F.map f ≫ adj.hom_equiv.inv_fun g :=
show F.map (f ≫ g) ≫ adj.counit.app Y = F.map f ≫ F.map g ≫ adj.counit.app Y,
by simp

@[simp] lemma hom_equiv_naturality' {X' X Y} (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
  adj.hom_equiv.to_fun (F.map f ≫ g) = f ≫ adj.hom_equiv.to_fun g :=
by dsimp [adjunction.hom_equiv]; erw [←assoc, adj.unit.naturality]; simp

@[simp] lemma hom_equiv_symm_naturality' {X Y Y'} (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
  adj.hom_equiv.inv_fun (f ≫ G.map g) = adj.hom_equiv.inv_fun f ≫ g :=
by dsimp [adjunction.hom_equiv]; conv { to_rhs, rw assoc }; erw ←adj.counit.naturality; simp

def nat_equiv {E : Type u₃} [category.{u₃ v₃} E] (X : E ⥤ C) (Y : E ⥤ D) :
  (X.comp F ⟹ Y) ≃ (X ⟹ Y.comp G) :=
{ to_fun := λ t,
  { app := λ e, adj.hom_equiv.to_fun (t.app e),
    naturality' := λ e e' f,
      by erw [←adj.hom_equiv_naturality, ←adj.hom_equiv_naturality', t.naturality] },
  inv_fun := λ t,
  { app := λ e, adj.hom_equiv.inv_fun (t.app e),
    naturality' := λ e e' f,
      by erw [←adj.hom_equiv_symm_naturality, ←adj.hom_equiv_symm_naturality', ←t.naturality] },
  left_inv := λ t, by ext e; apply adj.hom_equiv.left_inv,
  right_inv := λ t, by ext e; apply adj.hom_equiv.right_inv }

def nat_equiv' {E : Type u₃} [category.{u₃ v₃} E] (X : C ⥤ E) (Y : D ⥤ E) :
  (G.comp X ⟹ Y) ≃ (X ⟹ F.comp Y) :=
{ to_fun := λ t,
  { app := λ c, X.map (adj.unit.app c) ≫ t.app (F.obj c),
    naturality' := λ c c' f, begin
      erw [←assoc, ←X.map_comp, adj.unit.naturality, X.map_comp, assoc, assoc, t.naturality],
      refl
    end },
  inv_fun := λ t,
  { app := λ d, t.app (G.obj d) ≫ Y.map (adj.counit.app d),
    naturality' := λ d d' f, begin
      erw [assoc, ←Y.map_comp, ←adj.counit.naturality, Y.map_comp, ←assoc, ←assoc, ←t.naturality],
      refl
    end },
  left_inv := λ t, begin
    ext c, dsimp [],
    erw [assoc, ←t.naturality, ←assoc, ←X.map_comp, adj.right_triangle_components],
    dsimp, simp
  end,
  right_inv := λ t, begin
    ext d, dsimp [],
    erw [←assoc, t.naturality, assoc, ←Y.map_comp, adj.left_triangle_components],
    dsimp, simp
  end }

section mate
universes u₁' v₁' u₂' v₂'
variables {C' : Type u₁'} [𝒞' : category.{u₁' v₁'} C'] {D' : Type u₂'} [𝒟' : category.{u₂' v₂'} D']
include 𝒞' 𝒟'
variables {F' : C' ⥤ D'} {G' : D' ⥤ C'} (adj' : adjunction F' G')
variables {X : C ⥤ C'} {Y : D ⥤ D'}

def mate : (X.comp F' ⟹ F.comp Y) ≃ (G.comp X ⟹ Y.comp G') :=
calc
  (X.comp F' ⟹ F.comp Y)
    ≃ (X ⟹ (F.comp Y).comp G')  : adj'.nat_equiv _ _
... ≃ (X ⟹ F.comp (Y.comp G'))  : equiv.refl _
... ≃ (G.comp X ⟹ Y.comp G')    : (adj.nat_equiv' _ _).symm

-- TODO: This is a double functor, or something like that

end mate

section morphism
variables {F' : C ⥤ D} {G' : D ⥤ C} (adj' : adjunction F' G')

def nat_trans_equiv : (F' ⟹ F) ≃ (G ⟹ G') :=
calc
  (F' ⟹ F)
    ≃ ((functor.id C).comp F' ⟹ F.comp (functor.id D))
    : iso.hom_equiv_of_isos (functor.id_comp F') (functor.comp_id F).symm
... ≃ (G.comp (functor.id C) ⟹ (functor.id D).comp G')
    : mate adj adj'
... ≃ (G ⟹ G')
    : iso.hom_equiv_of_isos (functor.comp_id G).symm (functor.id_comp G')

lemma nat_trans_lemma (t : F' ⟹ F) {X Y} (f : F.obj X ⟶ Y) :
  adj'.hom_equiv.to_fun (t.app X ≫ f) =
  adj.hom_equiv.to_fun f ≫ (nat_trans_equiv adj adj' t).app Y :=
begin
  dsimp [hom_equiv],
  rw [assoc, nat_trans.naturality, G'.map_comp, ←assoc, ←assoc],
  congr' 1,
  dsimp [nat_trans_equiv, mate, nat_equiv', nat_equiv, hom_equiv, iso.hom_equiv_of_isos],
  simp only [id_comp, comp_id, assoc],
/-
            /\
           |  |
   /\      |  |   /\
  |  |     |  |  |  |
  t  |  =  |  |  t  |
  |  |     |  |  |  |
           |   \/   |
           |        |
-/
  conv in (adj.unit.app X) { change (functor.id _).map (adj.unit.app X) },
  erw [←assoc, adj'.unit.naturality, assoc], congr,
  erw [←G'.map_comp, ←G'.map_comp], congr,
  erw [←assoc, t.naturality, assoc, adj.left_triangle_components],
  symmetry, apply comp_id
end

lemma nat_trans_iff {t u} : nat_trans_equiv adj adj' t = u ↔ ∀ {X Y} (f : F.obj X ⟶ Y),
  adj'.hom_equiv.to_fun (t.app X ≫ f) = adj.hom_equiv.to_fun f ≫ u.app Y :=
begin
  split; intro H,
  { subst H, apply nat_trans_lemma },
  { ext Y,
    have := H (adj.hom_equiv.inv_fun (𝟙 (G.obj Y))),
    rw [adj.hom_equiv.right_inv, id_comp] at this,
    rw ←this,
    have := nat_trans_lemma adj adj' t (adj.hom_equiv.inv_fun (𝟙 (G.obj Y))),
    rw [adj.hom_equiv.right_inv, id_comp] at this,
    rw this }
end

lemma nat_trans_iff' {t u} : nat_trans_equiv adj adj' t = u ↔ ∀ {X Y} (f : X ⟶ G.obj Y),
  t.app X ≫ adj.hom_equiv.inv_fun f = adj'.hom_equiv.inv_fun (f ≫ u.app Y) :=
begin
  rw nat_trans_iff,
  apply forall_congr, intro X,
  apply forall_congr, intro Y,
  split; intros H f,
  { erw adj'.hom_equiv.eq_symm_apply, convert ←H _, exact (hom_equiv adj).right_inv f },
  { erw ←adj'.hom_equiv.eq_symm_apply, convert ←H _, exact (hom_equiv adj).left_inv f }
end

lemma nat_trans_equiv_id : nat_trans_equiv adj adj (𝟙 F) = (𝟙 G) :=
by rw nat_trans_iff; simp

variables {F'' : C ⥤ D} {G'' : D ⥤ C} (adj'' : adjunction F'' G'')

-- FIXME: (_ ⊟ _)
lemma nat_trans_equiv_vcomp {t' t} :
  nat_trans_equiv adj adj'' (t' ⊟ t) =
  (nat_trans_equiv adj adj' t ⊟ nat_trans_equiv adj' adj'' t') :=
by rw nat_trans_iff; intros X Y f; erw [←assoc, ←nat_trans_lemma, ←nat_trans_lemma, assoc]

lemma nat_trans_equiv_symm_id : (nat_trans_equiv adj adj).symm (𝟙 G) = (𝟙 F) :=
by rw [equiv.symm_apply_eq, nat_trans_equiv_id]

lemma nat_trans_equiv_symm_vcomp {t' t} :
  (nat_trans_equiv adj'' adj).symm (t' ⊟ t) =
  ((nat_trans_equiv adj' adj).symm t ⊟ (nat_trans_equiv adj'' adj').symm t') :=
by rw [equiv.symm_apply_eq, nat_trans_equiv_vcomp adj'' adj' adj]; simp

-- and therefore...

def nat_iso_equiv : (F' ≅ F) ≃ (G ≅ G') :=
⟨λ i,
 { hom := nat_trans_equiv adj adj' i.hom,
   inv := nat_trans_equiv adj' adj i.inv,
   hom_inv_id' := begin
     change (_ ⊟ _) = _,        -- FIXME
     rw ←nat_trans_equiv_vcomp,
     conv in (i.inv ⊟ i.hom) { change i.inv ≫ i.hom, rw i.inv_hom_id }, -- ugh
     apply nat_trans_equiv_id
   end,
   inv_hom_id' := begin
     change (_ ⊟ _) = _,        -- FIXME
     rw ←nat_trans_equiv_vcomp,
     conv in (i.hom ⊟ i.inv) { change i.hom ≫ i.inv, rw i.hom_inv_id }, -- ugh
     apply nat_trans_equiv_id
   end },
 λ i,
 { hom := (nat_trans_equiv adj adj').symm i.hom,
   inv := (nat_trans_equiv adj' adj).symm i.inv,
   hom_inv_id' := begin
     change (_ ⊟ _) = _,        -- FIXME
     rw ←nat_trans_equiv_symm_vcomp,
     conv in (i.inv ⊟ i.hom) { change i.inv ≫ i.hom, rw i.inv_hom_id }, -- ugh
     apply nat_trans_equiv_symm_id
   end,
   inv_hom_id' := begin
     change (_ ⊟ _) = _,        -- FIXME
     rw ←nat_trans_equiv_symm_vcomp,
     conv in (i.hom ⊟ i.inv) { change i.hom ≫ i.inv, rw i.hom_inv_id }, -- ugh
     apply nat_trans_equiv_symm_id
   end },
 λ i, by ext; simp,
 λ i, by ext; simp⟩

end morphism

section cat
-- Categories and adjunctions form a category. TODO: Lots

omit 𝒟
def id : adjunction (functor.id C) (functor.id C) :=
{ unit := nat_trans.id _,
  counit := nat_trans.id _,
  left_triangle := by tidy,
  right_triangle := by tidy }

@[simp] lemma id.hom_equiv_app {X Y : C} (f : X ⟶ Y) : id.hom_equiv.to_fun f = f :=
by dsimp [hom_equiv, id]; simp

@[simp] lemma id.hom_equiv_inv {X Y : C} (f : X ⟶ Y) : id.hom_equiv.inv_fun f = f :=
by dsimp [hom_equiv, id]; simp

end cat

end


section construction

section
variables {F : C ⥤ D} {G : D ⥤ C}
variables (e : Π X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
variables (heX : Π X' X Y f h, e X' Y (F.map f ≫ h) = f ≫ e X Y h)
variables (heY : Π X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)
include heX heY

def adjunction_of_equiv : adjunction F G :=
{ unit := 
  { app := λ X, e X (F.obj X) (𝟙 _),
    naturality' := λ X X' f, by erw [←heX, ←heY]; dsimp; simp },
  counit :=
  { app := λ Y, (e (G.obj Y) Y).symm (𝟙 _),
    naturality' := λ Y Y' g, by rw [←(e _ _).apply_eq_iff_eq]; erw [heX, heY]; dsimp; simp },
  left_triangle := by ext X; dsimp; rw [←(e _ _).apply_eq_iff_eq, heX]; simp,
  right_triangle := by ext Y; dsimp; rw [←heY]; simp }

lemma adjunction_of_equiv_equiv {X Y} : (adjunction_of_equiv e heX heY).hom_equiv = e X Y :=
begin
  ext h,
  dsimp [hom_equiv, adjunction_of_equiv],
  rw ←heY, simp
end

end

section construct_left
-- Construction of a left adjoint. In order to construct a left
-- adjoint to a functor G : D → C, it suffices to give the object part
-- of a functor F : C → D together with isomorphisms Hom(FX, Y) ≃
-- Hom(X, GY) natural in Y. The action of F on morphisms can be
-- constructed from this data.
variables {F_obj : C → D} {G : D ⥤ C}
variables (e : Π X Y, (F_obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
variables (he : Π X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)
include he

def left_adjoint_of_equiv : C ⥤ D :=
{ obj := F_obj,
  map := λ X X' f, (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _)),
  map_id' := λ X, by simp,
  map_comp' := λ X X' X'' f f', begin
    rw equiv.symm_apply_eq,
    rw he,
    rw equiv.apply_inverse_apply,
    conv { to_rhs, rw assoc, rw ←he, rw id_comp, rw equiv.apply_inverse_apply },
    simp
  end }

def adjunction_of_equiv_left : adjunction (left_adjoint_of_equiv e he) G :=
begin
  refine adjunction_of_equiv e _ he,
  intros X' X Y f h,
  dsimp [left_adjoint_of_equiv],
  rw [he, equiv.apply_inverse_apply, assoc, ←he],
  simp
end

lemma adjunction_of_equiv_left_equiv {X Y} :
  (adjunction_of_equiv_left e he).hom_equiv = e X Y :=
adjunction_of_equiv_equiv e _ he

end construct_left

section construct_right
-- Construction of a right adjoint, analogous to the above.
variables {F : C ⥤ D} {G_obj : D → C}
variables (e : Π X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G_obj Y))
variables (he : Π X' X Y f h, e X' Y (F.map f ≫ h) = f ≫ e X Y h)
include he

private lemma he' (X' X Y f h) : F.map f ≫ (e X Y).symm h = (e X' Y).symm (f ≫ h) :=
by intros; rw [equiv.eq_symm_apply, he]; simp

def right_adjoint_of_equiv : D ⥤ C :=
{ obj := G_obj,
  map := λ Y Y' g, (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g),
  map_id' := λ Y, by simp,
  map_comp' := λ Y Y' Y'' g g', begin
    rw ←equiv.eq_symm_apply,
    rw ←he' e he,
    rw equiv.inverse_apply_apply,
    conv { to_rhs, rw ←assoc, rw he' e he, rw comp_id, rw equiv.inverse_apply_apply },
    simp
  end }

def adjunction_of_equiv_right : adjunction F (right_adjoint_of_equiv e he) :=
begin
  refine adjunction_of_equiv e he _,
  intros X Y Y' g h,
  dsimp [right_adjoint_of_equiv],
  rw [←he, equiv.apply_eq_iff_eq, ←assoc, he' e he],
  simp
end

lemma adjunction_of_equiv_right_equiv {X Y} :
  (adjunction_of_equiv_right e he).hom_equiv = e X Y :=
adjunction_of_equiv_equiv e he _

end construct_right

end construction

end adjunction

end category_theory

-- For limits, we need to set up again with C and D having morphisms
-- living in the same universe.

namespace category_theory.adjunction
open category_theory
open category_theory.limits

universes u₁ u₂ v

variables {C : Type u₁} [𝒞 : category.{u₁ v} C] {D : Type u₂} [𝒟 : category.{u₂ v} D]
include 𝒞 𝒟

variables {F : C ⥤ D} {G : D ⥤ C} (adj : adjunction F G)

def cocone_equiv {J : Type v} [small_category J] {X : J ⥤ C} {Y : D} :
  (X.comp F ⟹ (functor.const J).obj Y) ≃ (X ⟹ (functor.const J).obj (G.obj Y)) :=
{ to_fun := λ t,
  { app := λ j, adj.hom_equiv.to_fun (t.app j),
    naturality' := λ j j' f, by erw [←hom_equiv_naturality', t.naturality]; dsimp; simp },
  inv_fun := λ t,
  { app := λ j, adj.hom_equiv.inv_fun (t.app j),
    naturality' := λ j j' f, begin
      erw [←adj.hom_equiv_symm_naturality, ←adj.hom_equiv_symm_naturality', t.naturality],
      congr, dsimp, simp
    end },
  left_inv := λ t, by ext j; apply adj.hom_equiv.left_inv,
  right_inv := λ t, by ext j; apply adj.hom_equiv.right_inv }

def cone_equiv {J : Type v} [small_category J] {X : C} {Y : J ⥤ D} :
  ((functor.const J).obj (F.obj X) ⟹ Y) ≃ ((functor.const J).obj X ⟹ Y.comp G) :=
{ to_fun := λ t,
  { app := λ j, adj.hom_equiv.to_fun (t.app j),
    naturality' := λ j j' f, begin
      erw [←adj.hom_equiv_naturality, ←adj.hom_equiv_naturality', ←t.naturality],
      dsimp, simp
    end },
  inv_fun := λ t,
  { app := λ j, adj.hom_equiv.inv_fun (t.app j),
    naturality' := λ j j' f,
      by erw [←adj.hom_equiv_symm_naturality', ←t.naturality]; dsimp; simp },
  left_inv := λ t, by ext j; apply adj.hom_equiv.left_inv,
  right_inv := λ t, by ext j; apply adj.hom_equiv.right_inv }

section preservation

include adj

/-- A left adjoint preserves colimits. -/
def left_adjoint_preserves_colimits : preserves_colimits F :=
⟨λ J 𝒥, by exactI λ Y c h, limits.is_colimit.of_equiv
  (λ Z, calc
     (F.obj c.X ⟶ Z) ≃ (c.X ⟶ G.obj Z)            : adj.hom_equiv
     ... ≃ (Y ⟹ (functor.const J).obj (G.obj Z))  : h.equiv
     ... ≃ (Y.comp F ⟹ (functor.const J).obj Z)   : adj.cocone_equiv.symm)
  (λ Z f j, begin
     dsimp [is_colimit.equiv, cocone_equiv],
     rw adj.hom_equiv_symm_naturality,
     erw adj.hom_equiv.left_inv f
   end)⟩

/-- A right adjoint preserves limits. -/
def right_adjoint_preserves_limits : preserves_limits G :=
⟨λ J 𝒥, by exactI λ Y c h, limits.is_limit.of_equiv
  (λ Z, calc
     (Z ⟶ G.obj c.X) ≃ (F.obj Z ⟶ c.X)            : adj.hom_equiv.symm
     ... ≃ ((functor.const J).obj (F.obj Z) ⟹ Y)  : (h.equiv (F.obj Z)).to_equiv
     ... ≃ ((functor.const J).obj Z ⟹ Y.comp G)   : adj.cone_equiv)
  (λ Z f j, begin
     dsimp [is_limit.equiv, cone_equiv],
     rw adj.hom_equiv_naturality,
     erw adj.hom_equiv.right_inv f,
     simp
   end)⟩

end preservation

end category_theory.adjunction
