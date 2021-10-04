/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Scott Morrison
-/
import category_theory.comma
import category_theory.punit
import category_theory.limits.shapes.terminal

/-!
# The category of "structured arrows"

For `T : C ⥤ D`, a `T`-structured arrow with source `S : D`
is just a morphism `S ⟶ T.obj Y`, for some `Y : D`.

These form a category with morphisms `g : Y ⟶ Y'` making the obvious diagram commute.

We prove that `𝟙 (T.obj Y)` is the initial object in `T`-structured objects with source `T.obj Y`.
-/

namespace category_theory

universes v₁ v₂ u₁ u₂ -- morphism levels before object levels. See note [category_theory universes].
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

/--
The category of `T`-structured arrows with domain `S : D` (here `T : C ⥤ D`),
has as its objects `D`-morphisms of the form `S ⟶ T Y`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
@[derive category, nolint has_inhabited_instance]
def structured_arrow (S : D) (T : C ⥤ D) := comma (functor.from_punit S) T

namespace structured_arrow

/-- The obvious projection functor from structured arrows. -/
@[simps]
def proj (S : D) (T : C ⥤ D) : structured_arrow S T ⥤ C := comma.snd _ _

variables {S S' S'' : D} {Y Y' : C} {T : C ⥤ D}

/-- Construct a structured arrow from a morphism. -/
def mk (f : S ⟶ T.obj Y) : structured_arrow S T := ⟨⟨⟩, Y, f⟩

@[simp] lemma mk_left (f : S ⟶ T.obj Y) : (mk f).left = punit.star := rfl
@[simp] lemma mk_right (f : S ⟶ T.obj Y) : (mk f).right = Y := rfl
@[simp] lemma mk_hom_eq_self (f : S ⟶ T.obj Y) : (mk f).hom = f := rfl

@[simp, reassoc] lemma w {A B : structured_arrow S T} (f : A ⟶ B) : A.hom ≫ T.map f.right = B.hom :=
by { have := f.w; tidy }

lemma eq_mk (f : structured_arrow S T) : f = mk f.hom :=
by { cases f, congr, ext, }

/--
To construct a morphism of structured arrows,
we need a morphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps]
def hom_mk {f f' : structured_arrow S T} (g : f.right ⟶ f'.right) (w : f.hom ≫ T.map g = f'.hom) :
  f ⟶ f' :=
{ left := eq_to_hom (by ext),
  right := g,
  w' := by { dsimp, simpa using w.symm, }, }

/--
To construct an isomorphism of structured arrows,
we need an isomorphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps]
def iso_mk {f f' : structured_arrow S T} (g : f.right ≅ f'.right)
  (w : f.hom ≫ T.map g.hom = f'.hom) : f ≅ f' :=
comma.iso_mk (eq_to_iso (by ext)) g (by simpa using w.symm)

/--
A morphism between source objects `S ⟶ S'`
contravariantly induces a functor between structured arrows,
`structured_arrow S' T ⥤ structured_arrow S T`.

Ideally this would be described as a 2-functor from `D`
(promoted to a 2-category with equations as 2-morphisms)
to `Cat`.
-/
@[simps]
def map (f : S ⟶ S') : structured_arrow S' T ⥤ structured_arrow S T :=
comma.map_left _ ((functor.const _).map f)

@[simp] lemma map_mk {f : S' ⟶ T.obj Y} (g : S ⟶ S') :
  (map g).obj (mk f) = mk (g ≫ f) := rfl

@[simp] lemma map_id {f : structured_arrow S T} : (map (𝟙 S)).obj f = f :=
by { rw eq_mk f, simp, }

@[simp] lemma map_comp {f : S ⟶ S'} {f' : S' ⟶ S''} {h : structured_arrow S'' T} :
  (map (f ≫ f')).obj h = (map f).obj ((map f').obj h) :=
by { rw eq_mk h, simp, }

instance proj_reflects_iso : reflects_isomorphisms (proj S T) :=
{ reflects := λ Y Z f t, by exactI
  ⟨⟨structured_arrow.hom_mk (inv ((proj S T).map f)) (by simp), by tidy⟩⟩ }

open category_theory.limits

/-- The identity structured arrow is initial. -/
def mk_id_initial [full T] [faithful T] : is_initial (mk (𝟙 (T.obj Y))) :=
{ desc := λ c, hom_mk (T.preimage c.X.hom) (by { dsimp, simp, }),
  uniq' := λ c m _, begin
    ext,
    apply T.map_injective,
    simpa only [hom_mk_right, T.image_preimage, ←w m] using (category.id_comp _).symm,
  end }

end structured_arrow


/--
The category of `S`-costructured arrows with target `T : D` (here `S : C ⥤ D`),
has as its objects `D`-morphisms of the form `S Y ⟶ T`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
@[derive category, nolint has_inhabited_instance]
def costructured_arrow (S : C ⥤ D) (T : D) := comma S (functor.from_punit T)

namespace costructured_arrow

/-- The obvious projection functor from costructured arrows. -/
@[simps]
def proj (S : C ⥤ D) (T : D) : costructured_arrow S T ⥤ C := comma.fst _ _

variables {T T' T'' : D} {Y Y' : C} {S : C ⥤ D}

/-- Construct a costructured arrow from a morphism. -/
def mk (f : S.obj Y ⟶ T) : costructured_arrow S T := ⟨Y, ⟨⟩, f⟩

@[simp] lemma mk_left (f : S.obj Y ⟶ T) : (mk f).left = Y := rfl
@[simp] lemma mk_right (f : S.obj Y ⟶ T) : (mk f).right = punit.star := rfl
@[simp] lemma mk_hom_eq_self (f : S.obj Y ⟶ T) : (mk f).hom = f := rfl

@[simp, reassoc] lemma w {A B : costructured_arrow S T} (f : A ⟶ B) :
  S.map f.left ≫ B.hom = A.hom :=
by tidy

lemma eq_mk (f : costructured_arrow S T) : f = mk f.hom :=
by { cases f, congr, ext, }

/--
To construct a morphism of costructured arrows,
we need a morphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps]
def hom_mk {f f' : costructured_arrow S T} (g : f.left ⟶ f'.left) (w : S.map g ≫ f'.hom = f.hom) :
  f ⟶ f' :=
{ left := g,
  right := eq_to_hom (by ext),
  w' := by simpa using w, }

/--
To construct an isomorphism of costructured arrows,
we need an isomorphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps]
def iso_mk {f f' : costructured_arrow S T} (g : f.left ≅ f'.left)
  (w : S.map g.hom ≫ f'.hom = f.hom) : f ≅ f' :=
comma.iso_mk g (eq_to_iso (by ext)) (by simpa using w)

/--
A morphism between target objects `T ⟶ T'`
covariantly induces a functor between costructured arrows,
`costructured_arrow S T ⥤ costructured_arrow S T'`.

Ideally this would be described as a 2-functor from `D`
(promoted to a 2-category with equations as 2-morphisms)
to `Cat`.
-/
@[simps]
def map (f : T ⟶ T') : costructured_arrow S T ⥤ costructured_arrow S T' :=
comma.map_right _ ((functor.const _).map f)

@[simp] lemma map_mk {f : S.obj Y ⟶ T} (g : T ⟶ T') :
  (map g).obj (mk f) = mk (f ≫ g) := rfl

@[simp] lemma map_id {f : costructured_arrow S T} : (map (𝟙 T)).obj f = f :=
by { rw eq_mk f, simp, }

@[simp] lemma map_comp {f : T ⟶ T'} {f' : T' ⟶ T''} {h : costructured_arrow S T} :
  (map (f ≫ f')).obj h = (map f').obj ((map f).obj h) :=
by { rw eq_mk h, simp, }

instance proj_reflects_iso : reflects_isomorphisms (proj S T) :=
{ reflects := λ Y Z f t, by exactI
  ⟨⟨costructured_arrow.hom_mk (inv ((proj S T).map f)) (by simp), by tidy⟩⟩ }

open category_theory.limits

/-- The identity costructured arrow is terminal. -/
def mk_id_terminal [full S] [faithful S] : is_terminal (mk (𝟙 (S.obj Y))) :=
{ lift := λ c, hom_mk (S.preimage c.X.hom) (by { dsimp, simp, }),
  uniq' := begin
    rintros c m -,
    ext,
    apply S.map_injective,
    simpa only [hom_mk_left, S.image_preimage, ←w m] using (category.comp_id _).symm,
  end }

end costructured_arrow

open opposite

namespace structured_arrow

/--
For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of structured arrows `d ⟶ F.obj c` to the category of costructured arrows
`F.op.obj c ⟶ (op d)`.
-/
@[simps]
def to_costructured_arrow (F : C ⥤ D) (d : D) :
  (structured_arrow d F)ᵒᵖ ⥤ costructured_arrow F.op (op d) :=
{ obj := λ X, @costructured_arrow.mk _ _ _ _ _ (op X.unop.right) F.op X.unop.hom.op,
  map := λ X Y f, costructured_arrow.hom_mk (f.unop.right.op)
  begin
    dsimp,
    rw [← op_comp, ← f.unop.w, functor.const.obj_map],
    erw category.id_comp,
  end }

/--
For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of structured arrows `op d ⟶ F.op.obj c` to the category of costructured arrows
`F.obj c ⟶ d`.
-/
@[simps]
def to_costructured_arrow' (F : C ⥤ D) (d : D) :
  (structured_arrow (op d) F.op)ᵒᵖ ⥤ costructured_arrow F d :=
{ obj := λ X, @costructured_arrow.mk _ _ _ _ _ (unop X.unop.right) F X.unop.hom.unop,
  map := λ X Y f, costructured_arrow.hom_mk f.unop.right.unop
  begin
    dsimp,
    rw [← quiver.hom.unop_op (F.map (quiver.hom.unop f.unop.right)), ← unop_comp, ← F.op_map,
      ← f.unop.w, functor.const.obj_map],
    erw category.id_comp,
  end }

end structured_arrow

namespace costructured_arrow

/--
For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of costructured arrows `F.obj c ⟶ d` to the category of structured arrows
`op d ⟶ F.op.obj c`.
-/
@[simps]
def to_structured_arrow (F : C ⥤ D) (d : D) :
  (costructured_arrow F d)ᵒᵖ ⥤ structured_arrow (op d) F.op :=
{ obj := λ X, @structured_arrow.mk _ _ _ _ _ (op X.unop.left) F.op X.unop.hom.op,
  map := λ X Y f, structured_arrow.hom_mk f.unop.left.op
  begin
    dsimp,
    rw [← op_comp, f.unop.w, functor.const.obj_map],
    erw category.comp_id,
  end }

/--
For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of costructured arrows `F.op.obj c ⟶ op d` to the category of structured arrows
`d ⟶ F.obj c`.
-/
@[simps]
def to_structured_arrow' (F : C ⥤ D) (d : D) :
  (costructured_arrow F.op (op d))ᵒᵖ ⥤ structured_arrow d F :=
{ obj := λ X, @structured_arrow.mk _ _ _ _ _ (unop X.unop.left) F X.unop.hom.unop,
  map := λ X Y f, structured_arrow.hom_mk (f.unop.left.unop)
  begin
    dsimp,
    rw [← quiver.hom.unop_op (F.map f.unop.left.unop), ← unop_comp, ← F.op_map,
      f.unop.w, functor.const.obj_map],
    erw category.comp_id,
  end }

end costructured_arrow

/--
For a functor `F : C ⥤ D` and an object `d : D`, the category of structured arrows `d ⟶ F.obj c`
is contravariantly equivalent to the category of costructured arrows `F.op.obj c ⟶ op d`.
-/
def structured_arrow_op_equivalence (F : C ⥤ D) (d : D) :
  (structured_arrow d F)ᵒᵖ ≌ costructured_arrow F.op (op d) :=
equivalence.mk (structured_arrow.to_costructured_arrow F d)
  (costructured_arrow.to_structured_arrow' F d).right_op
  (nat_iso.of_components (λ X, (@structured_arrow.iso_mk _ _ _ _ _ _
    (structured_arrow.mk (unop X).hom) (unop X) (iso.refl _) (by tidy)).op)
    (λ X Y f, quiver.hom.unop_inj $ begin ext, dsimp, simp end))
  (nat_iso.of_components (λ X, @costructured_arrow.iso_mk _ _ _ _ _ _
    (costructured_arrow.mk X.hom) X (iso.refl _) (by tidy))
    (λ X Y f, begin ext, dsimp, simp end))

/--
For a functor `F : C ⥤ D` and an object `d : D`, the category of costructured arrows
`F.obj c ⟶ d` is contravariantly equivalent to the category of structured arrows
`op d ⟶ F.op.obj c`.
-/
def costructured_arrow_op_equivalence (F : C ⥤ D) (d : D) :
  (costructured_arrow F d)ᵒᵖ ≌ structured_arrow (op d) F.op :=
equivalence.mk (costructured_arrow.to_structured_arrow F d)
  (structured_arrow.to_costructured_arrow' F d).right_op
  (nat_iso.of_components (λ X, (@costructured_arrow.iso_mk _ _ _ _ _ _
    (costructured_arrow.mk (unop X).hom) (unop X) (iso.refl _) (by tidy)).op)
    (λ X Y f, quiver.hom.unop_inj $ begin ext, dsimp, simp end))
  (nat_iso.of_components (λ X, @structured_arrow.iso_mk _ _ _ _ _ _
    (structured_arrow.mk X.hom) X (iso.refl _) (by tidy))
    (λ X Y f, begin ext, dsimp, simp end))

end category_theory
