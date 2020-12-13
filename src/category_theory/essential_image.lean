import category_theory.natural_isomorphism

universes v₁ v₂ u₁ u₂

noncomputable theory

namespace category_theory

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D] {i : D ⥤ C}

namespace functor

/--
The essential image of a functor `i` consists of those objects in the target category which are
isomorphic to an object in the image of the function `i.obj`. In other words, this is the closure
under isomorphism of the function `i.obj`.
This is the "non-evil" way of describing the image of a functor.
-/
def ess_image (i : D ⥤ C) : set C := λ A, ∃ (B : D), nonempty (i.obj B ≅ A)

/-- Get the witnessing object that `A` is in the subcategory given by `i`. -/
def ess_image.witness {A : C} (h : A ∈ i.ess_image) : D := h.some

/-- Extract the isomorphism between `i.obj h.witness` and `A` itself. -/
def ess_image.get_iso {A : C} (h : A ∈ i.ess_image) : i.obj h.witness ≅ A :=
classical.choice h.some_spec

/--
The functor `i` is essentially surjective if every object of `C` is essentially in the image of `i`.

More explicitly, a functor `F : C ⥤ D` is essentially surjective if for every `d : D`, there is
some `c : C` so `F.obj c ≅ D`.

See https://stacks.math.columbia.edu/tag/001C.
-/
def ess_surjective (i : D ⥤ C) : Prop := ∀ A, A ∈ ess_image i

/-- Being in the subcategory is a "hygenic" property: it is preserved under isomorphism. -/
lemma ess_image.of_iso {A A' : C} (h : A ≅ A') (hA : A ∈ ess_image i) :
  A' ∈ ess_image i :=
hA.imp (λ B, nonempty.map (≪≫ h))

/-- If `A` is in the essential image of `i` then it is in the essential image of `i'`. -/
lemma ess_image.of_nat_iso {i' : D ⥤ C} (h : i ≅ i') {A : C} (hA : A ∈ ess_image i) :
  A ∈ ess_image i' :=
hA.imp (λ B, nonempty.map (λ t, h.symm.app B ≪≫ t))

/-- Isomorphic functors have equal essential images. -/
lemma image_eq_of_nat_iso {i' : D ⥤ C} (h : i ≅ i') :
  ess_image i = ess_image i' :=
begin
  ext A,
  split,
  { apply ess_image.of_nat_iso h },
  { apply ess_image.of_nat_iso h.symm },
end

lemma obj_mem_ess_image (i : D ⥤ C) (B : D) : i.obj B ∈ ess_image i := ⟨B, ⟨iso.refl _⟩⟩

-- TODO: move this and the next
lemma hom_comp_eq_id {X Y : C} (g : X ⟶ Y) [is_iso g] {f : Y ⟶ X} : g ≫ f = 𝟙 X ↔ f = inv g :=
iso.hom_comp_eq_id (as_iso g)

lemma comp_hom_eq_id {X Y : C} (g : X ⟶ Y) [is_iso g] {f : Y ⟶ X} : f ≫ g = 𝟙 Y ↔ f = inv g :=
iso.comp_hom_eq_id (as_iso g)

end functor

/--
A functor `F : C ⥤ D` is essentially surjective if for every `d : D`, there is some `c : C`
with `F.obj c ≅ D`.

See https://stacks.math.columbia.edu/tag/001C.
-/
class ess_surj (F : C ⥤ D) : Prop :=
(mem_ess_image [] (d : D) : d ∈ F.ess_image)

variables (F : C ⥤ D) [ess_surj F]

/-- Given an essentially surjective functor, we can find a preimage for every object `d` in the
    codomain. Applying the functor to this preimage will yield an object isomorphic to `d`, see
    `fun_obj_preimage_iso`. -/
def functor.obj_preimage (d : D) : C := (ess_surj.mem_ess_image F d).witness
/-- Applying an essentially surjective functor to a preimage of `d` yields an object that is
    isomorphic to `d`. -/
def functor.obj_obj_preimage_iso (d : D) : F.obj (F.obj_preimage d) ≅ d :=
(ess_surj.mem_ess_image F d).get_iso

end category_theory
