/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.punit
import category_theory.structured_arrow
import category_theory.is_connected
import category_theory.limits.yoneda
import category_theory.limits.types

/-!
# Final and initial functors

A functor `F : C ⥤ D` is final if for every `d : D`,
the comma category of morphisms `d ⟶ F.obj c` is connected.

Dually, a functor `F : C ⥤ D` is initial if for every `d : D`,
the comma category of morphisms `F.obj c ⟶ d` is connected.

We show that right adjoints are examples of final functors, while
left adjoints are examples of initial functors.

For final functors, we prove that the following three statements are equivalent:
1. `F : C ⥤ D` is final.
2. Every functor `G : D ⥤ E` has a colimit if and only if `F ⋙ G` does,
   and these colimits are isomorphic via `colimit.pre G F`.
3. `colimit (F ⋙ coyoneda.obj (op d)) ≅ punit`.

Starting at 1. we show (in `cocones_equiv`) that
the categories of cocones over `G : D ⥤ E` and over `F ⋙ G` are equivalent.
(In fact, via an equivalence which does not change the cocone point.)
This readily implies 2., as `comp_has_colimit`, `has_colimit_of_comp`, and `colimit_iso`.

From 2. we can specialize to `G = coyoneda.obj (op d)` to obtain 3., as `colimit_comp_coyoneda_iso`.

From 3., we prove 1. directly in `cofinal_of_colimit_comp_coyoneda_iso_punit`.

Dually, we prove that if a functor `F : C ⥤ D` is initial, then any functor `G : D ⥤ E` has a
limit if and only if `F ⋙ G` does, and these limits are isomorphic via `limit.pre G F`.


## Naming
There is some discrepancy in the literature about naming; some say 'cofinal' instead of 'final'.
The explanation for this is that the 'co' prefix here is *not* the usual category-theoretic one
indicating duality, but rather indicating the sense of "along with".

## Future work
Dualise condition 3 above and the implications 2 ⇒ 3 and 3 ⇒ 1 to initial functors.

## References
* https://stacks.math.columbia.edu/tag/09WN
* https://ncatlab.org/nlab/show/final+functor
* Borceux, Handbook of Categorical Algebra I, Section 2.11.
  (Note he reverses the roles of definition and main result relative to here!)
-/

noncomputable theory

universes v u

namespace category_theory

namespace functor

open opposite
open category_theory.limits

variables {C : Type v} [small_category C]
variables {D : Type v} [small_category D]

/--
A functor `F : C ⥤ D` is final if for every `d : D`, the comma category of morphisms `d ⟶ F.obj c`
is connected.

See <https://stacks.math.columbia.edu/tag/04E6>
-/
class final (F : C ⥤ D) : Prop :=
(out (d : D) : is_connected (structured_arrow d F))

attribute [instance] final.out

/--
A functor `F : C ⥤ D` is initial if for every `d : D`, the comma category of morphisms
`F.obj c ⟶ d` is connected.
-/
class initial (F : C ⥤ D) : Prop :=
(out (d : D) : is_connected (costructured_arrow F d))

attribute [instance] initial.out

instance final_op_of_initial (F : C ⥤ D) [initial F] : final F.op :=
{ out := λ d, is_connected_of_equivalent (costructured_arrow_op_equivalence F (unop d)) }

instance initial_op_of_final (F : C ⥤ D) [final F] : initial F.op :=
{ out := λ d, is_connected_of_equivalent (structured_arrow_op_equivalence F (unop d)) }

lemma final_of_initial_op (F : C ⥤ D) [initial F.op] : final F :=
{ out := λ d, @is_connected_of_is_connected_op _ _
  (is_connected_of_equivalent (structured_arrow_op_equivalence F d).symm) }

lemma initial_of_final_op (F : C ⥤ D) [final F.op] : initial F :=
{ out := λ d, @is_connected_of_is_connected_op _ _
  (is_connected_of_equivalent (costructured_arrow_op_equivalence F d).symm) }

/-- If a functor `R : D ⥤ C` is a right adjoint, it is final. -/
lemma final_of_adjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) : final R :=
{ out := λ c,
  let u : structured_arrow c R := structured_arrow.mk (adj.unit.app c) in
  @zigzag_is_connected _ _ ⟨u⟩ $ λ f g, relation.refl_trans_gen.trans
    (relation.refl_trans_gen.single (show zag f u, from
      or.inr ⟨structured_arrow.hom_mk ((adj.hom_equiv c f.right).symm f.hom) (by simp)⟩))
    (relation.refl_trans_gen.single (show zag u g, from
      or.inl ⟨structured_arrow.hom_mk ((adj.hom_equiv c g.right).symm g.hom) (by simp)⟩)) }

/-- If a functor `L : C ⥤ D` is a left adjoint, it is initial. -/
lemma initial_of_adjunction {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) : initial L :=
{ out := λ d,
  let u : costructured_arrow L d := costructured_arrow.mk (adj.counit.app d) in
  @zigzag_is_connected _ _ ⟨u⟩ $ λ f g, relation.refl_trans_gen.trans
    (relation.refl_trans_gen.single (show zag f u, from
      or.inl ⟨costructured_arrow.hom_mk (adj.hom_equiv f.left d f.hom) (by simp)⟩))
    (relation.refl_trans_gen.single (show zag u g, from
      or.inr ⟨costructured_arrow.hom_mk (adj.hom_equiv g.left d g.hom) (by simp)⟩)) }

@[priority 100]
instance final_of_is_right_adjoint (F : C ⥤ D) [h : is_right_adjoint F] : final F :=
final_of_adjunction h.adj

@[priority 100]
instance initial_of_is_left_adjoint (F : C ⥤ D) [h : is_left_adjoint F] : initial F :=
initial_of_adjunction h.adj

namespace final

variables (F : C ⥤ D) [final F]

instance (d : D) : nonempty (structured_arrow d F) := is_connected.is_nonempty

variables {E : Type u} [category.{v} E] (G : D ⥤ E)

/--
When `F : C ⥤ D` is cofinal, we denote by `lift F d` an arbitrary choice of object in `C` such that
there exists a morphism `d ⟶ F.obj (lift F d)`.
-/
def lift (d : D) : C :=
(classical.arbitrary (structured_arrow d F)).right

/--
When `F : C ⥤ D` is cofinal, we denote by `hom_to_lift` an arbitrary choice of morphism
`d ⟶ F.obj (lift F d)`.
-/
def hom_to_lift (d : D) : d ⟶ F.obj (lift F d) :=
(classical.arbitrary (structured_arrow d F)).hom

/--
We provide an induction principle for reasoning about `lift` and `hom_to_lift`.
We want to perform some construction (usually just a proof) about
the particular choices `lift F d` and `hom_to_lift F d`,
it suffices to perform that construction for some other pair of choices
(denoted `X₀ : C` and `k₀ : d ⟶ F.obj X₀` below),
and to show how to transport such a construction
*both* directions along a morphism between such choices.
-/
def induction {d : D} (Z : Π (X : C) (k : d ⟶ F.obj X), Sort*)
  (h₁ : Π X₁ X₂ (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂),
    (k₁ ≫ F.map f = k₂) → Z X₁ k₁ → Z X₂ k₂)
  (h₂ : Π X₁ X₂ (k₁ : d ⟶ F.obj X₁) (k₂ : d ⟶ F.obj X₂) (f : X₁ ⟶ X₂),
    (k₁ ≫ F.map f = k₂) → Z X₂ k₂ → Z X₁ k₁)
  {X₀ : C} {k₀ : d ⟶ F.obj X₀} (z : Z X₀ k₀) : Z (lift F d) (hom_to_lift F d) :=
begin
  apply nonempty.some,
  apply @is_preconnected_induction _ _ _
    (λ (Y : structured_arrow d F), Z Y.right Y.hom) _ _ { right := X₀, hom := k₀, } z,
  { intros j₁ j₂ f a, fapply h₁ _ _ _ _ f.right _ a, convert f.w.symm, dsimp, simp, },
  { intros j₁ j₂ f a, fapply h₂ _ _ _ _ f.right _ a, convert f.w.symm, dsimp, simp, },
end

variables {F G}

/--
Given a cocone over `F ⋙ G`, we can construct a `cocone G` with the same cocone point.
-/
@[simps]
def extend_cocone : cocone (F ⋙ G) ⥤ cocone G :=
{ obj := λ c,
  { X := c.X,
    ι :=
    { app := λ X, G.map (hom_to_lift F X) ≫ c.ι.app (lift F X),
      naturality' := λ X Y f,
      begin
        dsimp, simp,
        -- This would be true if we'd chosen `lift F X` to be `lift F Y`
        -- and `hom_to_lift F X` to be `f ≫ hom_to_lift F Y`.
        apply induction F
          (λ Z k, G.map f ≫ G.map (hom_to_lift F Y) ≫ c.ι.app (lift F Y) = G.map k ≫ c.ι.app Z),
        { intros Z₁ Z₂ k₁ k₂ g a z,
        rw [←a, functor.map_comp, category.assoc, ←functor.comp_map, c.w, z], },
        { intros Z₁ Z₂ k₁ k₂ g a z,
        rw [←a, functor.map_comp, category.assoc, ←functor.comp_map, c.w] at z,
        rw z, },
        { rw [←functor.map_comp_assoc], },
      end } },
  map := λ X Y f,
  { hom := f.hom, } }

@[simp]
lemma colimit_cocone_comp_aux (s : cocone (F ⋙ G)) (j : C) :
  G.map (hom_to_lift F (F.obj j)) ≫ s.ι.app (lift F (F.obj j)) =
    s.ι.app j :=
begin
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `hom_to_lift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F (λ X k, G.map k ≫ s.ι.app X = (s.ι.app j : _)),
  { intros j₁ j₂ k₁ k₂ f w h, rw ←w, rw ← s.w f at h, simpa using h, },
  { intros j₁ j₂ k₁ k₂ f w h, rw ←w at h, rw ← s.w f, simpa using h, },
  { exact s.w (𝟙 _), },
end

variables (F G)

/--
If `F` is cofinal,
the category of cocones on `F ⋙ G` is equivalent to the category of cocones on `G`,
for any `G : D ⥤ E`.
-/
@[simps]
def cocones_equiv : cocone (F ⋙ G) ≌ cocone G :=
{ functor := extend_cocone,
  inverse := cocones.whiskering F,
  unit_iso := nat_iso.of_components (λ c, cocones.ext (iso.refl _) (by tidy)) (by tidy),
  counit_iso := nat_iso.of_components (λ c, cocones.ext (iso.refl _) (by tidy)) (by tidy), }.

variables {G}

/--
When `F : C ⥤ D` is cofinal, and `t : cocone G` for some `G : D ⥤ E`,
`t.whisker F` is a colimit cocone exactly when `t` is.
-/
def is_colimit_whisker_equiv (t : cocone G) : is_colimit (t.whisker F) ≃ is_colimit t :=
is_colimit.of_cocone_equiv (cocones_equiv F G).symm

/--
When `F` is cofinal, and `t : cocone (F ⋙ G)`,
`extend_cocone.obj t` is a colimit coconne exactly when `t` is.
-/
def is_colimit_extend_cocone_equiv (t : cocone (F ⋙ G)) :
  is_colimit (extend_cocone.obj t) ≃ is_colimit t :=
is_colimit.of_cocone_equiv (cocones_equiv F G)

/-- Given a colimit cocone over `G : D ⥤ E` we can construct a colimit cocone over `F ⋙ G`. -/
@[simps]
def colimit_cocone_comp (t : colimit_cocone G) :
  colimit_cocone (F ⋙ G) :=
{ cocone := _,
  is_colimit := (is_colimit_whisker_equiv F _).symm (t.is_colimit) }

@[priority 100]
instance comp_has_colimit [has_colimit G] :
  has_colimit (F ⋙ G) :=
has_colimit.mk (colimit_cocone_comp F (get_colimit_cocone G))

lemma colimit_pre_is_iso_aux {t : cocone G} (P : is_colimit t) :
  ((is_colimit_whisker_equiv F _).symm P).desc (t.whisker F) = 𝟙 t.X :=
begin
  dsimp [is_colimit_whisker_equiv],
  apply P.hom_ext,
  intro j,
  dsimp, simp, dsimp, simp, -- See library note [dsimp, simp].
end

instance colimit_pre_is_iso [has_colimit G] :
  is_iso (colimit.pre G F) :=
begin
  rw colimit.pre_eq (colimit_cocone_comp F (get_colimit_cocone G)) (get_colimit_cocone G),
  erw colimit_pre_is_iso_aux,
  dsimp,
  apply_instance,
end

section
variables (G)

/--
When `F : C ⥤ D` is cofinal, and `G : D ⥤ E` has a colimit, then `F ⋙ G` has a colimit also and
`colimit (F ⋙ G) ≅ colimit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def colimit_iso [has_colimit G] : colimit (F ⋙ G) ≅ colimit G := as_iso (colimit.pre G F)

end

/-- Given a colimit cocone over `F ⋙ G` we can construct a colimit cocone over `G`. -/
@[simps]
def colimit_cocone_of_comp (t : colimit_cocone (F ⋙ G)) :
  colimit_cocone G :=
{ cocone := extend_cocone.obj t.cocone,
  is_colimit := (is_colimit_extend_cocone_equiv F _).symm (t.is_colimit), }

/--
When `F` is cofinal, and `F ⋙ G` has a colimit, then `G` has a colimit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_has_colimit`.)
-/
lemma has_colimit_of_comp [has_colimit (F ⋙ G)] :
  has_colimit G :=
has_colimit.mk (colimit_cocone_of_comp F (get_colimit_cocone (F ⋙ G)))


section
local attribute [instance] has_colimit_of_comp

/--
When `F` is cofinal, and `F ⋙ G` has a colimit, then `G` has a colimit also and
`colimit (F ⋙ G) ≅ colimit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def colimit_iso' [has_colimit (F ⋙ G)] : colimit (F ⋙ G) ≅ colimit G := as_iso (colimit.pre G F)


end

/--
If the universal morphism `colimit (F ⋙ coyoneda.obj (op d)) ⟶ colimit (coyoneda.obj (op d))`
is an isomorphism (as it always is when `F` is cofinal),
then `colimit (F ⋙ coyoneda.obj (op d)) ≅ punit`
(simply because `colimit (coyoneda.obj (op d)) ≅ punit`).
-/
def colimit_comp_coyoneda_iso (d : D) [is_iso (colimit.pre (coyoneda.obj (op d)) F)] :
  colimit (F ⋙ coyoneda.obj (op d)) ≅ punit :=
as_iso (colimit.pre (coyoneda.obj (op d)) F) ≪≫ coyoneda.colimit_coyoneda_iso (op d)

lemma zigzag_of_eqv_gen_quot_rel {F : C ⥤ D} {d : D} {f₁ f₂ : Σ X, d ⟶ F.obj X}
  (t : eqv_gen (types.quot.rel.{v v} (F ⋙ coyoneda.obj (op d))) f₁ f₂) :
  zigzag (structured_arrow.mk f₁.2) (structured_arrow.mk f₂.2) :=
begin
  induction t,
  case eqv_gen.rel : x y r
  { obtain ⟨f, w⟩ := r,
    fconstructor,
    swap 2, fconstructor,
    left, fsplit,
    exact { right := f, } },
  case eqv_gen.refl
  { fconstructor, },
  case eqv_gen.symm : x y h ih
  { apply zigzag_symmetric,
    exact ih, },
  case eqv_gen.trans : x y z h₁ h₂ ih₁ ih₂
  { apply relation.refl_trans_gen.trans,
    exact ih₁, exact ih₂, }
end

/--
If `colimit (F ⋙ coyoneda.obj (op d)) ≅ punit` for all `d : D`, then `F` is cofinal.
-/
lemma cofinal_of_colimit_comp_coyoneda_iso_punit
  (I : Π d, colimit (F ⋙ coyoneda.obj (op d)) ≅ punit) : final F :=
⟨λ d, begin
  haveI : nonempty (structured_arrow d F),
  { have := (I d).inv punit.star,
    obtain ⟨j, y, rfl⟩ := limits.types.jointly_surjective'.{v v} this,
    exact ⟨structured_arrow.mk y⟩, },
  apply zigzag_is_connected,
  rintros ⟨⟨⟩,X₁,f₁⟩ ⟨⟨⟩,X₂,f₂⟩,
  dsimp at *,
  let y₁ := colimit.ι (F ⋙ coyoneda.obj (op d)) X₁ f₁,
  let y₂ := colimit.ι (F ⋙ coyoneda.obj (op d)) X₂ f₂,
  have e : y₁ = y₂,
  { apply (I d).to_equiv.injective, ext, },
  have t := types.colimit_eq.{v v} e,
  clear e y₁ y₂,
  exact zigzag_of_eqv_gen_quot_rel t,
end⟩

end final


namespace initial

variables (F : C ⥤ D) [initial F]

instance (d : D) : nonempty (costructured_arrow F d) := is_connected.is_nonempty

variables {E : Type u} [category.{v} E] (G : D ⥤ E)

/--
When `F : C ⥤ D` is initial, we denote by `lift F d` an arbitrary choice of object in `C` such that
there exists a morphism `F.obj (lift F d) ⟶ d`.
-/
def lift (d : D) : C := (classical.arbitrary (costructured_arrow F d)).left

/--
When `F : C ⥤ D` is initial, we denote by `hom_to_lift` an arbitrary choice of morphism
`F.obj (lift F d) ⟶ d`.
-/
def hom_to_lift (d : D) : F.obj (lift F d) ⟶ d :=
  (classical.arbitrary (costructured_arrow F d)).hom

/--
We provide an induction principle for reasoning about `lift` and `hom_to_lift`.
We want to perform some construction (usually just a proof) about
the particular choices `lift F d` and `hom_to_lift F d`,
it suffices to perform that construction for some other pair of choices
(denoted `X₀ : C` and `k₀ : F.obj X₀ ⟶ d` below),
and to show how to transport such a construction
*both* directions along a morphism between such choices.
-/
def induction {d : D} (Z : Π (X : C) (k : F.obj X ⟶ d), Sort*)
  (h₁ : Π X₁ X₂ (k₁ : F.obj X₁ ⟶ d) (k₂ : F.obj X₂ ⟶ d) (f : X₁ ⟶ X₂),
    (F.map f ≫ k₂ = k₁) → Z X₁ k₁ → Z X₂ k₂)
  (h₂ : Π X₁ X₂ (k₁ : F.obj X₁ ⟶ d) (k₂ : F.obj X₂ ⟶ d) (f : X₁ ⟶ X₂),
    (F.map f ≫ k₂ = k₁) → Z X₂ k₂ → Z X₁ k₁)
  {X₀ : C} {k₀ : F.obj X₀ ⟶ d} (z : Z X₀ k₀) : Z (lift F d) (hom_to_lift F d) :=
begin
  apply nonempty.some,
  apply @is_preconnected_induction _ _ _
    (λ Y : costructured_arrow F d, Z Y.left Y.hom) _ _ { left := X₀, hom := k₀ } z,
  { intros j₁ j₂ f a, fapply h₁ _ _ _ _ f.left _ a, convert f.w, dsimp, simp, },
  { intros j₁ j₂ f a, fapply h₂ _ _ _ _ f.left _ a, convert f.w, dsimp, simp, },
end

variables {F G}

/--
Given a cone over `F ⋙ G`, we can construct a `cone G` with the same cocone point.
-/
@[simps]
def extend_cone : cone (F ⋙ G) ⥤ cone G :=
{ obj := λ c,
  { X := c.X,
    π :=
    { app := λ d, c.π.app (lift F d) ≫ G.map (hom_to_lift F d),
      naturality' := λ X Y f,
      begin
        dsimp, simp,
        -- This would be true if we'd chosen `lift F Y` to be `lift F X`
        -- and `hom_to_lift F Y` to be `hom_to_lift F X ≫ f`.
        apply induction F (λ Z k, (c.π.app Z ≫ G.map k : c.X ⟶ _) =
          c.π.app (lift F X) ≫ G.map (hom_to_lift F X) ≫ G.map f),
        { intros Z₁ Z₂ k₁ k₂ g a z,
        rw [←a, functor.map_comp, ←functor.comp_map, ←category.assoc, ←category.assoc, c.w] at z,
        rw [z, category.assoc] },
        { intros Z₁ Z₂ k₁ k₂ g a z,
        rw [←a, functor.map_comp, ←functor.comp_map, ←category.assoc, ←category.assoc,
          c.w, z, category.assoc] },
        { rw [←functor.map_comp], },
      end } },
  map := λ X Y f,
  { hom := f.hom, } }

@[simp]
lemma limit_cone_comp_aux (s : cone (F ⋙ G)) (j : C) :
  s.π.app (lift F (F.obj j)) ≫ G.map (hom_to_lift F (F.obj j)) =
    s.π.app j :=
begin
  -- This point is that this would be true if we took `lift (F.obj j)` to just be `j`
  -- and `hom_to_lift (F.obj j)` to be `𝟙 (F.obj j)`.
  apply induction F (λ X k, s.π.app X ≫ G.map k = (s.π.app j : _)),
  { intros j₁ j₂ k₁ k₂ f w h, rw ←s.w f, rw ←w at h, simpa using h, },
  { intros j₁ j₂ k₁ k₂ f w h, rw ←s.w f at h, rw ←w, simpa using h, },
  { exact s.w (𝟙 _), },
end

variables (F G)

/--
If `F` is initial,
the category of cones on `F ⋙ G` is equivalent to the category of cones on `G`,
for any `G : D ⥤ E`.
-/
@[simps]
def cones_equiv : cone (F ⋙ G) ≌ cone G :=
{ functor := extend_cone,
  inverse := cones.whiskering F,
  unit_iso := nat_iso.of_components (λ c, cones.ext (iso.refl _) (by tidy)) (by tidy),
  counit_iso := nat_iso.of_components (λ c, cones.ext (iso.refl _) (by tidy)) (by tidy), }.

variables {G}

/--
When `F : C ⥤ D` is initial, and `t : cone G` for some `G : D ⥤ E`,
`t.whisker F` is a limit cone exactly when `t` is.
-/
def is_limit_whisker_equiv (t : cone G) : is_limit (t.whisker F) ≃ is_limit t :=
is_limit.of_cone_equiv (cones_equiv F G).symm

/--
When `F` is initial, and `t : cone (F ⋙ G)`,
`extend_cone.obj t` is a limit cone exactly when `t` is.
-/
def is_limit_extend_cone_equiv (t : cone (F ⋙ G)) :
  is_limit (extend_cone.obj t) ≃ is_limit t :=
is_limit.of_cone_equiv (cones_equiv F G)

/-- Given a limit cone over `G : D ⥤ E` we can construct a limit cone over `F ⋙ G`. -/
@[simps]
def limit_cone_comp (t : limit_cone G) :
  limit_cone (F ⋙ G) :=
{ cone := _,
  is_limit := (is_limit_whisker_equiv F _).symm (t.is_limit) }

@[priority 100]
instance comp_has_limit [has_limit G] :
  has_limit (F ⋙ G) :=
has_limit.mk (limit_cone_comp F (get_limit_cone G))

lemma limit_pre_is_iso_aux {t : cone G} (P : is_limit t) :
  ((is_limit_whisker_equiv F _).symm P).lift (t.whisker F) = 𝟙 t.X :=
begin
  dsimp [is_limit_whisker_equiv],
  apply P.hom_ext,
  intro j,
  simp,
end

instance limit_pre_is_iso [has_limit G] :
  is_iso (limit.pre G F) :=
begin
  rw limit.pre_eq (limit_cone_comp F (get_limit_cone G)) (get_limit_cone G),
  erw limit_pre_is_iso_aux,
  dsimp,
  apply_instance,
end

section
variables (G)

/--
When `F : C ⥤ D` is initial, and `G : D ⥤ E` has a limit, then `F ⋙ G` has a limit also and
`limit (F ⋙ G) ≅ limit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def limit_iso [has_limit G] : limit (F ⋙ G) ≅ limit G := (as_iso (limit.pre G F)).symm

end

/-- Given a limit cone over `F ⋙ G` we can construct a limit cone over `G`. -/
@[simps]
def limit_cone_of_comp (t : limit_cone (F ⋙ G)) :
  limit_cone G :=
{ cone := extend_cone.obj t.cone,
  is_limit := (is_limit_extend_cone_equiv F _).symm (t.is_limit), }

/--
When `F` is initial, and `F ⋙ G` has a limit, then `G` has a limit also.

We can't make this an instance, because `F` is not determined by the goal.
(Even if this weren't a problem, it would cause a loop with `comp_has_limit`.)
-/
lemma has_limit_of_comp [has_limit (F ⋙ G)] :
  has_limit G :=
has_limit.mk (limit_cone_of_comp F (get_limit_cone (F ⋙ G)))

section
local attribute [instance] has_limit_of_comp

/--
When `F` is initial, and `F ⋙ G` has a limit, then `G` has a limit also and
`limit (F ⋙ G) ≅ limit G`

https://stacks.math.columbia.edu/tag/04E7
-/
def limit_iso' [has_limit (F ⋙ G)] : limit (F ⋙ G) ≅ limit G :=
(as_iso (limit.pre G F)).symm

end

end initial

end functor

end category_theory
