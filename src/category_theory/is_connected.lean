/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import data.list.chain
import category_theory.punit
import category_theory.sigma.basic
import category_theory.full_subcategory

/-!
# Connected category

Define a connected category as a _nonempty_ category for which every functor
to a discrete category is isomorphic to the constant functor.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

We give some equivalent definitions:
- A nonempty category for which every functor to a discrete category is
  constant on objects.
  See `any_functor_const_on_obj` and `connected.of_any_functor_const_on_obj`.
- A nonempty category for which every function `F` for which the presence of a
  morphism `f : j₁ ⟶ j₂` implies `F j₁ = F j₂` must be constant everywhere.
  See `constant_of_preserves_morphisms` and `connected.of_constant_of_preserves_morphisms`.
- A nonempty category for which any subset of its elements containing the
  default and closed under morphisms is everything.
  See `induct_on_objects` and `connected.of_induct`.
- A nonempty category for which every object is related under the reflexive
  transitive closure of the relation "there is a morphism in some direction
  from `j₁` to `j₂`".
  See `connected_zigzag` and `zigzag_connected`.
- A nonempty category for which for any two objects there is a sequence of
  morphisms (some reversed) from one to the other.
  See `exists_zigzag'` and `connected_of_zigzag`.

We also prove the result that the functor given by `(X × -)` preserves any
connected limit. That is, any limit of shape `J` where `J` is a connected
category is preserved by the functor `(X × -)`. This appears in `category_theory.limits.connected`.
-/

universes v₁ v₂ v₃ u₁ u₂

noncomputable theory

open category_theory.category

namespace category_theory

/--
A possibly empty category for which every functor to a discrete category is constant.
-/
class is_preconnected (J : Type u₁) [category.{v₁} J] : Prop :=
(iso_constant : Π {α : Type u₁} (F : J ⥤ discrete α) (j : J),
  nonempty (F ≅ (functor.const J).obj (F.obj j)))

/--
We define a connected category as a _nonempty_ category for which every
functor to a discrete category is constant.

NB. Some authors include the empty category as connected, we do not.
We instead are interested in categories with exactly one 'connected
component'.

This allows us to show that the functor X ⨯ - preserves connected limits.

See https://stacks.math.columbia.edu/tag/002S
-/
class is_connected (J : Type u₂) [category.{v₁} J] extends is_preconnected J : Prop :=
[is_nonempty : nonempty J]

attribute [instance, priority 100] is_connected.is_nonempty

variables {J : Type u₁} [category.{v₁} J]
variables {K : Type u₂} [category.{v₂} K]

/--
If `J` is connected, any functor `F : J ⥤ discrete α` is isomorphic to
the constant functor with value `F.obj j` (for any choice of `j`).
-/
def iso_constant [is_preconnected J] {α : Type u₁} (F : J ⥤ discrete α) (j : J) :
  F ≅ (functor.const J).obj (F.obj j) :=
  (is_preconnected.iso_constant F j).some

/--
If J is connected, any functor to a discrete category is constant on objects.
The converse is given in `is_connected.of_any_functor_const_on_obj`.
-/
lemma any_functor_const_on_obj [is_preconnected J]
  {α : Type u₁} (F : J ⥤ discrete α) (j j' : J) :
  F.obj j = F.obj j' :=
((iso_constant F j').hom.app j).down.1

/--
If any functor to a discrete category is constant on objects, J is connected.
The converse of `any_functor_const_on_obj`.
-/
lemma is_connected.of_any_functor_const_on_obj [nonempty J]
  (h : ∀ {α : Type u₁} (F : J ⥤ discrete α), ∀ (j j' : J), F.obj j = F.obj j') :
  is_connected J :=
{ iso_constant := λ α F j',
  ⟨nat_iso.of_components (λ j, eq_to_iso (h F j j')) (λ _ _ _, subsingleton.elim _ _)⟩ }

/--
If `J` is connected, then given any function `F` such that the presence of a
morphism `j₁ ⟶ j₂` implies `F j₁ = F j₂`, we have that `F` is constant.
This can be thought of as a local-to-global property.

The converse is shown in `is_connected.of_constant_of_preserves_morphisms`
-/
lemma constant_of_preserves_morphisms [is_preconnected J] {α : Type u₁} (F : J → α)
  (h : ∀ (j₁ j₂ : J) (f : j₁ ⟶ j₂), F j₁ = F j₂) (j j' : J) :
  F j = F j' :=
any_functor_const_on_obj { obj := F, map := λ _ _ f, eq_to_hom (h _ _ f) } j j'

/--
`J` is connected if: given any function `F : J → α` which is constant for any
`j₁, j₂` for which there is a morphism `j₁ ⟶ j₂`, then `F` is constant.
This can be thought of as a local-to-global property.

The converse of `constant_of_preserves_morphisms`.
-/
lemma is_connected.of_constant_of_preserves_morphisms [nonempty J]
  (h : ∀ {α : Type u₁} (F : J → α), (∀ {j₁ j₂ : J} (f : j₁ ⟶ j₂), F j₁ = F j₂) → (∀ j j' : J, F j = F j')) :
  is_connected J :=
is_connected.of_any_functor_const_on_obj (λ _ F, h F.obj (λ _ _ f, (F.map f).down.1))

/--
An inductive-like property for the objects of a connected category.
If the set `p` is nonempty, and `p` is closed under morphisms of `J`,
then `p` contains all of `J`.

The converse is given in `is_connected.of_induct`.
-/
lemma induct_on_objects [is_preconnected J] (p : set J) {j₀ : J} (h0 : j₀ ∈ p)
  (h1 : ∀ {j₁ j₂ : J} (f : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈ p) (j : J) :
  j ∈ p :=
begin
  injection (constant_of_preserves_morphisms (λ k, ulift.up (k ∈ p)) (λ j₁ j₂ f, _) j j₀) with i,
  rwa i,
  dsimp,
  exact congr_arg ulift.up (propext (h1 f)),
end

/--
If any maximal connected component containing some element j₀ of J is all of J, then J is connected.

The converse of `induct_on_objects`.
-/
lemma is_connected.of_induct [nonempty J]
  {j₀ : J} (h : ∀ (p : set J), j₀ ∈ p → (∀ {j₁ j₂ : J} (f : j₁ ⟶ j₂), j₁ ∈ p ↔ j₂ ∈ p) → ∀ (j : J), j ∈ p) :
  is_connected J :=
is_connected.of_constant_of_preserves_morphisms (λ α F a,
begin
  have w := h {j | F j = F j₀} rfl (λ _ _ f, by simp [a f]),
  dsimp at w,
  intros j j',
  rw [w j, w j'],
end)

/--
Another induction principle for `is_preconnected J`:
given a type family `Z : J → Sort*` and
a rule for transporting in *both* directions along a morphism in `J`,
we can transport an `x : Z j₀` to a point in `Z j` for any `j`.
-/
lemma is_preconnected_induction [is_preconnected J] (Z : J → Sort*)
  (h₁ : Π {j₁ j₂ : J} (f : j₁ ⟶ j₂), Z j₁ → Z j₂)
  (h₂ : Π {j₁ j₂ : J} (f : j₁ ⟶ j₂), Z j₂ → Z j₁)
  {j₀ : J} (x : Z j₀) (j : J) : nonempty (Z j) :=
(induct_on_objects {j | nonempty (Z j)} ⟨x⟩
  (λ j₁ j₂ f, ⟨by { rintro ⟨y⟩, exact ⟨h₁ f y⟩, }, by { rintro ⟨y⟩, exact ⟨h₂ f y⟩, }⟩) j : _)

/-- j₁ and j₂ are related by `zag` if there is a morphism between them. -/
@[reducible]
def zag (j₁ j₂ : J) : Prop := nonempty (j₁ ⟶ j₂) ∨ nonempty (j₂ ⟶ j₁)

lemma zag_symmetric : symmetric (@zag J _) :=
λ j₂ j₁ h, h.swap

/--
`j₁` and `j₂` are related by `zigzag` if there is a chain of
morphisms from `j₁` to `j₂`, with backward morphisms allowed.
-/
@[reducible]
def zigzag : J → J → Prop := relation.refl_trans_gen zag

lemma zigzag_symmetric : symmetric (@zigzag J _) :=
relation.refl_trans_gen.symmetric zag_symmetric

lemma zigzag_equivalence : _root_.equivalence (@zigzag J _) :=
(mk_equivalence _
    relation.reflexive_refl_trans_gen
    zigzag_symmetric
    relation.transitive_refl_trans_gen)

def zigzag.setoid (J : Type u₂) [category.{v₁} J] : setoid J :=
{ r := zigzag,
  iseqv := zigzag_equivalence }

lemma zigzag_obj_of_zigzag (F : J ⥤ K) {j₁ j₂ : J} (h : zigzag j₁ j₂) :
  zigzag (F.obj j₁) (F.obj j₂) :=
begin
  refine relation.refl_trans_gen_lift _ _ h,
  intros j k,
  exact or.imp (nonempty.map (λ f, F.map f)) (nonempty.map (λ f, F.map f))
end

lemma zag_of_zag_obj (F : J ⥤ K) [full F] {j₁ j₂ : J} (h : zag (F.obj j₁) (F.obj j₂)) :
  zag j₁ j₂ :=
begin
  apply or.imp _ _ h,
  apply nonempty.map _,
  apply F.preimage,
  apply nonempty.map _,
  apply F.preimage,
end
/-- Any equivalence relation containing (⟶) holds for all pairs of a connected category. -/
lemma equiv_relation [is_connected J] (r : J → J → Prop) (hr : _root_.equivalence r)
  (h : ∀ {j₁ j₂ : J} (f : j₁ ⟶ j₂), r j₁ j₂) :
  ∀ (j₁ j₂ : J), r j₁ j₂ :=
begin
  have z : ∀ (j : J), r (classical.arbitrary J) j :=
    induct_on_objects (λ k, r (classical.arbitrary J) k)
        (hr.1 (classical.arbitrary J)) (λ _ _ f, ⟨λ t, hr.2.2 t (h f), λ t, hr.2.2 t (hr.2.1 (h f))⟩),
  intros, apply hr.2.2 (hr.2.1 (z _)) (z _)
end

/-- In a connected category, any two objects are related by `zigzag`. -/
lemma is_connected_zigzag [is_connected J] (j₁ j₂ : J) : zigzag j₁ j₂ :=
equiv_relation _ zigzag_equivalence
  (λ _ _ f, relation.refl_trans_gen.single (or.inl (nonempty.intro f))) _ _

/--
If any two objects in an nonempty category are related by `zigzag`, the category is connected.
-/
lemma zigzag_is_connected [nonempty J] (h : ∀ (j₁ j₂ : J), zigzag j₁ j₂) : is_connected J :=
begin
  apply is_connected.of_induct,
  intros p hp hjp j,
  have: ∀ (j₁ j₂ : J), zigzag j₁ j₂ → (j₁ ∈ p ↔ j₂ ∈ p),
  { introv k,
    induction k with _ _ rt_zag zag,
    { refl },
    { rw k_ih,
      rcases zag with ⟨⟨_⟩⟩ | ⟨⟨_⟩⟩,
      apply hjp zag,
      apply (hjp zag).symm } },
  rwa this j (classical.arbitrary J) (h _ _)
end

lemma exists_zigzag' [is_connected J] (j₁ j₂ : J) :
  ∃ l, list.chain zag j₁ l ∧ list.last (j₁ :: l) (list.cons_ne_nil _ _) = j₂ :=
list.exists_chain_of_relation_refl_trans_gen (is_connected_zigzag _ _)

/--
If any two objects in an nonempty category are linked by a sequence of (potentially reversed)
morphisms, then J is connected.

The converse of `exists_zigzag'`.
-/
lemma is_connected_of_zigzag [nonempty J]
  (h : ∀ (j₁ j₂ : J), ∃ l, list.chain zag j₁ l ∧ list.last (j₁ :: l) (list.cons_ne_nil _ _) = j₂) :
  is_connected J :=
begin
  apply is_connected.of_induct,
  intros p d k j,
  obtain ⟨l, zags, lst⟩ := h j (classical.arbitrary J),
  apply list.chain.induction p l zags lst _ d,
  rintros _ _ (⟨⟨xy⟩⟩ | ⟨⟨yx⟩⟩),
  { exact (k xy).2 },
  { exact (k yx).1 }
end

/-- If `discrete α` is connected, then `α` is (type-)equivalent to `punit`. -/
def discrete_is_connected_equiv_punit {α : Type*} [is_connected (discrete α)] : α ≃ punit :=
discrete.equiv_of_equivalence
  { functor := functor.star α,
    inverse := discrete.functor (λ _, classical.arbitrary _),
    unit_iso := by { exact (iso_constant _ (classical.arbitrary _)), },
    counit_iso := functor.punit_ext _ _ }

variables {C : Type u₂} [category.{u₁} C]

/--
For objects `X Y : C`, any natural transformation `α : const X ⟶ const Y` from a connected
category must be constant.
This is the key property of connected categories which we use to establish properties about limits.
-/
lemma nat_trans_from_is_connected [is_preconnected J] {X Y : C}
  (α : (functor.const J).obj X ⟶ (functor.const J).obj Y) :
  ∀ (j j' : J), α.app j = (α.app j' : X ⟶ Y) :=
@constant_of_preserves_morphisms _ _ _
  (X ⟶ Y)
  (λ j, α.app j)
  (λ _ _ f, (by { have := α.naturality f, erw [id_comp, comp_id] at this, exact this.symm }))

instance [nonempty J] : faithful (functor.const J : C ⥤ _) :=
{ map_injective' := λ X Y f g e, nat_trans.congr_app e (classical.arbitrary J) }

instance [is_connected J] : full (functor.const J : C ⥤ _) :=
{ preimage := λ X Y f, f.app (classical.arbitrary J),
  witness' := λ X Y f,
  begin
    ext j,
    apply nat_trans_from_is_connected f (classical.arbitrary J) j,
  end }

variable (J)

def connected_components : Type u₁ := quotient (zigzag.setoid J)

@[derive category]
def component (j : connected_components J) : Type u₁ := {k : J // quotient.mk' k = j}

@[derive [full, faithful]]
def include_component (j) : component J j ⥤ J :=
full_subcategory_inclusion _

instance (j) : nonempty (component J j) :=
begin
  apply quotient.induction_on' j,
  intro k,
  refine ⟨⟨k, rfl⟩⟩,
end

lemma list.last_map {α β : Type*} (l : list α) (f : α → β) (hl : l ≠ []) :
  (l.map f).last (mt list.eq_nil_of_map_eq_nil hl) = f (l.last hl) :=
begin
  induction l generalizing hl,
  { exfalso, apply hl, refl },
  { cases l_tl,
    { simp },
    { simpa using l_ih } }
end

lemma list.last_pmap {α β : Type*} (p : α → Prop) (f : Π a, p a → β)
  (l : list α) (hl₁ : ∀ a ∈ l, p a) (hl₂ : l ≠ []) :
  (l.pmap f hl₁).last (mt list.pmap_eq_nil.1 hl₂) = f (l.last hl₂) (hl₁ _ (list.last_mem hl₂)) :=
begin
  induction l generalizing hl₁ hl₂,
  { exfalso, apply hl₂, refl },
  { cases l_tl,
    { simp },
    { apply l_ih } }
end

instance (j) : is_connected (component J j) :=
begin
  apply zigzag_is_connected,
  rintro ⟨j₁, hj₁⟩ ⟨j₂, rfl⟩,
  have h₁₂ : zigzag j₁ j₂ := quotient.exact' hj₁,
  rcases list.exists_chain_of_relation_refl_trans_gen h₁₂ with ⟨l, hl₁, hl₂⟩,
  let f : Π x, zigzag x j₂ → component J (quotient.mk' j₂) :=
    λ x h, subtype.mk x (quotient.sound' h),
  have hf : ∀ (a : J), a ∈ l → zigzag a j₂,
  { intros i hi,
    apply list.chain.induction' (λ t, zigzag t j₂) _ hl₁ hl₂ _ _ _ (or.inr hi),
    { intros j k, apply relation.refl_trans_gen.head },
    { apply relation.refl_trans_gen.refl } },
  let l' : list (component J (quotient.mk' j₂)),
  { exact l.pmap f hf, },
  have : list.chain zigzag (⟨j₁, hj₁⟩ : component J _) l',
  { induction l generalizing hl₁ hl₂ j₁ hf,
    { apply list.chain.nil },
    { have hl₃ := list.chain_cons.1 hl₁,
      apply list.chain.cons,
      { apply relation.refl_trans_gen.single,
        refine zag_of_zag_obj (include_component J _) _,
        apply hl₃.1 },
      { refine l_ih _ _ _ hl₃.2 _ _,
        { apply relation.refl_trans_gen.head (zag_symmetric hl₃.1) h₁₂ },
        { rwa list.last_cons_cons at hl₂ } } } },
  apply list.chain.induction (λ t, zigzag t (⟨j₂, rfl⟩ : component J _)) _ this _ _ _,
  { refine ⟨_, rfl⟩ },
  { have h : ∀ (a : J), a ∈ j₁ :: l → zigzag a j₂,
    { simpa [h₁₂] using hf },
    change (list.pmap f (j₁ :: l) h).last _ = _,
    erw list.last_pmap _ _ _ _ (list.cons_ne_nil _ _),
    apply subtype.ext,
    apply hl₂ },
  { intros _ _, apply relation.refl_trans_gen.trans },
  { apply relation.refl_trans_gen.refl },
end

@[derive category]
def decomposed := Σ j, component J j

def inclusion (j) : component J j ⥤ decomposed J := incl _

def forward : decomposed J ⥤ J :=
desc (λ i, include_component _ _)

instance : full (forward J) :=
{ preimage :=
  begin
    rintro ⟨j', X, hX⟩ ⟨k', Y, hY⟩ f,
    dsimp [forward] at f,
    have : j' = k',
      rw [← hX, ← hY, quotient.eq'],
      exact relation.refl_trans_gen.single (or.inl ⟨f⟩),
    subst this,
    refine sigma_hom.matched _ _ _ f,
  end,
  witness' :=
  begin
    rintro ⟨j', X, hX⟩ ⟨_, Y, rfl⟩ f,
    have : quotient.mk' Y = j',
    { rw [← hX, quotient.eq'],
      exact relation.refl_trans_gen.single (or.inr ⟨f⟩) },
    subst this,
    refl,
  end }

instance : faithful (forward J) :=
{ map_injective' :=
  begin
    rintro ⟨_, j, rfl⟩ ⟨_, k, hY⟩ ⟨_, _, _, f⟩ ⟨_, _, _, g⟩ e,
    change f = g at e,
    subst e,
  end }

instance : ess_surj (forward J) :=
{ obj_preimage := λ j, ⟨_, j, rfl⟩,
  iso' := λ j, iso.refl _ }

-- This gives that any category is equivalent to a disjoint union of connected categories.
instance : is_equivalence (forward J) := equivalence.equivalence_of_fully_faithfully_ess_surj _

@[simps]
def thingy (H F : decomposed J ⥤ C) :
  (H ⟶ F) ≅ Π j, (incl j ⋙ H ⟶ incl j ⋙ F) :=
{ hom := λ α j, whisker_left _ α,
  inv := joining _ _ }

def thingy_natural {H H' F F' : decomposed J ⥤ C} (α : H' ⟶ H) (β : F ⟶ F') (γ : H ⟶ F) :
  (thingy J H' F').hom (α ≫ γ ≫ β) = (λ j, whisker_left _ α ≫ (thingy J H F).hom γ j ≫ whisker_left _ β) :=
begin
  ext j X,
  refl,
end

end category_theory
