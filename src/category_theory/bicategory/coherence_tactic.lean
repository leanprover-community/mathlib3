/-
Copyright (c) 2022. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yuma Mizuno, Oleksandr Manzyuk
-/
import category_theory.bicategory.coherence

/-!
# A `coherence` tactic for bicategorical categories, and `⊗≫` (composition up to associators)

We provide a `coherence` tactic,
which proves that any two morphisms (with the same source and target)
in a bicategorical category which are built out of associators and unitors
are equal.

We also provide `f ⊗≫ g`, the `bicategorical_comp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.
-/

noncomputable theory

universes w v u

open category_theory
open category_theory.free_bicategory
open_locale bicategory

variables {B : Type u} [bicategory.{w v} B] {a b c d e : B}

namespace category_theory.bicategory

/-- A typeclass carrying a choice of lift of a 1-morphism from `B` to `free_bicategory B`. -/
class lift_hom {a b : B} (f : a ⟶ b) :=
(lift : of.obj a ⟶ of.obj b)

instance lift_hom_id : lift_hom (𝟙 a) := { lift := 𝟙 (of.obj a), }
instance lift_hom_comp (f : a ⟶ b) (g : b ⟶ c) [lift_hom f] [lift_hom g] : lift_hom (f ≫ g) :=
{ lift := lift_hom.lift f ≫ lift_hom.lift g, }
@[priority 100]
instance lift_hom_of (f : a ⟶ b) : lift_hom f := { lift := of.map f, }

/-- A typeclass carrying a choice of lift of a 2-morphism from `B` to `free_bicategory B`. -/
class lift_hom₂ {f g : a ⟶ b} [lift_hom f] [lift_hom g] (η : f ⟶ g) :=
(lift : lift_hom.lift f ⟶ lift_hom.lift g)

instance lift_hom₂_id (f : a ⟶ b) [lift_hom f] : lift_hom₂ (𝟙 f) :=
{ lift := 𝟙 _, }
instance lift_hom₂_left_unitor_hom (f : a ⟶ b) [lift_hom f] : lift_hom₂ (λ_ f).hom :=
{ lift := (λ_ (lift_hom.lift f)).hom, }
instance lift_hom₂_left_unitor_inv (f : a ⟶ b) [lift_hom f] : lift_hom₂ (λ_ f).inv :=
{ lift := (λ_ (lift_hom.lift f)).inv, }
instance lift_hom₂_right_unitor_hom (f : a ⟶ b) [lift_hom f] : lift_hom₂ (ρ_ f).hom :=
{ lift := (ρ_ (lift_hom.lift f)).hom, }
instance lift_hom₂_right_unitor_inv (f : a ⟶ b) [lift_hom f] : lift_hom₂ (ρ_ f).inv :=
{ lift := (ρ_ (lift_hom.lift f)).inv, }
instance lift_hom₂_associator_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  [lift_hom f] [lift_hom g] [lift_hom h] :
  lift_hom₂ (α_ f g h).hom :=
{ lift := (α_ (lift_hom.lift f) (lift_hom.lift g) (lift_hom.lift h)).hom, }
instance lift_hom₂_associator_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d)
  [lift_hom f] [lift_hom g] [lift_hom h] :
  lift_hom₂ (α_ f g h).inv :=
{ lift := (α_ (lift_hom.lift f) (lift_hom.lift g) (lift_hom.lift h)).inv, }
instance lift_hom₂_comp {f g h : a ⟶ b} [lift_hom f] [lift_hom g] [lift_hom h] (η : f ⟶ g) (θ : g ⟶ h)
  [lift_hom₂ η] [lift_hom₂ θ] : lift_hom₂ (η ≫ θ) :=
{ lift := lift_hom₂.lift η ≫ lift_hom₂.lift θ }
instance lift_hom₂_whisker_left (f : a ⟶ b) [lift_hom f] {g h : b ⟶ c} (η : g ⟶ h)
  [lift_hom g] [lift_hom h] [lift_hom₂ η] : lift_hom₂ (f ◁ η) :=
{ lift := lift_hom.lift f ◁ lift_hom₂.lift η }
instance lift_hom₂_whisker_right {f g : a ⟶ b} (η : f ⟶ g) [lift_hom f] [lift_hom g] [lift_hom₂ η]
  {h : b ⟶ c} [lift_hom h] : lift_hom₂ (η ▷ h) :=
{ lift := lift_hom₂.lift η ▷ lift_hom.lift h }

-- We could likely turn this into a `Prop` valued existential if that proves useful.
class bicategorical_coherence (f g : a ⟶ b) [lift_hom f] [lift_hom g] :=
(lift_nonempty [] : nonempty (lift_hom.lift f ⟶ lift_hom.lift g))
--[is_iso : is_iso hom . tactic.apply_instance]

def bicategorical_coherence.lift (f g : a ⟶ b) [lift_hom f] [lift_hom g]
  [bicategorical_coherence f g] : lift_hom.lift f ⟶ lift_hom.lift g :=
classical.choice (bicategorical_coherence.lift_nonempty f g)

@[simp]
lemma lift_of_eq_self (f : a ⟶ b) : (free_bicategory.lift (prefunctor.id B)).map (lift_hom.lift f) = f :=
rfl

def bicategorical_coherence.hom (f g : a ⟶ b) [lift_hom f] [lift_hom g]
  [bicategorical_coherence f g] : f ⟶ g :=
begin
  sorry
end
-- eq_to_hom (lift_of_eq_self f).symm ≫
--   (free_bicategory.lift (prefunctor.id B)).map₂ (bicategorical_coherence.lift f g) ≫
--     eq_to_hom (lift_of_eq_self g)

instance is_iso (f g : a ⟶ b) [lift_hom f] [lift_hom g]
  [bicategorical_coherence f g] : is_iso (bicategorical_coherence.hom f g) :=
{ out := begin
  fsplit,
  refine eq_to_hom (lift_of_eq_self g).symm ≫
  (free_bicategory.lift (prefunctor.id B)).map₂ _ ≫
    eq_to_hom (lift_of_eq_self f),
  refine groupoid.inv _,
  refine bicategorical_coherence.lift f g,
  fsplit,
  dsimp only [eq_to_hom_refl, bicategorical_coherence.hom],
  simp only [category.comp_id, category.id_comp],
  change ((free_bicategory.lift (prefunctor.id B)).map_functor _ _).map (bicategorical_coherence.lift f g) ≫
    ((free_bicategory.lift (prefunctor.id B)).map_functor _ _).map (groupoid.inv $ bicategorical_coherence.lift f g) = 𝟙 f,
  rw [←functor.map_comp],
  rw groupoid.comp_inv,
  rw [category_theory.functor.map_id],
  refl,
  dsimp only [eq_to_hom_refl, bicategorical_coherence.hom],
  simp only [category.comp_id, category.id_comp],
  change ((free_bicategory.lift (prefunctor.id B)).map_functor _ _).map (groupoid.inv $ bicategorical_coherence.lift f g) ≫
    ((free_bicategory.lift (prefunctor.id B)).map_functor _ _).map (bicategorical_coherence.lift f g) = 𝟙 g,
  rw [←functor.map_comp],
  rw groupoid.inv_comp,
  rw [category_theory.functor.map_id],
  refl,
end }

--attribute [instance] bicategorical_coherence.is_iso

namespace bicategorical_coherence

@[simps]
instance refl (f : a ⟶ b) [lift_hom f] : bicategorical_coherence f f := ⟨⟨𝟙 _⟩⟩

@[simps]
instance whisker_left
  (f : a ⟶ b) (g h : b ⟶ c) [lift_hom f] [lift_hom g] [lift_hom h] [bicategorical_coherence g h] :
  bicategorical_coherence (f ≫ g) (f ≫ h) :=
⟨⟨lift_hom.lift f ◁ bicategorical_coherence.lift g h⟩⟩

@[simps]
instance whisker_right
  (f g : a ⟶ b) (h : b ⟶ c) [lift_hom f] [lift_hom g] [lift_hom h] [bicategorical_coherence f g] :
  bicategorical_coherence (f ≫ h) (g ≫ h) :=
⟨bicategorical_coherence.hom f g ▷ h⟩

@[simps]
instance tensor_right (f : a ⟶ b) (g : b ⟶ b) [lift_hom f] [lift_hom g]
  [bicategorical_coherence (𝟙 b) g] :
  bicategorical_coherence f (f ≫ g) :=
⟨(ρ_ f).inv ≫ (f ◁ bicategorical_coherence.hom (𝟙 b) g)⟩

@[simps]
instance tensor_right' (f : a ⟶ b) (g : b ⟶ b) [lift_hom f] [lift_hom g]
  [bicategorical_coherence g (𝟙 b)] :
  bicategorical_coherence (f ≫ g) f :=
⟨(f ◁ bicategorical_coherence.hom g (𝟙 b)) ≫ (ρ_ f).hom⟩

@[simps]
instance left (f g : a ⟶ b) [lift_hom f] [lift_hom g] [bicategorical_coherence f g] :
  bicategorical_coherence (𝟙 a ≫ f) g :=
⟨(λ_ f).hom ≫ bicategorical_coherence.hom f g⟩

@[simps]
instance left' (f g : a ⟶ b) [lift_hom f] [lift_hom g] [bicategorical_coherence f g] :
  bicategorical_coherence f (𝟙 a ≫ g) :=
⟨bicategorical_coherence.hom f g ≫ (λ_ g).inv⟩

@[simps]
instance right (f g : a ⟶ b) [lift_hom f] [lift_hom g] [bicategorical_coherence f g] :
  bicategorical_coherence (f ≫ 𝟙 b) g :=
⟨(ρ_ f).hom ≫ bicategorical_coherence.hom f g⟩

@[simps]
instance right' (f g : a ⟶ b) [lift_hom f] [lift_hom g] [bicategorical_coherence f g] :
  bicategorical_coherence f (g ≫ 𝟙 b) :=
⟨bicategorical_coherence.hom f g ≫ (ρ_ g).inv⟩

@[simps]
instance assoc (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d)
  [lift_hom f] [lift_hom g] [lift_hom h] [lift_hom i] [bicategorical_coherence (f ≫ (g ≫ h)) i] :
  bicategorical_coherence ((f ≫ g) ≫ h) i :=
⟨(α_ f g h).hom ≫ bicategorical_coherence.hom (f ≫ (g ≫ h)) i⟩

@[simps]
instance assoc' (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d)
  [lift_hom f] [lift_hom g] [lift_hom h] [lift_hom i] [bicategorical_coherence i (f ≫ (g ≫ h))] :
  bicategorical_coherence i ((f ≫ g) ≫ h) :=
⟨bicategorical_coherence.hom i (f ≫ (g ≫ h)) ≫ (α_ f g h).inv⟩

example (f : a ⟶ b) : bicategorical_coherence f ((f ≫ 𝟙 b) ≫ 𝟙 b) :=
by apply_instance

example (f : a ⟶ b) : bicategorical_coherence f (f ≫ 𝟙 b ≫ 𝟙 b) :=
by apply_instance

example (f : a ⟶ b) : bicategorical_coherence ((𝟙 a ≫ 𝟙 a ≫ 𝟙 a) ≫ f) (((f ≫ 𝟙 b) ≫ 𝟙 b) ≫ 𝟙 b) :=
by apply_instance

end bicategorical_coherence

/-- Construct an isomorphism between two objects in a bicategorical category
out of unitors and associators. -/
def bicategorical_iso (f g : a ⟶ b) [lift_hom f] [lift_hom g] [bicategorical_coherence f g] :
  f ≅ g :=
as_iso (bicategorical_coherence.hom f g)

/-- Compose two morphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
def bicategorical_comp {f g h i : a ⟶ b} [lift_hom g] [lift_hom h]
  [bicategorical_coherence g h] (η : f ⟶ g) (θ : h ⟶ i) : f ⟶ i :=
η ≫ bicategorical_coherence.hom g h ≫ θ

localized "infixr ` ⊗≫ `:80 := category_theory.bicategory.bicategorical_comp"
  in bicategory -- type as \ot \gg

/-- Compose two isomorphisms in a bicategorical category,
inserting unitors and associators between as necessary. -/
def bicategorical_iso_comp {f g h i : a ⟶ b} [lift_hom g] [lift_hom h]
  [bicategorical_coherence g h] (η : f ≅ g) (θ : h ≅ i) : f ≅ i :=
η ≪≫ as_iso (bicategorical_coherence.hom g h) ≪≫ θ

localized "infixr ` ≪⊗≫ `:80 := category_theory.bicategory.bicategorical_iso_comp"
  in bicategory -- type as \ot \gg

example {f' : a ⟶ d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {h' : a ⟶ d}
  (η : f' ⟶ f ≫ (g ≫ h)) (θ : (f ≫ g) ≫ h ⟶ h') : f' ⟶ h' := η ⊗≫ θ

-- To automatically insert unitors/associators at the beginning or end,
-- you can use `f ⊗≫ 𝟙 _`
example {f' : a ⟶ d } {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} (η : f' ⟶ (f ≫ g) ≫ h) :
  f' ⟶ f ≫ (g ≫ h) := η ⊗≫ 𝟙 _

@[simp] lemma bicategorical_comp_refl {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
  η ⊗≫ θ = η ≫ θ :=
by { dsimp [bicategorical_comp], simp, }

@[simp] lemma comp_id_of_lift {f g : a ⟶ b} [lift_hom f] [lift_hom g] (η : f ⟶ g) [lift_hom₂ η] :
  η ≫ bicategorical_coherence.hom g g = η :=
by { dsimp [bicategorical_comp], simp, }

@[simp] lemma id_comp_of_lift {f g : a ⟶ b} [lift_hom f] [lift_hom g] (η : f ⟶ g)
  [lift_hom₂ η] :
  bicategorical_coherence.hom f f ≫ η = η :=
by { dsimp [bicategorical_comp], simp, }

end category_theory.bicategory

open category_theory.bicategory

namespace tactic

open tactic
setup_tactic_parser

/-- Coherence tactic for bicategorical categories. -/
meta def bicategorical_coherence : tactic unit :=
do
  `(%%lhs = %%rhs) ← target,
  to_expr  ``((free_bicategory.lift (prefunctor.id _)).map₂ (lift_hom₂.lift %%lhs) =
    (free_bicategory.lift (prefunctor.id _)).map₂ (lift_hom₂.lift %%rhs))
    >>= tactic.change,
  congr

/--
`coherence` uses the coherence theorem for bicategorical categories to prove the goal.
It can prove any equality made up only of associators and unitors.
```lean
example {C : Type} [category C] [bicategorical_category C] :
  (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
by coherence
```
-/
-- TODO: provide the `bicategory_coherence` tactic, and add that here.
meta def pure_coherence : tactic unit := bicategorical_coherence

example (f : a ⟶ b) (g : b ⟶ c) :
  (f ◁ (λ_ g).inv) ≫ (α_ f (𝟙 b) g).inv = (ρ_ f).inv ▷ g :=
by pure_coherence

example :
  (λ_ $ 𝟙 a).hom = (ρ_ $ 𝟙 a).hom :=
by pure_coherence

namespace coherence

/--
Auxiliary simp lemma for the `coherence` tactic:
this move brackets to the left in order to expose a maximal prefix
built out of unitors and associators.
-/
lemma assoc_lift_hom₂ {f g h i : a ⟶ b} [lift_hom f] [lift_hom g] [lift_hom h]
  (η : f ⟶ g) (θ : g ⟶ h) (ι : h ⟶ i) [lift_hom₂ η] [lift_hom₂ θ] :
  η ≫ (θ ≫ ι) = (η ≫ θ) ≫ ι :=
(category.assoc _ _ _).symm


meta def assoc_simps : tactic unit :=
`[simp only [
  bicategory.bicategorical_comp,
  category.assoc,
  bicategory.comp_whisker_left,
  bicategory.id_whisker_left,
  bicategory.whisker_right_comp, bicategory.whisker_right_id,
  bicategory.whisker_left_comp,
  bicategory.whisker_left_id,
  bicategory.comp_whisker_right,
  bicategory.id_whisker_right,
  bicategory.whisker_assoc]]

/--
Internal tactic used in `coherence`.

Rewrites an equation `f = g` as `f₀ ≫ f₁ = g₀ ≫ g₁`,
where `f₀` and `g₀` are maximal prefixes of `f` and `g` (possibly after reassociating)
which are "liftable" (i.e. expressible as compositions of unitors and associators).
-/
meta def liftable_prefixes : tactic unit :=
try `[simp only [category.assoc]] >>
  `[apply (cancel_epi (𝟙 _)).1; try { apply_instance }] >>
    try `[simp only [tactic.coherence.assoc_lift_hom₂]]

open_locale bicategory
example {f g h i : a ⟶ b} (η : h ⟶ i) (θ) (w : false) : (λ_ _).hom ≫ η = θ :=
begin
  liftable_prefixes,
  guard_target (𝟙 _ ≫ (λ_ _).hom) ≫ η = (𝟙 _) ≫ θ,
  cases w,
end

end coherence

open coherence

-- meta def coherence_loop : tactic unit :=
--   pure_coherence <|> do
--   tactic.congr_core',
--   focus1 pure_coherence <|>
--     fail "`coherence` tactic failed, subgoal not true in the free bicategory",
--   reflexivity <|> (do
--     `(_ ≫ _ = _ ≫ _) ← target |
--       fail "`coherence` tactic failed, non-structural morphisms don't match",
--     tactic.congr_core',
--     reflexivity <|> fail "`coherence` tactic failed, non-structural morphisms don't match",
--     coherence_loop)

-- meta def coherence : tactic unit :=
-- do
--   pure_coherence <|> do
--   try assoc_simps,
--   liftable_prefixes <|>
--     fail ("Something went wrong in the `coherence` tactic: " ++
--       "is the target an equation in a bicategory?"),
--   coherence_loop

meta def coherence_loop : tactic unit :=
do
  -- To prove an equality `f = g` in a monoidal category,
  -- first try the `pure_coherence` tactic on the entire equation:
  pure_coherence <|> do
  -- Otherewise, rearrange so we have a maximal prefix of each side
  -- that is built out of unitors and associators:
  liftable_prefixes <|>
    fail ("Something went wrong in the `coherence` tactic: " ++
      "is the target an equation in a monoidal category?"),
  -- The goal should now look like `f₀ ≫ f₁ = g₀ ≫ g₁`,
  tactic.congr_core',
  -- and now we have two goals `f₀ = g₀` and `f₁ = g₁`.
  -- Discharge the first using `coherence`,
  focus1 pure_coherence <|>
    fail "`coherence` tactic failed, subgoal not true in the free monoidal_category",
  -- Then check that either `g₀` is identically `g₁`,
  reflexivity <|> (do
    -- or that both are compositions,
    `(_ ≫ _ = _ ≫ _) ← target |
      fail "`coherence` tactic failed, non-structural morphisms don't match",
    tactic.congr_core',
    -- with identical first terms,
    reflexivity <|> fail "`coherence` tactic failed, non-structural morphisms don't match",
    -- and whose second terms can be identified by recursively called `coherence`.
    coherence_loop)

meta def coherence : tactic unit :=
do
  try assoc_simps,
  coherence_loop

run_cmd add_interactive [`pure_coherence, `coherence]

add_tactic_doc
{ name        := "coherence",
  category    := doc_category.tactic,
  decl_names  := [`tactic.interactive.coherence],
  tags        := ["category theory"] }

open_locale bicategory

example (η : 𝟙 a ⟶ 𝟙 a ≫ 𝟙 a) :
  (λ_ (𝟙 _)).hom ≫ η ≫ (λ_ (𝟙 _)).hom = (ρ_ (𝟙 _)).hom ≫ η ≫ (ρ_ (𝟙 _)).hom :=
by coherence

example {f' : a ⟶ d} {f : a ⟶ b} {g : b ⟶ c} {h : c ⟶ d} {h' : a ⟶ d}
  (η : f' ⟶ f ≫ (g ≫ h)) (θ : (f ≫ g) ≫ h ⟶ h') :
  η ⊗≫ θ = η ≫ (α_ _ _ _).inv ≫ θ :=
by simp [bicategorical_comp]

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e)
  (η : f ≫ g ≫ h ≫ i ⟶ ((f ≫ g) ≫ h) ≫ i) :
  ((α_ f g h).hom ▷ i) ≫ (α_ f (g ≫ h) i).hom ≫ (f ◁ (α_ g h i).hom) ≫ η ≫
    (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom =
  (α_ (f ≫ g) h i).hom ≫ (α_ f g (h ≫ i)).hom ≫ η ≫
    ((α_ f g h).hom ▷ i) ≫ (α_ f (g ≫ h) i).hom ≫ (f ◁ (α_ g h i).hom) :=
by coherence

/-- normalize 1-morphisms -/
meta def normalize : expr → expr → tactic expr
| p `(%%f ≫ %%g) := do pf ← normalize p f, normalize pf g
| p `(𝟙 %%a)      := return p
| p f              := to_expr ``(%%p ≫ %%f)

meta def to_normalize_aux : expr → expr → tactic expr
| p `(%%f ≫ %%g) := do
    pf₂  ← to_normalize_aux p f,
    pf   ← normalize p f,
    pfg₂ ← to_normalize_aux pf g,
    to_expr ``((α_ %%p %%f %%g).symm ≪≫ whisker_right_iso %%pf₂ %%g ≪≫ %%pfg₂)
| p `(𝟙 %%a)     := to_expr ``(ρ_ %%p)
| p f             := to_expr ``(iso.refl (%%p ≫ %%f))

/-- 2-isomorphism between the original 1-morphism and the normalized 1-morphism -/
meta def to_normalize (f : expr) : tactic expr :=
do
  `(%%a ⟶ %%b) ← infer_type f,
  p  ← to_expr ``(𝟙 %%a),
  f' ← to_normalize_aux p f,
  to_expr ``((λ_ _).symm ≪≫ %%f')

/-- 2-isomorphism between `f` and `g` that are related by `id_comp`, `comp_id`, and `assoc`. -/
meta def can (f : expr) (g : expr) : tactic expr :=
do
  `(%%a ⟶ %%b) ← infer_type f,
  f' ← to_normalize f,
  g' ← to_normalize g,
  to_expr ``(%%f' ≪≫ iso.symm %%g')

namespace interactive
setup_tactic_parser

/--
The tactic `can` yields an isomorphism `f ≅ g` for 1-morphisms `f` and `g` that are
related by `id_comp`, `comp_id`, and `assoc`.
-/
meta def can_iso : tactic unit :=
do
  `(%%f ≅ %%g) ← get_goal >>= infer_type,
  f_to_g ← tactic.can f g,
  let s := simp_lemmas.mk,
  s ← s.add_simp ``iso.trans_assoc,
  s ← s.add_simp ``iso.refl_trans,
  s ← s.add_simp ``iso.trans_refl,
  (f_to_g', pr', _) ← simplify s [] f_to_g,
  tactic.exact f_to_g'

meta def can_hom : tactic unit :=
do
  `(%%f ⟶ %%g) ← get_goal >>= infer_type,
  f_to_g ← tactic.can f g,
  f_to_g' ← to_expr ``(iso.hom %%f_to_g),
  let s := simp_lemmas.mk,
  s ← s.add_simp ``iso.trans_hom,
  s ← s.add_simp ``iso.symm_hom,
  s ← s.add_simp ``iso.refl_hom,
  s ← s.add_simp ``iso.trans_inv,
  s ← s.add_simp ``iso.symm_inv,
  s ← s.add_simp ``iso.refl_inv,
  s ← s.add_simp ``bicategory.whisker_right_iso_hom,
  s ← s.add_simp ``bicategory.whisker_right_iso_inv,
  s ← s.add_simp ``bicategory.id_whisker_right,
  s ← s.add_simp ``category.assoc,
  s ← s.add_simp ``category.id_comp,
  s ← s.add_simp ``category.comp_id,
  (f_to_g'', pr', _) ← simplify s [] f_to_g',
  tactic.exact f_to_g''

meta def can : tactic unit :=
can_iso <|> can_hom

set_option class.instance_max_depth 50

set_option profiler true

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) (j : a ⟶ e)
  (η : f ≫ g ≫ h ≫ i ⟶ j):
  (by can : ((f ≫ g) ≫ h) ≫ i ⟶ f ≫ g ≫ h ≫ i) ≫ η ≫ (λ_ _).inv ≫ (ρ_ _).inv =
    (α_ _ _ _).hom ≫ (α_ _ _ _).hom ≫ η ≫ (λ_ _).inv ≫ (ρ_ _).inv :=
begin
  liftable_prefixes,
  erw comp_id_of_lift (𝟙 (((f ≫ g) ≫ h) ≫ i) ≫ (λ_ (((f ≫ g) ≫ h) ≫ i)).inv),
end

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) (j : a ⟶ e)
  (η : f ≫ g ≫ h ≫ i ⟶ j):
  (by can : ((f ≫ g) ≫ h) ≫ i ⟶ f ≫ g ≫ h ≫ i) ≫ η ≫ (λ_ _).inv ≫ (ρ_ _).inv =
    (α_ _ _ _).hom ≫ (α_ _ _ _).hom ≫ η ≫ (λ_ _).inv ≫ (ρ_ _).inv :=
begin
  coherence
end

example (f g : a ⟶ a) (η : 𝟙 a ⟶ f) (θ : f ⟶ g) (w : false) :
  (λ_ (𝟙 a)).hom ≫ η ≫ 𝟙 f ≫ θ = (ρ_ (𝟙 a)).hom ≫ η ≫ θ :=
begin
  coherence,
end

end interactive

end tactic
