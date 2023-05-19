/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Adam Topaz
-/
import topology.separation
import topology.subset_properties
import topology.locally_constant.basic

/-!

# Discrete quotients of a topological space.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the type of discrete quotients of a topological space,
denoted `discrete_quotient X`. To avoid quantifying over types, we model such
quotients as setoids whose equivalence classes are clopen.

## Definitions
1. `discrete_quotient X` is the type of discrete quotients of `X`.
  It is endowed with a coercion to `Type`, which is defined as the
  quotient associated to the setoid in question, and each such quotient
  is endowed with the discrete topology.
2. Given `S : discrete_quotient X`, the projection `X → S` is denoted
  `S.proj`.
3. When `X` is compact and `S : discrete_quotient X`, the space `S` is
  endowed with a `fintype` instance.

## Order structure

The type `discrete_quotient X` is endowed with an instance of a `semilattice_inf` with `order_top`.
The partial ordering `A ≤ B` mathematically means that `B.proj` factors through `A.proj`.
The top element `⊤` is the trivial quotient, meaning that every element of `X` is collapsed
to a point. Given `h : A ≤ B`, the map `A → B` is `discrete_quotient.of_le h`.

Whenever `X` is a locally connected space, the type `discrete_quotient X` is also endowed with an
instance of a `order_bot`, where the bot element `⊥` is given by the `connectedComponentSetoid`,
i.e., `x ~ y` means that `x` and `y` belong to the same connected component. In particular, if `X`
is a discrete topological space, then `x ~ y` is equivalent (propositionally, not definitionally) to
`x = y`.

Given `f : C(X, Y)`, we define a predicate `discrete_quotient.le_comap f A B` for `A :
discrete_quotient X` and `B : discrete_quotient Y`, asserting that `f` descends to `A → B`.  If
`cond : discrete_quotient.le_comap h A B`, the function `A → B` is obtained by
`discrete_quotient.map f cond`.

## Theorems

The two main results proved in this file are:

1. `discrete_quotient.eq_of_forall_proj_eq` which states that when `X` is compact, T₂, and totally
  disconnected, any two elements of `X` are equal if their projections in `Q` agree for all
  `Q : discrete_quotient X`.

2. `discrete_quotient.exists_of_compat` which states that when `X` is compact, then any
  system of elements of `Q` as `Q : discrete_quotient X` varies, which is compatible with
  respect to `discrete_quotient.of_le`, must arise from some element of `X`.

## Remarks
The constructions in this file will be used to show that any profinite space is a limit
of finite discrete spaces.
-/

open set function
variables {α X Y Z : Type*} [topological_space X] [topological_space Y]
  [topological_space Z]

/-- The type of discrete quotients of a topological space. -/
@[ext]
structure discrete_quotient (X : Type*) [topological_space X]  extends setoid X :=
(is_open_set_of_rel : ∀ x, is_open (set_of (to_setoid.rel x)))

namespace discrete_quotient

variables (S : discrete_quotient X)

/-- Construct a discrete quotient from a clopen set. -/
def of_clopen {A : set X} (h : is_clopen A) : discrete_quotient X :=
{ to_setoid := ⟨λ x y, x ∈ A ↔ y ∈ A, λ _, iff.rfl, λ _ _, iff.symm, λ _ _ _, iff.trans⟩,
  is_open_set_of_rel := λ x,
    by by_cases hx : x ∈ A; simp [setoid.rel, hx, h.1, h.2, ← compl_set_of] }

lemma refl : ∀ x, S.rel x x := S.refl'
lemma symm {x y : X} : S.rel x y → S.rel y x := S.symm'
lemma trans {x y z} : S.rel x y → S.rel y z → S.rel x z := S.trans'

/-- The setoid whose quotient yields the discrete quotient. -/
add_decl_doc to_setoid

instance : has_coe_to_sort (discrete_quotient X) Type* :=
⟨λ S, quotient S.to_setoid⟩

instance : topological_space S := quotient.topological_space

/-- The projection from `X` to the given discrete quotient. -/
def proj : X → S := quotient.mk'

lemma fiber_eq (x : X) : S.proj ⁻¹' {S.proj x} = set_of (S.rel x) :=
set.ext $ λ y, eq_comm.trans quotient.eq'

lemma proj_surjective : function.surjective S.proj := quotient.surjective_quotient_mk'
lemma proj_quotient_map : quotient_map S.proj := quotient_map_quot_mk
lemma proj_continuous : continuous S.proj := S.proj_quotient_map.continuous

instance : discrete_topology S :=
singletons_open_iff_discrete.1 $ S.proj_surjective.forall.2 $ λ x,
  by { rw [← S.proj_quotient_map.is_open_preimage, fiber_eq], exact S.is_open_set_of_rel _ }

lemma proj_is_locally_constant : is_locally_constant S.proj :=
(is_locally_constant.iff_continuous S.proj).2 S.proj_continuous

lemma is_clopen_preimage (A : set S) : is_clopen (S.proj ⁻¹' A) :=
(is_clopen_discrete A).preimage S.proj_continuous

lemma is_open_preimage (A : set S) : is_open (S.proj ⁻¹' A) := (S.is_clopen_preimage A).1
lemma is_closed_preimage (A : set S) : is_closed (S.proj ⁻¹' A) := (S.is_clopen_preimage A).2

theorem is_clopen_set_of_rel (x : X) : is_clopen (set_of (S.rel x)) :=
by { rw [← fiber_eq], apply is_clopen_preimage }

instance : has_inf (discrete_quotient X) :=
⟨λ S₁ S₂, ⟨S₁.1 ⊓ S₂.1, λ x, (S₁.2 x).inter (S₂.2 x)⟩⟩

instance : semilattice_inf (discrete_quotient X) :=
injective.semilattice_inf to_setoid ext (λ _ _, rfl)

instance : order_top (discrete_quotient X) :=
{ top := ⟨⊤, λ _, is_open_univ⟩,
  le_top := λ a, by tauto }

instance : inhabited (discrete_quotient X) := ⟨⊤⟩

instance inhabited_quotient [inhabited X] : inhabited S := ⟨S.proj default⟩
instance [nonempty X] : nonempty S := nonempty.map S.proj ‹_›

section comap

variables (g : C(Y, Z)) (f : C(X, Y))

/-- Comap a discrete quotient along a continuous map. -/
def comap (S : discrete_quotient Y) : discrete_quotient X :=
{ to_setoid := setoid.comap f S.1,
  is_open_set_of_rel := λ y, (S.2 _).preimage f.continuous }

@[simp]
lemma comap_id : S.comap (continuous_map.id X) = S := by { ext, refl }

@[simp]
lemma comap_comp (S : discrete_quotient Z) : S.comap (g.comp f) = (S.comap g).comap f := rfl

@[mono]
lemma comap_mono {A B : discrete_quotient Y} (h : A ≤ B) : A.comap f ≤ B.comap f :=
by tauto

end comap

section of_le

variables {A B C : discrete_quotient X}

/-- The map induced by a refinement of a discrete quotient. -/
def of_le (h : A ≤ B) : A → B := quotient.map' (λ x, x) h

@[simp] lemma of_le_refl : of_le (le_refl A) = id := by { ext ⟨⟩, refl }

lemma of_le_refl_apply (a : A) : of_le (le_refl A) a = a := by simp

@[simp] lemma of_le_of_le (h₁ : A ≤ B) (h₂ : B ≤ C) (x : A) :
  of_le h₂ (of_le h₁ x) = of_le (h₁.trans h₂) x := by { rcases x with ⟨⟩, refl }

@[simp] lemma of_le_comp_of_le (h₁ : A ≤ B) (h₂ : B ≤ C) :
  of_le h₂ ∘ of_le h₁ = of_le (le_trans h₁ h₂) :=
funext $ of_le_of_le _ _

lemma of_le_continuous (h : A ≤ B) : continuous (of_le h) :=
continuous_of_discrete_topology

@[simp] lemma of_le_proj (h : A ≤ B) (x : X) : of_le h (A.proj x) = B.proj x :=
quotient.sound' (B.refl _)

@[simp] lemma of_le_comp_proj (h : A ≤ B) : of_le h ∘ A.proj = B.proj :=
funext $ of_le_proj _

end of_le

/-- When `X` is a locally connected space, there is an `order_bot` instance on
`discrete_quotient X`. The bottom element is given by `connected_component_setoid X`
-/
instance [locally_connected_space X] : order_bot (discrete_quotient X) :=
{ bot :=
  { to_setoid := connected_component_setoid X,
    is_open_set_of_rel := λ x,
      begin
        have : connected_component x = {y | (connected_component_setoid X).rel x y},
        { ext y,
          simpa only [connected_component_setoid, ← connected_component_eq_iff_mem] using eq_comm },
        rw [← this],
        exact is_open_connected_component
      end },
  bot_le := λ S x y (h : connected_component x = connected_component y),
    (S.is_clopen_set_of_rel x).connected_component_subset (S.refl _) $
      h.symm ▸ mem_connected_component }

@[simp] theorem proj_bot_eq [locally_connected_space X] {x y : X} :
  proj ⊥ x = proj ⊥ y ↔ connected_component x = connected_component y :=
quotient.eq'

theorem proj_bot_inj [discrete_topology X] {x y : X} :
  proj ⊥ x = proj ⊥ y ↔ x = y := by simp

theorem proj_bot_injective [discrete_topology X] :
  injective (⊥ : discrete_quotient X).proj := λ _ _, proj_bot_inj.1

theorem proj_bot_bijective [discrete_topology X] :
  bijective (⊥ : discrete_quotient X).proj :=
⟨proj_bot_injective, proj_surjective _⟩

section map

variables (f : C(X, Y)) (A A' : discrete_quotient X) (B B' : discrete_quotient Y)

/-- Given `f : C(X, Y)`, `le_comap cont A B` is defined as `A ≤ B.comap f`. Mathematically this
means that `f` descends to a morphism `A → B`. -/
def le_comap : Prop := A ≤ B.comap f

theorem le_comap_id : le_comap (continuous_map.id X) A A := λ _ _, id

variables {A A' B B'} {f} {g : C(Y, Z)} {C : discrete_quotient Z}

@[simp] theorem le_comap_id_iff : le_comap (continuous_map.id X) A A' ↔ A ≤ A' := iff.rfl

theorem le_comap.comp :
  le_comap g B C → le_comap f A B → le_comap (g.comp f) A C := by tauto

theorem le_comap.mono (h : le_comap f A B) (hA : A' ≤ A) (hB : B ≤ B') : le_comap f A' B' :=
  hA.trans $ le_trans h $ comap_mono _ hB

/-- Map a discrete quotient along a continuous map. -/
def map (f : C(X, Y)) (cond : le_comap f A B) : A → B := quotient.map' f cond

theorem map_continuous (cond : le_comap f A B) : continuous (map f cond) :=
  continuous_of_discrete_topology

@[simp] theorem map_comp_proj (cond : le_comap f A B) : map f cond ∘ A.proj = B.proj ∘ f := rfl

@[simp]
theorem map_proj (cond : le_comap f A B) (x : X) : map f cond (A.proj x) = B.proj (f x) := rfl

@[simp] theorem map_id : map _ (le_comap_id A) = id := by ext ⟨⟩; refl

@[simp] theorem map_comp (h1 : le_comap g B C) (h2 : le_comap f A B) :
  map (g.comp f) (h1.comp h2) = map g h1 ∘ map f h2 :=
by { ext ⟨⟩, refl }

@[simp] theorem of_le_map (cond : le_comap f A B) (h : B ≤ B') (a : A) :
  of_le h (map f cond a) = map f (cond.mono le_rfl h) a :=
by { rcases a with ⟨⟩, refl }

@[simp] theorem of_le_comp_map (cond : le_comap f A B) (h : B ≤ B') :
  of_le h ∘ map f cond = map f (cond.mono le_rfl h) :=
funext $ of_le_map cond h

@[simp] theorem map_of_le (cond : le_comap f A B) (h : A' ≤ A) (c : A') :
  map f cond (of_le h c) = map f (cond.mono h le_rfl) c :=
by { rcases c with ⟨⟩, refl }

@[simp] theorem map_comp_of_le (cond : le_comap f A B) (h : A' ≤ A) :
  map f cond ∘ of_le h =  map f (cond.mono h le_rfl) :=
funext $ map_of_le cond h

end map

lemma eq_of_forall_proj_eq [t2_space X] [compact_space X] [disc : totally_disconnected_space X]
  {x y : X} (h : ∀ Q : discrete_quotient X, Q.proj x = Q.proj y) : x = y :=
begin
  rw [← mem_singleton_iff, ← connected_component_eq_singleton, connected_component_eq_Inter_clopen,
    mem_Inter],
  rintro ⟨U, hU1, hU2⟩,
  exact (quotient.exact' (h (of_clopen hU1))).mpr hU2
end

lemma fiber_subset_of_le {A B : discrete_quotient X} (h : A ≤ B) (a : A) :
  A.proj ⁻¹' {a} ⊆ B.proj ⁻¹' {of_le h a} :=
begin
  rcases A.proj_surjective a with ⟨a, rfl⟩,
  rw [fiber_eq, of_le_proj, fiber_eq],
  exact λ _ h', h h'
end

lemma exists_of_compat [compact_space X] (Qs : Π (Q : discrete_quotient X), Q)
  (compat : ∀ (A B : discrete_quotient X) (h : A ≤ B), of_le h (Qs _) = Qs _) :
  ∃ x : X, ∀ Q : discrete_quotient X, Q.proj x = Qs _ :=
begin
  obtain ⟨x,hx⟩ : (⋂ Q, proj Q ⁻¹' {Qs Q}).nonempty :=
    is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
      (λ (Q : discrete_quotient X), Q.proj ⁻¹' {Qs _}) (directed_of_inf $ λ A B h, _)
      (λ Q, (singleton_nonempty _).preimage Q.proj_surjective)
      (λ i,  (is_closed_preimage _ _).is_compact) (λ i, is_closed_preimage _ _),
  { refine ⟨x, λ Q, _⟩,
    exact hx _ ⟨Q,rfl⟩ },
  { rw [← compat _ _ h],
    exact fiber_subset_of_le _ _ },
end

instance [compact_space X] : finite S :=
begin
  have : compact_space S := quotient.compact_space,
  rwa [← is_compact_univ_iff, is_compact_iff_finite, finite_univ_iff] at this
end

end discrete_quotient

namespace locally_constant

variables {X} (f : locally_constant X α)

/-- Any locally constant function induces a discrete quotient. -/
def discrete_quotient : discrete_quotient X :=
{ to_setoid := setoid.comap f ⊥,
  is_open_set_of_rel := λ x, f.is_locally_constant _ }

/-- The (locally constant) function from the discrete quotient associated to a locally constant
function. -/
def lift : locally_constant f.discrete_quotient α :=
⟨λ a, quotient.lift_on' a f (λ a b, id), λ A, is_open_discrete _⟩

@[simp] lemma lift_comp_proj : f.lift ∘ f.discrete_quotient.proj = f := by { ext, refl }

end locally_constant
