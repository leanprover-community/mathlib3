/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/

import tactic.linarith
import category_theory.skeletal
import data.fintype.sort
import order.category.NonemptyFinLinOrd
import category_theory.functor.reflects_isomorphisms

/-! # The simplex category

We construct a skeletal model of the simplex category, with objects `ℕ` and the
morphism `n ⟶ m` being the monotone maps from `fin (n+1)` to `fin (m+1)`.

We show that this category is equivalent to `NonemptyFinLinOrd`.

## Remarks

The definitions `simplex_category` and `simplex_category.hom` are marked as irreducible.

We provide the following functions to work with these objects:
1. `simplex_category.mk` creates an object of `simplex_category` out of a natural number.
  Use the notation `[n]` in the `simplicial` locale.
2. `simplex_category.len` gives the "length" of an object of `simplex_category`, as a natural.
3. `simplex_category.hom.mk` makes a morphism out of a monotone map between `fin`'s.
4. `simplex_category.hom.to_order_hom` gives the underlying monotone map associated to a
  term of `simplex_category.hom`.

-/

universe v

open category_theory category_theory.limits

/-- The simplex category:
* objects are natural numbers `n : ℕ`
* morphisms from `n` to `m` are monotone functions `fin (n+1) → fin (m+1)`
-/
@[derive inhabited, irreducible]
def simplex_category := ℕ

namespace simplex_category

section
local attribute [semireducible] simplex_category

-- TODO: Make `mk` irreducible.
/-- Interpet a natural number as an object of the simplex category. -/
def mk (n : ℕ) : simplex_category := n

localized "notation (name := simplex_category.mk) `[`n`]` := simplex_category.mk n" in simplicial

-- TODO: Make `len` irreducible.
/-- The length of an object of `simplex_category`. -/
def len (n : simplex_category) : ℕ := n

@[ext] lemma ext (a b : simplex_category) : a.len = b.len → a = b := id
@[simp] lemma len_mk (n : ℕ) : [n].len = n := rfl
@[simp] lemma mk_len (n : simplex_category) : [n.len] = n := rfl

/-- A recursor for `simplex_category`. Use it as `induction Δ using simplex_category.rec`. -/
protected def rec {F : Π (Δ : simplex_category), Sort*} (h : ∀ (n : ℕ), F [n]) :
  Π X, F X := λ n, h n.len

/-- Morphisms in the simplex_category. -/
@[irreducible, nolint has_nonempty_instance]
protected def hom (a b : simplex_category) := fin (a.len + 1) →o fin (b.len + 1)

namespace hom

local attribute [semireducible] simplex_category.hom

/-- Make a moprhism in `simplex_category` from a monotone map of fin's. -/
def mk {a b : simplex_category} (f : fin (a.len + 1) →o fin (b.len + 1)) :
  simplex_category.hom a b := f

/-- Recover the monotone map from a morphism in the simplex category. -/
def to_order_hom {a b : simplex_category} (f : simplex_category.hom a b) :
  fin (a.len + 1) →o fin (b.len + 1) := f

@[ext] lemma ext {a b : simplex_category} (f g : simplex_category.hom a b) :
  f.to_order_hom = g.to_order_hom → f = g := id

@[simp] lemma mk_to_order_hom {a b : simplex_category}
  (f : simplex_category.hom a b) : mk (f.to_order_hom) = f := rfl

@[simp] lemma to_order_hom_mk {a b : simplex_category}
  (f : fin (a.len + 1) →o fin (b.len + 1)) : (mk f).to_order_hom = f := rfl

lemma mk_to_order_hom_apply {a b : simplex_category}
  (f : fin (a.len + 1) →o fin (b.len + 1)) (i : fin (a.len + 1)) :
  (mk f).to_order_hom i = f i := rfl

/-- Identity morphisms of `simplex_category`. -/
@[simp]
def id (a : simplex_category) :
  simplex_category.hom a a :=
mk order_hom.id

/-- Composition of morphisms of `simplex_category`. -/
@[simp]
def comp {a b c : simplex_category} (f : simplex_category.hom b c)
  (g : simplex_category.hom a b) : simplex_category.hom a c :=
mk $ f.to_order_hom.comp g.to_order_hom

end hom

@[simps]
instance small_category : small_category.{0} simplex_category :=
{ hom := λ n m, simplex_category.hom n m,
  id := λ m, simplex_category.hom.id _,
  comp := λ _ _ _ f g, simplex_category.hom.comp g f, }

/-- The constant morphism from [0]. -/
def const (x : simplex_category) (i : fin (x.len+1)) : [0] ⟶ x :=
  hom.mk $ ⟨λ _, i, by tauto⟩

@[simp]
lemma const_comp (x y : simplex_category) (i : fin (x.len + 1)) (f : x ⟶ y) :
  const x i ≫ f = const y (f.to_order_hom i) := rfl

/--
Make a morphism `[n] ⟶ [m]` from a monotone map between fin's.
This is useful for constructing morphisms beetween `[n]` directly
without identifying `n` with `[n].len`.
-/
@[simp]
def mk_hom {n m : ℕ} (f : (fin (n+1)) →o (fin (m+1))) : [n] ⟶ [m] :=
simplex_category.hom.mk f

lemma hom_zero_zero (f : [0] ⟶ [0]) : f = 𝟙 _ :=
by { ext : 2, dsimp, apply subsingleton.elim }

end

open_locale simplicial

section generators
/-!
## Generating maps for the simplex category

TODO: prove that the simplex category is equivalent to
one given by the following generators and relations.
-/

/-- The `i`-th face map from `[n]` to `[n+1]` -/
def δ {n} (i : fin (n+2)) : [n] ⟶ [n+1] :=
mk_hom (fin.succ_above i).to_order_hom

/-- The `i`-th degeneracy map from `[n+1]` to `[n]` -/
def σ {n} (i : fin (n+1)) : [n+1] ⟶ [n] := mk_hom
{ to_fun := fin.pred_above i,
  monotone' := fin.pred_above_right_monotone i }

/-- The generic case of the first simplicial identity -/
lemma δ_comp_δ {n} {i j : fin (n+2)} (H : i ≤ j) :
  δ i ≫ δ j.succ = δ j ≫ δ i.cast_succ :=
begin
  ext k,
  dsimp [δ, fin.succ_above],
  simp only [order_embedding.to_order_hom_coe,
    order_embedding.coe_of_strict_mono,
    function.comp_app,
    simplex_category.hom.to_order_hom_mk,
    order_hom.comp_coe],
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  rcases k with ⟨k, _⟩,
  split_ifs; { simp at *; linarith },
end

lemma δ_comp_δ' {n} {i : fin (n+2)} {j : fin (n+3)} (H : i.cast_succ < j) :
  δ i ≫ δ j = δ (j.pred (λ hj, by simpa only [hj, fin.not_lt_zero] using H)) ≫ δ i.cast_succ :=
begin
  rw ← δ_comp_δ,
  { rw fin.succ_pred, },
  { simpa only [fin.le_iff_coe_le_coe, ← nat.lt_succ_iff, nat.succ_eq_add_one, ← fin.coe_succ,
      j.succ_pred, fin.lt_iff_coe_lt_coe] using H, },
end

lemma δ_comp_δ'' {n} {i : fin (n+3)} {j : fin (n+2)} (H : i ≤ j.cast_succ) :
  δ (i.cast_lt (nat.lt_of_le_of_lt (fin.le_iff_coe_le_coe.mp H) j.is_lt)) ≫ δ j.succ =
    δ j ≫ δ i :=
begin
  rw δ_comp_δ,
  { refl, },
  { exact H, },
end

/-- The special case of the first simplicial identity -/
@[reassoc]
lemma δ_comp_δ_self {n} {i : fin (n+2)} : δ i ≫ δ i.cast_succ = δ i ≫ δ i.succ :=
(δ_comp_δ (le_refl i)).symm

@[reassoc]
lemma δ_comp_δ_self' {n} {i : fin (n+2)} {j : fin (n+3)} (H : j = i.cast_succ) :
  δ i ≫ δ j = δ i ≫ δ i.succ :=
by { subst H, rw δ_comp_δ_self, }

/-- The second simplicial identity -/
@[reassoc]
lemma δ_comp_σ_of_le {n} {i : fin (n+2)} {j : fin (n+1)} (H : i ≤ j.cast_succ) :
  δ i.cast_succ ≫ σ j.succ = σ j ≫ δ i :=
begin
  ext k,
  suffices : ite (j.succ.cast_succ < ite (k < i) k.cast_succ k.succ)
    (ite (k < i) (k:ℕ) (k + 1) - 1) (ite (k < i) k (k + 1)) =
      ite ((if h : (j:ℕ) < k
        then k.pred (by { rintro rfl, exact nat.not_lt_zero _ h })
        else k.cast_lt (by { cases j, cases k, simp only [len_mk], linarith })).cast_succ < i)
          (ite (j.cast_succ < k) (k - 1) k) (ite (j.cast_succ < k) (k - 1) k + 1),
  { dsimp [δ, σ, fin.succ_above, fin.pred_above],
    simp [fin.pred_above] with push_cast,
    convert rfl },
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  rcases k with ⟨k, _⟩,
  simp only [fin.mk_le_mk, fin.cast_succ_mk] at H,
  dsimp,
  split_ifs,
  -- Most of the goals can now be handled by `linarith`,
  -- but we have to deal with two of them by hand.
  swap 8,
  { exact (nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) ‹_›)).symm, },
  swap 7,
  { have : k ≤ i := nat.le_of_pred_lt ‹_›, linarith, },
  -- Hope for the best from `linarith`:
  all_goals { try { refl <|> simp at * }; linarith, },
end

/-- The first part of the third simplicial identity -/
@[reassoc]
lemma δ_comp_σ_self {n} {i : fin (n+1)} :
  δ i.cast_succ ≫ σ i = 𝟙 [n] :=
begin
  ext j,
  suffices : ite (fin.cast_succ i < ite (j < i) (fin.cast_succ j) j.succ)
    (ite (j < i) (j:ℕ) (j + 1) - 1) (ite (j < i) j (j + 1)) = j,
  { dsimp [δ, σ, fin.succ_above, fin.pred_above], simpa [fin.pred_above] with push_cast },
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  dsimp,
  split_ifs; { simp at *; linarith, },
end

@[reassoc]
lemma δ_comp_σ_self' {n} {j : fin (n+2)} {i : fin (n+1)} (H : j = i.cast_succ) :
  δ j ≫ σ i = 𝟙 [n] :=
by { subst H, rw δ_comp_σ_self, }

/-- The second part of the third simplicial identity -/
@[reassoc]
lemma δ_comp_σ_succ {n} {i : fin (n+1)} :
  δ i.succ ≫ σ i = 𝟙 [n] :=
begin
  ext j,
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  dsimp [δ, σ, fin.succ_above, fin.pred_above],
  simp [fin.pred_above] with push_cast,
  split_ifs; { simp at *; linarith, },
end

@[reassoc]
lemma δ_comp_σ_succ' {n} (j : fin (n+2)) (i : fin (n+1)) (H : j = i.succ) :
  δ j ≫ σ i = 𝟙 [n] :=
by { subst H, rw δ_comp_σ_succ, }

/-- The fourth simplicial identity -/
@[reassoc]
lemma δ_comp_σ_of_gt {n} {i : fin (n+2)} {j : fin (n+1)} (H : j.cast_succ < i) :
  δ i.succ ≫ σ j.cast_succ = σ j ≫ δ i :=
begin
  ext k,
  dsimp [δ, σ, fin.succ_above, fin.pred_above],
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  rcases k with ⟨k, _⟩,
  simp only [fin.mk_lt_mk, fin.cast_succ_mk] at H,
  suffices : ite (_ < ite (k < i + 1) _ _) _ _ =
    ite _ (ite (j < k) (k - 1) k) (ite (j < k) (k - 1) k + 1),
  { simpa [apply_dite fin.cast_succ, fin.pred_above] with push_cast, },
  split_ifs,
  -- Most of the goals can now be handled by `linarith`,
  -- but we have to deal with three of them by hand.
  swap 2,
  { simp only [fin.mk_lt_mk] at h_1,
    simp only [not_lt] at h_2,
    simp only [self_eq_add_right, one_ne_zero],
    exact lt_irrefl (k - 1) (lt_of_lt_of_le
      (nat.pred_lt (ne_of_lt (lt_of_le_of_lt (zero_le _) h_1)).symm)
      (le_trans (nat.le_of_lt_succ h) h_2)) },
  swap 4,
  { simp only [fin.mk_lt_mk] at h_1,
    simp only [not_lt] at h,
    simp only [nat.add_succ_sub_one, add_zero],
    exfalso,
    exact lt_irrefl _ (lt_of_le_of_lt (nat.le_pred_of_lt (nat.lt_of_succ_le h)) h_3), },
  swap 4,
  { simp only [fin.mk_lt_mk] at h_1,
    simp only [not_lt] at h_3,
    simp only [nat.add_succ_sub_one, add_zero],
    exact (nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) h_2)).symm, },
  -- Hope for the best from `linarith`:
  all_goals { simp at h_1 h_2 ⊢; linarith, },
end

@[reassoc]
lemma δ_comp_σ_of_gt' {n} {i : fin (n+3)} {j : fin (n+2)} (H : j.succ < i) :
  δ i ≫ σ j = σ (j.cast_lt ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le
      (by simpa only [fin.val_eq_coe, ← fin.coe_succ]
        using fin.lt_iff_coe_lt_coe.mp H) i.is_le))) ≫
    δ (i.pred (λ hi, by simpa only [fin.not_lt_zero, hi] using H)) :=
begin
  rw ← δ_comp_σ_of_gt,
  { simpa only [fin.succ_pred], },
  { rw [fin.cast_succ_cast_lt, ← fin.succ_lt_succ_iff, fin.succ_pred],
    exact H, },
end

local attribute [simp] fin.pred_mk

/-- The fifth simplicial identity -/
@[reassoc]
lemma σ_comp_σ {n} {i j : fin (n+1)} (H : i ≤ j) :
  σ i.cast_succ ≫ σ j = σ j.succ ≫ σ i :=
begin
  ext k,
  dsimp [σ, fin.pred_above],
  rcases i with ⟨i, _⟩,
  rcases j with ⟨j, _⟩,
  rcases k with ⟨k, _⟩,
  simp only [fin.mk_le_mk] at H,
  -- At this point `simp with push_cast` makes good progress, but neither `simp?` nor `squeeze_simp`
  -- return usable sets of lemmas.
  -- To avoid using a non-terminal simp, we make a `suffices` statement indicating the shape
  -- of the goal we're looking for, and then use `simpa with push_cast`.
  -- I'm not sure this is actually much more robust that a non-terminal simp.
  suffices : ite (_ < dite (i < k) _ _) _ _ =
    ite (_ < dite (j + 1 < k) _ _) _ _,
  { simpa [fin.pred_above] with push_cast, },
  split_ifs,
  -- `split_ifs` created 12 goals.
  -- Most of them are dealt with `by simp at *; linarith`,
  -- but we pull out two harder ones to do by hand.
  swap 3,
  { simp only [not_lt] at h_2,
    exact false.elim
    (lt_irrefl (k - 1)
      (lt_of_lt_of_le (nat.pred_lt (id (ne_of_lt (lt_of_le_of_lt (zero_le i) h)).symm))
        (le_trans h_2 (nat.succ_le_of_lt h_1)))) },
  swap 3,
  { simp only [subtype.mk_lt_mk, not_lt] at h_1,
    exact false.elim
    (lt_irrefl j (lt_of_lt_of_le (nat.pred_lt_pred (nat.succ_ne_zero j) h_2) h_1)) },
  -- Deal with the rest automatically.
  all_goals { simp at *; linarith, },
end

end generators

section skeleton

/-- The functor that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
@[simps obj map]
def skeletal_functor : simplex_category ⥤ NonemptyFinLinOrd.{v} :=
{ obj := λ a, NonemptyFinLinOrd.of $ ulift (fin (a.len + 1)),
  map := λ a b f,
    ⟨λ i, ulift.up (f.to_order_hom i.down), λ i j h, f.to_order_hom.monotone h⟩,
  map_id' := λ a, by { ext, simp, },
  map_comp' := λ a b c f g, by { ext, simp, }, }

lemma skeletal_functor.coe_map
  {Δ₁ Δ₂ : simplex_category} (f : Δ₁ ⟶ Δ₂) :
  coe_fn (skeletal_functor.{v}.map f) = ulift.up ∘ f.to_order_hom ∘ ulift.down := rfl

lemma skeletal : skeletal simplex_category :=
λ X Y ⟨I⟩,
begin
  suffices : fintype.card (fin (X.len+1)) = fintype.card (fin (Y.len+1)),
  { ext, simpa },
  { apply fintype.card_congr,
    refine equiv.ulift.symm.trans (((skeletal_functor ⋙ forget _).map_iso I).to_equiv.trans _),
    apply equiv.ulift }
end

namespace skeletal_functor

instance : full skeletal_functor.{v} :=
{ preimage := λ a b f, simplex_category.hom.mk ⟨λ i, (f (ulift.up i)).down, λ i j h, f.monotone h⟩,
  witness' := by { intros m n f, dsimp at *, ext1 ⟨i⟩, ext1, ext1, cases x, simp, } }

instance : faithful skeletal_functor.{v} :=
{ map_injective' := λ m n f g h,
  begin
    ext1, ext1, ext1 i, apply ulift.up.inj,
    change (skeletal_functor.map f) ⟨i⟩ = (skeletal_functor.map g) ⟨i⟩,
    rw h,
  end }

instance : ess_surj skeletal_functor.{v} :=
{ mem_ess_image := λ X, ⟨mk (fintype.card X - 1 : ℕ), ⟨begin
    have aux : fintype.card X = fintype.card X - 1 + 1,
    { exact (nat.succ_pred_eq_of_pos $ fintype.card_pos_iff.mpr ⟨⊥⟩).symm, },
    let f := mono_equiv_of_fin X aux,
    have hf := (finset.univ.order_emb_of_fin aux).strict_mono,
    refine
    { hom := ⟨λ i, f i.down, _⟩,
      inv := ⟨λ i, ⟨f.symm i⟩, _⟩,
      hom_inv_id' := _,
      inv_hom_id' := _ },
    { rintro ⟨i⟩ ⟨j⟩ h, show f i ≤ f j, exact hf.monotone h, },
    { intros i j h, show f.symm i ≤ f.symm j, rw ← hf.le_iff_le,
      show f (f.symm i) ≤ f (f.symm j), simpa only [order_iso.apply_symm_apply], },
    { ext1, ext1 ⟨i⟩, ext1, exact f.symm_apply_apply i },
    { ext1, ext1 i, exact f.apply_symm_apply i },
  end⟩⟩, }

noncomputable instance is_equivalence : is_equivalence (skeletal_functor.{v}) :=
equivalence.of_fully_faithfully_ess_surj skeletal_functor

end skeletal_functor

/-- The equivalence that exhibits `simplex_category` as skeleton
of `NonemptyFinLinOrd` -/
noncomputable def skeletal_equivalence : simplex_category ≌ NonemptyFinLinOrd.{v} :=
functor.as_equivalence skeletal_functor

end skeleton

/--
`simplex_category` is a skeleton of `NonemptyFinLinOrd`.
-/
noncomputable
def is_skeleton_of : is_skeleton_of NonemptyFinLinOrd simplex_category skeletal_functor.{v} :=
{ skel := skeletal,
  eqv := skeletal_functor.is_equivalence }

/-- The truncated simplex category. -/
@[derive small_category]
def truncated (n : ℕ) := full_subcategory (λ a : simplex_category, a.len ≤ n)

namespace truncated

instance {n} : inhabited (truncated n) := ⟨⟨[0],by simp⟩⟩

/--
The fully faithful inclusion of the truncated simplex category into the usual
simplex category.
-/
@[derive [full, faithful]]
def inclusion {n : ℕ} : simplex_category.truncated n ⥤ simplex_category :=
full_subcategory_inclusion _

end truncated

section concrete

instance : concrete_category.{0} simplex_category :=
{ forget :=
  { obj := λ i, fin (i.len + 1),
    map := λ i j f, f.to_order_hom },
  forget_faithful := {} }

end concrete

section epi_mono

/-- A morphism in `simplex_category` is a monomorphism precisely when it is an injective function
-/
theorem mono_iff_injective {n m : simplex_category} {f : n ⟶ m} :
  mono f ↔ function.injective f.to_order_hom :=
begin
  rw ← functor.mono_map_iff_mono skeletal_equivalence.functor.{0},
  dsimp only [skeletal_equivalence, functor.as_equivalence_functor],
  rw [NonemptyFinLinOrd.mono_iff_injective, skeletal_functor.coe_map,
    function.injective.of_comp_iff ulift.up_injective,
    function.injective.of_comp_iff' _ ulift.down_bijective],
end

/-- A morphism in `simplex_category` is an epimorphism if and only if it is a surjective function
-/
lemma epi_iff_surjective {n m : simplex_category} {f: n ⟶ m} :
  epi f ↔ function.surjective f.to_order_hom :=
begin
  rw ← functor.epi_map_iff_epi skeletal_equivalence.functor.{0},
  dsimp only [skeletal_equivalence, functor.as_equivalence_functor],
  rw [NonemptyFinLinOrd.epi_iff_surjective, skeletal_functor.coe_map,
    function.surjective.of_comp_iff' ulift.up_bijective,
    function.surjective.of_comp_iff _ ulift.down_surjective],
end

/-- A monomorphism in `simplex_category` must increase lengths-/
lemma len_le_of_mono {x y : simplex_category} {f : x ⟶ y} :
  mono f → (x.len ≤ y.len) :=
begin
  intro hyp_f_mono,
  have f_inj : function.injective f.to_order_hom.to_fun,
  { exact mono_iff_injective.elim_left (hyp_f_mono) },
  simpa using fintype.card_le_of_injective f.to_order_hom.to_fun f_inj,
end

lemma le_of_mono {n m : ℕ} {f : [n] ⟶ [m]} : (category_theory.mono f) → (n ≤ m) :=
len_le_of_mono

/-- An epimorphism in `simplex_category` must decrease lengths-/
lemma len_le_of_epi {x y : simplex_category} {f : x ⟶ y} :
  epi f → y.len ≤ x.len :=
begin
  intro hyp_f_epi,
  have f_surj : function.surjective f.to_order_hom.to_fun,
  { exact epi_iff_surjective.elim_left (hyp_f_epi) },
  simpa using fintype.card_le_of_surjective f.to_order_hom.to_fun f_surj,
end

lemma le_of_epi {n m : ℕ} {f : [n] ⟶ [m]} : epi f → (m ≤ n) :=
len_le_of_epi

instance {n : ℕ} {i : fin (n+2)} : mono (δ i) :=
begin
  rw mono_iff_injective,
  exact fin.succ_above_right_injective,
end

instance {n : ℕ} {i : fin (n+1)} : epi (σ i) :=
begin
  rw epi_iff_surjective,
  intro b,
  simp only [σ, mk_hom, hom.to_order_hom_mk, order_hom.coe_fun_mk],
  by_cases b ≤ i,
  { use b,
    rw fin.pred_above_below i b (by simpa only [fin.coe_eq_cast_succ] using h),
    simp only [fin.coe_eq_cast_succ, fin.cast_pred_cast_succ], },
  { use b.succ,
    rw [fin.pred_above_above i b.succ _, fin.pred_succ],
    rw not_le at h,
    rw fin.lt_iff_coe_lt_coe at h ⊢,
    simpa only [fin.coe_succ, fin.coe_cast_succ] using nat.lt.step h, }
end

instance : reflects_isomorphisms (forget simplex_category) :=
⟨begin
  intros x y f,
  introI,
  exact is_iso.of_iso
  { hom := f,
    inv := hom.mk
    { to_fun := inv ((forget simplex_category).map f),
      monotone' :=λ y₁ y₂ h, begin
          by_cases h' : y₁ < y₂,
          { by_contradiction h'',
            have eq := λ i, congr_hom (iso.inv_hom_id (as_iso ((forget _).map f))) i,
            have ineq := f.to_order_hom.monotone' (le_of_not_ge h''),
            dsimp at ineq,
            erw [eq, eq] at ineq,
            exact not_le.mpr h' ineq, },
          { rw eq_of_le_of_not_lt h h', }
        end, },
    hom_inv_id' := by { ext1, ext1, exact iso.hom_inv_id (as_iso ((forget _).map f)), },
    inv_hom_id' := by { ext1, ext1, exact iso.inv_hom_id (as_iso ((forget _).map f)), }, },
end⟩

lemma is_iso_of_bijective {x y : simplex_category} {f : x ⟶ y}
  (hf : function.bijective (f.to_order_hom.to_fun)) : is_iso f :=
begin
  haveI : is_iso ((forget simplex_category).map f) := (is_iso_iff_bijective _).mpr hf,
  exact is_iso_of_reflects_iso f (forget simplex_category),
end

/-- An isomorphism in `simplex_category` induces an `order_iso`. -/
@[simp]
def order_iso_of_iso {x y : simplex_category} (e : x ≅ y) :
  fin (x.len+1) ≃o fin (y.len+1) :=
equiv.to_order_iso
  { to_fun    := e.hom.to_order_hom,
    inv_fun   := e.inv.to_order_hom,
    left_inv  := λ i, by simpa only using congr_arg (λ φ, (hom.to_order_hom φ) i) e.hom_inv_id',
    right_inv := λ i, by simpa only using congr_arg (λ φ, (hom.to_order_hom φ) i) e.inv_hom_id', }
  e.hom.to_order_hom.monotone e.inv.to_order_hom.monotone

lemma iso_eq_iso_refl {x : simplex_category} (e : x ≅ x) :
  e = iso.refl x :=
begin
  have h : (finset.univ : finset (fin (x.len+1))).card = x.len+1 := finset.card_fin (x.len+1),
  have eq₁ := finset.order_emb_of_fin_unique' h
    (λ i, finset.mem_univ ((order_iso_of_iso e) i)),
  have eq₂ := finset.order_emb_of_fin_unique' h
    (λ i, finset.mem_univ ((order_iso_of_iso (iso.refl x)) i)),
  ext1, ext1,
  convert congr_arg (λ φ, (order_embedding.to_order_hom φ)) (eq₁.trans eq₂.symm),
  ext1, ext1 i,
  refl,
end

lemma eq_id_of_is_iso {x : simplex_category} (f : x ⟶ x) [hf : is_iso f] : f = 𝟙 _ :=
congr_arg (λ (φ : _ ≅ _), φ.hom) (iso_eq_iso_refl (as_iso f))

lemma eq_σ_comp_of_not_injective' {n : ℕ} {Δ' : simplex_category} (θ : mk (n+1) ⟶ Δ')
  (i : fin (n+1)) (hi : θ.to_order_hom i.cast_succ = θ.to_order_hom i.succ):
  ∃ (θ' : mk n ⟶ Δ'), θ = σ i ≫ θ' :=
begin
  use δ i.succ ≫ θ,
  ext1, ext1, ext1 x,
  simp only [hom.to_order_hom_mk, function.comp_app, order_hom.comp_coe,
    hom.comp, small_category_comp, σ, mk_hom, order_hom.coe_fun_mk],
  by_cases h' : x ≤ i.cast_succ,
  { rw fin.pred_above_below i x h',
    have eq := fin.cast_succ_cast_pred (gt_of_gt_of_ge (fin.cast_succ_lt_last i) h'),
    erw fin.succ_above_below i.succ x.cast_pred _, swap,
    { rwa [eq, ← fin.le_cast_succ_iff], },
    rw eq, },
  { simp only [not_le] at h',
    let y := x.pred begin
      intro h,
      rw h at h',
      simpa only [fin.lt_iff_coe_lt_coe, nat.not_lt_zero, fin.coe_zero] using h',
    end,
    simp only [show x = y.succ, by rw fin.succ_pred] at h' ⊢,
    rw [fin.pred_above_above i y.succ h', fin.pred_succ],
    by_cases h'' : y = i,
    { rw h'',
      convert hi.symm,
      erw fin.succ_above_below i.succ _,
      exact fin.lt_succ, },
    { erw fin.succ_above_above i.succ _,
      simp only [fin.lt_iff_coe_lt_coe, fin.le_iff_coe_le_coe, fin.coe_succ,
        fin.coe_cast_succ, nat.lt_succ_iff, fin.ext_iff] at h' h'' ⊢,
      cases nat.le.dest h' with c hc,
      cases c,
      { exfalso,
        rw [add_zero] at hc,
        rw [hc] at h'',
        exact h'' rfl, },
      { rw ← hc,
        simp only [add_le_add_iff_left, nat.succ_eq_add_one,
          le_add_iff_nonneg_left, zero_le], }, }, }
end

lemma eq_σ_comp_of_not_injective {n : ℕ} {Δ' : simplex_category} (θ : mk (n+1) ⟶ Δ')
  (hθ : ¬function.injective θ.to_order_hom) :
  ∃ (i : fin (n+1)) (θ' : mk n ⟶ Δ'), θ = σ i ≫ θ' :=
begin
  simp only [function.injective, exists_prop, not_forall] at hθ,
  -- as θ is not injective, there exists `x<y` such that `θ x = θ y`
  -- and then, `θ x = θ (x+1)`
  have hθ₂ : ∃ (x y : fin (n+2)), (hom.to_order_hom θ) x = (hom.to_order_hom θ) y ∧ x<y,
  { rcases hθ with ⟨x, y, ⟨h₁, h₂⟩⟩,
    by_cases x<y,
    { exact ⟨x, y, ⟨h₁, h⟩⟩, },
    { refine ⟨y, x, ⟨h₁.symm, _⟩⟩,
      cases lt_or_eq_of_le (not_lt.mp h) with h' h',
      { exact h', },
      { exfalso,
        exact h₂ h'.symm, }, }, },
  rcases hθ₂ with ⟨x, y, ⟨h₁, h₂⟩⟩,
  let z := x.cast_pred,
  use z,
  simp only [← (show z.cast_succ = x,
    by exact fin.cast_succ_cast_pred (lt_of_lt_of_le h₂ (fin.le_last y)))] at h₁ h₂,
  apply eq_σ_comp_of_not_injective',
  rw fin.cast_succ_lt_iff_succ_le at h₂,
  apply le_antisymm,
  { exact θ.to_order_hom.monotone (le_of_lt (fin.cast_succ_lt_succ z)), },
  { rw h₁,
    exact θ.to_order_hom.monotone h₂, },
end

lemma eq_comp_δ_of_not_surjective' {n : ℕ} {Δ : simplex_category} (θ : Δ ⟶ mk (n+1))
  (i : fin (n+2)) (hi : ∀ x, θ.to_order_hom x ≠ i) :
  ∃ (θ' : Δ ⟶ (mk n)), θ = θ' ≫ δ i :=
begin
  by_cases i < fin.last (n+1),
  { use θ ≫ σ (fin.cast_pred i),
    ext1, ext1, ext1 x,
    simp only [hom.to_order_hom_mk, function.comp_app,
      order_hom.comp_coe, hom.comp, small_category_comp],
    by_cases h' : θ.to_order_hom x ≤ i,
    { simp only [σ, mk_hom, hom.to_order_hom_mk, order_hom.coe_fun_mk],
      rw fin.pred_above_below (fin.cast_pred i) (θ.to_order_hom x)
        (by simpa [fin.cast_succ_cast_pred h] using h'),
      erw fin.succ_above_below i, swap,
      { simp only [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ],
        exact lt_of_le_of_lt (fin.coe_cast_pred_le_self _)
          (fin.lt_iff_coe_lt_coe.mp ((ne.le_iff_lt (hi x)).mp h')), },
      rw fin.cast_succ_cast_pred,
      apply lt_of_le_of_lt h' h, },
    { simp only [not_le] at h',
      simp only [σ, mk_hom, hom.to_order_hom_mk, order_hom.coe_fun_mk,
        fin.pred_above_above (fin.cast_pred i) (θ.to_order_hom x)
        (by simpa only [fin.cast_succ_cast_pred h] using h')],
      erw [fin.succ_above_above i _, fin.succ_pred],
      simpa only [fin.le_iff_coe_le_coe, fin.coe_cast_succ, fin.coe_pred]
          using nat.le_pred_of_lt (fin.lt_iff_coe_lt_coe.mp h'), }, },
  { obtain rfl := le_antisymm (fin.le_last i) (not_lt.mp h),
    use θ ≫ σ (fin.last _),
    ext1, ext1, ext1 x,
    simp only [hom.to_order_hom_mk, function.comp_app, order_hom.comp_coe, hom.comp,
      small_category_comp, σ, δ, mk_hom, order_hom.coe_fun_mk,
      order_embedding.to_order_hom_coe, fin.pred_above_last, fin.succ_above_last,
      fin.cast_succ_cast_pred ((ne.le_iff_lt (hi x)).mp (fin.le_last _))], },
end

lemma eq_comp_δ_of_not_surjective {n : ℕ} {Δ : simplex_category} (θ : Δ ⟶ mk (n+1))
  (hθ : ¬function.surjective θ.to_order_hom) :
  ∃ (i : fin (n+2)) (θ' : Δ ⟶ (mk n)), θ = θ' ≫ δ i :=
begin
  cases not_forall.mp hθ with i hi,
  use i,
  exact eq_comp_δ_of_not_surjective' θ i (not_exists.mp hi),
end

lemma eq_id_of_mono {x : simplex_category} (i : x ⟶ x) [mono i] : i = 𝟙 _ :=
begin
  suffices : is_iso i,
  { haveI := this, apply eq_id_of_is_iso, },
  apply is_iso_of_bijective,
  dsimp,
  rw [fintype.bijective_iff_injective_and_card i.to_order_hom, ← mono_iff_injective,
    eq_self_iff_true, and_true],
  apply_instance,
end

lemma eq_id_of_epi {x : simplex_category} (i : x ⟶ x) [epi i] : i = 𝟙 _ :=
begin
  suffices : is_iso i,
  { haveI := this, apply eq_id_of_is_iso, },
  apply is_iso_of_bijective,
  dsimp,
  rw [fintype.bijective_iff_surjective_and_card i.to_order_hom, ← epi_iff_surjective,
    eq_self_iff_true, and_true],
  apply_instance,
end

lemma eq_σ_of_epi {n : ℕ} (θ : mk (n+1) ⟶ mk n) [epi θ] : ∃ (i : fin (n+1)), θ = σ i :=
begin
  rcases eq_σ_comp_of_not_injective θ _ with ⟨i, θ', h⟩, swap,
  { by_contradiction,
    simpa only [nat.one_ne_zero, add_le_iff_nonpos_right, nonpos_iff_eq_zero]
      using le_of_mono (mono_iff_injective.mpr h), },
  use i,
  haveI : epi (σ i ≫ θ') := by { rw ← h, apply_instance, },
  haveI := category_theory.epi_of_epi (σ i) θ',
  rw [h, eq_id_of_epi θ', category.comp_id],
end

lemma eq_δ_of_mono {n : ℕ} (θ : mk n ⟶ mk (n+1)) [mono θ] : ∃ (i : fin (n+2)), θ = δ i :=
begin
  rcases eq_comp_δ_of_not_surjective θ _ with ⟨i, θ', h⟩, swap,
  { by_contradiction,
    simpa only [add_le_iff_nonpos_right, nonpos_iff_eq_zero]
      using le_of_epi (epi_iff_surjective.mpr h), },
  use i,
  haveI : mono (θ' ≫ δ i) := by { rw ← h, apply_instance, },
  haveI := category_theory.mono_of_mono θ' (δ i),
  rw [h, eq_id_of_mono θ', category.id_comp],
end

lemma len_lt_of_mono {Δ' Δ : simplex_category} (i : Δ' ⟶ Δ) [hi : mono i]
  (hi' : Δ ≠ Δ') : Δ'.len < Δ.len :=
begin
  cases lt_or_eq_of_le (len_le_of_mono hi),
  { exact h, },
  { exfalso,
    exact hi' (by { ext, exact h.symm,}), },
end

noncomputable instance : split_epi_category simplex_category :=
skeletal_equivalence.{0}.inverse.split_epi_category_imp_of_is_equivalence

instance : has_strong_epi_mono_factorisations simplex_category :=
functor.has_strong_epi_mono_factorisations_imp_of_is_equivalence
  simplex_category.skeletal_equivalence.{0}.inverse

instance : has_strong_epi_images simplex_category :=
  limits.has_strong_epi_images_of_has_strong_epi_mono_factorisations

instance (Δ Δ' : simplex_category) (θ : Δ ⟶ Δ') : epi (factor_thru_image θ) := strong_epi.epi

lemma image_eq {Δ Δ' Δ'' : simplex_category } {φ : Δ ⟶ Δ''}
  {e : Δ ⟶ Δ'} [epi e] {i : Δ' ⟶ Δ''} [mono i] (fac : e ≫ i = φ) :
  image φ = Δ' :=
begin
  haveI := strong_epi_of_epi e,
  let e := image.iso_strong_epi_mono e i fac,
  ext,
  exact le_antisymm (len_le_of_epi (infer_instance : epi e.hom))
    (len_le_of_mono (infer_instance : mono e.hom)),
end

lemma image_ι_eq {Δ Δ'' : simplex_category } {φ : Δ ⟶ Δ''}
  {e : Δ ⟶ image φ} [epi e] {i : image φ ⟶ Δ''} [mono i] (fac : e ≫ i = φ) :
  image.ι φ = i :=
begin
  haveI := strong_epi_of_epi e,
  rw [← image.iso_strong_epi_mono_hom_comp_ι e i fac,
    simplex_category.eq_id_of_is_iso (image.iso_strong_epi_mono e i fac).hom, category.id_comp],
end

lemma factor_thru_image_eq {Δ Δ'' : simplex_category } {φ : Δ ⟶ Δ''}
  {e : Δ ⟶ image φ} [epi e] {i : image φ ⟶ Δ''} [mono i] (fac : e ≫ i = φ) :
  factor_thru_image φ = e :=
by rw [← cancel_mono i, fac, ← image_ι_eq fac, image.fac]

end epi_mono

/-- This functor `simplex_category ⥤ Cat` sends `[n]` (for `n : ℕ`)
to the category attached to the ordered set `{0, 1, ..., n}` -/
@[simps obj map]
def to_Cat : simplex_category ⥤ Cat.{0} :=
simplex_category.skeletal_functor ⋙ forget₂ NonemptyFinLinOrd LinearOrder ⋙
  forget₂ LinearOrder Lattice ⋙ forget₂ Lattice PartialOrder ⋙
  forget₂ PartialOrder Preorder ⋙ Preorder_to_Cat

end simplex_category
