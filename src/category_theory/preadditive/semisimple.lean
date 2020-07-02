/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.constructions.products
import category_theory.preadditive.mutually_simple
import category_theory.preadditive.biproducts
import data.fintype.card
import data.pequiv

open category_theory.limits
open_locale big_operators

namespace category_theory

universes v u w
variables {C : Type u} [category.{v} C]

section
variables [preadditive C] [has_finite_biproducts C]
open preadditive

structure sum_over {ι : Type w} (Z : ι → C) :=
(κ : Type v)
[fintype : fintype κ]
[decidable_eq : decidable_eq κ]
(summand : κ → ι)

attribute [instance] sum_over.fintype sum_over.decidable_eq

variables {ι : Type w} {Z : ι → C}

def sum_over.sum (O : sum_over Z) : C := ⨁ (λ k, Z (O.summand k))

variables (Z)

def sum_over.single (i : ι) : sum_over Z :=
{ κ := punit.{v+1},
  summand := λ _, i, }

instance (i : ι) : unique (sum_over.single Z i).κ :=
by { dsimp [sum_over.single], apply_instance, }

structure decomposition_over {ι : Type w} (Z : ι → C) (X : C) :=
(O : sum_over Z)
(iso : X ≅ O.sum)

@[simps]
def decomposition_over.trivial (O : sum_over Z) : decomposition_over Z O.sum :=
{ O := O,
  iso := iso.refl _ }

def decomposition_over.single (i : ι) : decomposition_over Z (Z i) :=
{ O := sum_over.single Z i,
  iso := (product_over_unique_iso (Z ∘ (sum_over.single Z i).summand)).symm, }

variables {Z}

def decomposition_over.transport {X : C} (D : decomposition_over Z X) {Y : C} (i : X ≅ Y) :
  decomposition_over Z Y :=
{ O := D.O,
  iso := i.symm ≪≫ D.iso, }

section
variables [has_binary_biproducts C]

def sum_over.biprod (O O' : sum_over Z) : sum_over Z :=
{ κ := O.κ ⊕ O'.κ,
  summand := sum.elim O.summand O'.summand, }

def sum_over.biprod_comparison (O O' : sum_over Z) : O.sum ⊞ O'.sum ≅ (O.biprod O').sum :=
(biproduct_over_sum_iso (λ (k : (O.biprod O').κ), Z ((O.biprod O').summand k))).symm

-- TODO needs the biprod_comparison_π lemma
@[simp] lemma sum_over.biprod_comparison_hom_π (O O' : sum_over Z) (k) :
  (sum_over.biprod_comparison O O').hom ≫ biproduct.π _ k = sorry :=
begin
cases k,
  simp [sum_over.biprod_comparison, add_comp, sum_comp],
  simp [biproduct.ι_π, comp_dite],
  -- use injectivity of sum.inl
end

def decomposition_over.biprod {X Y : C} (D : decomposition_over Z X) (E : decomposition_over Z Y) :
  decomposition_over Z (X ⊞ Y) :=
{ O := D.O.biprod E.O,
  iso := (biprod.map_iso D.iso E.iso).trans (D.O.biprod_comparison E.O), }

def sum_over.insert (O : sum_over Z) (i : ι) : sum_over Z :=
{ κ := punit.{v+1} ⊕ O.κ,
  summand := sum.elim (λ _, i) O.summand, }

def decomposition_over.insert {X : C} (D : decomposition_over Z X)
  (i : ι) : decomposition_over Z (Z i ⊞ X) :=
{ O := D.O.insert i,
  iso :=
    (biprod.map_iso (iso.refl _) (D.iso)).trans
    (biproduct_over_punit_sum_iso (λ k, Z (sum.elim (λ _, i) D.O.summand k))).symm, }

end

structure simple_decomposition (X : C) :=
(ι : Type v)
[fintype : fintype ι]
[decidable_eq : decidable_eq ι]
(summand : ι → C)
[is_simple : Π i, simple (summand i)]
(iso : X ≅ ⨁ summand)

attribute [instance] simple_decomposition.fintype simple_decomposition.decidable_eq
attribute [instance] simple_decomposition.is_simple

def simple_decomposition.multiplicity
  [decidable_rel (λ X Y : C, nonempty (X ≅ Y))]
  {X : C} (D : simple_decomposition X) (Y : C) [simple Y] : ℕ :=
fintype.card { i // nonempty (D.summand i ≅ Y) }

lemma simple_decomposition.zero_of_card_zero
  {X : C} (D : simple_decomposition X) (h : fintype.card D.ι = 0) :
  𝟙 X = 0 :=
begin
  have e : D.ι ≃ pempty.{v+1} := fintype.card_eq_zero_equiv_equiv_pempty h,
  have z : 𝟙 (⨁ D.summand) = 0 := product_over_equiv_pempty_id_eq_zero e _,
  have t : 𝟙 X = D.iso.hom ≫ 𝟙 (⨁ D.summand) ≫ D.iso.inv := by simp,
  simpa [z] using t,
end

lemma simple_decomposition.card_zero_of_zero
  {X : C} (h : 𝟙 X = 0) (D : simple_decomposition.{v} X) : fintype.card D.ι = 0 :=
begin
  by_contradiction,
  cases fintype.card_pos_iff.1 (nat.pos_of_ne_zero a) with i,
  have : 𝟙 (D.summand i) = biproduct.ι _ i ≫ D.iso.inv ≫ 𝟙 X ≫ D.iso.hom ≫ biproduct.π _ i, simp,
  simp [h] at this,
  exact id_nonzero _ this,
end


end



lemma fintype.card_ne {α : Type v} [fintype α] [decidable_eq α] (a : α) :
  fintype.card {a' // a' ≠ a} = fintype.card α - 1 :=
begin
  have t := fintype.card_congr (equiv_punit_sum_of_term' a),
  simp only [fintype.card_punit, ne.def, fintype.card_sum] at t,
  exact (nat.sub_eq_of_eq_add t).symm,
end

def equiv_punit_sum_of_term {α : Type v} [decidable_eq α] [fintype α] (a : α) :
  Σ' (β : Type v) [decidable_eq β] [fintype β] (e : α ≃ punit.{v+1} ⊕ β),
     e.symm (sum.inl punit.star) = a ∧ (by exactI fintype.card β = fintype.card α - 1) :=
⟨{a' // a' ≠ a},
by apply_instance,
by apply_instance,
equiv_punit_sum_of_term' a,
rfl,
fintype.card_ne a⟩



section

variables [preadditive C] [has_finite_biproducts C] -- TODO these should add up to `additive`?
variables [has_binary_biproducts C] -- only needed inside the proof of diagonalization
variables [has_kernels C] -- We need this for Schur's lemma.
variables [∀ X Y : C, decidable_eq (X ⟶ Y)]

variables {ι : Type w} {Z : ι → C} (ms : mutually_simple Z)

/--
Given two objects which can be written as a sum of objects from a mutually simple family
(i.e. there are some isomorphisms `X ≅ ⨁ D`, `Y ≅ ⨁ E`),
and a morphism `f : X ⟶ Y`,
we say a "diagonalization" of `f` consists of
* a new choice of isomorphisms `d : X ≅ ⨁ D` and `e : Y ≅ ⨁ E`
* a partial equivalence between the summands of `X` and the summands of `Y`
* such that with respect to these new direct sum decompositions `f` is diagonal
  with respect to that partial equivalence
-/
structure diagonalization
  {X Y : C} (D : decomposition_over Z X) (E : decomposition_over Z Y) (f : X ⟶ Y) :=
(d : X ≅ D.O.sum)
(e : Y ≅ E.O.sum)
(p : D.O.κ ≃. E.O.κ)
(h : ∀ (x : D.O.κ) (y : E.O.κ), y ∈ p x ↔ biproduct.ι _ x ≫ d.inv ≫ f ≫ e.hom ≫ biproduct.π _ y ≠ 0)

def diagonalization_source_card_zero
  {X Y : C} (D : decomposition_over Z X) (E : decomposition_over Z Y) (f : X ⟶ Y)
  (h : fintype.card D.O.κ = 0) : diagonalization D E f := sorry

open_locale big_operators
open preadditive

example {C : Type u} {ι : Type w}
  [category C]
  [preadditive C]
  [has_finite_biproducts C]
  [has_binary_biproducts C]
  [has_kernels C]
  [Π (X Y : C), decidable_eq (X ⟶ Y)]
  {Z : ι → C}
  {X Y X' Y' : C}
  (D : decomposition_over Z X)
  (E : decomposition_over Z Y)
  (D' : decomposition_over Z X')
  (E' : decomposition_over Z Y')
  (f : X ⟶ Y)
  (f' : X' ⟶ Y')
  (Δ : diagonalization D E f)
  (Δ' : diagonalization D' E' f')
  (x : D.O.κ)
  (y : E.O.κ) :
  sum.inl y ∈ (Δ.p.sum_congr Δ'.p) (sum.inl x) ↔
    biproduct.ι (λ (k : (D.biprod D').O.κ), Z ((D.biprod D').O.summand k))
          (sum.inl x) ≫
        (biprod.map_iso Δ.d Δ'.d ≪≫ D.O.biprod_comparison D'.O).inv ≫
          biprod.map f f' ≫
            (biprod.map_iso Δ.e Δ'.e ≪≫
                 E.O.biprod_comparison E'.O).hom ≫
              biproduct.π
                (λ (k : (E.biprod E').O.κ), Z ((E.biprod E').O.summand k))
                (sum.inl y) ≠
      0 :=
begin
simp,
  -- simp only [sum_over.biprod_comparison, comp_add, add_comp, comp_sum, sum_comp],
end

def diagonalization.biprod {X Y X' Y' : C}
  (D : decomposition_over Z X) (E : decomposition_over Z Y)
  (D' : decomposition_over Z X') (E' : decomposition_over Z Y')
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  (Δ : diagonalization D E f) (Δ' : diagonalization D' E' f') :
  diagonalization (D.biprod D') (E.biprod E') (biprod.map f f') :=
{ d := (biprod.map_iso Δ.d Δ'.d).trans (sum_over.biprod_comparison _ _),
  e := (biprod.map_iso Δ.e Δ'.e).trans (sum_over.biprod_comparison _ _),
  p := Δ.p.sum_congr Δ'.p,
  h := λ x y, begin cases x, cases y, extract_goal, simp [sum_over.biprod_comparison, comp_add, add_comp, comp_sum, sum_comp], end, }


-- Okay, let's try again.
-- How does this work?
-- We're going to do an induction over `fintype.card D.O.κ`.
-- The base case is `diagonalization_source_card_zero`.
-- If `f` is zero, it's easy.
-- Otherwise, there's a non-zero matrix entry `i j`, (which is automatically an isomorphism).
-- We can set up isomorphisms `X ≅ X i ⊞ X'` and `Y ≅ Y j ⊞ Y'`


def diagonalization_conjugate
  {X Y X' Y' : C} (D : decomposition_over Z X) (E : decomposition_over Z Y) (f : X ⟶ Y)
  (Δ : diagonalization Z D E f) (iX : X ≅ X') (iY : Y ≅ Y') :
  diagonalization Z D E (iX.inv ≫ f ≫ iY.hom) := sorry

def diagonalization_conjugate'
  {X Y X' Y' : C} (D : sum_over Z) (E : sum_over Z) (f : X ⟶ Y)
  (iX : X ≅ X') (iY : Y ≅ Y')
  (Δ : diagonalization Z D E (iX.inv ≫ f ≫ iY.hom)) :
  diagonalization Z D E f := sorry

def diagonalization_foo
  {X Y : C} (D : decomposition_over.{v} Z X) (E : decomposition_over Z Y) (f : X ⟶ Y)
  (Δ : diagonalization Z D.O E.O (D.iso.inv ≫ f ≫ E.iso.hom)) :
  diagonalization Z D.O E.O f :=
diagonalization_conjugate' Z D.O E.O f D.iso E.iso Δ

def diagonalization_biprod {X Y : C} (D : sum_over Z) (E : sum_over Z) (f : X ⟶ Y)
  (Δ : diagonalization Z D E f) (i j : ι) (g : Z i ⟶ Z j) :
  diagonalization Z (D.insert i) (E.insert j) (biprod.map g f) := sorry

def diagonalization_gaussian {X Y : C} (D : sum_over Z) (E : sum_over Z) (i j : ι) (f : Z i ⊞ X ⟶ Z j ⊞ Y)
  [is_iso (biprod.inl ≫ f ≫ biprod.fst)] (Δ : diagonalization Z D E (biprod.gaussian f).2.2.1) :
  diagonalization Z (D.insert i) (E.insert j) f :=
begin
  obtain ⟨L, R, g, w⟩ := biprod.gaussian f,
  intro Δ, -- FIXME how did that get reverted??
  apply diagonalization_conjugate' _ _ _ _ L.symm R,
  simp,
  rw w,
  apply diagonalization_biprod,
  exact Δ,
end



def diagonalize'
  {X Y : C} (D : decomposition_over.{v} Z X) (E : decomposition_over Z Y) (f : X ⟶ Y)
  {n : ℕ} (h : fintype.card D.O.κ = n) :
  trunc (diagonalization Z D.O E.O f) :=
begin
  induction n with n ih generalizing X Y,
  { apply trunc.mk,
    apply diagonalization_source_card_zero,
    exact h, },
  { apply trunc.map,
    apply diagonalization_foo,
    generalize : D.iso.inv ≫ f ≫ E.iso.hom = f', clear f,
    by_cases w : ∀ (x : D.O.κ) (y : E.O.κ), biproduct.ι _ x ≫ f' ≫ biproduct.π _ y = 0,
    { apply trunc.mk,
      refine ⟨iso.refl _, iso.refl _, ⊥, _⟩,
      intros x y, split,
      rintro ⟨⟩, intro h', exfalso, dsimp at h', simp at h', erw [category.id_comp] at h', exact h' (w x y), },
    { -- Okay, we've found a nonzero entry!
      simp at w,
      replace w := trunc_sigma_of_exists w,
      trunc_cases w,
      rcases w with ⟨x, w⟩,
      replace w := trunc_sigma_of_exists w,
      trunc_cases w,
      rcases w with ⟨y, w⟩,
      apply trunc.map,
      apply diagonalization_conjugate',
      apply biproduct_iso_of_term.{v} _ x, assumption,
      apply biproduct_iso_of_term.{v} _ y, assumption,
      apply trunc.map,
      apply diagonalization_gaussian,
      -- now use conjugate?
      sorry,
    }, }
end


def diagonalize
  {X Y : C} (D : decomposition_over.{v} Z X) (E : decomposition_over Z Y) (f : X ⟶ Y) :
  trunc (diagonalization Z D E f) :=
diagonalize' Z D E f rfl

#exit

/--
An auxiliary definition for `equiv_of_simple_decomposition`,
with a specified cardinality for `D.ι`, so that we can do an induction.
-/
def equiv_of_simple_decompositions' (n : ℕ) {X : C}
  (D E : simple_decomposition.{v} X) (w : fintype.card D.ι = n) :
  trunc Σ e : D.ι ≃ E.ι, Π i, E.summand (e i) ≅ D.summand i :=
begin
  -- We proceed by induction on `n`.
  induction n with n ih generalizing X,
  { -- When the index set for `D` is empty, the index set for `E` must be empty as well.
    set e₁ := fintype.card_eq_zero_equiv_equiv_pempty w,
    set e₂ := fintype.card_eq_zero_equiv_equiv_pempty (E.card_zero_of_zero (D.zero_of_card_zero w)),
    apply trunc.mk,
    use e₁.trans (e₂.symm),
    intro i,
    cases e₁ i, },

  -- Otherwise, we consist the matrix of morphisms in `⨁ D.summand ≅ ⨁ E.summand`.
  set f : ⨁ D.summand ≅ ⨁ E.summand := D.iso.symm.trans E.iso,

  -- It has at least one column, because the cardinality of `D.ι` is positive.
  have s : trunc D.ι := trunc_of_card_pos (by { rw w, exact nat.succ_pos n, }),
  trunc_cases s,

  -- Since the whole matrix is an isomorphism, that column must have a nonzero entry.
  -- We pick such a `t`, and record as `nz` the fact that this matrix entry is nonzero.
  have column_nonzero :=
    biproduct.column_nonzero_of_iso s (id_nonzero _) f.hom,
  trunc_cases column_nonzero,
  rcases column_nonzero with ⟨t, nz⟩,

  -- In fact, by Schur's lemma that matrix entry is an isomorphism.
  haveI := is_iso_of_hom_simple nz,

  -- Our next task is to produce
  -- `h₁ : ⨁ D.summand ≅ (D.summand s) ⊞ (... the other summands ...)`
  -- `h₂ : ⨁ E.summand ≅ (E.summand t) ⊞ (... the other summands ...)`

  obtain ⟨ιD, dD, fD, eD, hD, cD⟩ := equiv_punit_sum_of_term s,
  obtain ⟨ιE, dE, fE, eE, hE, cE⟩ := equiv_punit_sum_of_term t,
  resetI,
  -- We write `X'` for "the other summands" from `D`.
  set X' : C := ⨁ (λ i, D.summand (eD.symm (sum.inr i))),

  -- We only use these internally, so it doesn't matter if they're not your favorites!
  haveI := has_binary_biproducts_of_finite_biproducts C,

  set h₁ : ⨁ D.summand ≅ (D.summand s) ⊞ (⨁ (λ i, D.summand (eD.symm (sum.inr i)))) :=
    (biproduct_iso_of_equiv_punit_sum D.summand eD).trans
      (biprod.map_iso (congr_eq_to_iso _ hD) (iso.refl _)),
  set h₂ : ⨁ E.summand ≅ (E.summand t) ⊞ (⨁ (λ i, E.summand (eE.symm (sum.inr i)))) :=
    (biproduct_iso_of_equiv_punit_sum E.summand eE).trans
      (biprod.map_iso (congr_eq_to_iso _ hE) (iso.refl _)),

  -- Now the key step of the inductive argument:
  -- because `D.summand s ≅ E.summand t`, we can produce an isomorphism between
  -- the other summands of `D` and the other summands of `E`.
  -- This uses a little argument based on Gaussian elimination.
  have h : ⨁ (λ i, D.summand (eD.symm (sum.inr i))) ≅ ⨁ (λ i, E.summand (eE.symm (sum.inr i))),
  { set h' := ((h₁.symm.trans f).trans h₂),
    have t : biprod.inl ≫ h'.hom ≫ biprod.fst =
      biproduct.ι D.summand s ≫ f.hom ≫ biproduct.π E.summand t,
    { simp only [h', h₁, h₂], simp, },
    haveI : is_iso (biprod.inl ≫ h'.hom ≫ biprod.fst) := by { rwa t, },
    exact biprod.iso_elim h', },

  -- With that in hand, we have two different decompositions of `X'`,
  -- and can use the inductive hypothesis.
  set D' : simple_decomposition X' :=
  { ι := ιD,
    summand := λ i, D.summand (eD.symm (sum.inr i)),
    iso := iso.refl _, },
  set E' : simple_decomposition X' :=
  { ι := ιE,
    summand := λ i, E.summand (eE.symm (sum.inr i)),
    iso := h, },
  have e₂ := ih D' E' (by { rw w at cD, exact cD, }),
  trunc_cases e₂ with e₂,
  rcases e₂ with ⟨e₂, π'⟩,

  -- Finally, we build the desired equivalence by sending `s` to `t`,
  -- and otherwise using the inductively constructed equivalence.
  set e := (eD.trans (equiv.sum_congr (equiv.refl _) e₂)).trans eE.symm,

  -- After that, it's just a matter of nailing down the correct behaviour
  -- of the chosen equivalence.
  have π : Π (i : D.ι), E.summand (e i) ≅ D.summand i,
  { intro i,
    by_cases i = s,
    { unfreezingI { subst h },
      simp only [e],
      have hD' : eD i = sum.inl punit.star, { rw ←hD, simp, },
      simp [hD', hE],
      exact (as_iso (biproduct.ι D.summand i ≫ f.hom ≫ biproduct.π E.summand t)).symm, },
    { have p : Σ' i' : ιD, (eD.symm) (sum.inr i') = i,
      { rcases w : eD i with ⟨⟨⟩⟩|i',
        { rw ←w at hD, simp only [equiv.symm_apply_apply] at hD, exfalso, exact h hD, },
        { use i', rw ←w, simp, }, },
      obtain ⟨i', w⟩ := p,
      calc E.summand (e i) ≅ E'.summand (e₂ i') : _
      ... ≅ D'.summand i' : π' i'
      ... ≅ D.summand i : _,
      { dsimp [E', e], rw ←w, simp, },
      { dsimp [D'], rw w, }, }, },
  exact trunc.mk ⟨e, π⟩,
end

/--
Given two decompositions of `X` into simple objects,
there is a bijection between the index sets,
such that the corresponding simple objects are isomorphic.
-/
def equiv_of_simple_decompositions {X : C} (D E : simple_decomposition.{v} X) :
  trunc Σ e : D.ι ≃ E.ι, Π i, E.summand (e i) ≅ D.summand i :=
equiv_of_simple_decompositions' (fintype.card D.ι) D E rfl

open_locale classical

lemma multiplicity_constant {X : C} (D E : simple_decomposition.{v} X) (Y : C) [simple.{v} Y] :
  D.multiplicity Y = E.multiplicity Y :=
begin
  obtain ⟨e, f⟩ := equiv_of_simple_decompositions D E,
  dsimp [simple_decomposition.multiplicity],
  apply fintype.card_congr,
  refine equiv.subtype_congr e _,
  intro i,
  refine equiv.nonempty_iff_nonempty _,
  exact
  { to_fun := λ e', (f i).trans e',
    inv_fun := λ e', (f i).symm.trans e',
    left_inv := by { intro i, simp, },
    right_inv := by { intro i, simp, }, }
end

end

variables (C) [preadditive.{v} C] [has_finite_biproducts.{v} C]

/--
A category is semisimple if every object can be written as a direct sum of simple objects.
-/
class semisimple :=
(simple_decomposition : Π X : C, trunc (simple_decomposition.{v} X))

variables {C} [semisimple.{v} C] [has_kernels.{v} C]
variables [decidable_rel (λ X Y : C, nonempty (X ≅ Y))]
variables [∀ X Y : C, decidable_eq (X ⟶ Y)]

/--
`multiplicity Y X` returns the number of simple summands of `X` which are isomorphic to `Y`.
-/
def multiplicity (Y : C) [simple.{v} Y] (X : C) : ℕ :=
begin
  have D := semisimple.simple_decomposition.{v} X,
  trunc_cases D,
  { exact D.multiplicity Y, },
  { convert multiplicity_constant a b Y, },
end

end category_theory
