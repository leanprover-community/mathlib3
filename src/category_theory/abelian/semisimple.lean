/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.zero
import category_theory.limits.shapes.kernels
import category_theory.limits.shapes.constructions.products
import category_theory.limits.shapes.constructions.binary_products
import category_theory.abelian.basic
import category_theory.abelian.additive
import category_theory.simple
import category_theory.schur
import category_theory.isomorphism_classes
import data.fintype.card
import data.pequiv

open category_theory.limits

namespace category_theory

universes v u w
variables {C : Type u} [category.{v} C]

section
variables (C)
variables [has_zero_morphisms.{v} C]

/-- `is_isomorphic` defines a setoid on the simple objects. -/
def simple_is_isomorphic_setoid : setoid (Σ (X : C), simple X) :=
{ r := λ X Y, is_isomorphic X.1 Y.1,
  iseqv := ⟨λ X, ⟨iso.refl X.1⟩, λ X Y ⟨α⟩, ⟨α.symm⟩, λ X Y Z ⟨α⟩ ⟨β⟩, ⟨α.trans β⟩⟩ }

/-- The isomorphism classes of simples in a category. -/
def iso_classes_of_simples : Type (max u v) := quotient (simple_is_isomorphic_setoid C)

local attribute [instance] simple_is_isomorphic_setoid


/-- An arbitrarily chosen representative of each isomorphism class of simple object. -/
noncomputable def simples : iso_classes_of_simples C → C :=
λ X, (quotient.out X).1

lemma simples_non_isomorphic (i j) (h : i ≠ j) (f : simples C i ≅ simples C j) : false :=
begin
  -- FIXME golf!
  apply h, clear h,
  induction i, induction j,
  simp [simples] at f,
  apply quotient.sound,
  transitivity,
  exact setoid.symm (quotient.mk_out _),
  transitivity,
  split,
  exact f,
  exact quotient.mk_out _,
  refl,
  refl,
end

variables {C}

/-- The isomorphism class of a simple object. -/
def simple.iso_class (X : C) [simple X] : iso_classes_of_simples C :=
quotient.mk ⟨X, by apply_instance⟩

/-- Every simple object is isomorphic to the chosen representative from its isomorphism class. -/
noncomputable def simple.iso_to_representative (X : C) [simple X] :
  X ≅ simples C (simple.iso_class X) :=
classical.choice (setoid.symm (quotient.mk_out (⟨X, by apply_instance⟩ : Σ (X : C), simple X)))

noncomputable instance simples_simple (X : iso_classes_of_simples C) : simple (simples C X) :=
(quotient.out X).2

/--
We say a family of objects `Z : ι → C` in a category with zero morphisms is
"mutually simple" if
* for distinct `i j`, every morphism `Z i ⟶ Z j` is zero,
* a morphism `f : Z i ⟶ Z i` is an isomorphism iff it is not zero.

As an example, in a preadditive category with kernels,
any collection of non-isomorphic simple objects is mutually simple (by Schur's lemma).

We abstract out this notion because
1. it's useful to state the definition of Müger semisimplicity
   (which is often used to show that diagrammatic categories are semisimple), and
2. it's the key property needed to diagonalize morphisms between semisimple objects (see below).
-/
structure mutually_simple {ι : Type w} (Z : ι → C) :=
(eq_zero : ∀ {i j} (h : i ≠ j) (f : Z i ⟶ Z j), f = 0)
(simple : Π i (f : Z i ⟶ Z i), is_iso f ≃ (f ≠ 0))

end

section
variables [preadditive.{v} C] [has_kernels.{v} C]

/--
In a preadditive category with kernels,
any family of non-isomorphic simple objects is "mutually simple".
-/
def simples_mutually_simple' {ι : Type w} (Z : ι → C)
  [Π i, simple (Z i)] [Π i j, decidable_eq (Z i ⟶ Z j)]
  (w : ∀ (i j) (h : i ≠ j), (Z i ≅ Z j) → false) :
  mutually_simple Z :=
{ eq_zero := λ i j h f,
  begin
    by_contradiction,
    haveI := is_iso_of_hom_simple a,
    exact w _ _ h (as_iso f),
  end,
  simple := λ i f, is_iso_equiv_nonzero }

/--
In a preadditive category with kernels,
an arbitrarily chosen representative of each isomorphism class of simples
provides a "mutually simple" family.
-/
noncomputable def simples_mutually_simple [Π i j, decidable_eq (simples C i ⟶ simples C j)] :
  mutually_simple.{v} (simples C) :=
simples_mutually_simple' (simples C) (simples_non_isomorphic C)

end

section
variables [has_zero_morphisms.{v} C] [has_finite_biproducts.{v} C]

structure decomposition_over {ι : Type w} (Z : ι → C) (X : C) :=
(κ : Type v)
[fintype : fintype κ]
[decidable_eq : decidable_eq κ]
(summand : κ → ι)
(iso : X ≅ ⨁ (λ k, Z (summand k)))

attribute [instance] decomposition_over.fintype decomposition_over.decidable_eq

@[simps]
def decomposition_over.trivial {ι : Type w} {Z : ι → C}
  {κ : Type v} [fintype κ] [decidable_eq κ] {summand : κ → ι} :
  decomposition_over Z (⨁ (λ k, Z (summand k))) :=
{ κ := κ,
  summand := summand,
  iso := iso.refl _ }

def decomposition_over.transport {ι : Type w} {Z : ι → C} {X : C} (D : decomposition_over Z X)
  {Y : C} (i : X ≅ Y) : decomposition_over Z Y :=
{ iso := i.symm ≪≫ D.iso,
  .. D }

section
variables [has_binary_biproducts.{v} C]

def decomposition_over.biprod_single {ι : Type w} {Z : ι → C} {X : C} (D : decomposition_over Z X)
  (i : ι) : decomposition_over Z (Z i ⊞ X) :=
{ κ := punit.{v+1} ⊕ D.κ,
  summand := sum.elim (λ _, i) D.summand,
  iso := sorry }

end

structure simple_decomposition (X : C) :=
(ι : Type v)
[fintype : fintype ι]
[decidable_eq : decidable_eq ι]
(summand : ι → C)
[is_simple : Π i, simple.{v} (summand i)]
(iso : X ≅ ⨁ summand)

attribute [instance] simple_decomposition.fintype simple_decomposition.decidable_eq
attribute [instance] simple_decomposition.is_simple

def simple_decomposition.multiplicity
  [decidable_rel (λ X Y : C, nonempty (X ≅ Y))]
  {X : C} (D : simple_decomposition.{v} X) (Y : C) [simple.{v} Y] : ℕ :=
fintype.card { i // nonempty (D.summand i ≅ Y) }

lemma simple_decomposition.zero_of_card_zero
  {X : C} (D : simple_decomposition.{v} X) (h : fintype.card D.ι = 0) :
  𝟙 X = 0 :=
begin
  have e : D.ι ≃ pempty.{v} := fintype.equiv_pempty h,
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



def equiv_punit_sum_of_term' {α : Type v} [decidable_eq α] [fintype α] (a : α) :
  α ≃ punit.{v+1} ⊕ {a' // a' ≠ a} :=
{ to_fun := λ a', if h : a' = a then sum.inl punit.star else sum.inr ⟨a', h⟩,
  inv_fun := λ p, match p with | sum.inl _ := a | sum.inr v := v.1 end,
  left_inv := λ a',
  begin
    dsimp, split_ifs,
    { subst h, unfold_aux, simp, },
    { unfold_aux, simp, }
  end,
  right_inv := λ p,
  begin
    rcases p with ⟨⟨p⟩⟩|⟨a',ne⟩,
    { unfold_aux, simp, },
    { unfold_aux, simp [ne], },
  end, }

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

variables [preadditive.{v} C] [has_finite_biproducts.{v} C] -- TODO these should add up to `additive`?
variables [has_binary_biproducts.{v} C] -- only needed inside the proof of diagonalization
variables [has_kernels.{v} C] -- We need this for Schur's lemma.
variables [∀ X Y : C, decidable_eq (X ⟶ Y)]

variables {ι : Type w} (Z : ι → C) (ms : mutually_simple Z)

/--
Given two objects which can be written as a sum of objects from a mutually simple family
(i.e. there are some isomorphisms `X ≅ ⨁ D`, `Y ≅ ⨁ E`),
and a morphism `f : X ⟶ Y`,
we say a "diagonalization" of `f` consists of
* a new choice of isomorphisms `d : X ≅ ⨁ D` and `e : Y ≅ ⨁ E`
* a partial equivalence between the summands of `X` and the summands of `Y`
* such that with respect to these direct sum decompositions `f` is diagonal
  with respect to that partial equivalence
-/
structure diagonalization
  {X Y : C} (D : decomposition_over.{v} Z X) (E : decomposition_over Z Y) (f : X ⟶ Y) :=
(d : X ≅ ⨁ (λ k, Z (D.summand k)))
(e : Y ≅ ⨁ (λ k, Z (E.summand k)))
(p : D.κ ≃. E.κ)
(h : ∀ (x : D.κ) (y : E.κ), y ∈ p x ↔ biproduct.ι _ x ≫ d.inv ≫ f ≫ e.hom ≫ biproduct.π _ y ≠ 0)

def diagonalization_source_card_zero
  {X Y : C} (D : decomposition_over.{v} Z X) (E : decomposition_over Z Y) (f : X ⟶ Y)
  (h : fintype.card D.κ = 0) : diagonalization Z D E f := sorry

def diagonalization_target_card_zero
  {X Y : C} (D : decomposition_over.{v} Z X) (E : decomposition_over Z Y) (f : X ⟶ Y)
  (h : fintype.card E.κ = 0) : diagonalization Z D E f := sorry

def diagonalization_conjugate
  {X Y X' Y' : C} (D : decomposition_over.{v} Z X) (E : decomposition_over Z Y) (f : X ⟶ Y)
  (Δ : diagonalization Z D E f) (iX : X ≅ X') (iY : Y ≅ Y') :
  diagonalization Z (D.transport iX) (E.transport iY) (iX.inv ≫ f ≫ iY.hom) := sorry

def diagonalization_conjugate'
  {X Y X' Y' : C} (D : decomposition_over.{v} Z X) (E : decomposition_over Z Y) (f : X ⟶ Y)
  (iX : X ≅ X') (iY : Y ≅ Y')
  (Δ : diagonalization Z (D.transport iX) (E.transport iY) (iX.inv ≫ f ≫ iY.hom)) :
  diagonalization Z D E f := sorry

def diagonalization_foo
  {X Y : C} (D : decomposition_over.{v} Z X) (E : decomposition_over Z Y) (f : X ⟶ Y)
  (Δ : diagonalization Z decomposition_over.trivial decomposition_over.trivial (D.iso.inv ≫ f ≫ E.iso.hom)) :
  diagonalization Z D E f :=
diagonalization_conjugate' Z D E f D.iso E.iso
begin
  convert Δ;
  { dsimp [decomposition_over.transport, decomposition_over.trivial],
    congr,
    simp, }
end

def diagonalization_biprod {X Y : C} (D : decomposition_over.{v} Z X) (E : decomposition_over Z Y) (f : X ⟶ Y)
  (Δ : diagonalization Z D E f) (i : ι) (g : Z i ≅ Z i) :
  diagonalization Z (D.biprod_single i) (E.biprod_single i) (biprod.map g.hom f) := sorry

def diagonalize'
  {X Y : C} (D : decomposition_over.{v} Z X) (E : decomposition_over Z Y) (f : X ⟶ Y)
  {n : ℕ} (h : fintype.card D.κ = n) :
  trunc (diagonalization Z D E f) :=
begin
  induction n with n ih generalizing X Y,
  { apply trunc.mk,
    apply diagonalization_source_card_zero,
    exact h, },
  { apply trunc.map,
    apply diagonalization_foo,
    generalize : D.iso.inv ≫ f ≫ E.iso.hom = f', clear f,
    by_cases w : ∀ (x : D.κ) (y : E.κ), biproduct.ι _ x ≫ f' ≫ biproduct.π _ y = 0,
    { apply trunc.mk,
      refine ⟨iso.refl _, iso.refl _, ⊥, _⟩,
      intros x y, split,
      rintro ⟨⟩, intro h', exfalso, dsimp at h', simp at h', exact h' (w x y), },
    { -- Okay, we've found a nonzero entry!
      simp at w,
      replace w := trunc_sigma_of_exists w,
      trunc_cases w,
      rcases w with ⟨x, w⟩,
      replace w := trunc_sigma_of_exists w,
      trunc_cases w,
      rcases w with ⟨y, w⟩,
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
    set e₁ := fintype.equiv_pempty w,
    set e₂ := fintype.equiv_pempty (E.card_zero_of_zero (D.zero_of_card_zero w)),
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
