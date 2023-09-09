/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.fintype.basic
import model_theory.substructures

/-!
# Elementary Maps Between First-Order Structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main Definitions
* A `first_order.language.elementary_embedding` is an embedding that commutes with the
  realizations of formulas.
* A `first_order.language.elementary_substructure` is a substructure where the realization of each
  formula agrees with the realization in the larger model.
* The `first_order.language.elementary_diagram` of a structure is the set of all sentences with
  parameters that the structure satisfies.
* `first_order.language.elementary_embedding.of_models_elementary_diagram` is the canonical
elementary embedding of any structure into a model of its elementary diagram.

## Main Results
* The Tarski-Vaught Test for embeddings: `first_order.language.embedding.is_elementary_of_exists`
gives a simple criterion for an embedding to be elementary.
* The Tarski-Vaught Test for substructures: `first_order.language.embedding.is_elementary_of_exists`
gives a simple criterion for a substructure to be elementary.
 -/

open_locale first_order
namespace first_order
namespace language
open Structure

variables (L : language) (M : Type*) (N : Type*) {P : Type*} {Q : Type*}
variables [L.Structure M] [L.Structure N] [L.Structure P] [L.Structure Q]

/-- An elementary embedding of first-order structures is an embedding that commutes with the
  realizations of formulas. -/
structure elementary_embedding :=
(to_fun : M → N)
(map_formula' : ∀ {{n}} (φ : L.formula (fin n)) (x : fin n → M),
  φ.realize (to_fun ∘ x) ↔ φ.realize x . obviously)

localized "notation (name := elementary_embedding)
  A ` ↪ₑ[`:25 L `] ` B := first_order.language.elementary_embedding L A B" in first_order

variables {L} {M} {N}

namespace elementary_embedding

instance fun_like : fun_like (M ↪ₑ[L] N) M (λ _, N) :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, begin
    cases f,
    cases g,
    simp only,
    ext x,
    exact function.funext_iff.1 h x end }

instance : has_coe_to_fun (M ↪ₑ[L] N) (λ _, M → N) := fun_like.has_coe_to_fun

@[simp] lemma map_bounded_formula (f : M ↪ₑ[L] N) {α : Type*} {n : ℕ}
  (φ : L.bounded_formula α n) (v : α → M) (xs : fin n → M) :
  φ.realize (f ∘ v) (f ∘ xs) ↔ φ.realize v xs :=
begin
  classical,
  rw [← bounded_formula.realize_restrict_free_var set.subset.rfl, set.inclusion_eq_id, iff_eq_eq],
  swap, { apply_instance },
  have h := f.map_formula' ((φ.restrict_free_var id).to_formula.relabel (fintype.equiv_fin _))
    ((sum.elim (v ∘ coe) xs) ∘ (fintype.equiv_fin _).symm),
  simp only [formula.realize_relabel, bounded_formula.realize_to_formula, iff_eq_eq] at h,
  rw [← function.comp.assoc _ _ ((fintype.equiv_fin _).symm),
    function.comp.assoc _ ((fintype.equiv_fin _).symm) (fintype.equiv_fin _),
    equiv.symm_comp_self, function.comp.right_id, function.comp.assoc, sum.elim_comp_inl,
    function.comp.assoc _ _ sum.inr, sum.elim_comp_inr,
    ← function.comp.assoc] at h,
  refine h.trans _,
  rw [function.comp.assoc _ _ (fintype.equiv_fin _), equiv.symm_comp_self,
    function.comp.right_id, sum.elim_comp_inl, sum.elim_comp_inr, ← set.inclusion_eq_id,
    bounded_formula.realize_restrict_free_var set.subset.rfl],
end

@[simp] lemma map_formula (f : M ↪ₑ[L] N) {α : Type*} (φ : L.formula α) (x : α → M) :
  φ.realize (f ∘ x) ↔ φ.realize x :=
by rw [formula.realize, formula.realize, ← f.map_bounded_formula, unique.eq_default (f ∘ default)]

lemma map_sentence (f : M ↪ₑ[L] N) (φ : L.sentence) :
  M ⊨ φ ↔ N ⊨ φ :=
by rw [sentence.realize, sentence.realize, ← f.map_formula, unique.eq_default (f ∘ default)]

lemma Theory_model_iff (f : M ↪ₑ[L] N) (T : L.Theory) :
  M ⊨ T ↔ N ⊨ T :=
by simp only [Theory.model_iff, f.map_sentence]

lemma elementarily_equivalent (f : M ↪ₑ[L] N) : M ≅[L] N :=
elementarily_equivalent_iff.2 f.map_sentence

@[simp] lemma injective (φ : M ↪ₑ[L] N) :
  function.injective φ :=
begin
  intros x y,
  have h := φ.map_formula ((var 0).equal (var 1) : L.formula (fin 2)) (λ i, if i = 0 then x else y),
  rw [formula.realize_equal, formula.realize_equal] at h,
  simp only [nat.one_ne_zero, term.realize, fin.one_eq_zero_iff, if_true, eq_self_iff_true,
    function.comp_app, if_false] at h,
  exact h.1,
end

instance embedding_like : embedding_like (M ↪ₑ[L] N) M N :=
{ injective' := injective,
  .. show fun_like (M ↪ₑ[L] N) M (λ _, N), from infer_instance }

@[simp] lemma map_fun (φ : M ↪ₑ[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) :=
begin
  have h := φ.map_formula (formula.graph f) (fin.cons (fun_map f x) x),
  rw [formula.realize_graph, fin.comp_cons, formula.realize_graph] at h,
  rw [eq_comm, h]
end

@[simp] lemma map_rel (φ : M ↪ₑ[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x :=
begin
  have h := φ.map_formula (r.formula var) x,
  exact h
end

instance strong_hom_class : strong_hom_class L (M ↪ₑ[L] N) M N :=
{ map_fun := map_fun,
  map_rel := map_rel }

@[simp] lemma map_constants (φ : M ↪ₑ[L] N) (c : L.constants) : φ c = c :=
hom_class.map_constants φ c

/-- An elementary embedding is also a first-order embedding. -/
def to_embedding (f : M ↪ₑ[L] N) : M ↪[L] N :=
{ to_fun := f,
  inj' := f.injective, }

/-- An elementary embedding is also a first-order homomorphism. -/
def to_hom (f : M ↪ₑ[L] N) : M →[L] N :=
{ to_fun := f }

@[simp] lemma to_embedding_to_hom (f : M ↪ₑ[L] N) : f.to_embedding.to_hom = f.to_hom := rfl

@[simp]
lemma coe_to_hom {f : M ↪ₑ[L] N} : (f.to_hom : M → N) = (f : M → N) := rfl

@[simp] lemma coe_to_embedding (f : M ↪ₑ[L] N) : (f.to_embedding : M → N) = (f : M → N) := rfl

lemma coe_injective : @function.injective (M ↪ₑ[L] N) (M → N) coe_fn :=
fun_like.coe_injective

@[ext]
lemma ext ⦃f g : M ↪ₑ[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

lemma ext_iff {f g : M ↪ₑ[L] N} : f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff

variables (L) (M)
/-- The identity elementary embedding from a structure to itself -/
@[refl] def refl : M ↪ₑ[L] M :=
{ to_fun := id }

variables {L} {M}

instance : inhabited (M ↪ₑ[L] M) := ⟨refl L M⟩

@[simp] lemma refl_apply (x : M) :
  refl L M x = x := rfl

/-- Composition of elementary embeddings -/
@[trans] def comp (hnp : N ↪ₑ[L] P) (hmn : M ↪ₑ[L] N) : M ↪ₑ[L] P :=
{ to_fun := hnp ∘ hmn }

@[simp] lemma comp_apply (g : N ↪ₑ[L] P) (f : M ↪ₑ[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of elementary embeddings is associative. -/
lemma comp_assoc (f : M ↪ₑ[L] N) (g : N ↪ₑ[L] P) (h : P ↪ₑ[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end elementary_embedding

variables (L) (M)

/-- The elementary diagram of an `L`-structure is the set of all sentences with parameters it
  satisfies. -/
abbreviation elementary_diagram : L[[M]].Theory := L[[M]].complete_theory M

/-- The canonical elementary embedding of an `L`-structure into any model of its elementary diagram
-/
@[simps] def elementary_embedding.of_models_elementary_diagram
  (N : Type*) [L.Structure N] [L[[M]].Structure N]
  [(Lhom_with_constants L M).is_expansion_on N] [N ⊨ L.elementary_diagram M] :
  M ↪ₑ[L] N :=
⟨(coe : L[[M]].constants → N) ∘ sum.inr, λ n φ x, begin
  refine trans _ ((realize_iff_of_model_complete_theory M N (((L.Lhom_with_constants
    M).on_bounded_formula φ).subst (constants.term ∘ sum.inr ∘ x)).alls).trans _),
  { simp_rw [sentence.realize, bounded_formula.realize_alls, bounded_formula.realize_subst,
      Lhom.realize_on_bounded_formula, formula.realize, unique.forall_iff, realize_constants] },
  { simp_rw [sentence.realize, bounded_formula.realize_alls, bounded_formula.realize_subst,
    Lhom.realize_on_bounded_formula, formula.realize, unique.forall_iff],
    refl }
end⟩

variables {L M}

namespace embedding

/-- The Tarski-Vaught test for elementarity of an embedding. -/
theorem is_elementary_of_exists (f : M ↪[L] N)
  (htv : ∀ (n : ℕ) (φ : L.bounded_formula empty (n + 1)) (x : fin n → M) (a : N),
    φ.realize default (fin.snoc (f ∘ x) a : _ → N) →
    ∃ b : M, φ.realize default (fin.snoc (f ∘ x) (f b) : _ → N)) :
  ∀{n} (φ : L.formula (fin n)) (x : fin n → M), φ.realize (f ∘ x) ↔ φ.realize x :=
begin
  suffices h : ∀ (n : ℕ) (φ : L.bounded_formula empty n) (xs : fin n → M),
    φ.realize (f ∘ default) (f ∘ xs) ↔ φ.realize default xs,
  { intros n φ x,
    refine φ.realize_relabel_sum_inr.symm.trans (trans (h n _ _) φ.realize_relabel_sum_inr), },
  refine λ n φ, φ.rec_on _ _ _ _ _,
  { exact λ _ _, iff.rfl },
  { intros,
    simp [bounded_formula.realize, ← sum.comp_elim, embedding.realize_term] },
  { intros,
    simp [bounded_formula.realize, ← sum.comp_elim, embedding.realize_term] },
  { intros _ _ _ ih1 ih2 _,
    simp [ih1, ih2] },
  { intros n φ ih xs,
    simp only [bounded_formula.realize_all],
    refine ⟨λ h a, _, _⟩,
    { rw [← ih, fin.comp_snoc],
      exact h (f a) },
    { contrapose!,
      rintro ⟨a, ha⟩,
      obtain ⟨b, hb⟩ := htv n φ.not xs a _,
      { refine ⟨b, λ h, hb (eq.mp _ ((ih _).2 h))⟩,
        rw [unique.eq_default (f ∘ default), fin.comp_snoc], },
      { rw [bounded_formula.realize_not, ← unique.eq_default (f ∘ default)],
        exact ha } } },
end

/-- Bundles an embedding satisfying the Tarski-Vaught test as an elementary embedding. -/
@[simps] def to_elementary_embedding (f : M ↪[L] N)
  (htv : ∀ (n : ℕ) (φ : L.bounded_formula empty (n + 1)) (x : fin n → M) (a : N),
    φ.realize default (fin.snoc (f ∘ x) a : _ → N) →
    ∃ b : M, φ.realize default (fin.snoc (f ∘ x) (f b) : _ → N)) :
  M ↪ₑ[L] N :=
⟨f, λ _, f.is_elementary_of_exists htv⟩

end embedding

namespace equiv

/-- A first-order equivalence is also an elementary embedding. -/
def to_elementary_embedding (f : M ≃[L] N) : M ↪ₑ[L] N :=
{ to_fun := f }

@[simp] lemma to_elementary_embedding_to_embedding (f : M ≃[L] N) :
  f.to_elementary_embedding.to_embedding = f.to_embedding := rfl

@[simp] lemma coe_to_elementary_embedding (f : M ≃[L] N) :
  (f.to_elementary_embedding : M → N) = (f : M → N) := rfl

end equiv

@[simp] lemma realize_term_substructure {α : Type*} {S : L.substructure M} (v : α → S)
  (t : L.term α) :
  t.realize (coe ∘ v) = (↑(t.realize v) : M) :=
S.subtype.realize_term t

namespace substructure

@[simp] lemma realize_bounded_formula_top {α : Type*} {n : ℕ} {φ : L.bounded_formula α n}
  {v : α → (⊤ : L.substructure M)} {xs : fin n → (⊤ : L.substructure M)} :
  φ.realize v xs ↔ φ.realize ((coe : _ → M) ∘ v) (coe ∘ xs) :=
begin
  rw ← substructure.top_equiv.realize_bounded_formula φ,
  simp,
end

@[simp] lemma realize_formula_top {α : Type*} {φ : L.formula α} {v : α → (⊤ : L.substructure M)} :
  φ.realize v ↔ φ.realize ((coe : (⊤ : L.substructure M) → M) ∘ v) :=
begin
  rw ← substructure.top_equiv.realize_formula φ,
  simp,
end

/-- A substructure is elementary when every formula applied to a tuple in the subtructure
  agrees with its value in the overall structure. -/
def is_elementary (S : L.substructure M) : Prop :=
∀ {{n}} (φ : L.formula (fin n)) (x : fin n → S), φ.realize ((coe : _ → M) ∘ x) ↔ φ.realize x

end substructure

variables (L M)
/-- An elementary substructure is one in which every formula applied to a tuple in the subtructure
  agrees with its value in the overall structure. -/
structure elementary_substructure :=
(to_substructure : L.substructure M)
(is_elementary' : to_substructure.is_elementary)

variables {L M}

namespace elementary_substructure

instance : has_coe (L.elementary_substructure M) (L.substructure M) :=
⟨elementary_substructure.to_substructure⟩

instance : set_like (L.elementary_substructure M) M :=
⟨λ x, x.to_substructure.carrier, λ ⟨⟨s, hs1⟩, hs2⟩ ⟨⟨t, ht1⟩, ht2⟩ h, begin
  congr,
  exact h,
end⟩

instance induced_Structure (S : L.elementary_substructure M) : L.Structure S :=
substructure.induced_Structure

@[simp] lemma is_elementary (S : L.elementary_substructure M) :
  (S : L.substructure M).is_elementary := S.is_elementary'

/-- The natural embedding of an `L.substructure` of `M` into `M`. -/
def subtype (S : L.elementary_substructure M) : S ↪ₑ[L] M :=
{ to_fun := coe,
  map_formula' := S.is_elementary }

@[simp] theorem coe_subtype {S : L.elementary_substructure M} : ⇑S.subtype = coe := rfl

/-- The substructure `M` of the structure `M` is elementary. -/
instance : has_top (L.elementary_substructure M) :=
⟨⟨⊤, λ n φ x, substructure.realize_formula_top.symm⟩⟩

instance : inhabited (L.elementary_substructure M) := ⟨⊤⟩

@[simp] lemma mem_top (x : M) : x ∈ (⊤ : L.elementary_substructure M) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : L.elementary_substructure M) : set M) = set.univ := rfl

@[simp] lemma realize_sentence (S : L.elementary_substructure M) (φ : L.sentence)  :
  S ⊨ φ ↔ M ⊨ φ :=
S.subtype.map_sentence φ

@[simp] lemma Theory_model_iff (S : L.elementary_substructure M) (T : L.Theory) :
  S ⊨ T ↔ M ⊨ T :=
by simp only [Theory.model_iff, realize_sentence]

instance Theory_model {T : L.Theory} [h : M ⊨ T] {S : L.elementary_substructure M} : S ⊨ T :=
(Theory_model_iff S T).2 h

instance [h : nonempty M] {S : L.elementary_substructure M} : nonempty S :=
(model_nonempty_theory_iff L).1 infer_instance

lemma elementarily_equivalent (S : L.elementary_substructure M) : S ≅[L] M :=
S.subtype.elementarily_equivalent

end elementary_substructure

namespace substructure

/-- The Tarski-Vaught test for elementarity of a substructure. -/
theorem is_elementary_of_exists (S : L.substructure M)
  (htv : ∀ (n : ℕ) (φ : L.bounded_formula empty (n + 1)) (x : fin n → S) (a : M),
    φ.realize default (fin.snoc (coe ∘ x) a : _ → M) →
    ∃ b : S, φ.realize default (fin.snoc (coe ∘ x) b : _ → M)) :
  S.is_elementary :=
λ n, S.subtype.is_elementary_of_exists htv

/-- Bundles a substructure satisfying the Tarski-Vaught test as an elementary substructure. -/
@[simps] def to_elementary_substructure (S : L.substructure M)
  (htv : ∀ (n : ℕ) (φ : L.bounded_formula empty (n + 1)) (x : fin n → S) (a : M),
    φ.realize default (fin.snoc (coe ∘ x) a : _ → M) →
    ∃ b : S, φ.realize default (fin.snoc (coe ∘ x) b : _ → M)) :
  L.elementary_substructure M :=
⟨S, S.is_elementary_of_exists htv⟩

end substructure

end language
end first_order
