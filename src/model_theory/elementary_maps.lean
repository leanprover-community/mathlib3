/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.fintype.basic
import model_theory.substructures
import model_theory.terms_and_formulas

/-!
# Elementary Maps Between First-Order Structures

## Main Definitions
* A `first_order.language.elementary_embedding` is an embedding that commutes with the
  realizations of formulas.
* A `first_order.language.elementary_substructure` is a substructure where the realization of each
  formula agrees with the realization in the larger model.

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
(map_formula' : ∀{n} (φ : L.formula (fin n)) (x : fin n → M),
  φ.realize (to_fun ∘ x) ↔ φ.realize x . obviously)

localized "notation A ` ↪ₑ[`:25 L `] ` B := L.elementary_embedding A B" in first_order

variables {L} {M} {N}

namespace elementary_embedding

instance has_coe_to_fun : has_coe_to_fun (M ↪ₑ[L] N) (λ _, M → N) :=
⟨λ f, f.to_fun⟩

@[simp] lemma map_formula (f : M ↪ₑ[L] N) {α : Type} [fintype α] (φ : L.formula α) (x : α → M) :
  φ.realize (f ∘ x) ↔ φ.realize x :=
begin
  have g := fintype.equiv_fin α,
  have h := f.map_formula' (φ.relabel g) (x ∘ g.symm),
  rw [formula.realize_relabel, formula.realize_relabel, function.comp.assoc x g.symm g,
    g.symm_comp_self, function.comp.right_id] at h,
  rw [← h, iff_eq_eq],
  congr,
  ext y,
  simp,
end

@[simp] lemma map_fun (φ : M ↪ₑ[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) :=
begin
  have h := φ.map_formula (formula.graph f) (fin.cons (fun_map f x) x),
  rw [formula.realize_graph, fin.comp_cons, formula.realize_graph] at h,
  rw [eq_comm, h]
end

@[simp] lemma map_constants (φ : M ↪ₑ[L] N) (c : L.constants) : φ c = c :=
(φ.map_fun c default).trans fun_map_eq_coe_constants

@[simp] lemma map_rel (φ : M ↪ₑ[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x :=
begin
  have h := φ.map_formula (r.formula var) x,
  exact h
end

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

lemma coe_injective : @function.injective (M ↪ₑ[L] N) (M → N) coe_fn
| f g h :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ↪ₑ[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M ↪ₑ[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

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
∀{n} (φ : L.formula (fin n)) (x : fin n → S), φ.realize ((coe : _ → M) ∘ x) ↔ φ.realize x

end substructure

variables (L) (M)
/-- An elementary substructure is one in which every formula applied to a tuple in the subtructure
  agrees with its value in the overall structure. -/
structure elementary_substructure :=
(to_substructure : L.substructure M)
(is_elementary' : to_substructure.is_elementary)

variables {L} {M}

namespace elementary_substructure

instance : has_coe (L.elementary_substructure M) (L.substructure M) :=
⟨elementary_substructure.to_substructure⟩

instance : set_like (L.elementary_substructure M) M :=
⟨λ x, x.to_substructure.carrier, λ ⟨⟨s, hs1⟩, hs2⟩ ⟨⟨t, ht1⟩, ht2⟩ h, begin
  congr,
  exact h,
end⟩

@[simp] lemma is_elementary (S : L.elementary_substructure M) :
  (S : L.substructure M).is_elementary := S.is_elementary'

/-- The natural embedding of an `L.substructure` of `M` into `M`. -/
def subtype (S : L.elementary_substructure M) : S ↪ₑ[L] M :=
{ to_fun := coe,
  map_formula' := λ n, S.is_elementary }

@[simp] theorem coe_subtype {S : L.elementary_substructure M} : ⇑S.subtype = coe := rfl

/-- The substructure `M` of the structure `M` is elementary. -/
instance : has_top (L.elementary_substructure M) :=
⟨⟨⊤, λ n φ x, substructure.realize_formula_top.symm⟩⟩

instance : inhabited (L.elementary_substructure M) := ⟨⊤⟩

@[simp] lemma mem_top (x : M) : x ∈ (⊤ : L.elementary_substructure M) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : L.elementary_substructure M) : set M) = set.univ := rfl

end elementary_substructure

end language
end first_order
