/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import data.nat.basic
import data.set_like.basic
import data.set.lattice
import data.fin
import data.fintype.basic
import order.closure

/-!
# Basics on First-Order Structures
This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions
* A `first_order.language` defines a language as a pair of functions from the natural numbers to
  `Type l`. One sends `n` to the type of `n`-ary functions, and the other sends `n` to the type of
  `n`-ary relations.
* A `first_order.language.Structure` interprets the symbols of a given `first_order.language` in the
  context of a given type.
* A `first_order.language.hom`, denoted `M →[L] N`, is a map from the `L`-structure `M` to the
  `L`-structure `N` that commutes with the interpretations of functions, and which preserves the
  interpretations of relations (although only in the forward direction).
* A `first_order.language.embedding`, denoted `M ↪[L] N`, is an embedding from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
* A `first_order.language.equiv`, denoted `M ≃[L] N`, is an equivalence from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
* A `first_order.language.term` is defined so that `L.term α` is the type of `L`-terms with free
  variables indexed by `α`.
* A `first_order.language.formula` is defined so that `L.formula α` is the type of `L`-formulas with
  free variables indexed by `α`.
* A `first_order.language.sentence` is a formula with no free variables.
* A `first_order.language.theory` is a set of sentences.
* A `first_order.language.definable_set` is defined so that `L.definable_set M α` is the boolean
  algebra of subsets of `α → M` defined by formulas.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/
universe variables u v

namespace first_order

/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
@[nolint check_univs] -- false positive
structure language :=
(functions : ℕ → Type u) (relations : ℕ → Type v)

namespace language

/-- The empty language has no symbols. -/
def empty : language := ⟨λ _, pempty, λ _, pempty⟩

instance : inhabited language := ⟨empty⟩

/-- The type of constants in a given language. -/
@[nolint has_inhabited_instance] def const (L : language) := L.functions 0

variable (L : language.{u v})

/-- A language is relational when it has no function symbols. -/
class is_relational : Prop :=
(empty_functions : ∀ n, L.functions n → false)

/-- A language is algebraic when it has no relation symbols. -/
class is_algebraic : Prop :=
(empty_relations : ∀ n, L.relations n → false)

variable {L}

instance is_relational_of_empty_functions {symb : ℕ → Type*} : is_relational ⟨λ _, pempty, symb⟩ :=
⟨by { intro n, apply pempty.elim }⟩

instance is_algebraic_of_empty_relations {symb : ℕ → Type*}  : is_algebraic ⟨symb, λ _, pempty⟩ :=
⟨by { intro n, apply pempty.elim }⟩

instance is_relational_empty : is_relational (empty) := language.is_relational_of_empty_functions
instance is_algebraic_empty : is_algebraic (empty) := language.is_algebraic_of_empty_relations

variables (L) (M : Type*)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
class Structure :=
(fun_map : ∀{n}, L.functions n → (fin n → M) → M)
(rel_map : ∀{n}, L.relations n → (fin n → M) → Prop)

variables (N : Type*) [L.Structure M] [L.Structure N]

open first_order.language.Structure

/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
structure hom :=
(to_fun : M → N)
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x) . obviously)
(map_rel' : ∀{n} (r : L.relations n) x, rel_map r x → rel_map r (to_fun ∘ x) . obviously)

localized "notation A ` →[`:25 L `] ` B := L.hom A B" in first_order

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
structure embedding extends M ↪ N :=
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x) . obviously)
(map_rel' : ∀{n} (r : L.relations n) x, rel_map r (to_fun ∘ x) ↔ rel_map r x . obviously)

localized "notation A ` ↪[`:25 L `] ` B := L.embedding A B" in first_order

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
structure equiv extends M ≃ N :=
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x) . obviously)
(map_rel' : ∀{n} (r : L.relations n) x, rel_map r (to_fun ∘ x) ↔ rel_map r x . obviously)

localized "notation A ` ≃[`:25 L `] ` B := L.equiv A B" in first_order

variables {L M N} {P : Type*} [L.Structure P] {Q : Type*} [L.Structure Q]

instance : has_coe_t L.const M :=
⟨λ c, fun_map c fin.elim0⟩

lemma fun_map_eq_coe_const {c : L.const} {x : fin 0 → M} :
  fun_map c x = c := congr rfl (funext fin.elim0)

namespace hom

@[simps] instance has_coe_to_fun : has_coe_to_fun (M →[L] N) :=
⟨(λ _, M → N), first_order.language.hom.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : M →[L] N} : f.to_fun = (f : M → N) := rfl

lemma coe_injective : @function.injective (M →[L] N) (M → N) coe_fn
| f g h := by {cases f, cases g, cases h, refl}

@[ext]
lemma ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M →[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

@[simp] lemma map_fun (φ : M →[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) := φ.map_fun' f x

@[simp] lemma map_const (φ : M →[L] N) (c : L.const) : φ c = c :=
(φ.map_fun c fin.elim0).trans (congr rfl (funext fin.elim0))

@[simp] lemma map_rel (φ : M →[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r x → rel_map r (φ ∘ x) := φ.map_rel' r x

variables (L) (M)
/-- The identity map from a structure to itself -/
@[refl] def id : M →[L] M :=
{ to_fun := id }

variables {L} {M}

instance : inhabited (M →[L] M) := ⟨id L M⟩

@[simp] lemma id_apply (x : M) :
  id L M x = x := rfl

/-- Composition of first-order homomorphisms -/
@[trans] def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P :=
{ to_fun := hnp ∘ hmn,
  map_rel' := λ _ _ _ h, by simp [h] }

@[simp] lemma comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order homomorphisms is associative. -/
lemma comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end hom

namespace embedding

@[simps] instance has_coe_to_fun : has_coe_to_fun (M ↪[L] N) :=
⟨(λ _, M → N), λ f, f.to_fun⟩

@[simp] lemma map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) := φ.map_fun' f x

@[simp] lemma map_const (φ : M ↪[L] N) (c : L.const) : φ c = c :=
(φ.map_fun c fin.elim0).trans (congr rfl (funext fin.elim0))

@[simp] lemma map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x := φ.map_rel' r x

/-- A first-order embedding is also a first-order homomorphism. -/
def to_hom (f : M ↪[L] N) : M →[L] N :=
{ to_fun := f }

@[simp]
lemma coe_to_hom {f : M ↪[L] N} : (f.to_hom : M → N) = f := rfl

lemma coe_injective : @function.injective (M ↪[L] N) (M → N) coe_fn
| f g h :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M ↪[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

lemma injective (f : M ↪[L] N) : function.injective f := f.to_embedding.injective

/-- In an algebraic language, any injective homomorphism is an embedding. -/
@[simps] def of_injective [L.is_algebraic] {f : M →[L] N} (hf : function.injective f) : M ↪[L] N :=
{ inj' := hf,
  map_rel' := λ n r, (is_algebraic.empty_relations n r).elim,
  .. f }

@[simp] lemma coe_fn_of_injective [L.is_algebraic] {f : M →[L] N} (hf : function.injective f) :
  (of_injective hf : M → N) = f := rfl

@[simp] lemma of_injective_to_hom [L.is_algebraic] {f : M →[L] N} (hf : function.injective f) :
  (of_injective hf).to_hom = f :=
by { ext, simp }

variables (L) (M)
/-- The identity embedding from a structure to itself -/
@[refl] def refl : M ↪[L] M :=
{ to_embedding := function.embedding.refl M }

variables {L} {M}

instance : inhabited (M ↪[L] M) := ⟨refl L M⟩

@[simp] lemma refl_apply (x : M) :
  refl L M x = x := rfl

/-- Composition of first-order embeddings -/
@[trans] def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P :=
{ to_fun := hnp ∘ hmn,
  inj' := hnp.injective.comp hmn.injective }

@[simp] lemma comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order embeddings is associative. -/
lemma comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end embedding

namespace equiv

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm] def symm (f : M ≃[L] N) : N ≃[L] M :=
{ map_fun' := λ n f' x, begin
    simp only [equiv.to_fun_as_coe],
    rw [equiv.symm_apply_eq],
    refine eq.trans _ (f.map_fun' f' (f.to_equiv.symm ∘ x)).symm,
    rw [← function.comp.assoc, equiv.to_fun_as_coe, equiv.self_comp_symm, function.comp.left_id]
  end,
  map_rel' := λ n r x, begin
    simp only [equiv.to_fun_as_coe],
    refine (f.map_rel' r (f.to_equiv.symm ∘ x)).symm.trans _,
    rw [← function.comp.assoc, equiv.to_fun_as_coe, equiv.self_comp_symm, function.comp.left_id]
  end,
  .. f.to_equiv.symm }

@[simps] instance has_coe_to_fun : has_coe_to_fun (M ≃[L] N) :=
⟨(λ _, M → N), λ f, f.to_fun⟩

@[simp]
lemma apply_symm_apply (f : M ≃[L] N) (a : N) : f (f.symm a) = a := f.to_equiv.apply_symm_apply a

@[simp]
lemma symm_apply_apply (f : M ≃[L] N) (a : M) : f.symm (f a) = a := f.to_equiv.symm_apply_apply a

@[simp] lemma map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) := φ.map_fun' f x

@[simp] lemma map_const (φ : M ≃[L] N) (c : L.const) : φ c = c :=
(φ.map_fun c fin.elim0).trans (congr rfl (funext fin.elim0))

@[simp] lemma map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x := φ.map_rel' r x

/-- A first-order equivalence is also a first-order embedding. -/
def to_embedding (f : M ≃[L] N) : M ↪[L] N :=
{ to_fun := f,
  inj' := f.to_equiv.injective }

/-- A first-order equivalence is also a first-order homomorphism. -/
def to_hom (f : M ≃[L] N) : M →[L] N :=
{ to_fun := f }

@[simp] lemma to_embedding_to_hom (f : M ≃[L] N) : f.to_embedding.to_hom = f.to_hom := rfl

@[simp]
lemma coe_to_hom {f : M ≃[L] N} : (f.to_hom : M → N) = (f : M → N) := rfl

@[simp] lemma coe_to_embedding (f : M ≃[L] N) : (f.to_embedding : M → N) = (f : M → N) := rfl

lemma coe_injective : @function.injective (M ≃[L] N) (M → N) coe_fn
| f g h :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M ≃[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

lemma injective (f : M ≃[L] N) : function.injective f := f.to_embedding.injective

variables (L) (M)
/-- The identity equivalence from a structure to itself -/
@[refl] def refl : M ≃[L] M :=
{ to_equiv := equiv.refl M }

variables {L} {M}

instance : inhabited (M ≃[L] M) := ⟨refl L M⟩

@[simp] lemma refl_apply (x : M) :
  refl L M x = x := rfl

/-- Composition of first-order equivalences -/
@[trans] def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
{ to_fun := hnp ∘ hmn,
  .. (hmn.to_equiv.trans hnp.to_equiv) }

@[simp] lemma comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order homomorphisms is associative. -/
lemma comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end equiv

section closed_under

open set

variables {n : ℕ} (f : L.functions n) (s : set M)

/-- Indicates that a set in a given structure is a closed under a function symbol. -/
def closed_under : Prop :=
∀ (x : fin n → M), (∀ i : fin n, x i ∈ s) → fun_map f x ∈ s

variable (L)

@[simp] lemma closed_under_univ : closed_under f (univ : set M) :=
λ _ _, mem_univ _

variables {L f s} {t : set M}

namespace closed_under

lemma inter (hs : closed_under f s) (ht : closed_under f t) :
  closed_under f (s ∩ t) :=
λ x h, mem_inter (hs x (λ i, mem_of_mem_inter_left (h i)))
  (ht x (λ i, mem_of_mem_inter_right (h i)))

lemma inf (hs : closed_under f s) (ht : closed_under f t) :
  closed_under f (s ⊓ t) := hs.inter ht

variables {S : set (set M)}

lemma Inf (hS : ∀ s, s ∈ S → closed_under f s) : closed_under f (Inf S) :=
λ x h s hs, hS s hs x (λ i, h i s hs)

end closed_under
end closed_under

variables (L) (M)

/-- A substructure of a structure `M` is a set closed under application of function symbols. -/
structure substructure :=
(carrier : set M)
(fun_mem : ∀{n}, ∀ (f : L.functions n), closed_under f carrier)

variables {L} {M}

namespace substructure

instance : set_like (L.substructure M) M :=
⟨substructure.carrier, λ p q h, by cases p; cases q; congr'⟩

/-- See Note [custom simps projection] -/
def simps.coe (S : L.substructure M) : set M := S
initialize_simps_projections substructure (carrier → coe)

@[simp]
lemma mem_carrier {s : L.substructure M} {x : M} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

/-- Two substructures are equal if they have the same elements. -/
@[ext]
theorem ext {S T : L.substructure M}
  (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

/-- Copy a substructure replacing `carrier` with a set that is equal to it. -/
protected def copy (S : L.substructure M) (s : set M) (hs : s = S) : L.substructure M :=
{ carrier := s,
  fun_mem := λ n f, hs.symm ▸ (S.fun_mem f) }

variable {S : L.substructure M}

@[simp] lemma coe_copy {s : set M} (hs : s = S) :
  (S.copy s hs : set M) = s := rfl

lemma copy_eq {s : set M} (hs : s = S) : S.copy s hs = S :=
set_like.coe_injective hs

lemma const_mem {c : L.const} : ↑c ∈ S :=
mem_carrier.2 (S.fun_mem c _ fin.elim0)

/-- The substructure `M` of the structure `M`. -/
instance : has_top (L.substructure M) :=
⟨{ carrier := set.univ,
   fun_mem := λ n f x h, set.mem_univ _ }⟩

instance : inhabited (L.substructure M) := ⟨⊤⟩

@[simp] lemma mem_top (x : M) : x ∈ (⊤ : L.substructure M) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : L.substructure M) : set M) = set.univ := rfl

/-- The inf of two substructures is their intersection. -/
instance : has_inf (L.substructure M) :=
⟨λ S₁ S₂,
  { carrier := S₁ ∩ S₂,
    fun_mem := λ n f, (S₁.fun_mem f).inf (S₂.fun_mem f) }⟩

@[simp]
lemma coe_inf (p p' : L.substructure M) : ((p ⊓ p' : L.substructure M) : set M) = p ∩ p' := rfl

@[simp]
lemma mem_inf {p p' : L.substructure M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

instance : has_Inf (L.substructure M) :=
⟨λ s, { carrier := ⋂ t ∈ s, ↑t,
        fun_mem := λ n f, closed_under.Inf begin
          rintro _ ⟨t, rfl⟩,
          by_cases h : t ∈ s,
          { simpa [h] using t.fun_mem f },
          { simp [h] }
        end }⟩

@[simp, norm_cast]
lemma coe_Inf (S : set (L.substructure M)) :
  ((Inf S : L.substructure M) : set M) = ⋂ s ∈ S, ↑s := rfl

lemma mem_Inf {S : set (L.substructure M)} {x : M} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
  set.mem_bInter_iff

lemma mem_infi {ι : Sort*} {S : ι → L.substructure M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp, norm_cast]
lemma coe_infi {ι : Sort*} {S : ι → L.substructure M} : (↑(⨅ i, S i) : set M) = ⋂ i, S i :=
by simp only [infi, coe_Inf, set.bInter_range]

/-- Substructures of a structure form a complete lattice. -/
instance : complete_lattice (L.substructure M) :=
{ le           := (≤),
  lt           := (<),
  top          := (⊤),
  le_top       := λ S x hx, mem_top x,
  inf          := (⊓),
  Inf          := has_Inf.Inf,
  le_inf       := λ a b c ha hb x hx, ⟨ha hx, hb hx⟩,
  inf_le_left  := λ a b x, and.left,
  inf_le_right := λ a b x, and.right,
  .. complete_lattice_of_Inf (L.substructure M) $ λ s,
    is_glb.of_image (λ S T,
      show (S : set M) ≤ T ↔ S ≤ T, from set_like.coe_subset_coe) is_glb_binfi }

variable (L)

/-- The `L.substructure` generated by a set. -/
def closure : lower_adjoint (coe : L.substructure M → set M) := ⟨λ s, Inf {S | s ⊆ S},
  λ s S, ⟨set.subset.trans (λ x hx, mem_Inf.2 $ λ S hS, hS hx), λ h, Inf_le h⟩⟩

variables {L} {s : set M}

lemma mem_closure {x : M} : x ∈ closure L s ↔ ∀ S : L.substructure M, s ⊆ S → x ∈ S :=
mem_Inf

/-- The substructure generated by a set includes the set. -/
@[simp]
lemma subset_closure : s ⊆ closure L s := (closure L).le_closure s

@[simp]
lemma closed (S : L.substructure M) : (closure L).closed (S : set M) :=
congr rfl ((closure L).eq_of_le set.subset.rfl (λ x xS, mem_closure.2 (λ T hT, hT xS)))

open set

/-- A substructure `S` includes `closure L s` if and only if it includes `s`. -/
@[simp]
lemma closure_le : closure L s ≤ S ↔ s ⊆ S := (closure L).closure_le_closed_iff_le s S.closed

/-- Substructure closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure L s ≤ closure L t`. -/
lemma closure_mono ⦃s t : set M⦄ (h : s ⊆ t) : closure L s ≤ closure L t :=
(closure L).monotone h

lemma closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure L s) : closure L s = S :=
(closure L).eq_of_le h₁ h₂

variable (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under function symbols, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_eliminator] lemma closure_induction {p : M → Prop} {x} (h : x ∈ closure L s)
  (Hs : ∀ x ∈ s, p x)
  (Hfun : ∀ {n : ℕ} (f : L.functions n), closed_under f (set_of p)) : p x :=
(@closure_le L M _ ⟨set_of p, λ n, Hfun⟩ _).2 Hs h

/-- If `s` is a dense set in a structure `M`, `substructure.closure L s = ⊤`, then in order to prove
that some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify
that `p` is preserved under function symbols. -/
@[elab_as_eliminator] lemma dense_induction {p : M → Prop} (x : M) {s : set M}
  (hs : closure L s = ⊤) (Hs : ∀ x ∈ s, p x)
  (Hfun : ∀ {n : ℕ} (f : L.functions n), closed_under f (set_of p)) : p x :=
have ∀ x ∈ closure L s, p x, from λ x hx, closure_induction hx Hs (λ n, Hfun),
by simpa [hs] using this x

variables (L) (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : galois_insertion (@closure L M _) coe :=
{ choice := λ s _, closure L s,
  gc := (closure L).gc,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variables {L} {M}

/-- Closure of a substructure `S` equals `S`. -/
@[simp] lemma closure_eq : closure L (S : set M) = S := (substructure.gi L M).l_u_eq S

@[simp] lemma closure_empty : closure L (∅ : set M) = ⊥ :=
(substructure.gi L M).gc.l_bot

@[simp] lemma closure_univ : closure L (univ : set M) = ⊤ :=
@coe_top L M _ ▸ closure_eq ⊤

lemma closure_union (s t : set M) : closure L (s ∪ t) = closure L s ⊔ closure L t :=
(substructure.gi L M).gc.l_sup

lemma closure_Union {ι} (s : ι → set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i) :=
(substructure.gi L M).gc.l_supr

/-!
### `comap` and `map`
-/

/-- The preimage of a substructure along a homomorphism is a substructure. -/
@[simps] def comap (φ : M →[L] N) (S : L.substructure N) : L.substructure M :=
{ carrier := (φ ⁻¹' S),
  fun_mem := λ n f x hx, begin
    rw [mem_preimage, φ.map_fun],
    exact S.fun_mem f (φ ∘ x) hx,
  end }

@[simp]
lemma mem_comap {S : L.substructure N} {f : M →[L] N} {x : M} : x ∈ S.comap f ↔ f x ∈ S := iff.rfl

lemma comap_comap (S : L.substructure P) (g : N →[L] P) (f : M →[L] N) :
  (S.comap g).comap f = S.comap (g.comp f) :=
rfl

@[simp]
lemma comap_id (S : L.substructure P) : S.comap (hom.id _ _) = S :=
ext (by simp)

/-- The image of a substructure along a homomorphism is a substructure. -/
@[simps] def map (φ : M →[L] N) (S : L.substructure M) : L.substructure N :=
{ carrier := (φ '' S),
  fun_mem := λ n f x hx, (mem_image _ _ _).1
    ⟨fun_map f (λ i, classical.some (hx i)),
     S.fun_mem f _ (λ i, (classical.some_spec (hx i)).1),
     begin
       simp only [hom.map_fun, set_like.mem_coe],
       exact congr rfl (funext (λ i, (classical.some_spec (hx i)).2)),
     end⟩ }

@[simp]
lemma mem_map {f : M →[L] N} {S : L.substructure M} {y : N} :
  y ∈ S.map f ↔ ∃ x ∈ S, f x = y :=
mem_image_iff_bex

lemma mem_map_of_mem (f : M →[L] N) {S : L.substructure M} {x : M} (hx : x ∈ S) : f x ∈ S.map f :=
mem_image_of_mem f hx

lemma apply_coe_mem_map (f : M →[L] N) (S : L.substructure M) (x : S) : f x ∈ S.map f :=
mem_map_of_mem f x.prop

lemma map_map (g : N →[L] P) (f : M →[L] N) : (S.map f).map g = S.map (g.comp f) :=
set_like.coe_injective $ image_image _ _ _

lemma map_le_iff_le_comap {f : M →[L] N} {S : L.substructure M} {T : L.substructure N} :
  S.map f ≤ T ↔ S ≤ T.comap f :=
image_subset_iff

lemma gc_map_comap (f : M →[L] N) : galois_connection (map f) (comap f) :=
λ S T, map_le_iff_le_comap

lemma map_le_of_le_comap {T : L.substructure N} {f : M →[L] N} : S ≤ T.comap f → S.map f ≤ T :=
(gc_map_comap f).l_le

lemma le_comap_of_map_le {T : L.substructure N} {f : M →[L] N} : S.map f ≤ T → S ≤ T.comap f :=
(gc_map_comap f).le_u

lemma le_comap_map {f : M →[L] N} : S ≤ (S.map f).comap f :=
(gc_map_comap f).le_u_l _

lemma map_comap_le {S : L.substructure N} {f : M →[L] N} : (S.comap f).map f ≤ S :=
(gc_map_comap f).l_u_le _

lemma monotone_map {f : M →[L] N} : monotone (map f) :=
(gc_map_comap f).monotone_l

lemma monotone_comap {f : M →[L] N} : monotone (comap f) :=
(gc_map_comap f).monotone_u

@[simp]
lemma map_comap_map {f : M →[L] N} : ((S.map f).comap f).map f = S.map f :=
congr_fun ((gc_map_comap f).l_u_l_eq_l) _

@[simp]
lemma comap_map_comap {S : L.substructure N} {f : M →[L] N} :
  ((S.comap f).map f).comap f = S.comap f :=
congr_fun ((gc_map_comap f).u_l_u_eq_u) _

lemma map_sup (S T : L.substructure M) (f : M →[L] N) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
(gc_map_comap f).l_sup

lemma map_supr {ι : Sort*} (f : M →[L] N) (s : ι → L.substructure M) :
  (supr s).map f = ⨆ i, (s i).map f :=
(gc_map_comap f).l_supr

lemma comap_inf (S T : L.substructure N) (f : M →[L] N) : (S ⊓ T).comap f = S.comap f ⊓ T.comap f :=
(gc_map_comap f).u_inf

lemma comap_infi {ι : Sort*} (f : M →[L] N) (s : ι → L.substructure N) :
  (infi s).comap f = ⨅ i, (s i).comap f :=
(gc_map_comap f).u_infi

@[simp] lemma map_bot (f : M →[L] N) : (⊥ : L.substructure M).map f = ⊥ :=
(gc_map_comap f).l_bot

@[simp] lemma comap_top (f : M →[L] N) : (⊤ : L.substructure N).comap f = ⊤ :=
(gc_map_comap f).u_top

@[simp] lemma map_id (S : L.substructure M) : S.map (hom.id L M) = S :=
ext (λ x, ⟨λ ⟨_, h, rfl⟩, h, λ h, ⟨_, h, rfl⟩⟩)

section galois_coinsertion

variables {ι : Type*} {f : M →[L] N} (hf : function.injective f)

include hf

/-- `map f` and `comap f` form a `galois_coinsertion` when `f` is injective. -/
def gci_map_comap : galois_coinsertion (map f) (comap f) :=
(gc_map_comap f).to_galois_coinsertion
  (λ S x, by simp [mem_comap, mem_map, hf.eq_iff])

lemma comap_map_eq_of_injective (S : L.substructure M) : (S.map f).comap f = S :=
(gci_map_comap hf).u_l_eq _

lemma comap_surjective_of_injective : function.surjective (comap f) :=
(gci_map_comap hf).u_surjective

lemma map_injective_of_injective : function.injective (map f) :=
(gci_map_comap hf).l_injective

lemma comap_inf_map_of_injective (S T : L.substructure M) : (S.map f ⊓ T.map f).comap f = S ⊓ T :=
(gci_map_comap hf).u_inf_l _ _

lemma comap_infi_map_of_injective (S : ι → L.substructure M) :
  (⨅ i, (S i).map f).comap f = infi S :=
(gci_map_comap hf).u_infi_l _

lemma comap_sup_map_of_injective (S T : L.substructure M) : (S.map f ⊔ T.map f).comap f = S ⊔ T :=
(gci_map_comap hf).u_sup_l _ _

lemma comap_supr_map_of_injective (S : ι → L.substructure M) :
  (⨆ i, (S i).map f).comap f = supr S :=
(gci_map_comap hf).u_supr_l _

lemma map_le_map_iff_of_injective {S T : L.substructure M} : S.map f ≤ T.map f ↔ S ≤ T :=
(gci_map_comap hf).l_le_l_iff

lemma map_strict_mono_of_injective : strict_mono (map f) :=
(gci_map_comap hf).strict_mono_l

end galois_coinsertion

section galois_insertion

variables {ι : Type*} {f : M →[L] N} (hf : function.surjective f)

include hf

/-- `map f` and `comap f` form a `galois_insertion` when `f` is surjective. -/
def gi_map_comap : galois_insertion (map f) (comap f) :=
(gc_map_comap f).to_galois_insertion
  (λ S x h, let ⟨y, hy⟩ := hf x in mem_map.2 ⟨y, by simp [hy, h]⟩)

lemma map_comap_eq_of_surjective (S : L.substructure N) : (S.comap f).map f = S :=
(gi_map_comap hf).l_u_eq _

lemma map_surjective_of_surjective : function.surjective (map f) :=
(gi_map_comap hf).l_surjective

lemma comap_injective_of_surjective : function.injective (comap f) :=
(gi_map_comap hf).u_injective

lemma map_inf_comap_of_surjective (S T : L.substructure N) :
  (S.comap f ⊓ T.comap f).map f = S ⊓ T :=
(gi_map_comap hf).l_inf_u _ _

lemma map_infi_comap_of_surjective (S : ι → L.substructure N) :
  (⨅ i, (S i).comap f).map f = infi S :=
(gi_map_comap hf).l_infi_u _

lemma map_sup_comap_of_surjective (S T : L.substructure N) :
  (S.comap f ⊔ T.comap f).map f = S ⊔ T :=
(gi_map_comap hf).l_sup_u _ _

lemma map_supr_comap_of_surjective (S : ι → L.substructure N) :
  (⨆ i, (S i).comap f).map f = supr S :=
(gi_map_comap hf).l_supr_u _

lemma comap_le_comap_iff_of_surjective {S T : L.substructure N} :
  S.comap f ≤ T.comap f ↔ S ≤ T :=
(gi_map_comap hf).u_le_u_iff

lemma comap_strict_mono_of_surjective : strict_mono (comap f) :=
(gi_map_comap hf).strict_mono_u

end galois_insertion

instance induced_Structure {S : L.substructure M} : L.Structure S :=
{ fun_map := λ n f x, ⟨fun_map f (λ i, x i), S.fun_mem f (λ i, x i) (λ i, (x i).2)⟩,
  rel_map := λ n r x, rel_map r (λ i, (x i : M)) }

/-- The natural embedding of an `L.substructure` of `M` into `M`. -/
def subtype (S : L.substructure M) : S ↪[L] M :=
{ to_fun := coe,
  inj' := subtype.coe_injective }

@[simp] theorem coe_subtype : ⇑S.subtype = coe := rfl

/-- An induction principle on elements of the type `substructure.closure L s`.
If `p` holds for `1` and all elements of `s`, and is preserved under multiplication, then `p`
holds for all elements of the closure of `s`.
The difference with `substructure.closure_induction` is that this acts on the subtype.
-/
@[elab_as_eliminator] lemma closure_induction' (s : set M) {p : closure L s → Prop}
  (Hs : ∀ x (h : x ∈ s), p ⟨x, subset_closure h⟩)
  (Hfun : ∀ {n : ℕ} (f : L.functions n), closed_under f (set_of p))
  (x : closure L s) :
  p x :=
subtype.rec_on x $ λ x hx, begin
  refine exists.elim _ (λ (hx : x ∈ closure L s) (hc : p ⟨x, hx⟩), hc),
  exact closure_induction hx (λ x hx, ⟨subset_closure hx, Hs x hx⟩) (λ n f x hx,
    ⟨(closure L s).fun_mem f _ (λ i, classical.some (hx i)),
    Hfun f (λ i, ⟨x i, classical.some (hx i)⟩) (λ i, classical.some_spec (hx i))⟩),
end

end substructure

namespace hom

open substructure

/-- The substructure of elements `x : M` such that `f x = g x` -/
def eq_locus (f g : M →[L] N) : substructure L M :=
{ carrier := {x : M | f x = g x},
  fun_mem := λ n fn x hx, by {
    have h : f ∘ x = g ∘ x := by { ext, repeat {rw function.comp_apply}, apply hx, },
    simp [h], } }

/-- If two `L.hom`s are equal on a set, then they are equal on its substructure closure. -/
lemma eq_on_closure {f g : M →[L] N} {s : set M} (h : set.eq_on f g s) :
  set.eq_on f g (closure L s) :=
show closure L s ≤ f.eq_locus g, from closure_le.2 h

lemma eq_of_eq_on_top {f g : M →[L] N} (h : set.eq_on f g (⊤ : substructure L M)) :
  f = g :=
ext $ λ x, h trivial

variable {s : set M}

lemma eq_of_eq_on_dense (hs : closure L s = ⊤) {f g : M →[L] N} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_top $ hs ▸ eq_on_closure h

end hom

variable (L)
/-- A term on `α` is either a variable indexed by an element of `α`
  or a function symbol applied to simpler terms. -/
inductive term (α : Type) : Type u
| var {} : ∀ (a : α), term
| func {} : ∀ {l : ℕ} (f : L.functions l) (ts : fin l → term), term
export term

variable {L}

/-- Relabels a term's variables along a particular function. -/
@[simp] def term.relabel {α β : Type} (g : α → β) : L.term α → L.term β
| (var i) := var (g i)
| (func f ts) := func f (λ i, (ts i).relabel)

instance {α : Type} [inhabited α] : inhabited (L.term α) :=
⟨var (default α)⟩

instance {α} : has_coe L.const (L.term α) :=
⟨λ c, func c fin_zero_elim⟩

/-- A term `t` with variables indexed by `α` can be evaluated by giving a value to each variable. -/
@[simp] def realize_term {α : Type} (v : α → M) :
  ∀ (t : L.term α), M
| (var k)         := v k
| (func f ts)     := fun_map f (λ i, realize_term (ts i))

@[simp] lemma realize_term_relabel {α β : Type} (g : α → β) (v : β → M) (t : L.term α) :
  realize_term v (t.relabel g) = realize_term (v ∘ g) t :=
begin
  induction t with _ n f ts ih,
  { refl, },
  { simp [ih] }
end

@[simp] lemma realize_term_hom {α : Type} [L.Structure N] (v : α → M)
  (t : L.term α) (g : M →[L] N) :
  realize_term (g ∘ v) t = g (realize_term v t) :=
begin
  induction t,
  { refl },
  { rw [realize_term, realize_term, g.map_fun],
    refine congr rfl _,
    ext x,
    simp [t_ih x], },
end

@[simp] lemma realize_term_embedding {α : Type} [L.Structure N] (v : α → M)
  (t : L.term α) (g : M ↪[L] N) :
  realize_term (g ∘ v) t = g (realize_term v t) :=
realize_term_hom v t g.to_hom

@[simp] lemma realize_term_equiv {α : Type} [L.Structure N] (v : α → M)
  (t : L.term α) (g : M ≃[L] N) :
  realize_term (g ∘ v) t = g (realize_term v t) :=
realize_term_hom v t g.to_hom

@[simp] lemma realize_term_substructure {α : Type} {S : L.substructure M} (v : α → S)
  (t : L.term α) :
  realize_term (coe ∘ v) t = (↑(realize_term v t) : M) :=
realize_term_embedding v t S.subtype

variable (L)
/-- `bounded_formula α n` is the type of formulas with free variables indexed by `α` and up to `n`
  additional free variables. -/
inductive bounded_formula (α : Type) : ℕ → Type (max u v)
| bd_falsum {} {n} : bounded_formula n
| bd_equal {n} (t₁ t₂ : L.term (α ⊕ fin n)) : bounded_formula n
| bd_rel {n l : ℕ} (R : L.relations l) (ts : fin l → L.term (α ⊕ fin n)) : bounded_formula n
| bd_imp {n} (f₁ f₂ : bounded_formula n) : bounded_formula n
| bd_all {n} (f : bounded_formula (n+1)) : bounded_formula n

export bounded_formula

instance {α : Type} {n : ℕ} : inhabited (L.bounded_formula α n) :=
⟨bd_falsum⟩

/-- `formula α` is the type of formulas with all free variables indexed by `α`. -/
@[reducible] def formula (α : Type) := L.bounded_formula α 0

/-- A sentence is a formula with no free variables. -/
@[reducible] def sentence           := L.formula pempty

/-- A theory is a set of sentences. -/
@[reducible] def theory := set L.sentence

variables {L} {α : Type}

section formula
variable {n : ℕ}

@[simps] instance : has_bot (L.bounded_formula α n) := ⟨bd_falsum⟩

/-- The negation of a bounded formula is also a bounded formula. -/
@[reducible] def bd_not (φ : L.bounded_formula α n) : L.bounded_formula α n :=
  bd_imp φ ⊥

@[simps] instance : has_top (L.bounded_formula α n) := ⟨bd_not bd_falsum⟩

@[simps] instance : has_inf (L.bounded_formula α n) := ⟨λ f g, bd_not (bd_imp f (bd_not g))⟩

@[simps] instance : has_sup (L.bounded_formula α n) := ⟨λ f g, bd_imp (bd_not f) g⟩

/-- Relabels a bounded formula's variables along a particular function. -/
@[simp] def bounded_formula.relabel {α β : Type} (g : α → β) :
  ∀ {n : ℕ}, L.bounded_formula α n → L.bounded_formula β n
| n bd_falsum := bd_falsum
| n (bd_equal t₁ t₂) := bd_equal (t₁.relabel (sum.elim (sum.inl ∘ g) sum.inr))
    (t₂.relabel (sum.elim (sum.inl ∘ g) sum.inr))
| n (bd_rel R ts) := bd_rel R ((term.relabel (sum.elim (sum.inl ∘ g) sum.inr)) ∘ ts)
| n (bd_imp f₁ f₂) := bd_imp f₁.relabel f₂.relabel
| n (bd_all f) := bd_all f.relabel

namespace formula

/-- The equality of two terms as a first-order formula. -/
def equal (t₁ t₂ : L.term α) : (L.formula α) :=
bd_equal (t₁.relabel sum.inl) (t₂.relabel sum.inl)

/-- The graph of a function as a first-order formula. -/
def graph (f : L.functions n) : L.formula (fin (n + 1)) :=
equal (func f (λ i, var i)) (var n)

end formula
end formula

variable {L}

instance nonempty_bounded_formula {α : Type} (n : ℕ) : nonempty $ L.bounded_formula α n :=
  nonempty.intro (by constructor)

variables (M)

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
@[simp] def realize_bounded_formula :
  ∀ {l} (f : L.bounded_formula α l) (v : α → M) (xs : fin l → M), Prop
| _ bd_falsum  v     xs := false
| _ (bd_equal t₁ t₂) v xs := realize_term (sum.elim v xs) t₁ = realize_term (sum.elim v xs) t₂
| _ (bd_rel R ts)   v   xs := rel_map R (λ i, realize_term (sum.elim v xs) (ts i))
| _ (bd_imp f₁ f₂)  v xs := realize_bounded_formula f₁ v xs → realize_bounded_formula f₂ v xs
| _ (bd_all f)     v   xs := ∀(x : M), realize_bounded_formula f v (fin.cons x xs)

/-- A bounded formula can be evaluated as true or false by giving values to each free variable. -/
@[reducible] def realize_formula (f : L.formula α) (v : α → M) : Prop :=
realize_bounded_formula M f v fin_zero_elim

/-- A sentence can be evaluated as true or false in a structure. -/
@[reducible] def realize_sentence (φ : L.sentence) : Prop :=
realize_formula M φ pempty.elim

variable {M}

@[simp] lemma realize_bounded_formula_relabel {α β : Type} {n : ℕ}
  (g : α → β) (v : β → M) (xs : fin n → M) (φ : L.bounded_formula α n) :
  realize_bounded_formula M (φ.relabel g) v xs ↔ realize_bounded_formula M φ (v ∘ g) xs :=
begin
  have h : ∀ (m : ℕ) (xs' : fin m → M), sum.elim v xs' ∘
    sum.elim (sum.inl ∘ g) sum.inr = sum.elim (v ∘ g) xs',
  { intros m xs',
    ext x,
    cases x;
    simp, },
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp [h _ xs] },
  { simp [h _ xs] },
  { simp [ih1, ih2] },
  { simp [ih3] }
end

@[simp] lemma realize_bounded_formula_equiv {α : Type} {n : ℕ} [L.Structure N] (v : α → M)
  (xs : fin n → M) (φ : L.bounded_formula α n) (g : M ≃[L] N) :
  realize_bounded_formula N φ (g ∘ v) (g ∘ xs) ↔ realize_bounded_formula M φ v xs :=
begin
  induction φ with _ _ _ _ _ _ _ _ _ _ _ ih1 ih2 _ _ ih3,
  { refl },
  { simp only [realize_bounded_formula, ← sum.comp_elim, realize_term_equiv, g.injective.eq_iff] },
  { simp only [realize_bounded_formula, ← sum.comp_elim, realize_term_equiv, g.map_rel], },
  { rw [realize_bounded_formula, ih1, ih2, realize_bounded_formula] },
  { rw [realize_bounded_formula, realize_bounded_formula],
    split,
    { intros h a,
      have h' := h (g a),
      rw [← fin.comp_cons, ih3] at h',
      exact h' },
    { intros h a,
      have h' := h (g.symm a),
      rw [← ih3, fin.comp_cons, g.apply_symm_apply] at h',
      exact h' }}
end

@[simp] lemma realize_bounded_formula_top {α : Type} {n : ℕ} (v : α → (⊤ : L.substructure M))
  (xs : fin n → (⊤ : L.substructure M)) (φ : L.bounded_formula α n) :
  realize_bounded_formula (⊤ : L.substructure M) φ v xs ↔
  realize_bounded_formula M φ (coe ∘ v) (coe ∘ xs) :=
begin
  induction φ with _ _ _ _ _ _ _ _ a b c d e f g h i j,
  { refl },
  { simp only [realize_bounded_formula, ← sum.comp_elim, realize_term_substructure],
    rw subtype.ext_iff, },
  { simp only [realize_bounded_formula, ← sum.comp_elim, realize_term_substructure],
    rw [← substructure.coe_subtype, (⊤ : L.substructure M).subtype.map_rel], },
  { rw [realize_bounded_formula, d, e, realize_bounded_formula] },
  { rw [realize_bounded_formula, realize_bounded_formula, set_like.forall],
    apply forall_congr,
    intro a,
    simp [h, fin.comp_cons], }
end

@[simp] lemma realize_not {l} (f : L.bounded_formula α l) (v : α → M) (xs : fin l → M) :
  realize_bounded_formula M (bd_not f) v xs = ¬ realize_bounded_formula M f v xs :=
rfl

@[simp] lemma realize_formula_relabel {α β : Type}
  (g : α → β) (v : β → M) (φ : L.formula α) :
  realize_formula M (φ.relabel g) v ↔ realize_formula M φ (v ∘ g) :=
by rw [realize_formula, realize_formula, realize_bounded_formula_relabel]

@[simp] lemma realize_formula_equiv {α : Type} [L.Structure N] (v : α → M) (φ : L.formula α)
  (g : M ≃[L] N) :
  realize_formula N φ (g ∘ v) ↔ realize_formula M φ v :=
begin
  rw [realize_formula, realize_formula, ← realize_bounded_formula_equiv v fin_zero_elim φ g,
    iff_eq_eq],
  exact congr rfl (funext fin_zero_elim),
end

@[simp]
lemma realize_equal {α : Type*} (t₁ t₂ : L.term α) (x : α → M) :
  realize_formula M (formula.equal t₁ t₂) x ↔ realize_term x t₁ = realize_term x t₂ :=
by simp [formula.equal, realize_formula]

@[simp]
lemma realize_graph {l : ℕ} (f : L.functions l) (x : fin l → M) (y : M) :
  realize_formula M (formula.graph f) (fin.snoc x y) ↔ fun_map f x = y :=
begin
  simp only [formula.graph, realize_term, fin.coe_eq_cast_succ, realize_equal, fin.snoc_cast_succ],
  rw [fin.coe_nat_eq_last, fin.snoc_last],
end

section definability

variables (L) [fintype α]

/-- A subset of a finite Cartesian product of a structure is definable when membership in
  the set is given by a first-order formula. -/
class is_definable (s : set (α → M)) : Prop :=
(exists_formula : ∃ (φ : L.formula α), s = set_of (realize_formula M φ))

@[simp]
lemma is_definable_empty : L.is_definable (∅ : set (α → M)) :=
⟨⟨⊥, by {ext, simp} ⟩⟩

@[simp]
lemma is_definable_univ : L.is_definable (set.univ : set (α → M)) :=
⟨⟨⊤, by {ext, simp} ⟩⟩

@[simp]
lemma is_definable_inter {f g : set (α → M)} (hf : L.is_definable f) (hg : L.is_definable g) :
  L.is_definable (f ∩ g) :=
⟨begin
  rcases hf.exists_formula with ⟨φ, hφ⟩,
  rcases hg.exists_formula with ⟨θ, hθ⟩,
  refine ⟨φ ⊓ θ, _⟩,
  ext,
  simp [hφ, hθ],
end⟩

@[simp]
lemma is_definable_union {f g : set (α → M)} (hf : L.is_definable f) (hg : L.is_definable g) :
  L.is_definable (f ∪ g) :=
⟨begin
  rcases hf.exists_formula with ⟨φ, hφ⟩,
  rcases hg.exists_formula with ⟨θ, hθ⟩,
  refine ⟨φ ⊔ θ, _⟩,
  ext,
  simp only [hφ, hθ, set.sup_eq_union, realize_not, realize_bounded_formula,
    bounded_formula.has_sup_sup, set.mem_union_eq, set.mem_set_of_eq],
  tauto,
end⟩

@[simp]
lemma is_definable_compl {s : set (α → M)} (hf : L.is_definable s) :
  L.is_definable sᶜ :=
⟨begin
  rcases hf.exists_formula with ⟨φ, hφ⟩,
  refine ⟨bd_not φ, _⟩,
  rw hφ,
  refl,
end⟩

@[simp]
lemma is_definable_sdiff {s t : set (α → M)} (hs : L.is_definable s)
  (ht : L.is_definable t) :
  L.is_definable (s \ t) :=
L.is_definable_inter hs (L.is_definable_compl ht)

variables (M) (α)

/-- Definable sets are subsets of finite Cartesian products of a structure such that membership is
  given by a first-order formula. -/
def definable_set := subtype (λ s : set (α → M), is_definable L s)

namespace definable_set
variables {M} {α}

instance : has_top (L.definable_set M α) := ⟨⟨⊤, L.is_definable_univ⟩⟩

instance : has_bot (L.definable_set M α) := ⟨⟨⊥, L.is_definable_empty⟩⟩

instance : inhabited (L.definable_set M α) := ⟨⊥⟩

instance : set_like (L.definable_set M α) (α → M) :=
{ coe := subtype.val,
  coe_injective' := subtype.val_injective }

@[simp]
lemma mem_top {x : α → M} : x ∈ (⊤ : L.definable_set M α) := set.mem_univ x

@[simp]
lemma coe_top : ((⊤ : L.definable_set M α) : set (α → M)) = ⊤ := rfl

@[simp]
lemma not_mem_bot {x : α → M} : ¬ x ∈ (⊥ : L.definable_set M α) := set.not_mem_empty x

@[simp]
lemma coe_bot : ((⊥ : L.definable_set M α) : set (α → M)) = ⊥ := rfl

instance : lattice (L.definable_set M α) :=
subtype.lattice (λ _ _, L.is_definable_union) (λ _ _, L.is_definable_inter)

lemma le_iff {s t : L.definable_set M α} : s ≤ t ↔ (s : set (α → M)) ≤ (t : set (α → M)) := iff.rfl

@[simp]
lemma coe_sup {s t : L.definable_set M α} : ((s ⊔ t : L.definable_set M α) : set (α → M)) = s ∪ t :=
rfl

@[simp]
lemma mem_sup {s t : L.definable_set M α} {x : α → M} : x ∈ s ⊔ t ↔ x ∈ s ∨ x ∈ t := iff.rfl

@[simp]
lemma coe_inf {s t : L.definable_set M α} : ((s ⊓ t : L.definable_set M α) : set (α → M)) = s ∩ t :=
rfl

@[simp]
lemma mem_inf {s t : L.definable_set M α} {x : α → M} : x ∈ s ⊓ t ↔ x ∈ s ∧ x ∈ t := iff.rfl

instance : bounded_lattice (L.definable_set M α) :=
{ bot_le := λ s x hx, false.elim hx,
  le_top := λ s x hx, set.mem_univ x,
  .. definable_set.has_top L,
  .. definable_set.has_bot L,
  .. definable_set.lattice L }

instance : bounded_distrib_lattice (L.definable_set M α) :=
{ le_sup_inf := begin
    intros s t u x,
    simp only [and_imp, set.mem_inter_eq, set_like.mem_coe, coe_sup, coe_inf, set.mem_union_eq,
      subtype.val_eq_coe],
    tauto,
  end,
  .. definable_set.bounded_lattice L }

/-- The complement of a definable set is also definable. -/
@[reducible] instance : has_compl (L.definable_set M α) :=
⟨λ ⟨s, hs⟩, ⟨sᶜ, L.is_definable_compl hs⟩⟩

@[simp]
lemma mem_compl {s : L.definable_set M α} {x : α → M} : x ∈ sᶜ ↔ ¬ x ∈ s :=
begin
  cases s with s hs,
  refl,
end

@[simp]
lemma coe_compl {s : L.definable_set M α} : ((sᶜ : L.definable_set M α) : set (α → M)) = sᶜ :=
begin
  ext,
  simp,
end

instance : boolean_algebra (L.definable_set M α) :=
{ sdiff := λ s t, s ⊓ tᶜ,
  sdiff_eq := λ s t, rfl,
  sup_inf_sdiff := λ ⟨s, hs⟩ ⟨t, ht⟩,
  begin
    apply le_antisymm;
    simp [le_iff],
  end,
  inf_inf_sdiff := λ ⟨s, hs⟩ ⟨t, ht⟩, begin
    rw eq_bot_iff,
    simp only [coe_compl, le_iff, coe_bot, coe_inf, subtype.coe_mk,
      set.le_eq_subset],
    intros x hx,
    simp only [set.mem_inter_eq, set.mem_compl_eq] at hx,
    tauto,
  end,
  inf_compl_le_bot := λ ⟨s, hs⟩, by simp [le_iff],
  top_le_sup_compl := λ ⟨s, hs⟩, by simp [le_iff],
  .. definable_set.has_compl L,
  .. definable_set.bounded_distrib_lattice L }

end definable_set
end definability

variables (L) (M) (N)

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
structure elementary_embedding :=
(to_fun : M → N)
(map_formula' : ∀{n} (φ : L.formula (fin n)) (x : fin n → M),
  realize_formula N φ (to_fun ∘ x) ↔ realize_formula M φ x . obviously)

localized "notation A ` ↪ₑ[`:25 L `] ` B := L.elementary_embedding A B" in first_order

variables {L} {M} {N}

namespace elementary_embedding

@[simps] instance has_coe_to_fun : has_coe_to_fun (M ↪ₑ[L] N) :=
⟨(λ _, M → N), λ f, f.to_fun⟩

@[simp] lemma map_formula (f : M ↪ₑ[L] N) {α : Type} [fintype α] (φ : L.formula α)
  (x : α → M) :
  realize_formula N φ (f ∘ x) ↔ realize_formula M φ x :=
begin
  have g := fintype.equiv_fin α,
  have h := f.map_formula' (φ.relabel g) (x ∘ g.symm),
  rw [realize_formula_relabel, realize_formula_relabel,
    function.comp.assoc x g.symm g, g.symm_comp_self, function.comp.right_id] at h,
  rw [← h, iff_eq_eq],
  congr,
  ext y,
  simp,
end

@[simp] lemma map_fun (φ : M ↪ₑ[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) :=
begin
  have h := φ.map_formula (formula.graph f) (fin.snoc x (fun_map f x)),
  rw [realize_graph, fin.comp_snoc, realize_graph] at h,
  rw [eq_comm, h]
end

@[simp] lemma map_const (φ : M ↪ₑ[L] N) (c : L.const) : φ c = c :=
(φ.map_fun c fin.elim0).trans (congr rfl (funext fin.elim0))

@[simp] lemma map_rel (φ : M ↪ₑ[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x :=
begin
  have h := φ.map_formula (bd_rel r (var ∘ sum.inl)) x,
  exact h
end

@[simp] lemma injective (φ : M ↪ₑ[L] N) :
  function.injective φ :=
begin
  intros x y,
  have h := φ.map_formula (formula.equal (var 0) (var 1) : L.formula (fin 2))
    (λ i, if i = 0 then x else y),
  rw [realize_equal, realize_equal] at h,
  simp only [nat.one_ne_zero, realize_term, fin.one_eq_zero_iff, if_true, eq_self_iff_true,
    function.comp_app, if_false] at h,
  exact h.1,
end

/-- An elementary embedding is in fact a first-order embedding. -/
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

namespace substructure

/-- A substructure is elementary when every formula applied to a tuple in the subtructure
  agrees with its value in the overall structure. -/
def is_elementary (S : L.substructure M) : Prop :=
∀{n} (φ : L.formula (fin n)) (x : fin n → S), realize_formula M φ (coe ∘ x) ↔ realize_formula S φ x

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
⟨⟨⊤, λ n φ x, begin
  rw formula at φ,
  rw [realize_formula, realize_formula, realize_bounded_formula_top, iff_eq_eq],
  exact congr rfl (funext fin_zero_elim),
end⟩⟩

instance : inhabited (L.elementary_substructure M) := ⟨⊤⟩

@[simp] lemma mem_top (x : M) : x ∈ (⊤ : L.elementary_substructure M) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : L.elementary_substructure M) : set M) = set.univ := rfl

end elementary_substructure

end language
end first_order
