/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.quotients
import order.filter.germ
import order.filter.ultrafilter

/-! # Ultraproducts, Łoś's Theorem, and Compactness

## Main Definitions
* `first_order.language.ultraproduct.Structure` is a structure on `filter.product`.

## Main Results
* Łoś's Theorem: `first_order.language.ultraproduct.sentence_realize`. An ultraproduct models a
sentence `φ` if and only if the set of structures in the product that model `φ` is in the
ultrafilter.
* The Compactness Theorem: `first_order.language.Theory.is_satisfiable_iff_is_finitely_satisfiable`.
A theory is satisfiable if and only if it is finitely satisfiable.

## Tags
ultraproduct, Los's theorem, compactness

-/

universes u v
variables {α : Type*} (M : α → Type*) (u : ultrafilter α)

open_locale first_order filter

open filter

namespace first_order
namespace language

open Structure

variables {L : language.{u v}} [Π a, L.Structure (M a)]

namespace ultraproduct

instance setoid_prestructure : L.prestructure ((u : filter α).product_setoid M) :=
{ to_structure := { fun_map := λ n f x a, fun_map f (λ i, x i a),
             rel_map := λ n r x, ∀ᶠ (a : α) in u, rel_map r (λ i, x i a) },
  fun_equiv := λ n f x y xy, begin
    refine mem_of_superset (Inter_mem.2 xy) (λ a ha, _),
    simp only [set.mem_Inter, set.mem_set_of_eq] at ha,
    simp only [set.mem_set_of_eq, ha],
  end,
  rel_equiv := λ n r x y xy, begin
    rw ← iff_eq_eq,
    refine ⟨λ hx, _, λ hy, _⟩,
    { refine mem_of_superset (inter_mem hx (Inter_mem.2 xy)) _,
      rintro a ⟨ha1, ha2⟩,
      simp only [set.mem_Inter, set.mem_set_of_eq] at *,
      rw ← funext ha2,
      exact ha1 },
    { refine mem_of_superset (inter_mem hy (Inter_mem.2 xy)) _,
      rintro a ⟨ha1, ha2⟩,
      simp only [set.mem_Inter, set.mem_set_of_eq] at *,
      rw funext ha2,
      exact ha1 },
  end,
  .. (u : filter α).product_setoid M }

variables {M} {u}

instance Structure : L.Structure ((u : filter α).product M) := language.quotient_structure

lemma fun_map_cast {n : ℕ} (f : L.functions n) (x : fin n → (Π a, M a)) :
  fun_map f (λ i, ((x i) : (u : filter α).product M)) = λ a, fun_map f (λ i, x i a) :=
by apply fun_map_quotient_mk

lemma term_realize_cast {β : Type*} (x : β → (Π a, M a)) (t : L.term β) :
  t.realize (λ i, ((x i) : (u : filter α).product M)) = λ a, t.realize (λ i, x i a) :=
begin
  convert @term.realize_quotient_mk L _  ((u : filter α).product_setoid M)
    (ultraproduct.setoid_prestructure M u) _ t x,
  ext a,
  induction t,
  { refl },
  { simp only [term.realize, t_ih],
    refl }
end

variables [Π a : α, nonempty (M a)]

theorem bounded_formula_realize_cast {β : Type*} {n : ℕ} (φ : L.bounded_formula β n)
  (x : β → (Π a, M a)) (v : fin n → (Π a, M a)) :
  φ.realize (λ (i : β), ((x i) : (u : filter α).product M)) (λ i, (v i)) ↔
    ∀ᶠ (a : α) in u, φ.realize (λ (i : β), x i a) (λ i, v i a) :=
begin
  letI := ((u : filter α).product_setoid M),
  induction φ with _ _ _ _ _ _ _ _ m _ _ ih ih' k φ ih,
  { simp only [bounded_formula.realize, eventually_const], },
  { have h2 : ∀ a : α, sum.elim (λ (i : β), x i a) (λ i, v i a) = λ i, sum.elim x v i a :=
      λ a, funext (λ i, sum.cases_on i (λ i, rfl) (λ i, rfl)),
    simp only [bounded_formula.realize, (sum.comp_elim coe x v).symm, h2, term_realize_cast],
    exact quotient.eq' },
  { have h2 : ∀ a : α, sum.elim (λ (i : β), x i a) (λ i, v i a) = λ i, sum.elim x v i a :=
      λ a, funext (λ i, sum.cases_on i (λ i, rfl) (λ i, rfl)),
    simp only [bounded_formula.realize, (sum.comp_elim coe x v).symm, term_realize_cast, h2],
    exact rel_map_quotient_mk _ _ },
  { simp only [bounded_formula.realize, ih v, ih' v],
    rw ultrafilter.eventually_imp },
  { simp only [bounded_formula.realize],
    transitivity (∀ (m : Π (a : α), M a), φ.realize (λ (i : β), (x i : (u : filter α).product M))
      (fin.snoc (coe ∘ v) (↑m : (u : filter α).product M))),
    { exact forall_quotient_iff },
    have h' : ∀ (m : Π a, M a) (a : α), (λ (i : fin (k + 1)), (fin.snoc v m : _ → Π a, M a) i a) =
      fin.snoc (λ (i : fin k), v i a) (m a),
    { refine λ m a, funext (fin.reverse_induction _ (λ i hi, _)),
      { simp only [fin.snoc_last] },
      { simp only [fin.snoc_cast_succ] } },
    simp only [← fin.comp_snoc, ih, h'],
    refine ⟨λ h, _, λ h m, _⟩,
    { contrapose! h,
      simp_rw [← ultrafilter.eventually_not, not_forall] at h,
      refine ⟨λ a : α, classical.epsilon (λ m : M a, ¬ φ.realize (λ i, x i a)
        (fin.snoc (λ i, v i a) m)), _⟩,
      rw [← ultrafilter.eventually_not],
      exact filter.mem_of_superset h (λ a ha, classical.epsilon_spec ha) },
    { rw filter.eventually_iff at *,
      exact filter.mem_of_superset h (λ a ha, ha (m a)) } }
end

theorem realize_formula_cast {β : Type*} (φ : L.formula β) (x : β → (Π a, M a)) :
  φ.realize (λ i, ((x i) : (u : filter α).product M)) ↔
    ∀ᶠ (a : α) in u, φ.realize (λ i, (x i a)) :=
begin
  simp_rw [formula.realize, ← bounded_formula_realize_cast φ x, iff_eq_eq],
  exact congr rfl (subsingleton.elim _ _),
end

/-- Łoś's Theorem : A sentence is true in an ultraproduct if and only if the set of structures it is
  true in is in the ultrafilter. -/
theorem sentence_realize (φ : L.sentence) :
  ((u : filter α).product M) ⊨ φ ↔ ∀ᶠ (a : α) in u, (M a) ⊨ φ :=
begin
  simp_rw [sentence.realize, ← realize_formula_cast φ, iff_eq_eq],
  exact congr rfl (subsingleton.elim _ _),
end

end ultraproduct

namespace Theory

/-- The Compactness Theorem of first-order logic: A theory is satisfiable if and only if it is
finitely satisfiable. -/
theorem is_satisfiable_iff_is_finitely_satisfiable {T : L.Theory} :
  T.is_satisfiable ↔ T.is_finitely_satisfiable :=
⟨Theory.is_satisfiable.is_finitely_satisfiable, λ h, begin
  classical,
  set M : Π (T0 : finset T), Type (max u v) :=
    λ T0, (h (T0.map (function.embedding.subtype (λ x, x ∈ T)))
      T0.map_subtype_subset).some_model with hM,
  letI : Π (T0 : finset T), L.Structure (M T0) := λ T0, is_satisfiable.some_model_structure _,
  haveI : (filter.at_top : filter (finset T)).ne_bot := at_top_ne_bot,
  refine ⟨(↑(ultrafilter.of filter.at_top) : filter _).product M, infer_instance,
    ultraproduct.Structure, ⟨_⟩⟩,
  intros φ hφ,
  rw ultraproduct.sentence_realize,
  refine filter.eventually.filter_mono (ultrafilter.of_le _) (filter.eventually_at_top.2 ⟨{⟨φ, hφ⟩},
    λ s h', Theory.realize_sentence_of_mem (s.map (function.embedding.subtype (λ x, x ∈ T))) _⟩),
  simp only [finset.coe_map, function.embedding.coe_subtype, set.mem_image, finset.mem_coe,
    subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right],
  exact ⟨hφ, h' (finset.mem_singleton_self _)⟩,
end⟩

end Theory

end language
end first_order
