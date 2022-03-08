/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.quotients
import order.filter.germ
import order.filter.ultrafilter

/-! # Ultraproducts, Łos's Theorem, and Compactness

## Main Definitions
* `filter.ultraproduct` is a dependent version of `filter.germ`.

## Main Results
* Łos's Theorem: `first_order.language.ultraproduct.sentence_realize`. An ultraproduct models a
sentence `φ` if and only if the set of structures in the product that model `φ` is in the
ultrafilter.
* The Compactness Theorem: `first_order.language.Theory.is_satisfiable_iff_is_finitely_satisfiable`.
A theory is satisfiable if and only if it is finitely satisfiable.

-/

universes u v
variables {α : Type*} (M : α → Type*) (u : ultrafilter α)

open_locale first_order filter

namespace filter

variables (l : filter α) (β : α → Type*)

/-- Setoid used to define the ultraproduct. This is a dependent version of
  `filter.germ_setoid`. -/
def ultraproduct_setoid : setoid (Π a, β a) :=
{ r := λ f g, ∀ᶠ a in l, f a = g a,
  iseqv := ⟨λ _, eventually_of_forall (λ _, rfl),
    λ _ _ h, h.mono (λ _, eq.symm),
    λ x y z h1 h2, h1.congr (h2.mono (λ x hx, hx ▸ iff.rfl))⟩ }

/-- The ultraproduct `Π (a : α), β a` at a filter `l`. This is a dependent version of
  `filter.germ`. -/
def ultraproduct : Type* := quotient (ultraproduct_setoid l β)

variables {l} {β}

instance : has_coe_t (Π a, β a) (ultraproduct l β) := ⟨quotient.mk'⟩

instance [Π a, inhabited (β a)] : inhabited (ultraproduct l β) :=
⟨(↑(λ a, (default : β a)) : ultraproduct l β)⟩

end filter

open filter

namespace first_order
namespace language

open Structure

variables {L : language.{u v}} [Π a, L.Structure (M a)]

namespace ultraproduct

instance setoid_prestructure : L.prestructure (ultraproduct_setoid ↑u M) :=
{ to_structure := { fun_map := λ n f x a, fun_map f (λ i, x i a),
             rel_map := λ n r x, ∀ᶠ (a : α) in ↑u, rel_map r (λ i, x i a) },
  fun_equiv := λ n f x y xy, begin
    refine mem_of_superset (Inter_mem.2 xy) (λ a ha, _),
    rw set.mem_Inter at ha,
    simp only [set.mem_set_of_eq],
    exact congr rfl (funext ha),
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
  .. ultraproduct_setoid ↑u M }

variables {M} {u}

instance Structure : L.Structure (ultraproduct ↑u M) := language.quotient_structure

lemma fun_map_cast {n : ℕ} (f : L.functions n) (x : fin n → (Π a, M a)) :
  fun_map f (λ i, ((x i) : ultraproduct ↑u M)) = λ a, fun_map f (λ i, x i a) :=
by apply fun_map_quotient_mk

lemma term_realize_cast {β : Type*} (x : β → (Π a, M a)) (t : L.term β) :
  t.realize (λ i, ((x i) : ultraproduct ↑u M)) = λ a, t.realize (λ i, x i a) :=
begin
  convert @term.realize_quotient_mk L _  (ultraproduct_setoid ↑u M)
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
  φ.realize (λ (i : β), ((x i) : ultraproduct ↑u M)) (λ i, (v i)) ↔
    ∀ᶠ (a : α) in ↑u, φ.realize (λ (i : β), x i a) (λ i, v i a) :=
begin
  induction φ with _ _ _ _ _ _ _ _ m _ _ ih ih' k φ ih,
  { simp only [bounded_formula.realize, eventually_const], },
  { have h2 : ∀ a : α, sum.elim (λ (i : β), x i a) (λ i, v i a) = λ i, sum.elim x v i a :=
      λ a, funext (λ i, sum.cases_on i (λ i, rfl) (λ i, rfl)),
    simp only [bounded_formula.realize, (sum.comp_elim coe x v).symm, h2, term_realize_cast],
    exact quotient.eq' },
  { have h2 : ∀ a : α, sum.elim (λ (i : β), x i a) (λ i, v i a) = λ i, sum.elim x v i a :=
      λ a, funext (λ i, sum.cases_on i (λ i, rfl) (λ i, rfl)),
    simp only [bounded_formula.realize, (sum.comp_elim coe x v).symm, h2, term_realize_cast],
    unfold rel_map,
    change quotient.lift _ _ (quotient.fin_choice (λ _, ⟦_⟧)) ↔ _,
    simp_rw [quotient.fin_choice_eq, quotient.lift_mk] },
  { simp only [bounded_formula.realize, ih v, ih' v],
    rw ultrafilter.eventually_imp },
  { simp only [bounded_formula.realize],
    transitivity (∀ (m : Π (a : α), M a), φ.realize (λ (i : β), (x i : ultraproduct ↑u M))
      (fin.snoc (coe ∘ v) (↑m : ultraproduct ↑u M))),
    { exact (@forall_quotient_iff _ (ultraproduct_setoid ↑u M) _) },
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
  φ.realize (λ i, ((x i) : ultraproduct ↑u M)) ↔
    ∀ᶠ (a : α) in u, φ.realize (λ i, (x i a)) :=
begin
  simp_rw [formula.realize],
  convert bounded_formula_realize_cast φ x default,
  { simp },
  ext,
  rw iff_eq_eq,
  refine congr rfl _,
  simp,
end

/-- Łoś's Theorem : A sentence is true in an ultraproduct if and only if the set of structures it is
  true in is in the ultrafilter. -/
theorem sentence_realize (φ : L.sentence) :
  (ultraproduct ↑u M) ⊨ φ ↔ ∀ᶠ (a : α) in u, (M a) ⊨ φ :=
begin
  simp_rw [sentence.realize, iff_eq_eq],
  exact (congr rfl (subsingleton.elim _ _)).trans (iff_eq_eq.mp (realize_formula_cast φ _))
end

end ultraproduct

namespace Theory

/-- The Compactness Theorem of first-order logic: A theory is satisfiable if and only if it is
finitely satisfiable. -/
theorem is_satisfiable_iff_is_finitely_satisfiable {T : L.Theory} :
  T.is_satisfiable ↔ T.is_finitely_satisfiable :=
⟨Theory.is_satisfiable.is_finitely_satisfiable, λ h, begin
  classical,
  unfold is_finitely_satisfiable at h,
  set M : Π (T0 : finset T), Type (max u v) :=
    λ T0, (h (T0.map (function.embedding.subtype (λ x, x ∈ T)))
      T0.map_subtype_subset).some_model with hM,
  cases fintype_or_infinite T; resetI,
  { refine (congr rfl _).mp (h (finset.univ.map (function.embedding.subtype (λ x, x ∈ T)))
      finset.univ.map_subtype_subset),
    rw [finset.coe_map, function.embedding.coe_subtype, finset.coe_univ, set.image_univ,
      subtype.range_coe_subtype, set.set_of_mem_eq], },
  { letI : Π (T0 : finset T), L.Structure (M T0) := λ T0, is_satisfiable.some_model_structure _,
    haveI : (filter.at_top : filter (finset T)).ne_bot := at_top_ne_bot,
    refine ⟨ultraproduct ↑(ultrafilter.of filter.at_top) M, _, ultraproduct.Structure, _⟩,
    { haveI : Π (T0 : finset T), inhabited (M T0),
      { exact λ T0, classical.inhabited_of_nonempty (is_satisfiable.nonempty_some_model _) },
      exact nonempty_of_inhabited },
    intros φ hφ,
    rw ultraproduct.sentence_realize,
    refine filter.eventually.filter_mono (ultrafilter.of_le _) (filter.eventually_at_top.2
      ⟨{⟨φ, hφ⟩}, _⟩),
    rintro ⟨s, hs⟩ h',
    simp only [ge_iff_le, finset.le_eq_subset, finset.singleton_subset_iff, finset.mem_mk] at h',
    refine is_satisfiable.some_model_models _ _ _,
    simp only [finset.coe_map, function.embedding.coe_subtype, set.mem_image, finset.mem_coe,
      finset.mem_mk, set_coe.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right],
    exact ⟨hφ, h'⟩, },
end⟩

end Theory

end language
end first_order
