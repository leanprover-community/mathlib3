/-
Copyright (c) 2022 Jocchim Breitner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joachim Breitner
-/
import group_theory.subgroup.basic
import tactic.group
import group_theory.general_commutator
import group_theory.order_of_element
import data.finset.noncomm_prod

/-!
# TODO

-/

variables {G : Type*} [group G]

lemma mul_eq_one_of_disjoint
  {H₁ H₂ : subgroup G} (hdis : disjoint H₁ H₂) {x y : G} (hx : x ∈ H₁) (hy : y ∈ H₂)
  (heq : x * y = 1) : x = 1 ∧ y = 1 :=
begin
  have : y = x⁻¹ := symm (inv_eq_iff_mul_eq_one.mpr heq),
  subst this,
  have hy := H₂.inv_mem_iff.mp hy,
  have : x ∈ H₁ ⊓ H₂, by { simp, cc },
  rw [hdis.eq_bot, subgroup.mem_bot] at this,
  subst this,
  simp
end

namespace pi_hom

variables {I : Type*} [fintype I] {H : I → Type*} [∀ i, group (H i)] (ϕ : Π (i : I), H i →* G)

variables (f g : Π (i : I), H i)

-- A bit like `finset.noncomm_prodi`, but without the dependent Prop arg that makes things tricky

/-- TODO -/
noncomputable
def fun_on (S : finset I) : G := (list.map (λ i, ϕ i (f i)) S.to_list).prod

/-- TODO -/
noncomputable
def to_fun : G := fun_on ϕ f finset.univ

@[simp]
lemma fun_on_empty : fun_on ϕ f ∅ = 1 := by simp [fun_on]

variables [hcomm : fact (∀ (i j : I), i ≠ j → ∀ (x : H i) (y : H j), commute (ϕ i x) (ϕ j y)) ]
include hcomm

lemma fun_on_perm {S : finset I} {l : list I} (h : S.to_list ~ l) :
  fun_on ϕ f S = (list.map (λ i, ϕ i (f i)) l).prod :=
begin
  unfold fun_on,
  have hnd : l.nodup := h.nodup_iff.mp (finset.nodup_to_list S),
  induction h with x l₁ l₂ hl₁l₂ ih x y l₁ l₁ l₂ l₃ hl₁l₂ hl₂l₃ ih12 ih23,
  { reflexivity },
  { specialize ih (list.nodup_cons.mp hnd).2, simpa },
  { simp only [list.map, list.prod_cons, ← mul_assoc],
    congr' 1,
    apply fact.elim hcomm,
    simp only [list.nodup_cons, list.mem_cons_iff] at hnd,
    cc, },
  { specialize ih12 (hl₂l₃.nodup_iff.mpr hnd),
    specialize ih23 hnd,
    rw [ih12, ih23], }
end

@[simp]
lemma fun_on_cons (S : finset I) (i : I) (h : i ∉ S) :
  fun_on ϕ f (finset.cons i S h) = ϕ i (f i) * fun_on ϕ f S :=
by { rw fun_on_perm ϕ f (finset.to_list_cons h), simp [fun_on] }

@[simp]
lemma fun_on_one (S : finset I) : fun_on ϕ 1 S = 1 :=
begin
   induction S using finset.cons_induction_on with i S hnmem ih,
   { simp },
   { simp [ih] }
end

@[simp]
lemma to_fun_one : to_fun ϕ 1 = 1 := fun_on_one _ _

lemma fun_on_commutes (S : finset I) (i : I) (hnmem : i ∉ S) :
  ϕ i (g i) * fun_on ϕ f S = fun_on ϕ f S * ϕ i (g i) :=
begin
  induction S using finset.cons_induction_on with j S hnmem ih,
  { simp, },
  { repeat { rw fun_on_cons },
    have hij : i ≠ j, by {simp at hnmem, cc},
    have hiS : i ∉ S, by {simp at hnmem, cc},
    calc ϕ i (g i) * (ϕ j (f j) * fun_on ϕ f S)
        = (ϕ i (g i) * ϕ j (f j)) * fun_on ϕ f S : by rw ← mul_assoc
    ... = (ϕ j (f j) * ϕ i (g i)) * fun_on ϕ f S : by {congr' 1, apply (fact.elim hcomm _ _ hij)}
    ... = ϕ j (f j) * (ϕ i (g i) * fun_on ϕ f S) : by rw mul_assoc
    ... = ϕ j (f j) * (fun_on ϕ f S * ϕ i (g i)) : by { congr' 1, apply (ih hiS) }
    ... = (ϕ j (f j) * fun_on ϕ f S) * ϕ i (g i) : by rw ← mul_assoc }
end

@[simp]
lemma fun_on_mul (S : finset I) : fun_on ϕ (f * g) S = fun_on ϕ f S * fun_on ϕ g S :=
begin
  induction S using finset.cons_induction_on with i S hnmem ih,
  { simp, },
  { repeat { rw [fun_on_cons] },
    rw ih, clear ih,
    simp only [pi.mul_apply, map_mul],
    repeat { rw mul_assoc }, congr' 1,
    repeat { rw ← mul_assoc }, congr' 1,
    exact (fun_on_commutes _ _ _ S i hnmem), }
end

lemma fun_on_in_sup_range (S : finset I) :
  fun_on ϕ f S ∈ ⨆ (i : I) (H_1 : i ∈ S), (ϕ i).range :=
begin
  induction S using finset.cons_induction_on with i S hnmem ih,
  { simp, },
  { repeat { rw fun_on_cons },
    refine (subgroup.mul_mem _ _ _),
    { apply (subgroup.mem_Sup_of_mem), { use i }, { simp, }, },
    { refine (@bsupr_le_bsupr' _ _ _ _ _ _ (λ i, (ϕ i).range) _ ih),
      by { intro, simp, intro h, right, exact h}, } }
end

lemma to_fun_in_sup_range : to_fun ϕ f ∈ ⨆ (i : I), (ϕ i).range :=
bsupr_le_supr _ (λ i, (ϕ i).range) (fun_on_in_sup_range ϕ f finset.univ)

@[simp]
lemma to_fun_mul : to_fun ϕ (f * g) = to_fun ϕ f * to_fun ϕ g := fun_on_mul _ _ _ _

noncomputable
def hom : (Π (i : I), H i) →* G :=
{ to_fun := to_fun ϕ,
  map_one' := to_fun_one _,
  map_mul' := λ f g, to_fun_mul _ f g, }

omit hcomm
def just_one [decidable_eq I] (i : I) (y : H i) : Π (i : I), H i :=
  λ j, if h : j = i then by { subst h; exact y} else 1

@[simp]
lemma just_one_eq [decidable_eq I] (i : I) (y : H i) : just_one i y i = y :=
by { unfold just_one, simp }

@[simp]
lemma just_one_ne [decidable_eq I] (i : I) (y : H i) (j : I) (h : i ≠ j) :
  just_one i y j = (1 : H j) :=
by { unfold just_one, have : ¬ (j = i), by cc, simp [this], }

include hcomm

lemma fun_on_just_one [decidable_eq I] (i : I) (y : H i) (S : finset I) :
  fun_on ϕ (just_one i y) S = if i ∈ S then ϕ i y else 1 :=
begin
  induction S using finset.cons_induction_on with j S hnmem ih,
  { simp, },
  { repeat { rw fun_on_cons },
    by_cases (i = j),
    { subst h,
      rw ih,
      simp only [just_one_eq, mul_ite, mul_one, finset.cons_eq_insert, finset.mem_insert,
        eq_self_iff_true, true_or, if_true, ite_eq_right_iff, mul_left_eq_self],
      intro i, contradiction, },
    { change i ≠ j at h,
      simp [h],
      exact ih, } }
end

lemma to_fun_just_one [decidable_eq I] (i : I) (y : H i) :
  to_fun ϕ (just_one i y) = ϕ i y :=
begin
  unfold to_fun,
  rw fun_on_just_one ϕ i y _,
  simp,
end

lemma range_eq [decidable_eq I] : (hom ϕ).range = (⨆ (i : I), (ϕ i).range) :=
begin
  apply le_antisymm,
  { rintro x ⟨f, rfl⟩,
    exact (to_fun_in_sup_range ϕ f), },
  { refine (supr_le _),
    rintro i x ⟨y, rfl⟩,
    exact ⟨_, to_fun_just_one _ i y⟩, }
end


variables (hind : complete_lattice.independent (λ i, (ϕ i).range))
variables (hinj : ∀ i, function.injective (ϕ i))

include hind
include hinj

lemma injective_of_independent : function.injective (hom ϕ) :=
begin
  apply (monoid_hom.ker_eq_bot_iff _).mp,
  apply eq_bot_iff.mpr,
  intro f,
  show fun_on ϕ f finset.univ = 1 → f = 1,
  suffices : fun_on ϕ f finset.univ = 1 → (∀ (i : I), i ∈ finset.univ → f i = 1),
  by exact (λ h, funext (λ (i : I), this h i (finset.mem_univ i))),
  induction (finset.univ : finset I) using finset.cons_induction_on with i S hnmem ih,
  { simp },
  { intro heq1,
    rw fun_on_cons at heq1,
    have hnmem' : i ∉ (S : set I), by simpa,
    have heq1' : ϕ i (f i) = 1 ∧ fun_on ϕ f S = 1,
    { apply mul_eq_one_of_disjoint (hind.disjoint_bsupr hnmem') _ _ heq1,
      { simp, },
      { apply fun_on_in_sup_range, }, },
    rcases heq1' with ⟨ heq1i, heq1S ⟩,
    specialize ih heq1S,
    intros i h,
    simp only [finset.mem_cons] at h,
    rcases h with ⟨rfl | _⟩,
    { apply hinj i, simpa, },
    { exact (ih _ h), } }
end

noncomputable
def mul_equiv [decidable_eq I] :
  (Π (i : I), H i) ≃* (⨆ (i : I), (ϕ i).range : subgroup G) :=
begin
  rw ← range_eq,
  exact (monoid_hom.of_injective (injective_of_independent _ hind hinj)),
end

end pi_hom
