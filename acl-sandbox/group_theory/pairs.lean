import tactic.basic
import data.set.basic
import data.set.finite

/-!
# Subpairs

Subpairs are sets of the form {a, b} .
I reserve the word pairs for those for which a ≠ b.

-/

variables {α : Type*}

section subpairs

/-- a is in {a, b} -/
lemma is_in_subpair_left {a b : α} : a ∈ ({ a , b } : set α) :=
begin
  simp only [set.mem_insert_iff, true_or, eq_self_iff_true],
end

/-- b is in {a, b} -/
lemma is_in_subpair_right {a b : α} : b ∈ ({ a , b } : set α) :=
begin
  simp only [set.mem_insert_iff, set.mem_singleton, or_true],
end

/-- c is in {a, b} iff c = a or c = b -/
lemma is_in_subpair_iff {a b c : α} : c ∈ ({a, b} : set α) ↔ c = a ∨ c = b :=
begin
  simp only [set.mem_insert_iff, imp_self, set.mem_singleton_iff]
end


/- Old version
  split,
  { simp only [set.mem_insert_iff, imp_self, set.mem_singleton_iff],
   rintro ⟨rfl, rfl⟩,
    refine or.intro_left _ rfl,
    simp only [set.mem_singleton_iff],
    rw ᾰ, exact or.intro_right _ rfl },
  { rintro ⟨rfl⟩,
    exact is_in_subpair_left,
    rw  ᾰ, exact is_in_subpair_right }
-/

-- Used ?
lemma is_not_in_subpair {a b c : α} (ha : c ≠ a) (hb : c ≠ b) :
  c ∉ ({ a, b} : set α) :=
begin
  intro hc,
  simp only [set.mem_insert_iff, set.mem_singleton_iff] at hc,
  cases hc with ha' hb' ,
  rw ha' at ha, trivial,
  rw hb' at hb, trivial,
end

/-- The subpair {a, b} equals the subpair {b, a} -/
lemma subpair_symm {a b : α} : ({a, b} : set α) = {b, a} :=
begin
  ext x,
  have : ∀ (a b x : α), x ∈ {a, b} → x ∈ {b, a},
  { intros a b x hx,
    cases is_in_subpair_iff.mp hx,
    rw h, exact is_in_subpair_right,
    rw h, exact is_in_subpair_left, },
  split,
  exact this a b x,
  exact this b a x,
end

/-- Necessary and condition for two subpairs to be equal -/
lemma subpair_eq_iff  {a b a' b' : α} :
  ({a, b} : set α) = {a', b'} ↔ (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') :=
begin
  split,
    { intro H_eq,
      have a'_mem : a' ∈ {a, b}, rw H_eq, apply is_in_subpair_left,
      have b_mem : b' ∈ {a, b}, rw H_eq, apply is_in_subpair_right,
      have a_mem : a ∈ {a', b'}, rw ← H_eq, apply is_in_subpair_left,
      have b_mem : b ∈ {a', b'}, rw ← H_eq, apply is_in_subpair_right,
      cases is_in_subpair_iff.mp a_mem with haa' hab',
      { rw ← haa' at *,
        apply or.intro_left _,
        split, exact rfl,
        cases is_in_subpair_iff.mp b_mem with hba hbb',
          rw hba at *,
          rw set.pair_eq_singleton at *,
          exact (set.mem_singleton_iff.mpr b_mem).symm,
        exact hbb', },
      apply or.intro_right _,
      rw ← hab' at *,
      split, exact rfl,
      cases is_in_subpair_iff.mp a'_mem with ha'a ha'b,
        rw ha'a at *,
        rw set.pair_eq_singleton at b_mem,
        exact (set.mem_singleton_iff.mpr b_mem),
      exact ha'b.symm, },
  intro H,
  cases H with  H H,
  rw [H.left, H.right],
  rw [H.left, H.right, set.pair_comm],
end


/- set.image_pair does the job
/-- set image of a subpair -/
def subpair_apply {β : Type*} (f : α → β) (a b : α) :
  f '' ({a, b} : set α) = {f a, f b} :=
begin
  ext x,
  split,
  { simp only [and_imp, set.mem_insert_iff, forall_eq_or_imp, forall_exists_index, set.mem_image, set.mem_singleton_iff, forall_eq],
    split,
    intro h, refine or.intro_left _ h.symm,
    intro h, refine or.intro_right _ h.symm, },
  intro h,
  simp only [set.mem_insert_iff, set.mem_singleton_iff] at h,
  cases h with ha hb,
    rw ha, use a, simp only [set.mem_insert_iff, true_or, eq_self_iff_true, and_self],
  rw hb, use b, simp only [set.mem_insert_iff, set.mem_singleton, eq_self_iff_true, or_true, and_self],
 end
-/

end subpairs

section pairs
namespace pair

/-- The set of pairs of a type -/
def pairs_of (α: Type*) : set (set α) :=
  { s | ∃ (a b : α), a ≠ b ∧ s = {a , b}}

/-- make a pair from an inequality a ≠ b -/
def mk {a b : α} (h : a ≠ b) : pairs_of α :=
begin
  use {a,b},
  split, swap, use a, use b, split, exact h, exact rfl
end

/-- `pairs.mk` makes pairs -/
lemma is_mem {a b : α} {h : a ≠ b} :
  (mk h : set α) ∈ pairs_of α :=
begin
  unfold mk, unfold pairs_of,
  use a, use b,
  split, exact h,
  simp only [subtype.coe_mk],
end

/-- The pair given by an inequality is the one you think  -/
lemma is_def {a b : α} (h : a ≠ b) :
  (mk h : set α)= {a, b} := rfl

/-- The two elements belong to the pair they create -/
lemma is_mem' {a b : α} (h : a ≠ b) : ({a, b} : set α) ∈ pairs_of α :=
begin
  rw ← is_def h, exact is_mem,
end

/-- The pointwise image of a pair under an injective map is a pair -/
lemma map {β : Type*} {f : α → β} (hf : function.injective f) (x : pairs_of α) :
  f '' x ∈ pairs_of β :=
begin
  rcases x with ⟨_, a, b, hab, rfl⟩,
  rw subtype.coe_mk,
  rw set.image_pair,
  have hab' : f a ≠ f b,
  { intro h, exact hab (hf h) },
  exact is_mem' hab',
end

lemma apply {β : Type*} {f : α → β} (hf : function.injective f) {a b : α} (hab : a ≠ b) :
-- let hab' : f a ≠ f b  := λ h, hab (hf h) in
  f '' (mk hab) = mk (λ h, hab (hf h)) :=
begin
  rw is_def hab, rw is_def (λ h, hab (hf h)),
  rw set.image_pair,
end

/-- (Noncomputably) lift a pair to a product type -/
noncomputable
def lift (x : pairs_of α) : α × α :=
  (x.prop.some, x.prop.some_spec.some)

/-- The two components of a lift of pair are distinct -/
lemma lift.ne (x : pairs_of α) :
  (pair.lift x).1 ≠ (pair.lift x).2 :=
x.prop.some_spec.some_spec.left

/-- A pair equals the subpair defined by its lift -/
def lift.spec (x : pairs_of α) :
  (x : set α) = {(pair.lift x).1, (pair.lift x).2} :=
x.prop.some_spec.some_spec.right

/-- A pair equals the pair defined by its lift -/
lemma lift.eq (x : pairs_of α) :
  mk (lift.ne x) = x :=
begin
  unfold mk,
  ext a,
  rw [lift.spec x, subtype.coe_mk],
end

/-- An element belongs to a pair iff it is equal to one of the components of its lift-/
lemma is_mem_iff (a : α) (x : pairs_of α) :
  a ∈ (x : set α) ↔ a = (pair.lift x).1 ∨ a = (pair.lift x).2  :=
begin
  rw pair.lift.spec x,
  exact is_in_subpair_iff
end

lemma is_finite (x : pairs_of α) : (x : set α).finite :=
begin
  rw ← lift.eq x,
  unfold mk,
  simp only [set.finite_singleton, set.finite.insert, subtype.coe_mk],
end

/-
lemma to_finset_eq [fintype α] (x : pairs_of α) :
  (x : set α).to_finset = (pair.is_finite x).to_finset :=
begin
  apply finset.coe_inj.mp,
  simp only [set.finite.coe_to_finset, set.coe_to_finset],
end
-/

/-
lemma finset_coe (x : pairs_of α) : (x : set α) = (is_finite_pair x).to_finset :=
begin
  simp only [set.finite.coe_to_finset],
end
-/

lemma card_eq_two [decidable_eq α] (p : pairs_of α) :
  (pair.is_finite p).to_finset.card = 2 :=
begin
  apply finset.card_eq_two.mpr,
  rw ← lift.eq p,
  use (pair.lift p).fst, use (pair.lift p).snd,
  apply and.intro (lift.ne p),
  apply finset.coe_inj.mp,
  rw set.finite.coe_to_finset ,
  rw pair.lift.eq,
  rw pair.lift.spec p,
  simp only [finset.coe_insert, finset.coe_singleton],
  assumption,
end

end pair
end pairs
