-- this should all be moved

-- import algebra.inj_surj
import data.nat.choose
import data.int.gcd
import data.mv_polynomial
import data.zmod.basic
import data.fintype.card
import data.finset.lattice
import data.set.disjointed
import ring_theory.multiplicity
import algebra.invertible
import number_theory.basic

universes u v w u₁

-- ### FOR_MATHLIB
-- everything in this file should move to other files


-- namespace alg_hom
-- open mv_polynomial

-- note: this has moved to the mv_polynomial namespace, is that reasonable?
-- it also doesn't seem to be used

-- lemma comp_aeval {σ : Type*}
--   {R : Type*} {A : Type*} {B : Type*}
--    [comm_semiring R] [comm_semiring A] [algebra R A] [comm_semiring B] [algebra R B]
--   (f : σ → A) (φ : A →ₐ[R] B) :
--   φ.comp (aeval f) = (aeval (λ i, φ (f i))) :=
-- begin
--   apply mv_polynomial.alg_hom_ext,
--   intros i,
--   rw [comp_apply, aeval_X, aeval_X],
-- end

-- end alg_hom



namespace finset

open_locale classical

@[simp]
lemma fold_union_empty_singleton {α : Type*} (s : finset α) :
  finset.fold (∪) ∅ singleton s = s :=
begin
  apply finset.induction_on s,
  { simp only [fold_empty], },
  { intros a s has ih, rw [fold_insert has, ih, insert_eq], }
end

@[simp]
lemma fold_sup_bot_singleton {α : Type*} (s : finset α) :
  finset.fold (⊔) ⊥ singleton s = s :=
fold_union_empty_singleton s

end finset

namespace mv_polynomial
open finsupp

variables (σ R A : Type*) [comm_semiring R] [comm_semiring A]


section constant_coeff
open_locale classical
variables {σ R}

noncomputable
def constant_coeff : mv_polynomial σ R →+* R :=
{ to_fun := coeff 0,
  map_one' := by simp [coeff, add_monoid_algebra.one_def],
  map_mul' := by simp [coeff_mul, finsupp.support_single_ne_zero],
  map_zero' := coeff_zero _,
  map_add' := coeff_add _ }

-- I think neither direction should be simp.
-- But I one of them must be simp, then: ←
lemma constant_coeff_eq : (constant_coeff : mv_polynomial σ R → R) = coeff 0 := rfl

@[simp]
lemma constant_coeff_C (r : R) :
  constant_coeff (C r : mv_polynomial σ R) = r :=
by simp [constant_coeff_eq]

@[simp]
lemma constant_coeff_X (i : σ) :
  constant_coeff (X i : mv_polynomial σ R) = 0 :=
by simp [constant_coeff_eq]

lemma constant_coeff_monomial (d : σ →₀ ℕ) (r : R) :
  constant_coeff (monomial d r) = if d = 0 then r else 0 :=
by rw [constant_coeff_eq, coeff_monomial]

end constant_coeff

@[simp] lemma aeval_zero [algebra R A] (p : mv_polynomial σ R) :
  aeval (0 : σ → A) p = algebra_map _ _ (constant_coeff p) :=
begin
  apply mv_polynomial.induction_on p,
  { simp only [aeval_C, forall_const, if_true, constant_coeff_C, eq_self_iff_true] },
  { intros, simp only [*, alg_hom.map_add, ring_hom.map_add, coeff_add] },
  { intros,
    simp only [ring_hom.map_mul, constant_coeff_X, pi.zero_apply, ring_hom.map_zero, eq_self_iff_true,
      mem_support_iff, not_true, aeval_X, if_false, ne.def, mul_zero, alg_hom.map_mul, zero_apply] }
end

@[simp] lemma aeval_zero' [algebra R A] (p : mv_polynomial σ R) :
  aeval (λ _, 0 : σ → A) p = algebra_map _ _ (constant_coeff p) :=
aeval_zero σ R A p

open_locale big_operators

lemma C_dvd_iff_dvd_coeff {σ : Type*} {R : Type*} [comm_ring R]
  (r : R) (φ : mv_polynomial σ R) :
  C r ∣ φ ↔ ∀ i, r ∣ (φ.coeff i) :=
begin
  split,
  { rintros ⟨φ, rfl⟩ c, rw coeff_C_mul, apply dvd_mul_right },
  { intro h,
    choose c hc using h,
    classical,
    let c' : (σ →₀ ℕ) → R := λ i, if i ∈ φ.support then c i else 0,
    let ψ : mv_polynomial σ R := ∑ i in φ.support, monomial i (c' i),
    use ψ,
    apply mv_polynomial.ext, intro i,
    simp only [coeff_C_mul, coeff_sum, coeff_monomial],
    rw [finset.sum_eq_single i, if_pos rfl],
    { dsimp [c'], split_ifs with hi hi,
      { rw hc },
      { rw finsupp.not_mem_support_iff at hi, rwa [mul_zero] } },
    { intros j hj hji, convert if_neg hji },
    { intro hi, rw [if_pos rfl], exact if_neg hi } }
end

-- Johan: why the hack does ring_hom.ker not exist!!!
-- Rob: it does now, why do you ask here?

lemma C_dvd_iff_map_hom_eq_zero {σ : Type*} {R : Type*} {S : Type*} [comm_ring R] [comm_ring S]
  (q : R →+* S) (hq : function.surjective q) (r : R) (hr : ∀ r' : R, q r' = 0 ↔ r ∣ r')
  (φ : mv_polynomial σ R) :
  C r ∣ φ ↔ map q φ = 0 :=
begin
  rw C_dvd_iff_dvd_coeff,
  split,
  { intro h, apply mv_polynomial.ext, intro i,
    simp only [coeff_map, *, ring_hom.coe_of, coeff_zero], },
  { rw mv_polynomial.ext_iff,
    simp only [coeff_map, *, ring_hom.coe_of, coeff_zero, imp_self] }
end

lemma C_dvd_iff_zmod {σ : Type*} (n : ℕ) (φ : mv_polynomial σ ℤ) :
  C (n:ℤ) ∣ φ ↔ map (int.cast_ring_hom (zmod n)) φ = 0 :=
begin
  apply C_dvd_iff_map_hom_eq_zero,
  { exact zmod.int_cast_surjective },
  { exact char_p.int_cast_eq_zero_iff (zmod n) n, }
end

end mv_polynomial

namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {υ : Type*} {R S : Type*} [comm_semiring R] [comm_semiring S]
variables (f : R →+* S)
variables (p q : mv_polynomial σ R)

open function
open_locale classical big_operators

section monomial

lemma eval₂_hom_monomial (f : R →+* S) (g : σ → S) (d : σ →₀ ℕ) (r : R) :
  eval₂_hom f g (monomial d r) = f r * d.prod (λ i k, g i ^ k) :=
by simp only [monomial_eq, ring_hom.map_mul, eval₂_hom_C, finsupp.prod,
  ring_hom.map_prod, ring_hom.map_pow, eval₂_hom_X']

lemma aeval_monomial [algebra R S] (g : σ → S) (d : σ →₀ ℕ) (r : R) :
  aeval g (monomial d r) = algebra_map _ _ r * d.prod (λ i k, g i ^ k) :=
eval₂_hom_monomial _ _ _ _

end monomial

section vars

lemma vars_add_subset :
  (p + q).vars ⊆ p.vars ∪ q.vars :=
begin
  intros x hx,
  simp only [vars, finset.mem_union, multiset.mem_to_finset] at hx ⊢,
  simpa using multiset.mem_of_le (degrees_add _ _) hx,
end

lemma finset.mem_sup {α β} [decidable_eq α] [decidable_eq β] {s : finset α} {f : α → multiset β} {x : β} : x ∈ s.sup f ↔
  ∃ v ∈ s, x ∈ f v :=
begin
  apply s.induction_on,
  { simp },
  { intros a s has hxs,
    rw [finset.sup_insert, multiset.sup_eq_union, multiset.mem_union],
    split,
    { intro hxi,
      cases hxi with hf hf,
      { refine ⟨a, _, hf⟩,
        simp only [true_or, eq_self_iff_true, finset.mem_insert] },
      { rcases hxs.mp hf with ⟨v, hv, hfv⟩,
        refine ⟨v, _, hfv⟩,
        simp only [hv, or_true, finset.mem_insert] } },
    { rintros ⟨v, hv, hfv⟩,
      rw [finset.mem_insert] at hv,
      rcases hv with rfl | hv,
      { exact or.inl hfv },
      { refine or.inr (hxs.mpr ⟨v, hv, hfv⟩) } } },
end

-- generalize from multiset?
lemma finset.sup_subset {α β} {s t : finset α} (hst : s ⊆ t) (f : α → multiset β) :
  s.sup f ≤ t.sup f :=
calc t.sup f = (s ∪ t).sup f : by rw [finset.union_eq_right_iff_subset.mpr hst]
         ... = s.sup f ⊔ t.sup f : by rw finset.sup_union
         ... ≥ s.sup f : le_sup_left

lemma multiset.mem_iff_count_ne_zero {α : Type*} (s : multiset α) (a : α) :
  a ∈ s ↔ s.count a ≠ 0 :=
by rw [ne.def, multiset.count_eq_zero, not_not]

@[simp] lemma finsupp.mem_to_multiset (f : σ →₀ ℕ) (i : σ) :
  i ∈ f.to_multiset ↔ i ∈ f.support :=
by rw [multiset.mem_iff_count_ne_zero, finsupp.count_to_multiset, finsupp.mem_support_iff]

lemma mem_degrees (p : mv_polynomial σ R) (i : σ) :
  i ∈ p.degrees ↔ ∃ d, p.coeff d ≠ 0 ∧ i ∈ d.support :=
by simp only [degrees, finset.mem_sup, ← finsupp.mem_support_iff, coeff,
    finsupp.mem_to_multiset, exists_prop]

lemma le_degrees_add (p q : mv_polynomial σ R) (h : p.degrees.disjoint q.degrees) :
  p.degrees ≤ (p + q).degrees :=
begin
  apply finset.sup_le,
  intros d hd,
  rw multiset.disjoint_iff_ne at h,
  rw multiset.le_iff_count,
  intros i,
  rw [degrees, multiset.count_sup],
  simp only [finsupp.count_to_multiset],
  by_cases h0 : d = 0,
  { simp only [h0, zero_le, finsupp.zero_apply], },
  { refine @finset.le_sup _ _ _ (p + q).support _ d _,
    rw [finsupp.mem_support_iff, ← coeff, coeff_add],
    suffices : q.coeff d = 0,
    { rwa [this, add_zero, coeff, ← finsupp.mem_support_iff], },
    rw [← finsupp.support_eq_empty, ← ne.def, ← finset.nonempty_iff_ne_empty] at h0,
    obtain ⟨j, hj⟩ := h0,
    contrapose! h,
    rw finsupp.mem_support_iff at hd,
    refine ⟨j, _, j, _, rfl⟩,
    all_goals { rw mem_degrees, refine ⟨d, _, hj⟩, assumption } }
end

lemma degrees_add_of_disjoint (h : multiset.disjoint p.degrees q.degrees) :
  (p + q).degrees = p.degrees ∪ q.degrees :=
begin
  apply le_antisymm,
  { apply degrees_add },
  { apply multiset.union_le,
    { apply le_degrees_add p q h },
    { rw add_comm, apply le_degrees_add q p h.symm } }
end

lemma multiset.disjoint_to_finset {α} (m1 m2 : multiset α) :
  disjoint m1.to_finset m2.to_finset ↔ m1.disjoint m2 :=
begin
  rw finset.disjoint_iff_ne,
  split,
  { intro h,
    intros a ha1 ha2,
    rw ← multiset.mem_to_finset at ha1 ha2,
    exact h _ ha1 _ ha2 rfl },
  { rintros h a ha b hb rfl,
    rw multiset.mem_to_finset at ha hb,
    exact h ha hb }
end

@[simp] lemma multiset.to_finset_subset {α} (m1 m2 : multiset α) :
  m1.to_finset ⊆ m2.to_finset ↔ m1 ⊆ m2 :=
by simp only [finset.subset_iff, multiset.subset_iff, multiset.mem_to_finset]

@[simp] lemma multiset.to_finset_union {α} (m1 m2 : multiset α) :
  (m1 ∪ m2).to_finset = m1.to_finset ∪ m2.to_finset :=
by ext; simp

lemma vars_add_of_disjoint (h : disjoint p.vars q.vars) :
  (p + q).vars = p.vars ∪ q.vars :=
begin
  apply finset.subset.antisymm (vars_add_subset p q),
  intros x hx,
  simp only [vars, multiset.disjoint_to_finset] at h hx ⊢,
  rw [degrees_add_of_disjoint _ _ h, multiset.to_finset_union],
  exact hx
end

section sum
variables {ι : Type*} (s : finset ι) (φ : ι → mv_polynomial σ R)

lemma finset.union_subset_union {α} {s1 t1 s2 t2 : finset α} (h1 : s1 ⊆ t1) (h2 : s2 ⊆ t2) :
  s1 ∪ s2 ⊆ t1 ∪ t2 :=
by { intros x hx, rw finset.mem_union at hx ⊢, tauto }

lemma vars_sum_subset :
  (∑ i in s, φ i).vars ⊆ finset.bind s (λ i, (φ i).vars) :=
begin
  apply s.induction_on,
  { simp },
  { intros a s has hsum,
    rw [finset.bind_insert, finset.sum_insert has],
    refine finset.subset.trans (vars_add_subset _ _)
      (finset.union_subset_union (finset.subset.refl _) _),
    assumption }
end

lemma vars_sum_of_disjoint (h : pairwise $ disjoint on (λ i, (φ i).vars)) :
  (∑ i in s, φ i).vars = finset.bind s (λ i, (φ i).vars) :=
begin
  apply s.induction_on,
  { simp },
  { intros a s has hsum,
    rw [finset.bind_insert, finset.sum_insert has, vars_add_of_disjoint, hsum],
    unfold pairwise on_fun at h,
    rw hsum,
    simp only [finset.disjoint_iff_ne] at h ⊢,
    intros v hv v2 hv2,
    rw finset.mem_bind at hv2,
    rcases hv2 with ⟨i, his, hi⟩,
    refine h a i _ _ hv _ hi,
    rintro rfl,
    contradiction }
end

end sum

lemma mv_polynomial.support_map_subset : (map f p).support ⊆ p.support :=
begin
  intro x,
  simp only [finsupp.mem_support_iff],
  contrapose!,
  change p.coeff x = 0 → (map f p).coeff x = 0,
  rw coeff_map,
  intro hx,
  rw hx,
  exact ring_hom.map_zero f
end

lemma mv_polynomial.support_map_of_injective (hf : injective f) : (map f p).support = p.support :=
begin
  apply finset.subset.antisymm,
  { exact mv_polynomial.support_map_subset _ _ },
  intros x hx,
  rw finsupp.mem_support_iff,
  contrapose! hx,
  simp only [not_not, finsupp.mem_support_iff],
  change (map f p).coeff x = 0 at hx,
  rw [coeff_map, ← f.map_zero] at hx,
  exact hf hx
end

lemma degrees_map : (map f p).degrees ⊆ p.degrees :=
begin
  dsimp only [degrees],
  apply multiset.subset_of_le,
  convert finset.sup_subset _ _,
  apply mv_polynomial.support_map_subset
end

lemma degrees_map_of_injective (hf : injective f) : (map f p).degrees = p.degrees :=
by simp only [degrees, mv_polynomial.support_map_of_injective _ _ hf]

lemma vars_map : (map f p).vars ⊆ p.vars :=
by simp [vars, degrees_map]

lemma vars_map_of_injective (hf : injective f) :
  (map f p).vars = p.vars :=
by simp [vars, degrees_map_of_injective _ _ hf]

lemma vars_monomial_single (i : σ) (e : ℕ) (r : R) (he : e ≠ 0) (hr : r ≠ 0) :
  (monomial (finsupp.single i e) r).vars = {i} :=
by rw [vars_monomial hr, finsupp.support_single_ne_zero he]

lemma mem_vars (p : mv_polynomial σ R) (i : σ) :
  i ∈ p.vars ↔ ∃ (d : σ →₀ ℕ) (H : d ∈ p.support), i ∈ d.support :=
by simp only [vars, multiset.mem_to_finset, mem_degrees, coeff, finsupp.mem_support_iff, exists_prop]

lemma vars_eq_support_bind_support (p : mv_polynomial σ R) :
  p.vars = p.support.bind finsupp.support :=
by {ext i, rw [mem_vars, finset.mem_bind] }

lemma eval₂_hom_eq_constant_coeff_of_vars (f : R →+* S) (g : σ → S)
  (p : mv_polynomial σ R) (hp : ∀ i ∈ p.vars, g i = 0) :
  eval₂_hom f g p = f (constant_coeff p) :=
begin
  conv_lhs { rw p.as_sum },
  simp only [ring_hom.map_sum, eval₂_hom_monomial],
  by_cases h0 : constant_coeff p = 0,
  work_on_goal 0
  { rw [h0, f.map_zero, finset.sum_eq_zero],
    intros d hd },
  work_on_goal 1
  { rw [finset.sum_eq_single (0 : σ →₀ ℕ)],
    { rw [finsupp.prod_zero_index, mul_one],
      refl },
    intros d hd hd0, },
  repeat
  { obtain ⟨i, hi⟩ : d.support.nonempty,
    { rw [constant_coeff_eq, coeff, ← finsupp.not_mem_support_iff] at h0,
      rw [finset.nonempty_iff_ne_empty, ne.def, finsupp.support_eq_empty],
      rintro rfl, contradiction },
    rw [finsupp.prod, finset.prod_eq_zero hi, mul_zero],
    rw [hp, zero_pow (nat.pos_of_ne_zero $ finsupp.mem_support_iff.mp hi)],
    rw [mem_vars],
    exact ⟨d, hd, hi⟩ },
  { rw [constant_coeff_eq, coeff, ← ne.def, ← finsupp.mem_support_iff] at h0,
    intro, contradiction }
end

lemma aeval_eq_constant_coeff_of_vars [algebra R S] (g : σ → S)
  (p : mv_polynomial σ R) (hp : ∀ i ∈ p.vars, g i = 0) :
  aeval g p = algebra_map _ _ (constant_coeff p) :=
eval₂_hom_eq_constant_coeff_of_vars _ g p hp

end vars

end mv_polynomial


namespace mv_polynomial
variables {σ : Type*} {τ : Type*} {υ : Type*} {R : Type*} [comm_semiring R]

/-- This is an example of a map of “algebraic varieties for dummies” over `R`.
(Not meant in a degrading way. Just that we don'y have any actual varieties in Lean yet.) -/
noncomputable def comap (f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R) :
  (τ → R) → (σ → R) :=
λ x i, aeval x (f (X i))

@[simp] lemma comap_apply (f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R) (x : τ → R) (i : σ) :
  comap f x i = aeval x (f (X i)) := rfl

@[simp] lemma comap_id_apply (x : σ → R) : comap (alg_hom.id R (mv_polynomial σ R)) x = x :=
by { funext i, simp only [comap, alg_hom.id_apply, id.def, aeval_X], }

variables (σ R)

lemma comap_id : comap (alg_hom.id R (mv_polynomial σ R)) = id :=
by { funext x, exact comap_id_apply x }

variables {σ R}

lemma comap_comp_apply (f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R)
  (g : mv_polynomial τ R →ₐ[R] mv_polynomial υ R) (x : υ → R) :
  comap (g.comp f) x = (comap f) (comap g x) :=
begin
  funext i,
  transitivity (aeval x (aeval (λ i, g (X i)) (f (X i)))),
  { apply eval₂_hom_congr rfl rfl,
    rw alg_hom.comp_apply,
    suffices : g = aeval (λ i, g (X i)), { rw ← this, },
    apply mv_polynomial.alg_hom_ext g,
    intro, rw [aeval_X], },
  { simp only [comap, aeval_eq_eval₂_hom, map_eval₂_hom, alg_hom.comp_apply],
    refine eval₂_hom_congr _ rfl rfl,
    ext r, apply aeval_C },
end

lemma comap_comp (f : mv_polynomial σ R →ₐ[R] mv_polynomial τ R)
  (g : mv_polynomial τ R →ₐ[R] mv_polynomial υ R) (x : υ → R) :
  comap (g.comp f) = (comap f) ∘ (comap g) :=
by { funext x, exact comap_comp_apply _ _ _ }

lemma comap_eq_id_of_eq_id (f : mv_polynomial σ R →ₐ[R] mv_polynomial σ R)
  (hf : ∀ φ, f φ = φ) (x : σ → R) :
  comap f x = x :=
by { convert comap_id_apply x, ext1 φ, rw [hf, alg_hom.id_apply] }

noncomputable def comap_equiv (f : mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R) :
  (τ → R) ≃ (σ → R) :=
{ to_fun    := comap f,
  inv_fun   := comap f.symm,
  left_inv  := by { intro x, rw [← comap_comp_apply], apply comap_eq_id_of_eq_id, intro,
    simp only [alg_hom.id_apply, alg_equiv.comp_symm], },
  right_inv := by { intro x, rw [← comap_comp_apply], apply comap_eq_id_of_eq_id, intro,
  simp only [alg_hom.id_apply, alg_equiv.symm_comp] }, }

@[simp] lemma comap_equiv_coe (f : mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R) :
  (comap_equiv f : (τ → R) → (σ → R)) = comap f := rfl

@[simp] lemma comap_equiv_symm_coe (f : mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R) :
  ((comap_equiv f).symm : (σ → R) → (τ → R)) = comap f.symm := rfl

lemma equiv_of_family_aux (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (h : ∀ i, aeval g (f i) = X i) (φ : mv_polynomial σ R) :
  (aeval g) (aeval f φ) = φ :=
begin
  rw ← alg_hom.comp_apply,
  suffices : (aeval g).comp (aeval f) = alg_hom.id _ _,
  { rw [this, alg_hom.id_apply], },
  refine mv_polynomial.alg_hom_ext _ (alg_hom.id _ _) _,
  intro i,
  rw [alg_hom.comp_apply, alg_hom.id_apply, aeval_X, h],
end

noncomputable def equiv_of_family (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i) :
  mv_polynomial σ R ≃ₐ[R] mv_polynomial τ R :=
{ to_fun    := aeval f,
  inv_fun   := aeval g,
  left_inv  := equiv_of_family_aux f g hfg,
  right_inv := equiv_of_family_aux g f hgf,
  .. aeval f}

@[simp] lemma equiv_of_family_coe (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i) :
  (equiv_of_family f g hfg hgf : mv_polynomial σ R →ₐ[R] mv_polynomial τ R) = aeval f := rfl

@[simp] lemma equiv_of_family_symm_coe (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i) :
  ((equiv_of_family f g hfg hgf).symm : mv_polynomial τ R →ₐ[R] mv_polynomial σ R) = aeval g := rfl

@[simp] lemma equiv_of_family_apply (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i)
  (φ : mv_polynomial σ R) :
  equiv_of_family f g hfg hgf φ = aeval f φ := rfl

@[simp] lemma equiv_of_family_symm_apply (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
  (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i)
  (φ : mv_polynomial τ R) :
  (equiv_of_family f g hfg hgf).symm φ = aeval g φ := rfl

-- I think this stuff should move back to the witt_vector file
namespace witt_structure_machine
variable {idx : Type*}
variables (f : σ → mv_polynomial τ R) (g : τ → mv_polynomial σ R)
variables (hfg : ∀ i, aeval g (f i) = X i) (hgf : ∀ i, aeval f (g i) = X i)

noncomputable def structure_polynomial (Φ : mv_polynomial idx R) (t : τ) :
  mv_polynomial (idx × τ) R :=
aeval (λ s : σ, (aeval (λ i, (rename (λ t', (i,t')) (f s)))) Φ) (g t)

include hfg

theorem structure_polynomial_prop (Φ : mv_polynomial idx R) (s : σ) :
  aeval (structure_polynomial f g Φ) (f s) = aeval (λ b, (rename (λ i, (b,i)) (f s))) Φ :=
calc aeval (structure_polynomial f g Φ) (f s) =
      aeval (λ s', aeval (λ b, (rename (prod.mk b)) (f s')) Φ) (aeval g (f s)) :
      by { conv_rhs { rw [aeval_eq_eval₂_hom, map_aeval] },
           apply eval₂_hom_congr _ rfl rfl,
           ext1 r, symmetry, apply eval₂_hom_C, }
... = aeval (λ i, (rename (λ t', (i,t')) (f s))) Φ : by rw [hfg, aeval_X]

include hgf

theorem exists_unique (Φ : mv_polynomial idx R) :
  ∃! (φ : τ → mv_polynomial (idx × τ) R),
    ∀ (s : σ), aeval φ (f s) = aeval (λ i, (rename (λ t', (i,t')) (f s))) Φ :=
begin
  refine ⟨structure_polynomial f g Φ, structure_polynomial_prop _ _ hfg _, _⟩,
  { intros φ H,
    funext t,
    calc φ t = aeval φ (aeval (f) (g t))    : by rw [hgf, aeval_X]
         ... = structure_polynomial f g Φ t : _,
    rw [aeval_eq_eval₂_hom, map_aeval],
    apply eval₂_hom_congr _ _ rfl,
    { ext1 r, exact eval₂_C _ _ r, },
    { funext k, exact H k } }
end

end witt_structure_machine

end mv_polynomial

-- ### end FOR_MATHLIB
