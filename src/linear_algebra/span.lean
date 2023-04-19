/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
import linear_algebra.basic
import order.compactly_generated
import order.omega_complete_partial_order

/-!
# The span of a set of vectors, as a submodule

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

* `submodule.span s` is defined to be the smallest submodule containing the set `s`.

## Notations

* We introduce the notation `R ∙ v` for the span of a singleton, `submodule.span R {v}`.  This is
  `\.`, not the same as the scalar multiplication `•`/`\bub`.

-/
variables {R R₂ K M M₂ V S : Type*}

namespace submodule

open function set
open_locale pointwise

section add_comm_monoid

variables [semiring R] [add_comm_monoid M] [module R M]
variables {x : M} (p p' : submodule R M)
variables [semiring R₂] {σ₁₂ : R →+* R₂}
variables [add_comm_monoid M₂] [module R₂ M₂]

section
variables (R)

/-- The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`. -/
def span (s : set M) : submodule R M := Inf {p | s ⊆ p}
end

variables {s t : set M}
lemma mem_span : x ∈ span R s ↔ ∀ p : submodule R M, s ⊆ p → x ∈ p := mem_Inter₂

lemma subset_span : s ⊆ span R s :=
λ x h, mem_span.2 $ λ p hp, hp h

lemma span_le {p} : span R s ≤ p ↔ s ⊆ p :=
⟨subset.trans subset_span, λ ss x h, mem_span.1 h _ ss⟩

lemma span_mono (h : s ⊆ t) : span R s ≤ span R t :=
span_le.2 $ subset.trans h subset_span

lemma span_monotone : monotone (span R : set M → submodule R M) :=
λ _ _, span_mono

lemma span_eq_of_le (h₁ : s ⊆ p) (h₂ : p ≤ span R s) : span R s = p :=
le_antisymm (span_le.2 h₁) h₂

lemma span_eq : span R (p : set M) = p :=
span_eq_of_le _ (subset.refl _) subset_span

lemma span_eq_span (hs : s ⊆ span R t) (ht : t ⊆ span R s) : span R s = span R t :=
le_antisymm (span_le.2 hs) (span_le.2 ht)

/-- A version of `submodule.span_eq` for when the span is by a smaller ring. -/
@[simp] lemma span_coe_eq_restrict_scalars
  [semiring S] [has_smul S R] [module S M] [is_scalar_tower S R M] :
  span S (p : set M) = p.restrict_scalars S :=
span_eq (p.restrict_scalars S)

lemma map_span [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (s : set M) :
  (span R s).map f = span R₂ (f '' s) :=
eq.symm $ span_eq_of_le _ (set.image_subset f subset_span) $
map_le_iff_le_comap.2 $ span_le.2 $ λ x hx, subset_span ⟨x, hx, rfl⟩

alias submodule.map_span ← _root_.linear_map.map_span

lemma map_span_le [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) (s : set M)
  (N : submodule R₂ M₂) : map f (span R s) ≤ N ↔ ∀ m ∈ s, f m ∈ N :=
begin
  rw [f.map_span, span_le, set.image_subset_iff],
  exact iff.rfl
end

alias submodule.map_span_le ← _root_.linear_map.map_span_le

@[simp] lemma span_insert_zero : span R (insert (0 : M) s) = span R s :=
begin
  refine le_antisymm _ (submodule.span_mono (set.subset_insert 0 s)),
  rw [span_le, set.insert_subset],
  exact ⟨by simp only [set_like.mem_coe, submodule.zero_mem], submodule.subset_span⟩,
end

/- See also `span_preimage_eq` below. -/
lemma span_preimage_le (f : M →ₛₗ[σ₁₂] M₂) (s : set M₂) :
  span R (f ⁻¹' s) ≤ (span R₂ s).comap f :=
by { rw [span_le, comap_coe], exact preimage_mono (subset_span), }

alias submodule.span_preimage_le ← _root_.linear_map.span_preimage_le

lemma closure_subset_span {s : set M} :
  (add_submonoid.closure s : set M) ⊆ span R s :=
(@add_submonoid.closure_le _ _ _ (span R s).to_add_submonoid).mpr subset_span

lemma closure_le_to_add_submonoid_span {s : set M} :
  add_submonoid.closure s ≤ (span R s).to_add_submonoid :=
closure_subset_span

@[simp] lemma span_closure {s : set M} : span R (add_submonoid.closure s : set M) = span R s :=
le_antisymm (span_le.mpr closure_subset_span) (span_mono add_submonoid.subset_closure)

/-- An induction principle for span membership. If `p` holds for 0 and all elements of `s`, and is
preserved under addition and scalar multiplication, then `p` holds for all elements of the span of
`s`. -/
@[elab_as_eliminator] lemma span_induction {p : M → Prop} (h : x ∈ span R s)
  (Hs : ∀ x ∈ s, p x) (H0 : p 0)
  (H1 : ∀ x y, p x → p y → p (x + y))
  (H2 : ∀ (a:R) x, p x → p (a • x)) : p x :=
(@span_le _ _ _ _ _ _ ⟨p, H1, H0, H2⟩).2 Hs h

/-- A dependent version of `submodule.span_induction`. -/
lemma span_induction' {p : Π x, x ∈ span R s → Prop}
  (Hs : ∀ x (h : x ∈ s), p x (subset_span h))
  (H0 : p 0 (submodule.zero_mem _))
  (H1 : ∀ x hx y hy, p x hx → p y hy → p (x + y) (submodule.add_mem _ ‹_› ‹_›))
  (H2 : ∀ (a : R) x hx, p x hx → p (a • x) (submodule.smul_mem _ _ ‹_›)) {x} (hx : x ∈ span R s) :
  p x hx :=
begin
  refine exists.elim _ (λ (hx : x ∈ span R s) (hc : p x hx), hc),
  refine span_induction hx (λ m hm, ⟨subset_span hm, Hs m hm⟩) ⟨zero_mem _, H0⟩
    (λ x y hx hy, exists.elim hx $ λ hx' hx, exists.elim hy $ λ hy' hy,
    ⟨add_mem hx' hy', H1 _ _ _ _ hx hy⟩) (λ r x hx, exists.elim hx $ λ hx' hx,
    ⟨smul_mem _ _ hx', H2 r _ _ hx⟩)
end

@[simp] lemma span_span_coe_preimage : span R ((coe : span R s → M) ⁻¹' s) = ⊤ :=
eq_top_iff.2 $ λ x, subtype.rec_on x $ λ x hx _, begin
  refine span_induction' (λ x hx, _) _ (λ x y _ _, _) (λ r x _, _) hx,
  { exact subset_span hx },
  { exact zero_mem _ },
  { exact add_mem },
  { exact smul_mem _ _ }
end

lemma span_nat_eq_add_submonoid_closure (s : set M) :
  (span ℕ s).to_add_submonoid = add_submonoid.closure s :=
begin
  refine eq.symm (add_submonoid.closure_eq_of_le subset_span _),
  apply add_submonoid.to_nat_submodule.symm.to_galois_connection.l_le _,
  rw span_le,
  exact add_submonoid.subset_closure,
end

@[simp] lemma span_nat_eq (s : add_submonoid M) : (span ℕ (s : set M)).to_add_submonoid = s :=
by rw [span_nat_eq_add_submonoid_closure, s.closure_eq]

lemma span_int_eq_add_subgroup_closure {M : Type*} [add_comm_group M] (s : set M) :
  (span ℤ s).to_add_subgroup = add_subgroup.closure s :=
eq.symm $ add_subgroup.closure_eq_of_le _ subset_span $ λ x hx, span_induction hx
  (λ x hx, add_subgroup.subset_closure hx) (add_subgroup.zero_mem _)
  (λ _ _, add_subgroup.add_mem _) (λ _ _ _, add_subgroup.zsmul_mem _ ‹_› _)

@[simp] lemma span_int_eq {M : Type*} [add_comm_group M] (s : add_subgroup M) :
  (span ℤ (s : set M)).to_add_subgroup = s :=
by rw [span_int_eq_add_subgroup_closure, s.closure_eq]

section
variables (R M)

/-- `span` forms a Galois insertion with the coercion from submodule to set. -/
protected def gi : galois_insertion (@span R M _ _ _) coe :=
{ choice := λ s _, span R s,
  gc := λ s t, span_le,
  le_l_u := λ s, subset_span,
  choice_eq := λ s h, rfl }

end

@[simp] lemma span_empty : span R (∅ : set M) = ⊥ :=
(submodule.gi R M).gc.l_bot

@[simp] lemma span_univ : span R (univ : set M) = ⊤ :=
eq_top_iff.2 $ set_like.le_def.2 $ subset_span

lemma span_union (s t : set M) : span R (s ∪ t) = span R s ⊔ span R t :=
(submodule.gi R M).gc.l_sup

lemma span_Union {ι} (s : ι → set M) : span R (⋃ i, s i) = ⨆ i, span R (s i) :=
(submodule.gi R M).gc.l_supr

lemma span_Union₂ {ι} {κ : ι → Sort*} (s : Π i, κ i → set M) :
  span R (⋃ i j, s i j) = ⨆ i j, span R (s i j) :=
(submodule.gi R M).gc.l_supr₂

lemma span_attach_bUnion [decidable_eq M] {α : Type*} (s : finset α) (f : s → finset M) :
  span R (s.attach.bUnion f : set M) = ⨆ x, span R (f x) :=
by simpa [span_Union]

lemma sup_span : p ⊔ span R s = span R (p ∪ s) :=
by rw [submodule.span_union, p.span_eq]

lemma span_sup : span R s ⊔ p = span R (s ∪ p) :=
by rw [submodule.span_union, p.span_eq]

/- Note that the character `∙` U+2219 used below is different from the scalar multiplication
character `•` U+2022 and the matrix multiplication character `⬝` U+2B1D. -/
notation R` ∙ `:1000 x := span R (@singleton _ _ set.has_singleton x)

lemma span_eq_supr_of_singleton_spans (s : set M) : span R s = ⨆ x ∈ s, R ∙ x :=
by simp only [←span_Union, set.bUnion_of_singleton s]

lemma span_range_eq_supr {ι : Type*} {v : ι → M} : span R (range v) = ⨆ i, R ∙ v i :=
by rw [span_eq_supr_of_singleton_spans, supr_range]

lemma span_smul_le (s : set M) (r : R) :
  span R (r • s) ≤ span R s :=
begin
  rw span_le,
  rintros _ ⟨x, hx, rfl⟩,
  exact smul_mem (span R s) r (subset_span hx),
end

lemma subset_span_trans {U V W : set M} (hUV : U ⊆ submodule.span R V)
  (hVW : V ⊆ submodule.span R W) :
  U ⊆ submodule.span R W :=
(submodule.gi R M).gc.le_u_l_trans hUV hVW

/-- See `submodule.span_smul_eq` (in `ring_theory.ideal.operations`) for
`span R (r • s) = r • span R s` that holds for arbitrary `r` in a `comm_semiring`. -/
lemma span_smul_eq_of_is_unit (s : set M) (r : R) (hr : is_unit r) :
  span R (r • s) = span R s :=
begin
  apply le_antisymm,
  { apply span_smul_le },
  { convert span_smul_le (r • s) ((hr.unit ⁻¹ : _) : R),
    rw smul_smul,
    erw hr.unit.inv_val,
    rw one_smul }
end

@[simp] theorem coe_supr_of_directed {ι} [hι : nonempty ι]
  (S : ι → submodule R M) (H : directed (≤) S) :
  ((supr S : submodule R M) : set M) = ⋃ i, S i :=
begin
  refine subset.antisymm _ (Union_subset $ le_supr S),
  suffices : (span R (⋃ i, (S i : set M)) : set M) ⊆ ⋃ (i : ι), ↑(S i),
    by simpa only [span_Union, span_eq] using this,
  refine (λ x hx, span_induction hx (λ _, id) _ _ _);
    simp only [mem_Union, exists_imp_distrib],
  { exact hι.elim (λ i, ⟨i, (S i).zero_mem⟩) },
  { intros x y i hi j hj,
    rcases H i j with ⟨k, ik, jk⟩,
    exact ⟨k, add_mem (ik hi) (jk hj)⟩ },
  { exact λ a x i hi, ⟨i, smul_mem _ a hi⟩ },
end

@[simp] theorem mem_supr_of_directed {ι} [nonempty ι]
  (S : ι → submodule R M) (H : directed (≤) S) {x} :
  x ∈ supr S ↔ ∃ i, x ∈ S i :=
by { rw [← set_like.mem_coe, coe_supr_of_directed S H, mem_Union], refl }

theorem mem_Sup_of_directed {s : set (submodule R M)}
  {z} (hs : s.nonempty) (hdir : directed_on (≤) s) :
  z ∈ Sup s ↔ ∃ y ∈ s, z ∈ y :=
begin
  haveI : nonempty s := hs.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed _ hdir.directed_coe, set_coe.exists, subtype.coe_mk]
end

@[norm_cast, simp] lemma coe_supr_of_chain (a : ℕ →o submodule R M) :
  (↑(⨆ k, a k) : set M) = ⋃ k, (a k : set M) :=
coe_supr_of_directed a a.monotone.directed_le

/-- We can regard `coe_supr_of_chain` as the statement that `coe : (submodule R M) → set M` is
Scott continuous for the ω-complete partial order induced by the complete lattice structures. -/
lemma coe_scott_continuous : omega_complete_partial_order.continuous'
  (coe : submodule R M → set M) :=
⟨set_like.coe_mono, coe_supr_of_chain⟩

@[simp] lemma mem_supr_of_chain (a : ℕ →o submodule R M) (m : M) :
  m ∈ (⨆ k, a k) ↔ ∃ k, m ∈ a k :=
mem_supr_of_directed a a.monotone.directed_le

section

variables {p p'}

lemma mem_sup : x ∈ p ⊔ p' ↔ ∃ (y ∈ p) (z ∈ p'), y + z = x :=
⟨λ h, begin
  rw [← span_eq p, ← span_eq p', ← span_union] at h,
  apply span_induction h,
  { rintro y (h | h),
    { exact ⟨y, h, 0, by simp, by simp⟩ },
    { exact ⟨0, by simp, y, h, by simp⟩ } },
  { exact ⟨0, by simp, 0, by simp⟩ },
  { rintro _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩,
    exact ⟨_, add_mem hy₁ hy₂, _, add_mem hz₁ hz₂, by simp [add_assoc]; cc⟩ },
  { rintro a _ ⟨y, hy, z, hz, rfl⟩,
    exact ⟨_, smul_mem _ a hy, _, smul_mem _ a hz, by simp [smul_add]⟩ }
end,
by rintro ⟨y, hy, z, hz, rfl⟩; exact add_mem
  ((le_sup_left : p ≤ p ⊔ p') hy)
  ((le_sup_right : p' ≤ p ⊔ p') hz)⟩

lemma mem_sup' : x ∈ p ⊔ p' ↔ ∃ (y : p) (z : p'), (y:M) + z = x :=
mem_sup.trans $ by simp only [set_like.exists, coe_mk]

variables (p p')

lemma coe_sup : ↑(p ⊔ p') = (p + p' : set M) :=
by { ext, rw [set_like.mem_coe, mem_sup, set.mem_add], simp, }

lemma sup_to_add_submonoid :
  (p ⊔ p').to_add_submonoid = p.to_add_submonoid ⊔ p'.to_add_submonoid :=
begin
  ext x,
  rw [mem_to_add_submonoid, mem_sup, add_submonoid.mem_sup],
  refl,
end

lemma sup_to_add_subgroup {R M : Type*} [ring R] [add_comm_group M] [module R M]
  (p p' : submodule R M) :
  (p ⊔ p').to_add_subgroup = p.to_add_subgroup ⊔ p'.to_add_subgroup :=
begin
  ext x,
  rw [mem_to_add_subgroup, mem_sup, add_subgroup.mem_sup],
  refl,
end

end

lemma mem_span_singleton_self (x : M) : x ∈ R ∙ x := subset_span rfl

lemma nontrivial_span_singleton {x : M} (h : x ≠ 0) : nontrivial (R ∙ x) :=
⟨begin
    use [0, x, submodule.mem_span_singleton_self x],
    intros H,
    rw [eq_comm, submodule.mk_eq_zero] at H,
    exact h H
end⟩

lemma mem_span_singleton {y : M} : x ∈ (R ∙ y) ↔ ∃ a:R, a • y = x :=
⟨λ h, begin
  apply span_induction h,
  { rintro y (rfl|⟨⟨⟩⟩), exact ⟨1, by simp⟩ },
  { exact ⟨0, by simp⟩ },
  { rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩,
    exact ⟨a + b, by simp [add_smul]⟩ },
  { rintro a _ ⟨b, rfl⟩,
    exact ⟨a * b, by simp [smul_smul]⟩ }
end,
by rintro ⟨a, y, rfl⟩; exact
  smul_mem _ _ (subset_span $ by simp)⟩

lemma le_span_singleton_iff {s : submodule R M} {v₀ : M} :
  s ≤ (R ∙ v₀) ↔ ∀ v ∈ s, ∃ r : R, r • v₀ = v :=
by simp_rw [set_like.le_def, mem_span_singleton]

variables (R)

lemma span_singleton_eq_top_iff (x : M) : (R ∙ x) = ⊤ ↔ ∀ v, ∃ r : R, r • x = v :=
by { rw [eq_top_iff, le_span_singleton_iff], tauto }

@[simp] lemma span_zero_singleton : (R ∙ (0:M)) = ⊥ :=
by { ext, simp [mem_span_singleton, eq_comm] }

lemma span_singleton_eq_range (y : M) : ↑(R ∙ y) = range ((• y) : R → M) :=
set.ext $ λ x, mem_span_singleton

lemma span_singleton_smul_le {S} [monoid S] [has_smul S R] [mul_action S M]
  [is_scalar_tower S R M] (r : S) (x : M) : (R ∙ (r • x)) ≤ R ∙ x :=
begin
  rw [span_le, set.singleton_subset_iff, set_like.mem_coe],
  exact smul_of_tower_mem _ _ (mem_span_singleton_self _)
end

lemma span_singleton_group_smul_eq {G} [group G] [has_smul G R] [mul_action G M]
  [is_scalar_tower G R M] (g : G) (x : M) : (R ∙ (g • x)) = R ∙ x :=
begin
  refine le_antisymm (span_singleton_smul_le R g x) _,
  convert span_singleton_smul_le R (g⁻¹) (g • x),
  exact (inv_smul_smul g x).symm
end

variables {R}

lemma span_singleton_smul_eq {r : R} (hr : is_unit r) (x : M) : (R ∙ (r • x)) = R ∙ x :=
begin
  lift r to Rˣ using hr,
  rw ←units.smul_def,
  exact span_singleton_group_smul_eq R r x,
end

lemma disjoint_span_singleton {K E : Type*} [division_ring K] [add_comm_group E] [module K E]
  {s : submodule K E} {x : E} :
  disjoint s (K ∙ x) ↔ (x ∈ s → x = 0) :=
begin
  refine disjoint_def.trans ⟨λ H hx, H x hx $ subset_span $ mem_singleton x, _⟩,
  assume H y hy hyx,
  obtain ⟨c, rfl⟩ := mem_span_singleton.1 hyx,
  by_cases hc : c = 0,
  { rw [hc, zero_smul] },
  { rw [s.smul_mem_iff hc] at hy,
    rw [H hy, smul_zero] }
end

lemma disjoint_span_singleton' {K E : Type*} [division_ring K] [add_comm_group E] [module K E]
  {p : submodule K E} {x : E} (x0 : x ≠ 0) :
  disjoint p (K ∙ x) ↔ x ∉ p :=
disjoint_span_singleton.trans ⟨λ h₁ h₂, x0 (h₁ h₂), λ h₁ h₂, (h₁ h₂).elim⟩

lemma mem_span_singleton_trans {x y z : M} (hxy : x ∈ R ∙ y) (hyz : y ∈ R ∙ z) :
  x ∈ R ∙ z :=
begin
  rw [← set_like.mem_coe, ← singleton_subset_iff] at *,
  exact submodule.subset_span_trans hxy hyz
end

lemma mem_span_insert {y} : x ∈ span R (insert y s) ↔ ∃ (a:R) (z ∈ span R s), x = a • y + z :=
begin
  simp only [← union_singleton, span_union, mem_sup, mem_span_singleton, exists_prop,
    exists_exists_eq_and],
  rw [exists_comm],
  simp only [eq_comm, add_comm, exists_and_distrib_left]
end

lemma mem_span_pair {x y z : M} : z ∈ span R ({x, y} : set M) ↔ ∃ a b : R, a • x + b • y = z :=
by simp_rw [mem_span_insert, mem_span_singleton, exists_prop, exists_exists_eq_and, eq_comm]

lemma span_insert (x) (s : set M) : span R (insert x s) = span R ({x} : set M) ⊔ span R s :=
by rw [insert_eq, span_union]

lemma span_insert_eq_span (h : x ∈ span R s) : span R (insert x s) = span R s :=
span_eq_of_le _ (set.insert_subset.mpr ⟨h, subset_span⟩) (span_mono $ subset_insert _ _)

lemma span_span : span R (span R s : set M) = span R s := span_eq _

variables (R S s)

/-- If `R` is "smaller" ring than `S` then the span by `R` is smaller than the span by `S`. -/
lemma span_le_restrict_scalars [semiring S] [has_smul R S] [module S M] [is_scalar_tower R S M] :
  span R s ≤ (span S s).restrict_scalars R :=
submodule.span_le.2 submodule.subset_span

/-- A version of `submodule.span_le_restrict_scalars` with coercions. -/
@[simp] lemma span_subset_span [semiring S] [has_smul R S] [module S M] [is_scalar_tower R S M] :
  ↑(span R s) ⊆ (span S s : set M) :=
span_le_restrict_scalars R S s

/-- Taking the span by a large ring of the span by the small ring is the same as taking the span
by just the large ring. -/
lemma span_span_of_tower [semiring S] [has_smul R S] [module S M] [is_scalar_tower R S M] :
  span S (span R s : set M) = span S s :=
le_antisymm (span_le.2 $ span_subset_span R S s) (span_mono subset_span)

variables {R S s}

lemma span_eq_bot : span R (s : set M) = ⊥ ↔ ∀ x ∈ s, (x:M) = 0 :=
eq_bot_iff.trans ⟨
  λ H x h, (mem_bot R).1 $ H $ subset_span h,
  λ H, span_le.2 (λ x h, (mem_bot R).2 $ H x h)⟩

@[simp] lemma span_singleton_eq_bot : (R ∙ x) = ⊥ ↔ x = 0 :=
span_eq_bot.trans $ by simp

@[simp] lemma span_zero : span R (0 : set M) = ⊥ := by rw [←singleton_zero, span_singleton_eq_bot]

lemma span_singleton_eq_span_singleton {R M : Type*} [ring R] [add_comm_group M] [module R M]
  [no_zero_smul_divisors R M] {x y : M} : (R ∙ x) = (R ∙ y) ↔ ∃ z : Rˣ, z • x = y :=
begin
  by_cases hx : x = 0,
  { rw [hx, span_zero_singleton, eq_comm, span_singleton_eq_bot],
    exact ⟨λ hy, ⟨1, by rw [hy, smul_zero]⟩, λ ⟨_, hz⟩, by rw [← hz, smul_zero]⟩ },
  by_cases hy : y = 0,
  { rw [hy, span_zero_singleton, span_singleton_eq_bot],
    exact ⟨λ hx, ⟨1, by rw [hx, smul_zero]⟩, λ ⟨z, hz⟩, (smul_eq_zero_iff_eq z).mp hz⟩ },
  split,
  { intro hxy,
    cases mem_span_singleton.mp (by { rw [hxy], apply mem_span_singleton_self }) with v hv,
    cases mem_span_singleton.mp (by { rw [← hxy], apply mem_span_singleton_self }) with i hi,
    have vi : v * i = 1 :=
    by { rw [← one_smul R y, ← hi, smul_smul] at hv, exact smul_left_injective R hy hv },
    have iv : i * v = 1 :=
    by { rw [← one_smul R x, ← hv, smul_smul] at hi, exact smul_left_injective R hx hi },
    exact ⟨⟨v, i, vi, iv⟩, hv⟩ },
  { rintro ⟨v, rfl⟩,
    rw span_singleton_group_smul_eq }
end

@[simp] lemma span_image [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) :
  span R₂ (f '' s) = map f (span R s) :=
(map_span f s).symm

lemma apply_mem_span_image_of_mem_span
   [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) {x : M} {s : set M} (h : x ∈ submodule.span R s) :
   f x ∈ submodule.span R₂ (f '' s) :=
begin
  rw submodule.span_image,
  exact submodule.mem_map_of_mem h
end

@[simp] lemma map_subtype_span_singleton {p : submodule R M} (x : p) :
  map p.subtype (R ∙ x) = R ∙ (x : M) :=
by simp [← span_image]

/-- `f` is an explicit argument so we can `apply` this theorem and obtain `h` as a new goal. -/
lemma not_mem_span_of_apply_not_mem_span_image
   [ring_hom_surjective σ₁₂] (f : M →ₛₗ[σ₁₂] M₂) {x : M} {s : set M}
   (h : f x ∉ submodule.span R₂ (f '' s)) :
   x ∉ submodule.span R s :=
h.imp (apply_mem_span_image_of_mem_span f)

lemma supr_span {ι : Sort*} (p : ι → set M) : (⨆ i, span R (p i)) = span R (⋃ i, p i) :=
le_antisymm (supr_le $ λ i, span_mono $ subset_Union _ i) $
  span_le.mpr $ Union_subset $ λ i m hm, mem_supr_of_mem i $ subset_span hm

lemma supr_eq_span {ι : Sort*} (p : ι → submodule R M) : (⨆ i, p i) = span R (⋃ i, ↑(p i)) :=
by simp_rw [← supr_span, span_eq]

lemma supr_to_add_submonoid {ι : Sort*} (p : ι → submodule R M) :
  (⨆ i, p i).to_add_submonoid = ⨆ i, (p i).to_add_submonoid :=
begin
  refine le_antisymm (λ x, _) (supr_le $ λ i, to_add_submonoid_mono $ le_supr _ i),
  simp_rw [supr_eq_span, add_submonoid.supr_eq_closure, mem_to_add_submonoid, coe_to_add_submonoid],
  intros hx,
  refine submodule.span_induction hx (λ x hx, _) _ (λ x y hx hy, _) (λ r x hx, _),
  { exact add_submonoid.subset_closure hx },
  { exact add_submonoid.zero_mem _ },
  { exact add_submonoid.add_mem _ hx hy },
  { apply add_submonoid.closure_induction hx,
    { rintros x ⟨_, ⟨i, rfl⟩, hix : x ∈ p i⟩,
      apply add_submonoid.subset_closure (set.mem_Union.mpr ⟨i, _⟩),
      exact smul_mem _ r hix },
    { rw smul_zero,
      exact add_submonoid.zero_mem _ },
    { intros x y hx hy,
      rw smul_add,
      exact add_submonoid.add_mem _ hx hy, } }
end

/-- An induction principle for elements of `⨆ i, p i`.
If `C` holds for `0` and all elements of `p i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `p`. -/
@[elab_as_eliminator]
lemma supr_induction {ι : Sort*} (p : ι → submodule R M) {C : M → Prop} {x : M} (hx : x ∈ ⨆ i, p i)
  (hp : ∀ i (x ∈ p i), C x)
  (h0 : C 0)
  (hadd : ∀ x y, C x → C y → C (x + y)) : C x :=
begin
  rw [←mem_to_add_submonoid, supr_to_add_submonoid] at hx,
  exact add_submonoid.supr_induction _ hx hp h0 hadd,
end

/-- A dependent version of `submodule.supr_induction`. -/
@[elab_as_eliminator]
lemma supr_induction' {ι : Sort*} (p : ι → submodule R M) {C : Π x, (x ∈ ⨆ i, p i) → Prop}
  (hp : ∀ i (x ∈ p i), C x (mem_supr_of_mem i ‹_›))
  (h0 : C 0 (zero_mem _))
  (hadd : ∀ x y hx hy, C x hx → C y hy → C (x + y) (add_mem ‹_› ‹_›))
  {x : M} (hx : x ∈ ⨆ i, p i) : C x hx :=
begin
  refine exists.elim _ (λ (hx : x ∈ ⨆ i, p i) (hc : C x hx), hc),
  refine supr_induction p hx (λ i x hx, _) _ (λ x y, _),
  { exact ⟨_, hp _ _ hx⟩ },
  { exact ⟨_, h0⟩ },
  { rintro ⟨_, Cx⟩ ⟨_, Cy⟩,
    refine ⟨_, hadd _ _ _ _ Cx Cy⟩ },
end

@[simp] lemma span_singleton_le_iff_mem (m : M) (p : submodule R M) : (R ∙ m) ≤ p ↔ m ∈ p :=
by rw [span_le, singleton_subset_iff, set_like.mem_coe]

lemma singleton_span_is_compact_element (x : M) :
  complete_lattice.is_compact_element (span R {x} : submodule R M) :=
begin
  rw complete_lattice.is_compact_element_iff_le_of_directed_Sup_le,
  intros d hemp hdir hsup,
  have : x ∈ Sup d, from (set_like.le_def.mp hsup) (mem_span_singleton_self x),
  obtain ⟨y, ⟨hyd, hxy⟩⟩ := (mem_Sup_of_directed hemp hdir).mp this,
  exact ⟨y, ⟨hyd, by simpa only [span_le, singleton_subset_iff]⟩⟩,
end

/-- The span of a finite subset is compact in the lattice of submodules. -/
lemma finset_span_is_compact_element (S : finset M) :
  complete_lattice.is_compact_element (span R S : submodule R M) :=
begin
  rw span_eq_supr_of_singleton_spans,
  simp only [finset.mem_coe],
  rw ←finset.sup_eq_supr,
  exact complete_lattice.finset_sup_compact_of_compact S
    (λ x _, singleton_span_is_compact_element x),
end

/-- The span of a finite subset is compact in the lattice of submodules. -/
lemma finite_span_is_compact_element (S : set M) (h : S.finite) :
  complete_lattice.is_compact_element (span R S : submodule R M) :=
finite.coe_to_finset h ▸ (finset_span_is_compact_element h.to_finset)

instance : is_compactly_generated (submodule R M) :=
⟨λ s, ⟨(λ x, span R {x}) '' s, ⟨λ t ht, begin
  rcases (set.mem_image _ _ _).1 ht with ⟨x, hx, rfl⟩,
  apply singleton_span_is_compact_element,
end, by rw [Sup_eq_supr, supr_image, ←span_eq_supr_of_singleton_spans, span_eq]⟩⟩⟩

/-- A submodule is equal to the supremum of the spans of the submodule's nonzero elements. -/
lemma submodule_eq_Sup_le_nonzero_spans (p : submodule R M) :
  p = Sup {T : submodule R M | ∃ (m : M) (hm : m ∈ p) (hz : m ≠ 0), T = span R {m}} :=
begin
  let S := {T : submodule R M | ∃ (m : M) (hm : m ∈ p) (hz : m ≠ 0), T = span R {m}},
  apply le_antisymm,
  { intros m hm, by_cases h : m = 0,
    { rw h, simp },
    { exact @le_Sup _ _ S _ ⟨m, ⟨hm, ⟨h, rfl⟩⟩⟩ m (mem_span_singleton_self m) } },
  { rw Sup_le_iff, rintros S ⟨_, ⟨_, ⟨_, rfl⟩⟩⟩, rwa span_singleton_le_iff_mem }
end

lemma lt_sup_iff_not_mem {I : submodule R M} {a : M} : I < I ⊔ (R ∙ a) ↔ a ∉ I :=
begin
  split,
  { intro h,
    by_contra akey,
    have h1 : I ⊔ (R ∙ a) ≤ I,
    { simp only [sup_le_iff],
      split,
      { exact le_refl I, },
      { exact (span_singleton_le_iff_mem a I).mpr akey, } },
    have h2 := gt_of_ge_of_gt h1 h,
    exact lt_irrefl I h2, },
  { intro h,
    apply set_like.lt_iff_le_and_exists.mpr, split,
    simp only [le_sup_left],
    use a,
    split, swap, { assumption, },
    { have : (R ∙ a) ≤ I ⊔ (R ∙ a) := le_sup_right,
      exact this (mem_span_singleton_self a), } },
end

lemma mem_supr {ι : Sort*} (p : ι → submodule R M) {m : M} :
  (m ∈ ⨆ i, p i) ↔ (∀ N, (∀ i, p i ≤ N) → m ∈ N) :=
begin
  rw [← span_singleton_le_iff_mem, le_supr_iff],
  simp only [span_singleton_le_iff_mem],
end

section

open_locale classical

/-- For every element in the span of a set, there exists a finite subset of the set
such that the element is contained in the span of the subset. -/
lemma mem_span_finite_of_mem_span {S : set M} {x : M} (hx : x ∈ span R S) :
  ∃ T : finset M, ↑T ⊆ S ∧ x ∈ span R (T : set M) :=
begin
  refine span_induction hx (λ x hx, _) _ _ _,
  { refine ⟨{x}, _, _⟩,
    { rwa [finset.coe_singleton, set.singleton_subset_iff] },
    { rw finset.coe_singleton,
      exact submodule.mem_span_singleton_self x } },
  { use ∅, simp },
  { rintros x y ⟨X, hX, hxX⟩ ⟨Y, hY, hyY⟩,
    refine ⟨X ∪ Y, _, _⟩,
    { rw finset.coe_union,
      exact set.union_subset hX hY },
    rw [finset.coe_union, span_union, mem_sup],
    exact ⟨x, hxX, y, hyY, rfl⟩, },
  { rintros a x ⟨T, hT, h2⟩,
    exact ⟨T, hT, smul_mem _ _ h2⟩ }
end

end

variables {M' : Type*} [add_comm_monoid M'] [module R M'] (q₁ q₁' : submodule R M')

/-- The product of two submodules is a submodule. -/
def prod : submodule R (M × M') :=
{ carrier   := p ×ˢ q₁,
  smul_mem' := by rintro a ⟨x, y⟩ ⟨hx, hy⟩; exact ⟨smul_mem _ a hx, smul_mem _ a hy⟩,
  .. p.to_add_submonoid.prod q₁.to_add_submonoid }

@[simp] lemma prod_coe : (prod p q₁ : set (M × M')) = p ×ˢ q₁ := rfl

@[simp] lemma mem_prod {p : submodule R M} {q : submodule R M'} {x : M × M'} :
  x ∈ prod p q ↔ x.1 ∈ p ∧ x.2 ∈ q := set.mem_prod

lemma span_prod_le (s : set M) (t : set M') :
  span R (s ×ˢ t) ≤ prod (span R s) (span R t) :=
span_le.2 $ set.prod_mono subset_span subset_span

@[simp] lemma prod_top : (prod ⊤ ⊤ : submodule R (M × M')) = ⊤ :=
by ext; simp

@[simp] lemma prod_bot : (prod ⊥ ⊥ : submodule R (M × M')) = ⊥ :=
by ext ⟨x, y⟩; simp [prod.zero_eq_mk]

lemma prod_mono {p p' : submodule R M} {q q' : submodule R M'} :
  p ≤ p' → q ≤ q' → prod p q ≤ prod p' q' := prod_mono

@[simp] lemma prod_inf_prod : prod p q₁ ⊓ prod p' q₁' = prod (p ⊓ p') (q₁ ⊓ q₁') :=
set_like.coe_injective set.prod_inter_prod

@[simp] lemma prod_sup_prod : prod p q₁ ⊔ prod p' q₁' = prod (p ⊔ p') (q₁ ⊔ q₁') :=
begin
  refine le_antisymm (sup_le
    (prod_mono le_sup_left le_sup_left)
    (prod_mono le_sup_right le_sup_right)) _,
  simp [set_like.le_def], intros xx yy hxx hyy,
  rcases mem_sup.1 hxx with ⟨x, hx, x', hx', rfl⟩,
  rcases mem_sup.1 hyy with ⟨y, hy, y', hy', rfl⟩,
  refine mem_sup.2 ⟨(x, y), ⟨hx, hy⟩, (x', y'), ⟨hx', hy'⟩, rfl⟩
end

end add_comm_monoid

section add_comm_group

variables [ring R] [add_comm_group M] [module R M]

@[simp] lemma span_neg (s : set M) : span R (-s) = span R s :=
calc span R (-s) = span R ((-linear_map.id : M →ₗ[R] M) '' s) : by simp
 ... = map (-linear_map.id) (span R s) : ((-linear_map.id).map_span _).symm
... = span R s : by simp

lemma mem_span_insert' {x y} {s : set M} : x ∈ span R (insert y s) ↔ ∃(a:R), x + a • y ∈ span R s :=
begin
  rw mem_span_insert, split,
  { rintro ⟨a, z, hz, rfl⟩, exact ⟨-a, by simp [hz, add_assoc]⟩ },
  { rintro ⟨a, h⟩, exact ⟨-a, _, h, by simp [add_comm, add_left_comm]⟩ }
end

instance : is_modular_lattice (submodule R M) :=
⟨λ x y z xz a ha, begin
  rw [mem_inf, mem_sup] at ha,
  rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩,
  rw mem_sup,
  refine ⟨b, hb, c, mem_inf.2 ⟨hc, _⟩, rfl⟩,
  rw [← add_sub_cancel c b, add_comm],
  apply z.sub_mem haz (xz hb),
end⟩

end add_comm_group

section add_comm_group

variables [semiring R] [semiring R₂]
variables [add_comm_group M] [module R M] [add_comm_group M₂] [module R₂ M₂]
variables {τ₁₂ : R →+* R₂} [ring_hom_surjective τ₁₂]
variables {F : Type*} [sc : semilinear_map_class F τ₁₂ M M₂]

include sc
lemma comap_map_eq (f : F) (p : submodule R M) :
  comap f (map f p) = p ⊔ (linear_map.ker f) :=
begin
  refine le_antisymm _ (sup_le (le_comap_map _ _) (comap_mono bot_le)),
  rintro x ⟨y, hy, e⟩,
  exact mem_sup.2 ⟨y, hy, x - y, by simpa using sub_eq_zero.2 e.symm, by simp⟩
end

lemma comap_map_eq_self {f : F} {p : submodule R M} (h : linear_map.ker f ≤ p) :
  comap f (map f p) = p :=
by rw [submodule.comap_map_eq, sup_of_le_left h]
omit sc

end add_comm_group

end submodule

namespace linear_map

open submodule function

section add_comm_group

variables [semiring R] [semiring R₂]
variables [add_comm_group M] [add_comm_group M₂]
variables [module R M] [module R₂ M₂]
variables {τ₁₂ : R →+* R₂} [ring_hom_surjective τ₁₂]
variables {F : Type*} [sc : semilinear_map_class F τ₁₂ M M₂]
include R

include sc
protected lemma map_le_map_iff (f : F) {p p'} : map f p ≤ map f p' ↔ p ≤ p' ⊔ ker f :=
by rw [map_le_iff_le_comap, submodule.comap_map_eq]

theorem map_le_map_iff' {f : F} (hf : ker f = ⊥) {p p'} :
  map f p ≤ map f p' ↔ p ≤ p' :=
by rw [linear_map.map_le_map_iff, hf, sup_bot_eq]

theorem map_injective {f : F} (hf : ker f = ⊥) : injective (map f) :=
λ p p' h, le_antisymm ((map_le_map_iff' hf).1 (le_of_eq h)) ((map_le_map_iff' hf).1 (ge_of_eq h))

theorem map_eq_top_iff {f : F} (hf : range f = ⊤) {p : submodule R M} :
  p.map f = ⊤ ↔ p ⊔ linear_map.ker f = ⊤ :=
by simp_rw [← top_le_iff, ← hf, range_eq_map, linear_map.map_le_map_iff]

end add_comm_group

section
variables (R) (M) [semiring R] [add_comm_monoid M] [module R M]

/-- Given an element `x` of a module `M` over `R`, the natural map from
    `R` to scalar multiples of `x`.-/
@[simps] def to_span_singleton (x : M) : R →ₗ[R] M := linear_map.id.smul_right x

/-- The range of `to_span_singleton x` is the span of `x`.-/
lemma span_singleton_eq_range (x : M) : (R ∙ x) = (to_span_singleton R M x).range :=
submodule.ext $ λ y, by {refine iff.trans _ linear_map.mem_range.symm, exact mem_span_singleton }

@[simp] lemma to_span_singleton_one (x : M) : to_span_singleton R M x 1 = x := one_smul _ _

@[simp] lemma to_span_singleton_zero : to_span_singleton R M 0 = 0 := by { ext, simp, }

end

section add_comm_monoid

variables [semiring R] [add_comm_monoid M] [module R M]
variables [semiring R₂] [add_comm_monoid M₂] [module R₂ M₂]
variables {σ₁₂ : R →+* R₂}

/-- If two linear maps are equal on a set `s`, then they are equal on `submodule.span s`.

See also `linear_map.eq_on_span'` for a version using `set.eq_on`. -/
lemma eq_on_span {s : set M} {f g : M →ₛₗ[σ₁₂] M₂} (H : set.eq_on f g s) ⦃x⦄ (h : x ∈ span R s) :
  f x = g x :=
by apply span_induction h H; simp {contextual := tt}

/-- If two linear maps are equal on a set `s`, then they are equal on `submodule.span s`.

This version uses `set.eq_on`, and the hidden argument will expand to `h : x ∈ (span R s : set M)`.
See `linear_map.eq_on_span` for a version that takes `h : x ∈ span R s` as an argument. -/
lemma eq_on_span' {s : set M} {f g : M →ₛₗ[σ₁₂] M₂} (H : set.eq_on f g s) :
  set.eq_on f g (span R s : set M) :=
eq_on_span H

/-- If `s` generates the whole module and linear maps `f`, `g` are equal on `s`, then they are
equal. -/
lemma ext_on {s : set M} {f g : M →ₛₗ[σ₁₂] M₂} (hv : span R s = ⊤) (h : set.eq_on f g s) :
  f = g :=
linear_map.ext (λ x, eq_on_span h (eq_top_iff'.1 hv _))

/-- If the range of `v : ι → M` generates the whole module and linear maps `f`, `g` are equal at
each `v i`, then they are equal. -/
lemma ext_on_range {ι : Type*} {v : ι → M} {f g : M →ₛₗ[σ₁₂] M₂} (hv : span R (set.range v) = ⊤)
  (h : ∀i, f (v i) = g (v i)) : f = g :=
ext_on hv (set.forall_range_iff.2 h)

end add_comm_monoid

section field

variables {K V} [field K] [add_comm_group V] [module K V]

noncomputable theory
open_locale classical

lemma span_singleton_sup_ker_eq_top (f : V →ₗ[K] K) {x : V} (hx : f x ≠ 0) :
  (K ∙ x) ⊔ f.ker = ⊤ :=
eq_top_iff.2 (λ y hy, submodule.mem_sup.2 ⟨(f y * (f x)⁻¹) • x,
  submodule.mem_span_singleton.2 ⟨f y * (f x)⁻¹, rfl⟩,
    ⟨y - (f y * (f x)⁻¹) • x,
      by rw [linear_map.mem_ker, f.map_sub, f.map_smul, smul_eq_mul, mul_assoc,
             inv_mul_cancel hx, mul_one, sub_self],
      by simp only [add_sub_cancel'_right]⟩⟩)

variables (K V)

lemma ker_to_span_singleton {x : V} (h : x ≠ 0) : (to_span_singleton K V x).ker = ⊥ :=
begin
  ext c, split,
  { intros hc, rw submodule.mem_bot, rw mem_ker at hc, by_contra hc',
    have : x = 0,
      calc x = c⁻¹ • (c • x) : by rw [← mul_smul, inv_mul_cancel hc', one_smul]
      ... = c⁻¹ • ((to_span_singleton K V x) c) : rfl
      ... = 0 : by rw [hc, smul_zero],
    tauto },
  { rw [mem_ker, submodule.mem_bot], intros h, rw h, simp }
end

end field

end linear_map

open linear_map

namespace linear_equiv

section field

variables (K V) [field K] [add_comm_group V] [module K V]

/-- Given a nonzero element `x` of a vector space `V` over a field `K`, the natural
    map from `K` to the span of `x`, with invertibility check to consider it as an
    isomorphism.-/
def to_span_nonzero_singleton (x : V) (h : x ≠ 0) : K ≃ₗ[K] (K ∙ x) :=
linear_equiv.trans
  (linear_equiv.of_injective
    (linear_map.to_span_singleton K V x) (ker_eq_bot.1 $ linear_map.ker_to_span_singleton K V h))
  (linear_equiv.of_eq (to_span_singleton K V x).range (K ∙ x)
    (span_singleton_eq_range K V x).symm)

lemma to_span_nonzero_singleton_one (x : V) (h : x ≠ 0) :
  linear_equiv.to_span_nonzero_singleton K V x h 1 =
    (⟨x, submodule.mem_span_singleton_self x⟩ : K ∙ x) :=
begin
  apply set_like.coe_eq_coe.mp,
  have : ↑(to_span_nonzero_singleton K V x h 1) = to_span_singleton K V x 1 := rfl,
  rw [this, to_span_singleton_one, submodule.coe_mk],
end

/-- Given a nonzero element `x` of a vector space `V` over a field `K`, the natural map
    from the span of `x` to `K`.-/
abbreviation coord (x : V) (h : x ≠ 0) : (K ∙ x) ≃ₗ[K] K :=
(to_span_nonzero_singleton K V x h).symm

lemma coord_self (x : V) (h : x ≠ 0) :
  (coord K V x h) (⟨x, submodule.mem_span_singleton_self x⟩ : K ∙ x) = 1 :=
by rw [← to_span_nonzero_singleton_one K V x h, linear_equiv.symm_apply_apply]

end field

end linear_equiv
