/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import algebra.algebra.restrict_scalars
import algebra.algebra.subalgebra.basic
import group_theory.finiteness
import ring_theory.ideal.operations

/-!
# Finiteness conditions in commutative algebra

In this file we define a notion of finiteness that is common in commutative algebra.

## Main declarations

- `submodule.fg`, `ideal.fg`
  These express that some object is finitely generated as *submodule* over some base ring.

- `module.finite`, `ring_hom.finite`, `alg_hom.finite`
  all of these express that some object is finitely generated *as module* over some base ring.

## Main results

* `exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` is Nakayama's lemma, in the following form:
  if N is a finitely generated submodule of an ambient R-module M and I is an ideal of R
  such that N ⊆ IN, then there exists r ∈ 1 + I such that rN = 0.

-/

open function (surjective)
open_locale big_operators

namespace submodule
variables {R : Type*} {M : Type*} [semiring R] [add_comm_monoid M] [module R M]

open set

/-- A submodule of `M` is finitely generated if it is the span of a finite subset of `M`. -/
def fg (N : submodule R M) : Prop := ∃ S : finset M, submodule.span R ↑S = N

theorem fg_def {N : submodule R M} :
  N.fg ↔ ∃ S : set M, S.finite ∧ span R S = N :=
⟨λ ⟨t, h⟩, ⟨_, finset.finite_to_set t, h⟩, begin
  rintro ⟨t', h, rfl⟩,
  rcases finite.exists_finset_coe h with ⟨t, rfl⟩,
  exact ⟨t, rfl⟩
end⟩

lemma fg_iff_add_submonoid_fg (P : submodule ℕ M) :
  P.fg ↔ P.to_add_submonoid.fg :=
⟨λ ⟨S, hS⟩, ⟨S, by simpa [← span_nat_eq_add_submonoid_closure] using hS⟩,
  λ ⟨S, hS⟩, ⟨S, by simpa [← span_nat_eq_add_submonoid_closure] using hS⟩⟩

lemma fg_iff_add_subgroup_fg {G : Type*} [add_comm_group G] (P : submodule ℤ G) :
  P.fg ↔ P.to_add_subgroup.fg :=
⟨λ ⟨S, hS⟩, ⟨S, by simpa [← span_int_eq_add_subgroup_closure] using hS⟩,
  λ ⟨S, hS⟩, ⟨S, by simpa [← span_int_eq_add_subgroup_closure] using hS⟩⟩

lemma fg_iff_exists_fin_generating_family {N : submodule R M} :
  N.fg ↔ ∃ (n : ℕ) (s : fin n → M), span R (range s) = N :=
begin
  rw fg_def,
  split,
  { rintros ⟨S, Sfin, hS⟩,
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding,
    exact ⟨n, f, hS⟩, },
  { rintros ⟨n, s, hs⟩,
    refine ⟨range s, finite_range s, hs⟩ },
end

/-- **Nakayama's Lemma**. Atiyah-Macdonald 2.5, Eisenbud 4.7, Matsumura 2.2,
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV) -/
theorem exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type*} [comm_ring R]
  {M : Type*} [add_comm_group M] [module R M]
  (I : ideal R) (N : submodule R M) (hn : N.fg) (hin : N ≤ I • N) :
  ∃ r : R, r - 1 ∈ I ∧ ∀ n ∈ N, r • n = (0 : M) :=
begin
  rw fg_def at hn, rcases hn with ⟨s, hfs, hs⟩,
  have : ∃ r : R, r - 1 ∈ I ∧ N ≤ (I • span R s).comap (linear_map.lsmul R M r) ∧ s ⊆ N,
  { refine ⟨1, _, _, _⟩,
    { rw sub_self, exact I.zero_mem },
    { rw [hs], intros n hn, rw [mem_comap], change (1:R) • n ∈ I • N, rw one_smul, exact hin hn },
    { rw [← span_le, hs], exact le_refl N } },
  clear hin hs, revert this,
  refine set.finite.dinduction_on hfs (λ H, _) (λ i s his hfs ih H, _),
  { rcases H with ⟨r, hr1, hrn, hs⟩, refine ⟨r, hr1, λ n hn, _⟩, specialize hrn hn,
    rwa [mem_comap, span_empty, smul_bot, mem_bot] at hrn },
  apply ih, rcases H with ⟨r, hr1, hrn, hs⟩,
  rw [← set.singleton_union, span_union, smul_sup] at hrn,
  rw [set.insert_subset] at hs,
  have : ∃ c : R, c - 1 ∈ I ∧ c • i ∈ I • span R s,
  { specialize hrn hs.1, rw [mem_comap, mem_sup] at hrn,
    rcases hrn with ⟨y, hy, z, hz, hyz⟩, change y + z = r • i at hyz,
    rw mem_smul_span_singleton at hy, rcases hy with ⟨c, hci, rfl⟩,
    use r-c, split,
    { rw [sub_right_comm], exact I.sub_mem hr1 hci },
    { rw [sub_smul, ← hyz, add_sub_cancel'], exact hz } },
  rcases this with ⟨c, hc1, hci⟩, refine ⟨c * r, _, _, hs.2⟩,
  { simpa only [mul_sub, mul_one, sub_add_sub_cancel] using I.add_mem (I.mul_mem_left c hr1) hc1 },
  { intros n hn, specialize hrn hn, rw [mem_comap, mem_sup] at hrn,
    rcases hrn with ⟨y, hy, z, hz, hyz⟩, change y + z = r • n at hyz,
    rw mem_smul_span_singleton at hy, rcases hy with ⟨d, hdi, rfl⟩,
    change _ • _ ∈ I • span R s,
    rw [mul_smul, ← hyz, smul_add, smul_smul, mul_comm, mul_smul],
    exact add_mem (smul_mem _ _ hci) (smul_mem _ _ hz) }
end

theorem exists_mem_and_smul_eq_self_of_fg_of_le_smul {R : Type*} [comm_ring R]
  {M : Type*} [add_comm_group M] [module R M]
  (I : ideal R) (N : submodule R M) (hn : N.fg) (hin : N ≤ I • N) :
  ∃ r ∈ I, ∀ n ∈ N, r • n = n :=
begin
  obtain ⟨r, hr, hr'⟩ := N.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I hn hin,
  exact ⟨-(r-1), I.neg_mem hr, λ n hn, by simpa [sub_smul] using hr' n hn⟩,
end

theorem fg_bot : (⊥ : submodule R M).fg :=
⟨∅, by rw [finset.coe_empty, span_empty]⟩

lemma _root_.subalgebra.fg_bot_to_submodule {R A : Type*}
  [comm_semiring R] [semiring A] [algebra R A] :
  (⊥ : subalgebra R A).to_submodule.fg :=
⟨{1}, by simp [algebra.to_submodule_bot] ⟩

lemma fg_unit {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  (I : (submodule R A)ˣ) : (I : submodule R A).fg :=
begin
  have : (1 : A) ∈ (I * ↑I⁻¹ : submodule R A),
  { rw I.mul_inv, exact one_le.mp le_rfl },
  obtain ⟨T, T', hT, hT', one_mem⟩ := mem_span_mul_finite_of_mem_mul this,
  refine ⟨T, span_eq_of_le _ hT _⟩,
  rw [← one_mul ↑I, ← mul_one (span R ↑T)],
  conv_rhs { rw [← I.inv_mul, ← mul_assoc] },
  refine mul_le_mul_left (le_trans _ $ mul_le_mul_right $ span_le.mpr hT'),
  rwa [one_le, span_mul_span],
end

lemma fg_of_is_unit {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
  {I : submodule R A} (hI : is_unit I) : I.fg := fg_unit hI.unit

theorem fg_span {s : set M} (hs : s.finite) : fg (span R s) :=
⟨hs.to_finset, by rw [hs.coe_to_finset]⟩

theorem fg_span_singleton (x : M) : fg (R ∙ x) :=
fg_span (finite_singleton x)

theorem fg.sup {N₁ N₂ : submodule R M}
  (hN₁ : N₁.fg) (hN₂ : N₂.fg) : (N₁ ⊔ N₂).fg :=
let ⟨t₁, ht₁⟩ := fg_def.1 hN₁, ⟨t₂, ht₂⟩ := fg_def.1 hN₂ in
fg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [span_union, ht₁.2, ht₂.2]⟩

lemma fg_finset_sup {ι : Type*} (s : finset ι) (N : ι → submodule R M) (h : ∀ i ∈ s, (N i).fg) :
  (s.sup N).fg :=
finset.sup_induction fg_bot (λ a ha b hb, ha.sup hb) h

lemma fg_bsupr {ι : Type*} (s : finset ι) (N : ι → submodule R M) (h : ∀ i ∈ s, (N i).fg) :
  (⨆ i ∈ s, N i).fg :=
by simpa only [finset.sup_eq_supr] using fg_finset_sup s N h

lemma fg_supr {ι : Type*} [finite ι] (N : ι → submodule R M) (h : ∀ i, (N i).fg) :
  (supr N).fg :=
by { casesI nonempty_fintype ι, simpa using fg_bsupr finset.univ N (λ i hi, h i) }

variables {P : Type*} [add_comm_monoid P] [module R P]
variables (f : M →ₗ[R] P)

theorem fg.map {N : submodule R M} (hs : N.fg) : (N.map f).fg :=
let ⟨t, ht⟩ := fg_def.1 hs in fg_def.2 ⟨f '' t, ht.1.image _, by rw [span_image, ht.2]⟩

variables {f}

lemma fg_of_fg_map_injective (f : M →ₗ[R] P) (hf : function.injective f) {N : submodule R M}
  (hfn : (N.map f).fg) : N.fg :=
let ⟨t, ht⟩ := hfn in ⟨t.preimage f $ λ x _ y _ h, hf h,
submodule.map_injective_of_injective hf $ by { rw [f.map_span, finset.coe_preimage,
    set.image_preimage_eq_inter_range, set.inter_eq_self_of_subset_left, ht],
  rw [← linear_map.range_coe, ← span_le, ht, ← map_top], exact map_mono le_top }⟩

lemma fg_of_fg_map {R M P : Type*} [ring R] [add_comm_group M] [module R M]
  [add_comm_group P] [module R P] (f : M →ₗ[R] P) (hf : f.ker = ⊥) {N : submodule R M}
  (hfn : (N.map f).fg) : N.fg :=
fg_of_fg_map_injective f (linear_map.ker_eq_bot.1 hf) hfn

lemma fg_top (N : submodule R M) : (⊤ : submodule R N).fg ↔ N.fg :=
⟨λ h, N.range_subtype ▸ map_top N.subtype ▸ h.map _,
λ h, fg_of_fg_map_injective N.subtype subtype.val_injective $ by rwa [map_top, range_subtype]⟩

lemma fg_of_linear_equiv (e : M ≃ₗ[R] P) (h : (⊤ : submodule R P).fg) :
  (⊤ : submodule R M).fg :=
e.symm.range ▸ map_top (e.symm : P →ₗ[R] M) ▸ h.map _

theorem fg.prod {sb : submodule R M} {sc : submodule R P}
  (hsb : sb.fg) (hsc : sc.fg) : (sb.prod sc).fg :=
let ⟨tb, htb⟩ := fg_def.1 hsb, ⟨tc, htc⟩ := fg_def.1 hsc in
fg_def.2 ⟨linear_map.inl R M P '' tb ∪ linear_map.inr R M P '' tc,
  (htb.1.image _).union (htc.1.image _),
  by rw [linear_map.span_inl_union_inr, htb.2, htc.2]⟩

theorem fg_pi {ι : Type*} {M : ι → Type*} [finite ι] [Π i, add_comm_monoid (M i)]
  [Π i, module R (M i)] {p : Π i, submodule R (M i)} (hsb : ∀ i, (p i).fg) :
  (submodule.pi set.univ p).fg :=
begin
  classical,
  simp_rw fg_def at hsb ⊢,
  choose t htf hts using hsb,
  refine ⟨
    ⋃ i, (linear_map.single i : _ →ₗ[R] _) '' t i, set.finite_Union $ λ i, (htf i).image _, _⟩,
  simp_rw [span_Union, span_image, hts, submodule.supr_map_single],
end

/-- If 0 → M' → M → M'' → 0 is exact and M' and M'' are
finitely generated then so is M. -/
theorem fg_of_fg_map_of_fg_inf_ker {R M P : Type*} [ring R] [add_comm_group M] [module R M]
  [add_comm_group P] [module R P] (f : M →ₗ[R] P)
  {s : submodule R M} (hs1 : (s.map f).fg) (hs2 : (s ⊓ f.ker).fg) : s.fg :=
begin
  haveI := classical.dec_eq R, haveI := classical.dec_eq M, haveI := classical.dec_eq P,
  cases hs1 with t1 ht1, cases hs2 with t2 ht2,
  have : ∀ y ∈ t1, ∃ x ∈ s, f x = y,
  { intros y hy,
    have : y ∈ map f s, { rw ← ht1, exact subset_span hy },
    rcases mem_map.1 this with ⟨x, hx1, hx2⟩,
    exact ⟨x, hx1, hx2⟩ },
  have : ∃ g : P → M, ∀ y ∈ t1, g y ∈ s ∧ f (g y) = y,
  { choose g hg1 hg2,
    existsi λ y, if H : y ∈ t1 then g y H else 0,
    intros y H, split,
    { simp only [dif_pos H], apply hg1 },
    { simp only [dif_pos H], apply hg2 } },
  cases this with g hg, clear this,
  existsi t1.image g ∪ t2,
  rw [finset.coe_union, span_union, finset.coe_image],
  apply le_antisymm,
  { refine sup_le (span_le.2 $ image_subset_iff.2 _) (span_le.2 _),
    { intros y hy, exact (hg y hy).1 },
    { intros x hx, have := subset_span hx,
      rw ht2 at this,
      exact this.1 } },
  intros x hx,
  have : f x ∈ map f s, { rw mem_map, exact ⟨x, hx, rfl⟩ },
  rw [← ht1,← set.image_id ↑t1, finsupp.mem_span_image_iff_total] at this,
  rcases this with ⟨l, hl1, hl2⟩,
  refine mem_sup.2 ⟨(finsupp.total M M R id).to_fun
    ((finsupp.lmap_domain R R g : (P →₀ R) → M →₀ R) l), _,
    x - finsupp.total M M R id ((finsupp.lmap_domain R R g : (P →₀ R) → M →₀ R) l),
    _, add_sub_cancel'_right _ _⟩,
  { rw [← set.image_id (g '' ↑t1), finsupp.mem_span_image_iff_total], refine ⟨_, _, rfl⟩,
    haveI : inhabited P := ⟨0⟩,
    rw [← finsupp.lmap_domain_supported _ _ g, mem_map],
    refine ⟨l, hl1, _⟩,
    refl, },
  rw [ht2, mem_inf], split,
  { apply s.sub_mem hx,
    rw [finsupp.total_apply, finsupp.lmap_domain_apply, finsupp.sum_map_domain_index],
    refine s.sum_mem _,
    { intros y hy, exact s.smul_mem _ (hg y (hl1 hy)).1 },
    { exact zero_smul _ }, { exact λ _ _ _, add_smul _ _ _ } },
  { rw [linear_map.mem_ker, f.map_sub, ← hl2],
    rw [finsupp.total_apply, finsupp.total_apply, finsupp.lmap_domain_apply],
    rw [finsupp.sum_map_domain_index, finsupp.sum, finsupp.sum, f.map_sum],
    rw sub_eq_zero,
    refine finset.sum_congr rfl (λ y hy, _),
    unfold id,
    rw [f.map_smul, (hg y (hl1 hy)).2],
    { exact zero_smul _ }, { exact λ _ _ _, add_smul _ _ _ } }
end

lemma fg_induction (R M : Type*) [semiring R] [add_comm_monoid M] [module R M]
  (P : submodule R M → Prop)
  (h₁ : ∀ x, P (submodule.span R {x})) (h₂ : ∀ M₁ M₂, P M₁ → P M₂ → P (M₁ ⊔ M₂))
  (N : submodule R M) (hN : N.fg) : P N :=
begin
  classical,
  obtain ⟨s, rfl⟩ := hN,
  induction s using finset.induction,
  { rw [finset.coe_empty, submodule.span_empty, ← submodule.span_zero_singleton], apply h₁ },
  { rw [finset.coe_insert, submodule.span_insert], apply h₂; apply_assumption }
end

/-- The kernel of the composition of two linear maps is finitely generated if both kernels are and
the first morphism is surjective. -/
lemma fg_ker_comp {R M N P : Type*} [ring R] [add_comm_group M] [module R M]
  [add_comm_group N] [module R N] [add_comm_group P] [module R P] (f : M →ₗ[R] N)
  (g : N →ₗ[R] P) (hf1 : f.ker.fg) (hf2 : g.ker.fg) (hsur : function.surjective f) :
  (g.comp f).ker.fg :=
begin
  rw linear_map.ker_comp,
  apply fg_of_fg_map_of_fg_inf_ker f,
  { rwa [submodule.map_comap_eq, linear_map.range_eq_top.2 hsur, top_inf_eq] },
  { rwa [inf_of_le_right (show f.ker ≤ (comap f g.ker), from comap_mono bot_le)] }
end

lemma fg_restrict_scalars {R S M : Type*} [comm_semiring R] [semiring S] [algebra R S]
  [add_comm_group M] [module S M] [module R M] [is_scalar_tower R S M] (N : submodule S M)
  (hfin : N.fg) (h : function.surjective (algebra_map R S)) : (submodule.restrict_scalars R N).fg :=
begin
  obtain ⟨X, rfl⟩ := hfin,
  use X,
  exact (submodule.restrict_scalars_span R S h ↑X).symm
end

lemma fg.stablizes_of_supr_eq {M' : submodule R M} (hM' : M'.fg)
  (N : ℕ →o submodule R M) (H : supr N = M') : ∃ n, M' = N n :=
begin
  obtain ⟨S, hS⟩ := hM',
  have : ∀ s : S, ∃ n, (s : M) ∈ N n :=
    λ s, (submodule.mem_supr_of_chain N s).mp
      (by { rw [H, ← hS], exact submodule.subset_span s.2 }),
  choose f hf,
  use S.attach.sup f,
  apply le_antisymm,
  { conv_lhs { rw ← hS },
    rw submodule.span_le,
    intros s hs,
    exact N.2 (finset.le_sup $ S.mem_attach ⟨s, hs⟩) (hf _) },
  { rw ← H, exact le_supr _ _ }
end

/-- Finitely generated submodules are precisely compact elements in the submodule lattice. -/
theorem fg_iff_compact (s : submodule R M) : s.fg ↔ complete_lattice.is_compact_element s :=
begin
  classical,
  -- Introduce shorthand for span of an element
  let sp : M → submodule R M := λ a, span R {a},
  -- Trivial rewrite lemma; a small hack since simp (only) & rw can't accomplish this smoothly.
  have supr_rw : ∀ t : finset M, (⨆ x ∈ t, sp x) = (⨆ x ∈ (↑t : set M), sp x), from λ t, by refl,
  split,
  { rintro ⟨t, rfl⟩,
    rw [span_eq_supr_of_singleton_spans, ←supr_rw, ←(finset.sup_eq_supr t sp)],
    apply complete_lattice.finset_sup_compact_of_compact,
    exact λ n _, singleton_span_is_compact_element n, },
  { intro h,
    -- s is the Sup of the spans of its elements.
    have sSup : s = Sup (sp '' ↑s),
    by rw [Sup_eq_supr, supr_image, ←span_eq_supr_of_singleton_spans, eq_comm, span_eq],
    -- by h, s is then below (and equal to) the sup of the spans of finitely many elements.
    obtain ⟨u, ⟨huspan, husup⟩⟩ := h (sp '' ↑s) (le_of_eq sSup),
    have ssup : s = u.sup id,
    { suffices : u.sup id ≤ s, from le_antisymm husup this,
      rw [sSup, finset.sup_id_eq_Sup], exact Sup_le_Sup huspan, },
    obtain ⟨t, ⟨hts, rfl⟩⟩ := finset.subset_image_iff.mp huspan,
    rw [finset.sup_finset_image, function.comp.left_id, finset.sup_eq_supr, supr_rw,
      ←span_eq_supr_of_singleton_spans, eq_comm] at ssup,
    exact ⟨t, ssup⟩, },
end

end submodule

namespace submodule

section map₂
variables {R M N P : Type*}
variables [comm_semiring R] [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P]
variables [module R M] [module R N] [module R P]

theorem fg.map₂ (f : M →ₗ[R] N →ₗ[R] P) {p : submodule R M} {q : submodule R N}
  (hp : p.fg) (hq : q.fg) : (map₂ f p q).fg :=
let ⟨sm, hfm, hm⟩ := fg_def.1 hp, ⟨sn, hfn, hn⟩ := fg_def.1 hq in
fg_def.2 ⟨set.image2 (λ m n, f m n) sm sn,
  hfm.image2 _ hfn, map₂_span_span R f sm sn ▸ hm ▸ hn ▸ rfl⟩

end map₂

section mul
variables {R : Type*} {A : Type*} [comm_semiring R] [semiring A] [algebra R A]
variables {M N : submodule R A}

theorem fg.mul (hm : M.fg) (hn : N.fg) : (M * N).fg := hm.map₂ _ hn

lemma fg.pow (h : M.fg) (n : ℕ) : (M ^ n).fg :=
nat.rec_on n
  (⟨{1}, by simp [one_eq_span]⟩)
  (λ n ih, by simpa [pow_succ] using h.mul ih)

end mul

end submodule

namespace ideal

variables {R : Type*} {M : Type*} [semiring R] [add_comm_monoid M] [module R M]

/-- An ideal of `R` is finitely generated if it is the span of a finite subset of `R`.

This is defeq to `submodule.fg`, but unfolds more nicely. -/
def fg (I : ideal R) : Prop := ∃ S : finset R, ideal.span ↑S = I

/-- The image of a finitely generated ideal is finitely generated.

This is the `ideal` version of `submodule.fg.map`. -/
lemma fg.map {R S : Type*} [semiring R] [semiring S] {I : ideal R} (h : I.fg)
  (f : R →+* S) : (I.map f).fg :=
begin
  classical,
  obtain ⟨s, hs⟩ := h,
  refine ⟨s.image f, _⟩,
  rw [finset.coe_image, ←ideal.map_span, hs],
end

lemma fg_ker_comp {R S A : Type*} [comm_ring R] [comm_ring S] [comm_ring A]
  (f : R →+* S) (g : S →+* A) (hf : f.ker.fg) (hg : g.ker.fg) (hsur : function.surjective f) :
  (g.comp f).ker.fg :=
begin
  letI : algebra R S := ring_hom.to_algebra f,
  letI : algebra R A := ring_hom.to_algebra (g.comp f),
  letI : algebra S A := ring_hom.to_algebra g,
  letI : is_scalar_tower R S A := is_scalar_tower.of_algebra_map_eq (λ _, rfl),
  let f₁ := algebra.linear_map R S,
  let g₁ := (is_scalar_tower.to_alg_hom R S A).to_linear_map,
  exact submodule.fg_ker_comp f₁ g₁ hf (submodule.fg_restrict_scalars g.ker hg hsur) hsur
end

lemma exists_radical_pow_le_of_fg {R : Type*} [comm_semiring R] (I : ideal R) (h : I.radical.fg) :
  ∃ n : ℕ, I.radical ^ n ≤ I :=
begin
  have := le_refl I.radical, revert this,
  refine submodule.fg_induction _ _ (λ J, J ≤ I.radical → ∃ n : ℕ, J ^ n ≤ I) _ _ _ h,
  { intros x hx, obtain ⟨n, hn⟩ := hx (subset_span (set.mem_singleton x)),
    exact ⟨n, by rwa [← ideal.span, span_singleton_pow, span_le, set.singleton_subset_iff]⟩ },
  { intros J K hJ hK hJK,
    obtain ⟨n, hn⟩ := hJ (λ x hx, hJK $ ideal.mem_sup_left hx),
    obtain ⟨m, hm⟩ := hK (λ x hx, hJK $ ideal.mem_sup_right hx),
    use n + m,
    rw [← ideal.add_eq_sup, add_pow, ideal.sum_eq_sup, finset.sup_le_iff],
    refine λ i hi, ideal.mul_le_right.trans _,
    obtain h | h := le_or_lt n i,
    { exact ideal.mul_le_right.trans ((ideal.pow_le_pow h).trans hn) },
    { refine ideal.mul_le_left.trans ((ideal.pow_le_pow _).trans hm),
      rw [add_comm, nat.add_sub_assoc h.le], apply nat.le_add_right } },
end

end ideal

section module_and_algebra

variables (R A B M N : Type*)

/-- A module over a semiring is `finite` if it is finitely generated as a module. -/
class module.finite [semiring R] [add_comm_monoid M] [module R M] :
  Prop := (out : (⊤ : submodule R M).fg)

namespace module

variables [semiring R] [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]

lemma finite_def {R M} [semiring R] [add_comm_monoid M] [module R M] :
  finite R M ↔ (⊤ : submodule R M).fg := ⟨λ h, h.1, λ h, ⟨h⟩⟩

namespace finite
open _root_.submodule set

lemma iff_add_monoid_fg {M : Type*} [add_comm_monoid M] : module.finite ℕ M ↔ add_monoid.fg M :=
⟨λ h, add_monoid.fg_def.2 $ (fg_iff_add_submonoid_fg ⊤).1 (finite_def.1 h),
  λ h, finite_def.2 $ (fg_iff_add_submonoid_fg ⊤).2 (add_monoid.fg_def.1 h)⟩

lemma iff_add_group_fg {G : Type*} [add_comm_group G] : module.finite ℤ G ↔ add_group.fg G :=
⟨λ h, add_group.fg_def.2 $ (fg_iff_add_subgroup_fg ⊤).1 (finite_def.1 h),
  λ h, finite_def.2 $ (fg_iff_add_subgroup_fg ⊤).2 (add_group.fg_def.1 h)⟩

variables {R M N}

lemma exists_fin [finite R M] : ∃ (n : ℕ) (s : fin n → M), span R (range s) = ⊤ :=
submodule.fg_iff_exists_fin_generating_family.mp out

lemma of_surjective [hM : finite R M] (f : M →ₗ[R] N) (hf : surjective f) :
  finite R N :=
⟨begin
  rw [← linear_map.range_eq_top.2 hf, ← submodule.map_top],
  exact hM.1.map f
end⟩

variables (R)

instance self : finite R R :=
⟨⟨{1}, by simpa only [finset.coe_singleton] using ideal.span_singleton_one⟩⟩

variable (M)

lemma of_restrict_scalars_finite (R A M : Type*) [comm_semiring R] [semiring A] [add_comm_monoid M]
  [module R M] [module A M] [algebra R A] [is_scalar_tower R A M] [hM : finite R M] :
  finite A M :=
begin
  rw [finite_def, fg_def] at hM ⊢,
  obtain ⟨S, hSfin, hSgen⟩ := hM,
  refine ⟨S, hSfin, eq_top_iff.2 _⟩,
  have := submodule.span_le_restrict_scalars R A S,
  rw hSgen at this,
  exact this
end

variables {R M}

instance prod [hM : finite R M] [hN : finite R N] : finite R (M × N) :=
⟨begin
  rw ← submodule.prod_top,
  exact hM.1.prod hN.1
end⟩

instance pi {ι : Type*} {M : ι → Type*} [_root_.finite ι] [Π i, add_comm_monoid (M i)]
  [Π i, module R (M i)] [h : ∀ i, finite R (M i)] : finite R (Π i, M i) :=
⟨begin
  rw ← submodule.pi_top,
  exact submodule.fg_pi (λ i, (h i).1),
end⟩

lemma equiv [hM : finite R M] (e : M ≃ₗ[R] N) : finite R N :=
of_surjective (e : M →ₗ[R] N) e.surjective

section algebra

lemma trans {R : Type*} (A B : Type*) [comm_semiring R] [comm_semiring A] [algebra R A]
  [semiring B] [algebra R B] [algebra A B] [is_scalar_tower R A B] :
  ∀ [finite R A] [finite A B], finite R B
| ⟨⟨s, hs⟩⟩ ⟨⟨t, ht⟩⟩ := ⟨submodule.fg_def.2
  ⟨set.image2 (•) (↑s : set A) (↑t : set B),
    set.finite.image2 _ s.finite_to_set t.finite_to_set,
    by rw [set.image2_smul, submodule.span_smul_of_span_eq_top hs (↑t : set B),
      ht, submodule.restrict_scalars_top]⟩⟩

end algebra

end finite

end module

instance module.finite.base_change [comm_semiring R] [semiring A] [algebra R A]
  [add_comm_monoid M] [module R M] [h : module.finite R M] :
  module.finite A (tensor_product R A M) :=
begin
  classical,
  obtain ⟨s, hs⟩ := h.out,
  refine ⟨⟨s.image (tensor_product.mk R A M 1), eq_top_iff.mpr $ λ x _, _⟩⟩,
  apply tensor_product.induction_on x,
  { exact zero_mem _ },
  { intros x y,
    rw [finset.coe_image, ← submodule.span_span_of_tower R, submodule.span_image, hs,
      submodule.map_top, linear_map.range_coe],
      change _ ∈ submodule.span A (set.range $ tensor_product.mk R A M 1),
    rw [← mul_one x, ← smul_eq_mul, ← tensor_product.smul_tmul'],
    exact submodule.smul_mem _ x (submodule.subset_span $ set.mem_range_self y) },
  { exact λ _ _, submodule.add_mem _ }
end

instance module.finite.tensor_product [comm_semiring R]
  [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]
  [hM : module.finite R M] [hN : module.finite R N] : module.finite R (tensor_product R M N) :=
{ out := (tensor_product.map₂_mk_top_top_eq_top R M N).subst (hM.out.map₂ _ hN.out) }

end module_and_algebra

namespace ring_hom
variables {A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C]

/-- A ring morphism `A →+* B` is `finite` if `B` is finitely generated as `A`-module. -/
def finite (f : A →+* B) : Prop :=
by letI : algebra A B := f.to_algebra; exact module.finite A B

namespace finite

variables (A)

lemma id : finite (ring_hom.id A) := module.finite.self A

variables {A}

lemma of_surjective (f : A →+* B) (hf : surjective f) : f.finite :=
begin
  letI := f.to_algebra,
  exact module.finite.of_surjective (algebra.of_id A B).to_linear_map hf
end

lemma comp {g : B →+* C} {f : A →+* B} (hg : g.finite) (hf : f.finite) : (g.comp f).finite :=
@module.finite.trans A B C _ _ f.to_algebra _ (g.comp f).to_algebra g.to_algebra
begin
  fconstructor,
  intros a b c,
  simp only [algebra.smul_def, ring_hom.map_mul, mul_assoc],
  refl
end
hf hg

lemma of_comp_finite {f : A →+* B} {g : B →+* C} (h : (g.comp f).finite) : g.finite :=
begin
  letI := f.to_algebra,
  letI := g.to_algebra,
  letI := (g.comp f).to_algebra,
  letI : is_scalar_tower A B C := restrict_scalars.is_scalar_tower A B C,
  letI : module.finite A C := h,
  exact module.finite.of_restrict_scalars_finite A B C
end

end finite

end ring_hom

namespace alg_hom

variables {R A B C : Type*} [comm_ring R]
variables [comm_ring A] [comm_ring B] [comm_ring C]
variables [algebra R A] [algebra R B] [algebra R C]

/-- An algebra morphism `A →ₐ[R] B` is finite if it is finite as ring morphism.
In other words, if `B` is finitely generated as `A`-module. -/
def finite (f : A →ₐ[R] B) : Prop := f.to_ring_hom.finite

namespace finite

variables (R A)

lemma id : finite (alg_hom.id R A) := ring_hom.finite.id A

variables {R A}

lemma comp {g : B →ₐ[R] C} {f : A →ₐ[R] B} (hg : g.finite) (hf : f.finite) : (g.comp f).finite :=
ring_hom.finite.comp hg hf

lemma of_surjective (f : A →ₐ[R] B) (hf : surjective f) : f.finite :=
ring_hom.finite.of_surjective f hf

lemma of_comp_finite {f : A →ₐ[R] B} {g : B →ₐ[R] C} (h : (g.comp f).finite) : g.finite :=
ring_hom.finite.of_comp_finite h

end finite

end alg_hom
