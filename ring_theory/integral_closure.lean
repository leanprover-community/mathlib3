import ring_theory.polynomial

universes u v

namespace finsupp

variables {α : Type u} {β : Type v} [has_zero β] [decidable_eq β]

def range (f : α →₀ β) : finset β :=
finset.image f f.support

theorem mem_range {f : α →₀ β} {y : β} :
  y ∈ f.range ↔ y ≠ 0 ∧ ∃ x, f x = y :=
finset.mem_image.trans
⟨λ ⟨x, hx1, hx2⟩, ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩,
λ ⟨hy, x, hx⟩, ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩

theorem zero_not_mem_range {f : α →₀ β} : (0:β) ∉ f.range :=
λ H, (mem_range.1 H).1 rfl

variables [decidable_eq α]

theorem range_single {x : α} {y : β} : range (single x y) ⊆ {y} :=
λ r hr, let ⟨t, ht1, ht2⟩ := mem_range.1 hr in ht2 ▸
(by rw single_apply at ht2 ⊢; split_ifs at ht2 ⊢; [exact finset.mem_singleton_self _, cc])

end finsupp

namespace polynomial
variables {R : Type u} [comm_ring R] [decidable_eq R]

theorem closure_union_singleton_eq_range (S : set R) [is_subring S] (x : R) :
  ring.closure (S ∪ {x}) = set.range (polynomial.eval₂ (subtype.val : S → R) x) :=
begin
  haveI : is_semiring_hom (subtype.val : S → R) :=
    @@is_ring_hom.is_semiring_hom _ _ _ is_ring_hom.is_ring_hom,
  rw ring.closure_union_eq_range, ext r, split; rintro ⟨p, rfl⟩,
  { refine ⟨mv_polynomial.eval₂ C (λ _, X) p, _⟩,
    refine mv_polynomial.induction_on p _ _ _,
    { intro s, rw [mv_polynomial.eval₂_C, mv_polynomial.eval₂_C, eval₂_C] },
    { intros p q hp hq,
      rw [mv_polynomial.eval₂_add, mv_polynomial.eval₂_add, eval₂_add, hp, hq] },
    { intros p x' hp,
      rw [mv_polynomial.eval₂_mul, mv_polynomial.eval₂_X, mv_polynomial.eval₂_mul, mv_polynomial.eval₂_X],
      rw [eval₂_mul, eval₂_X, hp],
      rcases x' with ⟨_, rfl | H⟩, {refl}, {cases H} } },
  refine ⟨eval₂ mv_polynomial.C (mv_polynomial.X ⟨x, or.inl rfl⟩) p, _⟩,
  refine polynomial.induction_on p _ _ _,
  { intro s, rw [eval₂_C, mv_polynomial.eval₂_C, eval₂_C] },
  { intros p q hp hq,
    rw [eval₂_add, mv_polynomial.eval₂_add, eval₂_add, hp, hq] },
  { intros n x' ih,
    rw [pow_succ', ← mul_assoc, eval₂_mul, mv_polynomial.eval₂_mul, ih],
    conv_rhs {rw eval₂_mul},
    rw [eval₂_X, mv_polynomial.eval₂_X, eval₂_X] }
end

def restriction (p : polynomial R) : polynomial (ring.closure (↑p.range : set R)) :=
⟨p.support, λ i, ⟨p.to_fun i,
  if H : p.to_fun i = 0 then H.symm ▸ is_add_submonoid.zero_mem _
  else ring.subset_closure $ finsupp.mem_range.2 ⟨H, i, rfl⟩⟩,
λ i, finsupp.mem_support_iff.trans (not_iff_not_of_iff ⟨λ H, subtype.eq H, subtype.mk.inj⟩)⟩

theorem coeff_restriction {p : polynomial R} {n : ℕ} : ↑(coeff (restriction p) n) = coeff p n := rfl

theorem coeff_restriction' {p : polynomial R} {n : ℕ} : (coeff (restriction p) n).1 = coeff p n := rfl

theorem degree_restriction {p : polynomial R} : (restriction p).degree = p.degree := rfl

theorem nat_degree_restriction {p : polynomial R} : (restriction p).nat_degree = p.nat_degree := rfl

theorem monic_restriction {p : polynomial R} : monic (restriction p) ↔ monic p :=
⟨λ H, congr_arg subtype.val H, λ H, subtype.eq H⟩

theorem restriction_zero : restriction (0 : polynomial R) = 0 := rfl

theorem restriction_one : restriction (1 : polynomial R) = 1 :=
ext.2 $ λ i, subtype.eq $ by rw [coeff_restriction', coeff_one, coeff_one]; split_ifs; refl

variables {S : Type v} [comm_ring S] {f : R → S} {x : S}

theorem eval₂_restriction {p : polynomial R} :
  eval₂ f x p = eval₂ (f ∘ subtype.val) x p.restriction :=
rfl

section base_change
variables (p : polynomial R) (T : set R) [is_subring T]

def base_change (hp : ↑p.range ⊆ T) : polynomial T :=
⟨p.support, λ i, ⟨p.to_fun i,
  if H : p.to_fun i = 0 then H.symm ▸ is_add_submonoid.zero_mem _
  else hp $ finsupp.mem_range.2 ⟨H, i, rfl⟩⟩,
λ i, finsupp.mem_support_iff.trans (not_iff_not_of_iff ⟨λ H, subtype.eq H, subtype.mk.inj⟩)⟩

variables (hp : ↑p.range ⊆ T)
include hp

theorem coeff_base_change {n : ℕ} : ↑(coeff (base_change p T hp) n) = coeff p n := rfl

theorem coeff_base_change' {n : ℕ} : (coeff (base_change p T hp) n).1 = coeff p n := rfl

theorem degree_base_change : (base_change p T hp).degree = p.degree := rfl

theorem nat_degree_base_change : (base_change p T hp).nat_degree = p.nat_degree := rfl

theorem monic_base_change : monic (base_change p T hp) ↔ monic p :=
⟨λ H, congr_arg subtype.val H, λ H, subtype.eq H⟩

omit hp

theorem base_change_zero : base_change (0 : polynomial R) T (set.empty_subset _) = 0 := rfl

theorem base_change_one : base_change (1 : polynomial R) T
  (set.subset.trans (finset.coe_subset.2 (@finsupp.range_single _ _ _ _ nat.decidable_eq 0 1))
    (set.singleton_subset_iff.2 (is_submonoid.one_mem _))) = 1 :=
ext.2 $ λ i, subtype.eq $ by rw [coeff_base_change', coeff_one, coeff_one]; split_ifs; refl
end base_change

variables (T : set R) [is_subring T]

def of_subtype (p : polynomial T) : polynomial R :=
⟨p.support, subtype.val ∘ p.to_fun,
λ n, finsupp.mem_support_iff.trans (not_iff_not_of_iff
  ⟨λ h, congr_arg subtype.val h, λ h, subtype.eq h⟩)⟩

theorem range_of_subtype {p : polynomial T} :
  ↑(p.of_subtype T).range ⊆ T :=
λ y H, let ⟨hy, x, hx⟩ := finsupp.mem_range.1 H in hx ▸ (p.to_fun x).2

variables {p : polynomial S}

end polynomial

open polynomial submodule

variables {R : Type u} [comm_ring R] [decidable_eq R]
variables (S : set R) [is_subring S]

def is_integral (x : R) : Prop :=
∃ p : polynomial S, monic p ∧ p.eval₂ subtype.val x = 0

theorem is_integral_of_mem {x} (H : x ∈ S) : is_integral S x :=
⟨X - C ⟨x, H⟩, monic_X_sub_C _,
by haveI : is_ring_hom (subtype.val : S → R) := is_ring_hom.is_ring_hom;
rw [is_ring_hom.map_sub (eval₂ (subtype.val : S → R) x), eval₂_X, eval₂_C, sub_self]⟩

theorem is_integral_of_subring {x} (T : set R) [is_subring T]
  (hts : T ⊆ S) (hx : is_integral T x) : is_integral S x :=
let ⟨p, hpm, hpx⟩ := hx in
⟨⟨p.support, λ n, ⟨(p.to_fun n).1, hts (p.to_fun n).2⟩,
  λ n, finsupp.mem_support_iff.trans (not_iff_not_of_iff
    ⟨λ H, have _ := congr_arg subtype.val H, subtype.eq this,
    λ H, have _ := congr_arg subtype.val H, subtype.eq this⟩)⟩,
have _ := congr_arg subtype.val hpm, subtype.eq this, hpx⟩

def subring.module : module S R :=
module.of_core { 
  smul := λ r x , r.1 * x,
  smul_add := λ r, mul_add _,
  add_smul := λ r s, add_mul _ _,
  mul_smul := λ r s, mul_assoc _ _,
  one_smul := one_mul }

local attribute [instance] subring.module

theorem fg_of_integral (x : R) (hx : is_integral S x) :
  ∃ s : set R, set.finite s ∧ ↑(span s) = ring.closure (S ∪ {x}) :=
begin
  rcases hx with ⟨f, hfm, hfx⟩, resetI,
  refine ⟨↑(finset.image ((^) x) (finset.range (nat_degree f + 1))), _, _⟩,
  { exact finset.finite_to_set _ },
  ext r, split; intro hr,
  { refine span_induction hr _ _ _ _,
    { intros s hs, rw [finset.mem_coe, finset.mem_image] at hs,
      rcases hs with ⟨k, hk, rfl⟩, clear hk,
      exact is_submonoid.pow_mem (ring.subset_closure (or.inr (set.mem_singleton _))) },
    { exact is_add_submonoid.zero_mem _ },
    { intros _ _, exact is_add_submonoid.add_mem },
    { intros s t ht, exact is_submonoid.mul_mem
        (ring.subset_closure (or.inl s.2)) ht } },
  rw closure_union_singleton_eq_range at hr, rcases hr with ⟨p, rfl⟩,
  rw ← mod_by_monic_add_div p hfm,
  haveI : is_semiring_hom (subtype.val : S → R) :=
    @@is_ring_hom.is_semiring_hom _ _ _ is_ring_hom.is_ring_hom,
  rw [eval₂_add, eval₂_mul, hfx, zero_mul, add_zero],
  have : degree (p %ₘ f) ≤ degree f := degree_mod_by_monic_le p hfm,
  generalize_hyp : p %ₘ f = q at this ⊢,
  rw [← sum_C_mul_X_eq q, eval₂_sum, finsupp.sum, mem_coe],
  refine sum_mem _ (λ k hkq, _),
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X],
  refine smul_mem _ _ (subset_span _),
  rw [finset.mem_coe, finset.mem_image], refine ⟨_, _, rfl⟩,
  rw [finset.mem_range, nat.lt_succ_iff], refine le_of_not_lt (λ hk, _),
  rw [degree_le_iff_coeff_zero] at this,
  rw [finsupp.mem_support_iff] at hkq, apply hkq, apply this,
  exact lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 hk)
end

theorem ring.closure_union {s t : set R} : ring.closure (S ∪ (s ∪ t)) =
  ↑(span { z : R | ∃ x ∈ ring.closure (S ∪ s), ∃ y ∈ ring.closure (S ∪ t), x * y = z }) :=
begin
  ext r, rw mem_coe, split; intro hr,
  { refine add_group.in_closure.rec_on hr _ _ _ _,
    { intros r hr, apply subset_span,
      refine monoid.in_closure.rec_on hr _ _ _,
      { rintros r (hr | hr | hr),
        { exact ⟨r, ring.subset_closure (or.inl hr), 1, is_submonoid.one_mem _, mul_one _⟩ },
        { exact ⟨r, ring.subset_closure (or.inr hr), 1, is_submonoid.one_mem _, mul_one _⟩ },
        { exact ⟨1, is_submonoid.one_mem _, r, ring.subset_closure (or.inr hr), one_mul _⟩ } },
      { exact ⟨1, is_submonoid.one_mem _, 1, is_submonoid.one_mem _, mul_one _⟩ },
      { rintros _ _ _ _ ⟨x1, hx1, y1, hy1, rfl⟩ ⟨x2, hx2, y2, hy2, rfl⟩,
        rw [mul_assoc, mul_left_comm y1, ← mul_assoc],
        exact ⟨_, is_submonoid.mul_mem hx1 hx2, _, is_submonoid.mul_mem hy1 hy2, rfl⟩ } },
    { exact zero_mem _ },
    { intros _ _ hr, rw ← neg_one_mul, exact smul_mem _ (-1) hr },
    { intros _ _ _ _, exact add_mem _ } },
  refine span_induction hr _ _ _ _,
  { rintro _ ⟨x, hx, y, hy, rfl⟩,
    exact is_submonoid.mul_mem
      (ring.closure_mono (set.union_subset_union_right _ (set.subset_union_left _ _)) hx)
      (ring.closure_mono (set.union_subset_union_right _ (set.subset_union_right _ _)) hy) },
  { exact is_add_submonoid.zero_mem _ },
  { exact λ _ _, is_add_submonoid.add_mem },
  { exact λ s r hr, is_submonoid.mul_mem (ring.subset_closure (or.inl s.2)) hr }
end

theorem is_integral_add {x y : R}
  (hx : is_integral S x) (hy : is_integral S y) :
  is_integral S (x + y) :=
begin
  rcases hx with ⟨f, hfm, hfx⟩,
  rcases hy with ⟨g, hgm, hgy⟩,
  let R₀ := ring.closure (↑(f.of_subtype S).range ∪ ↑(g.of_subtype S).range : set R),
  let f' := (f.of_subtype S).base_change R₀ (set.subset.trans
    (set.subset_union_left _ _) ring.subset_closure),
  let g' := (g.of_subtype S).base_change R₀ (set.subset.trans
    (set.subset_union_right _ _) ring.subset_closure),
  apply is_integral_of_subring S R₀ (ring.closure_subset $
    set.union_subset (range_of_subtype _) (range_of_subtype _)),
  have hx : is_integral R₀ x,
  { replace hfm := congr_arg subtype.val hfm,
    exact ⟨f', subtype.eq hfm, hfx⟩ },
  have hy : is_integral R₀ y,
  { replace hgm := congr_arg subtype.val hgm,
    exact ⟨g', subtype.eq hgm, hgy⟩ },
  rcases fg_of_integral _ _ hx with ⟨sf, hsf1, hsf2⟩,
  rcases fg_of_integral _ _ hy with ⟨sg, hsg1, hsg2⟩,
  have HR₀ : is_noetherian_ring R₀,
  { exact is_noetherian_ring_closure _ (set.finite_union
      (finset.finite_to_set _) (finset.finite_to_set _)) },
  haveI : is_subring R₀ := by apply_instance,
  have : ∃ s : set R, set.finite s ∧ ↑(span s : submodule R₀ R) = ring.closure (R₀ ∪ {x, y}),
  { refine ⟨set.image (λ p : R × R, p.1 * p.2) (sf.prod sg),
      set.finite_image _ (set.finite_prod hsf1 hsg1), _⟩,
    refine eq.trans (submodule.ext'_iff.2 _) (ring.closure_union R₀).symm,
    apply le_antisymm,
    { refine span_le.2 _,
      { rw ← ring.closure_union R₀, rintros _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩,
        have hx' := subset_span hx, rw hsf2 at hx',
        have hy' := subset_span hy, rw hsg2 at hy',
        exact is_submonoid.mul_mem
          (ring.closure_mono (set.union_subset_union_right _ (set.singleton_subset_iff.2 (or.inr (or.inl rfl)))) hx')
          (ring.closure_mono (set.union_subset_union_right _ (set.singleton_subset_iff.2 (or.inl rfl))) hy') } },
    { refine span_le.2 _, rintros _ ⟨p, hp, q, hq, rfl⟩,
      replace hp : p ∈ ring.closure (R₀ ∪ {y}) := ring.closure_mono
        (set.union_subset_union_right _ (λ b, set.mem_singleton_of_eq)) hp,
      rw ← hsg2 at hp, rw ← hsf2 at hq, rw mem_coe at hp hq ⊢,
      refine span_induction hp _ _ _ _,
      { intros r hrg,
        refine span_induction hq _ _ _ _,
        { intros s hsf, rw mul_comm r s,
          exact subset_span ⟨(s, r), ⟨hsf, hrg⟩, rfl⟩ },
        { rw mul_zero, exact submodule.zero_mem _ },
        { intros _ _, rw mul_add, exact submodule.add_mem _ },
        { intros s z hz, change _ * (_ * _) ∈ _, rw mul_left_comm,
          exact submodule.smul_mem _ _ hz } },
      { rw zero_mul, exact submodule.zero_mem _ },
      { intros _ _, rw add_mul, exact submodule.add_mem _ },
      { intros s z hz, change _ * _ * _ ∈ _, rw mul_assoc,
        exact submodule.smul_mem _ _ hz } } },
  sorry
end
