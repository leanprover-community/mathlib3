import ring_theory.adjoin
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

theorem fg_of_integral' (x : R) (hx : is_integral S x) :
  (ring.madjoin S {x}).fg :=
begin
  rcases hx with ⟨f, hfm, hfx⟩,
  existsi finset.image ((^) x) (finset.range (nat_degree f + 1)),
  apply le_antisymm,
  { rw span_le, intros s hs, rw [finset.mem_coe, finset.mem_image] at hs,
    rcases hs with ⟨k, hk, rfl⟩, clear hk,
    exact is_submonoid.pow_mem (ring.subset_adjoin (set.mem_singleton _)) },
  intros r hr, change r ∈ ring.closure _ at hr,
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

theorem le_of_le_of_not_lt {α : Type u} [partial_order α] {x y : α}
  (H1 : x ≤ y) (H2 : ¬x < y) : y ≤ x :=
classical.by_contradiction $ λ H3, H2 $ lt_of_le_not_le H1 H3

theorem eq_of_le_of_not_lt {α : Type u} [partial_order α] {x y : α}
  (H1 : x ≤ y) (H2 : ¬x < y) : x = y :=
(lt_or_eq_of_le H1).resolve_left H2

theorem monic_X_pow_add {R : Type u} [comm_semiring R] [decidable_eq R]
  {p : polynomial R} {n : ℕ} (H1 : degree p ≤ n) : monic (X ^ (n+1) + p) :=
decidable.by_cases
  (assume H : (0:R) = 1, @subsingleton.elim _ (subsingleton_of_zero_eq_one _ H) _ _)
  (assume H : (0:R) ≠ 1, begin
    have : degree (X ^ (n+1)) = n+1,
    { rw [← one_mul (X^(n+1)), ← @C_1 R, ← single_eq_C_mul_X],
      change finset.sup (ite _ _ _) _ = _,
      rw if_neg H.symm, refl },
    have : degree (X ^ (n+1) + p) = n+1,
    { rw [← this, add_comm], apply degree_add_eq_of_degree_lt,
      apply lt_of_le_of_lt H1, rw this, apply with_bot.coe_lt_coe.2,
      exact nat.lt_succ_self n },
    rw [monic, leading_coeff, nat_degree, this, coeff_add, coeff_X_pow],
    change ite (n+1=n+1) _ _ + coeff p (n+1) = _,
    rw [if_pos rfl, (degree_le_iff_coeff_zero _ _).1 H1 _
      (with_bot.coe_lt_coe.2 (nat.lt_succ_self _)), add_zero]
  end)

theorem monic_X_pow_sub {p : polynomial R} {n : ℕ}
  (H : degree p ≤ n) : monic (X ^ (n+1) - p) :=
monic_X_pow_add ((degree_neg p).symm ▸ H)

theorem is_integral_of_noetherian' (H : is_noetherian S R) (x : R) :
  is_integral S x :=
begin
  letI : module S (polynomial S) := polynomial.module,
  haveI : is_ring_hom (subtype.val : S → R) := is_ring_hom.is_ring_hom,
  let leval : @linear_map S (polynomial S) R _ _ _ _ _,
  { refine ⟨eval₂ subtype.val x, λ _ _, eval₂_add _ _, λ r p, _⟩,
    rw [← C_mul', eval₂_mul, eval₂_C], refl },
  let D : ℕ → submodule S R := λ n, (degree_le S n).map leval,
  let M := well_founded.min (is_noetherian_iff_well_founded.1 H)
    (set.range D) (set.ne_empty_of_mem ⟨0, rfl⟩),
  have HM : M ∈ set.range D := well_founded.min_mem _ _ _,
  cases HM with N HN,
  have HM : ¬M < D (N+1) := well_founded.not_lt_min
    (is_noetherian_iff_well_founded.1 H) (set.range D) _ ⟨N+1, rfl⟩,
  rw ← HN at HM,
  have HN2 : D (N+1) ≤ D N := le_of_le_of_not_lt (map_mono (degree_le_mono
    (with_bot.coe_le_coe.2 (nat.le_succ N)))) HM,
  have HN3 : leval (X^(N+1)) ∈ D N,
  { exact HN2 (mem_map_of_mem (mem_degree_le.2 (degree_X_pow_le _))) },
  rcases HN3 with ⟨p, hdp, hpe⟩,
  refine ⟨X^(N+1) - p, monic_X_pow_sub (mem_degree_le.1 hdp), _⟩,
  change leval (X ^ (N + 1) - p) = 0,
  rw [linear_map.map_sub, hpe, sub_self]
end

theorem is_integral_of_noetherian (M : submodule S R)
  [HM1 : is_subring (M : set R)] (HM2 : S ⊆ M)
  (H : is_noetherian S M) (x : R) (hx : x ∈ M) :
  is_integral S x :=
begin
  rw is_noetherian_submodule at H,
  letI : module S R := ring.subring.module S,
  haveI : is_subring M.1 := HM1,
  letI : ring (subtype M.1) := subtype.ring,
  let S' : set (subtype M.1) := subtype.val ⁻¹' S,
  have H1 : @is_subring (subtype M.1) _inst_5 S',
  { refine {..},
    { change (0:R) ∈ S, exact is_add_submonoid.zero_mem S },
    { exact λ _ _, @is_add_submonoid.add_mem R _ S _ _ _ },
    { exact λ _, @is_add_subgroup.neg_mem R _ S _ _ },
    { change (1:R) ∈ S, exact is_submonoid.one_mem S },
    { exact λ _ _, @is_submonoid.mul_mem R _ S _ _ _ } },
  resetI,
  have H2 : is_noetherian S' (subtype M.1),
  { intro N',
    let N : submodule S R :=
    { carrier := subtype.val '' N'.1,
      zero := ⟨0, N'.2, rfl⟩,
      add := by rintros _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact ⟨x + y, N'.3 hx hy, rfl⟩,
      smul := by rintros s _ ⟨x, hx, rfl⟩; exact ⟨⟨s.1, HM2 s.2⟩ • x, N'.4 ⟨⟨s.1, HM2 s.2⟩, s.2⟩ hx, rfl⟩ },
    have HN : N ≤ M,
    { rintros _ ⟨x, hx, rfl⟩, exact x.2 },
    rcases fg_def.1 (H N HN) with ⟨s, hf, hs⟩,
    refine fg_def.2 ⟨subtype.val ⁻¹' s, set.finite_preimage subtype.val_injective hf, _⟩,
    apply le_antisymm,
    { rw span_le, rintros ⟨r, hr⟩ hrn, change r ∈ s at hrn,
      have : r ∈ span s := subset_span hrn, rw hs at this,
      rcases this with ⟨⟨r, hr⟩, HR, rfl⟩, exact HR },
    { rintros ⟨r, hr⟩ hrn, have : r ∈ N := ⟨⟨r, hr⟩, hrn, rfl⟩, rw ← hs at this,
      suffices : ∃ hr, (⟨r, hr⟩ : subtype M.carrier) ∈ span (subtype.val ⁻¹' s),
      { cases this with hr1 hr2, exact (mem_coe _).2 hr2 },
      refine span_induction this _ _ _ _,
      { intros z hz, exact ⟨HN (hs ▸ subset_span hz : z ∈ N), subset_span hz⟩ },
      { exact ⟨zero_mem _, zero_mem _⟩ },
      { rintros x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩, refine ⟨M.3 hx1 hy1, _⟩,
        change (⟨x, hx1⟩ + ⟨y, hy1⟩ : M.1) ∈ _, exact add_mem _ hx2 hy2 },
      { rintros ⟨z, hz⟩ x ⟨hx1, hx2⟩, refine ⟨M.4 _ hx1, _⟩,
        letI : module (subtype S') (subtype M.1) := ring.subring.module _,
        change @has_scalar.smul S' M.1 _inst_6.to_has_scalar ⟨⟨z, HM2 hz⟩, hz⟩ ⟨x, hx1⟩ ∈ _,
        exact smul_mem _ _ hx2 } } },
  rcases is_integral_of_noetherian' S' H2 ⟨x, hx⟩ with ⟨p, hpm, hpx⟩,
  refine ⟨base_change (of_subtype _ (of_subtype _ p)) S _, _, _⟩,
  { intros r hr, rcases finsupp.mem_range.1 hr with ⟨_, i, rfl⟩, exact (p.2 i).2 },
  { replace hpm := congr_arg subtype.val hpm,
    replace hpm := congr_arg subtype.val hpm,
    exact subtype.eq hpm },
  unfold eval₂ finsupp.sum base_change of_subtype at hpx ⊢, dsimp only,
  replace hpx := congr_arg subtype.val hpx,
  rw ← finset.sum_hom (subtype.val : M → R) at hpx,
  change (_:R) = (_:R) at hpx,
  refine eq.trans _ hpx,
  refine finset.sum_congr rfl _,
  { intros, conv_rhs { rw is_ring_hom.map_mul (subtype.val : (subtype M.1) → R),
      rw is_semiring_hom.map_pow (subtype.val : (subtype M.1) → R) },
    refl },
  { refl },
  { intros, refl }
end

theorem is_integral_of_mem_closure {x y z : R}
  (hx : is_integral S x) (hy : is_integral S y)
  (hz : z ∈ ring.closure ({x, y} : set R)) :
  is_integral S z :=
begin
  rcases hx with ⟨f, hfm, hfx⟩,
  rcases hy with ⟨g, hgm, hgy⟩,
  let R₀ := ring.closure (↑(f.of_subtype S).range ∪ ↑(g.of_subtype S).range : set R),
  have HR₀ : is_noetherian_ring R₀,
  { exact is_noetherian_ring_closure _ (set.finite_union
      (finset.finite_to_set _) (finset.finite_to_set _)) },
  haveI : is_subring R₀ := by apply_instance,
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
  have := ring.fg_mul (fg_of_integral' R₀ x hx) (fg_of_integral' R₀ y hy),
  rw [← ring.madjoin_union, set.union_singleton, insert] at this,
  have HN := is_noetherian_of_fg_of_noetherian _ HR₀ this,
  exact is_integral_of_noetherian R₀ (ring.madjoin R₀ {x, y}) ring.base_subset_adjoin HN
    z (ring.closure_mono (set.subset_union_right _ _) hz)
end

theorem is_integral_zero : is_integral S 0 :=
is_integral_of_mem S (is_add_submonoid.zero_mem S)

theorem is_integral_one : is_integral S 1 :=
is_integral_of_mem S (is_submonoid.one_mem S)

theorem is_integral_add {x y : R}
  (hx : is_integral S x) (hy : is_integral S y) :
  is_integral S (x + y) :=
is_integral_of_mem_closure S hx hy (is_add_submonoid.add_mem
  (ring.subset_closure (or.inr (or.inl rfl))) (ring.subset_closure (or.inl rfl)))

theorem is_integral_neg {x : R}
  (hx : is_integral S x) : is_integral S (-x) :=
is_integral_of_mem_closure S hx hx (is_add_subgroup.neg_mem
  (ring.subset_closure (or.inl rfl))) 

theorem is_integral_sub {x y : R}
  (hx : is_integral S x) (hy : is_integral S y) : is_integral S (x - y) :=
is_integral_add S hx (is_integral_neg S hy)

theorem is_integral_mul {x y : R}
  (hx : is_integral S x) (hy : is_integral S y) :
  is_integral S (x * y) :=
is_integral_of_mem_closure S hx hy (is_submonoid.mul_mem
  (ring.subset_closure (or.inr (or.inl rfl))) (ring.subset_closure (or.inl rfl)))

def integral_closure : set R :=
{ r | is_integral S r }

instance : is_subring (integral_closure S) :=
{ zero_mem := is_integral_zero S,
  one_mem := is_integral_one S,
  add_mem := λ _ _, is_integral_add S,
  neg_mem := λ _, is_integral_neg S,
  mul_mem := λ _ _, is_integral_mul S, }
