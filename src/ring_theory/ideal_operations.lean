/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

More operations on modules and ideals.
-/
import data.nat.choose
import data.equiv.ring
import ring_theory.algebra_operations

universes u v w x


namespace submodule

variables {R : Type u} {M : Type v}
variables [comm_ring R] [add_comm_group M] [module R M]

instance has_scalar' : has_scalar (ideal R) (submodule R M) :=
⟨λ I N, ⨆ r : I, N.map (r.1 • linear_map.id)⟩

def annihilator (N : submodule R M) : ideal R :=
(linear_map.lsmul R N).ker

def colon (N P : submodule R M) : ideal R :=
annihilator (P.map N.mkq)

variables {I J : ideal R} {N N₁ N₂ P P₁ P₂ : submodule R M}

theorem mem_annihilator {r} : r ∈ N.annihilator ↔ ∀ n ∈ N, r • n = (0:M) :=
⟨λ hr n hn, congr_arg subtype.val (linear_map.ext_iff.1 (linear_map.mem_ker.1 hr) ⟨n, hn⟩),
λ h, linear_map.mem_ker.2 $ linear_map.ext $ λ n, subtype.eq $ h n.1 n.2⟩

theorem mem_annihilator' {r} : r ∈ N.annihilator ↔ N ≤ comap (r • linear_map.id) ⊥ :=
mem_annihilator.trans ⟨λ H n hn, (mem_bot R).2 $ H n hn, λ H n hn, (mem_bot R).1 $ H hn⟩

theorem annihilator_bot : (⊥ : submodule R M).annihilator = ⊤ :=
(ideal.eq_top_iff_one _).2 $ mem_annihilator'.2 bot_le

theorem annihilator_eq_top_iff : N.annihilator = ⊤ ↔ N = ⊥ :=
⟨λ H, eq_bot_iff.2 $ λ (n:M) hn, (mem_bot R).2 $ one_smul R n ▸ mem_annihilator.1 ((ideal.eq_top_iff_one _).1 H) n hn,
λ H, H.symm ▸ annihilator_bot⟩

theorem annihilator_mono (h : N ≤ P) : P.annihilator ≤ N.annihilator :=
λ r hrp, mem_annihilator.2 $ λ n hn, mem_annihilator.1 hrp n $ h hn

theorem annihilator_supr (ι : Sort w) (f : ι → submodule R M) :
  (annihilator ⨆ i, f i) = ⨅ i, annihilator (f i) :=
le_antisymm (le_infi $ λ i, annihilator_mono $ le_supr _ _)
(λ r H, mem_annihilator'.2 $ supr_le $ λ i,
  have _ := (mem_infi _).1 H i, mem_annihilator'.1 this)

theorem mem_colon {r} : r ∈ N.colon P ↔ ∀ p ∈ P, r • p ∈ N :=
mem_annihilator.trans ⟨λ H p hp, (quotient.mk_eq_zero N).1 (H (quotient.mk p) (mem_map_of_mem hp)),
λ H m ⟨p, hp, hpm⟩, hpm ▸ (N.mkq).map_smul r p ▸ (quotient.mk_eq_zero N).2 $ H p hp⟩

theorem mem_colon' {r} : r ∈ N.colon P ↔ P ≤ comap (r • linear_map.id) N :=
mem_colon

theorem colon_mono (hn : N₁ ≤ N₂) (hp : P₁ ≤ P₂) : N₁.colon P₂ ≤ N₂.colon P₁ :=
λ r hrnp, mem_colon.2 $ λ p₁ hp₁, hn $ mem_colon.1 hrnp p₁ $ hp hp₁

theorem infi_colon_supr (ι₁ : Sort w) (f : ι₁ → submodule R M)
  (ι₂ : Sort x) (g : ι₂ → submodule R M) :
  (⨅ i, f i).colon (⨆ j, g j) = ⨅ i j, (f i).colon (g j) :=
le_antisymm (le_infi $ λ i, le_infi $ λ j, colon_mono (infi_le _ _) (le_supr _ _))
(λ r H, mem_colon'.2 $ supr_le $ λ j, map_le_iff_le_comap.1 $ le_infi $ λ i,
  map_le_iff_le_comap.2 $ mem_colon'.1 $ have _ := ((mem_infi _).1 H i),
  have _ := ((mem_infi _).1 this j), this)

theorem smul_mem_smul {r} {n} (hr : r ∈ I) (hn : n ∈ N) : r • n ∈ I • N :=
(le_supr _ ⟨r, hr⟩ : _ ≤ I • N) ⟨n, hn, rfl⟩

theorem smul_le {P : submodule R M} : I • N ≤ P ↔ ∀ (r ∈ I) (n ∈ N), r • n ∈ P :=
⟨λ H r hr n hn, H $ smul_mem_smul hr hn,
λ H, supr_le $ λ r, map_le_iff_le_comap.2 $ λ n hn, H r.1 r.2 n hn⟩

@[elab_as_eliminator]
theorem smul_induction_on {p : M → Prop} {x} (H : x ∈ I • N)
  (Hb : ∀ (r ∈ I) (n ∈ N), p (r • n)) (H0 : p 0)
  (H1 : ∀ x y, p x → p y → p (x + y))
  (H2 : ∀ (c:R) n, p n → p (c • n)) : p x :=
(@smul_le _ _ _ _ _ _ _ ⟨p, H0, H1, H2⟩).2 Hb H

theorem mem_smul_span_singleton {I : ideal R} {m : M} {x : M} :
  x ∈ I • span R ({m} : set M) ↔ ∃ y ∈ I, y • m = x :=
⟨λ hx, smul_induction_on hx
  (λ r hri n hnm, let ⟨s, hs⟩ := mem_span_singleton.1 hnm in ⟨r * s, I.mul_mem_right hri, hs ▸ mul_smul r s m⟩)
  ⟨0, I.zero_mem, by rw [zero_smul]⟩
  (λ m1 m2 ⟨y1, hyi1, hy1⟩ ⟨y2, hyi2, hy2⟩, ⟨y1 + y2, I.add_mem hyi1 hyi2, by rw [add_smul, hy1, hy2]⟩)
  (λ c r ⟨y, hyi, hy⟩, ⟨c * y, I.mul_mem_left hyi, by rw [mul_smul, hy]⟩),
λ ⟨y, hyi, hy⟩, hy ▸ smul_mem_smul hyi (subset_span $ set.mem_singleton m)⟩

theorem smul_le_right : I • N ≤ N :=
smul_le.2 $ λ r hr n, N.smul_mem r

theorem smul_mono (hij : I ≤ J) (hnp : N ≤ P) : I • N ≤ J • P :=
smul_le.2 $ λ r hr n hn, smul_mem_smul (hij hr) (hnp hn)

theorem smul_mono_left (h : I ≤ J) : I • N ≤ J • N :=
smul_mono h (le_refl N)

theorem smul_mono_right (h : N ≤ P) : I • N ≤ I • P :=
smul_mono (le_refl I) h

variables (I J N P)
@[simp] theorem smul_bot : I • (⊥ : submodule R M) = ⊥ :=
eq_bot_iff.2 $ smul_le.2 $ λ r hri s hsb,
(submodule.mem_bot R).2 $ ((submodule.mem_bot R).1 hsb).symm ▸ smul_zero r

@[simp] theorem bot_smul : (⊥ : ideal R) • N = ⊥ :=
eq_bot_iff.2 $ smul_le.2 $ λ r hrb s hsi,
(submodule.mem_bot R).2 $ ((submodule.mem_bot R).1 hrb).symm ▸ zero_smul _ s

@[simp] theorem top_smul : (⊤ : ideal R) • N = N :=
le_antisymm smul_le_right $ λ r hri, one_smul R r ▸ smul_mem_smul mem_top hri

theorem smul_sup : I • (N ⊔ P) = I • N ⊔ I • P :=
le_antisymm (smul_le.2 $ λ r hri m hmnp, let ⟨n, hn, p, hp, hnpm⟩ := mem_sup.1 hmnp in
  mem_sup.2 ⟨_, smul_mem_smul hri hn, _, smul_mem_smul hri hp, hnpm ▸ (smul_add _ _ _).symm⟩)
(sup_le (smul_mono_right le_sup_left)
  (smul_mono_right le_sup_right))

theorem sup_smul : (I ⊔ J) • N = I • N ⊔ J • N :=
le_antisymm (smul_le.2 $ λ r hrij n hn, let ⟨ri, hri, rj, hrj, hrijr⟩ := mem_sup.1 hrij in
  mem_sup.2 ⟨_, smul_mem_smul hri hn, _, smul_mem_smul hrj hn, hrijr ▸ (add_smul _ _ _).symm⟩)
(sup_le (smul_mono_left le_sup_left)
  (smul_mono_left le_sup_right))

theorem smul_assoc : (I • J) • N = I • (J • N) :=
le_antisymm (smul_le.2 $ λ rs hrsij t htn,
  smul_induction_on hrsij
  (λ r hr s hs, (@smul_eq_mul R _ r s).symm ▸ smul_smul r s t ▸ smul_mem_smul hr (smul_mem_smul hs htn))
  ((zero_smul R t).symm ▸ submodule.zero_mem _)
  (λ x y, (add_smul x y t).symm ▸ submodule.add_mem _)
  (λ r s h, (@smul_eq_mul R _ r s).symm ▸ smul_smul r s t ▸ submodule.smul_mem _ _ h))
(smul_le.2 $ λ r hr sn hsn, suffices J • N ≤ submodule.comap (r • linear_map.id) ((I • J) • N), from this hsn,
smul_le.2 $ λ s hs n hn, show r • (s • n) ∈ (I • J) • N, from mul_smul r s n ▸ smul_mem_smul (smul_mem_smul hr hs) hn)

variables (S : set R) (T : set M)

theorem span_smul_span : (ideal.span S) • (span R T) =
  span R (⋃ (s ∈ S) (t ∈ T), {s • t}) :=
le_antisymm (smul_le.2 $ λ r hrS n hnT, span_induction hrS
  (λ r hrS, span_induction hnT
    (λ n hnT, subset_span $ set.mem_bUnion hrS $
      set.mem_bUnion hnT $ set.mem_singleton _)
    ((smul_zero r : r • 0 = (0:M)).symm ▸ submodule.zero_mem _)
    (λ x y, (smul_add r x y).symm ▸ submodule.add_mem _)
    (λ c m, by rw [smul_smul, mul_comm, mul_smul]; exact submodule.smul_mem _ _))
  ((zero_smul R n).symm ▸ submodule.zero_mem _)
  (λ r s, (add_smul r s n).symm ▸ submodule.add_mem _)
  (λ c r, by rw [smul_eq_mul, mul_smul]; exact submodule.smul_mem _ _)) $
span_le.2 $ set.bUnion_subset $ λ r hrS, set.bUnion_subset $ λ n hnT, set.singleton_subset_iff.2 $
smul_mem_smul (subset_span hrS) (subset_span hnT)

end submodule

namespace ideal

section chinese_remainder
variables {R : Type u} [comm_ring R] {ι : Type v}

theorem exists_sub_one_mem_and_mem (s : finset ι) {f : ι → ideal R}
  (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ⊔ f j = ⊤) (i : ι) (his : i ∈ s) :
  ∃ r : R, r - 1 ∈ f i ∧ ∀ j ∈ s, j ≠ i → r ∈ f j :=
begin
  have : ∀ j ∈ s, j ≠ i → ∃ r : R, ∃ H : r - 1 ∈ f i, r ∈ f j,
  { intros j hjs hji, specialize hf i his j hjs hji.symm,
    rw [eq_top_iff_one, submodule.mem_sup] at hf,
    rcases hf with ⟨r, hri, s, hsj, hrs⟩, refine ⟨1 - r, _, _⟩,
    { rw [sub_right_comm, sub_self, zero_sub], exact (f i).neg_mem hri },
    { rw [← hrs, add_sub_cancel'], exact hsj } },
  classical,
  have : ∃ g : ι → R, (∀ j, g j - 1 ∈ f i) ∧ ∀ j ∈ s, j ≠ i → g j ∈ f j,
  { choose g hg1 hg2,
    refine ⟨λ j, if H : j ∈ s ∧ j ≠ i then g j H.1 H.2 else 1, λ j, _, λ j, _⟩,
    { split_ifs with h, { apply hg1 }, rw sub_self, exact (f i).zero_mem },
    { intros hjs hji, rw dif_pos, { apply hg2 }, exact ⟨hjs, hji⟩ } },
  rcases this with ⟨g, hgi, hgj⟩, use (s.erase i).prod g, split,
  { rw [← quotient.eq, quotient.mk_one, quotient.mk_prod],
    apply finset.prod_eq_one, intros, rw [← quotient.mk_one, quotient.eq], apply hgi },
  intros j hjs hji, rw [← quotient.eq_zero_iff_mem, quotient.mk_prod],
  refine finset.prod_eq_zero (finset.mem_erase_of_ne_of_mem hji hjs) _,
  rw quotient.eq_zero_iff_mem, exact hgj j hjs hji
end

theorem exists_sub_mem [fintype ι] {f : ι → ideal R}
  (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) (g : ι → R) :
  ∃ r : R, ∀ i, r - g i ∈ f i :=
begin
  have : ∃ φ : ι → R, (∀ i, φ i - 1 ∈ f i) ∧ (∀ i j, i ≠ j → φ i ∈ f j),
  { have := exists_sub_one_mem_and_mem (finset.univ : finset ι) (λ i _ j _ hij, hf i j hij),
    choose φ hφ,
    existsi λ i, φ i (finset.mem_univ i),
    exact ⟨λ i, (hφ i _).1, λ i j hij, (hφ i _).2 j (finset.mem_univ j) hij.symm⟩ },
  rcases this with ⟨φ, hφ1, hφ2⟩,
  use finset.univ.sum (λ i, g i * φ i),
  intros i,
  rw [← quotient.eq, quotient.mk_sum],
  refine eq.trans (finset.sum_eq_single i _ _) _,
  { intros j _ hji, rw quotient.eq_zero_iff_mem, exact (f i).mul_mem_left (hφ2 j i hji) },
  { intros hi, exact (hi $ finset.mem_univ i).elim },
  specialize hφ1 i, rw [← quotient.eq, quotient.mk_one] at hφ1,
  rw [quotient.mk_mul, hφ1, mul_one]
end

def quotient_inf_to_pi_quotient (f : ι → ideal R) :
  (⨅ i, f i).quotient →+* Π i, (f i).quotient :=
begin
  refine quotient.lift (⨅ i, f i) _ _,
  { convert @@pi.ring_hom (λ i, quotient (f i)) (λ i, ring.to_semiring) ring.to_semiring
      (λ i, quotient.mk_hom (f i)) },
  { intros r hr,
    rw submodule.mem_infi at hr,
    ext i,
    exact quotient.eq_zero_iff_mem.2 (hr i) }
end

theorem bijective_quotient_inf_to_pi_quotient [fintype ι] {f : ι → ideal R}
  (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) :
  function.bijective (quotient_inf_to_pi_quotient f) :=
⟨λ x y, quotient.induction_on₂' x y $ λ r s hrs, quotient.eq.2 $
  (submodule.mem_infi _).2 $ λ i, quotient.eq.1 $
  show quotient_inf_to_pi_quotient f (quotient.mk' r) i = _, by rw hrs; refl,
λ g, let ⟨r, hr⟩ := exists_sub_mem hf (λ i, quotient.out' (g i)) in
⟨quotient.mk _ r, funext $ λ i, quotient.out_eq' (g i) ▸ quotient.eq.2 (hr i)⟩⟩

/-- Chinese Remainder Theorem. Eisenbud Ex.2.6. Similar to Atiyah-Macdonald 1.10 and Stacks 00DT -/
noncomputable def quotient_inf_ring_equiv_pi_quotient [fintype ι] (f : ι → ideal R)
  (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) :
  (⨅ i, f i).quotient ≃+* Π i, (f i).quotient :=
{ .. equiv.of_bijective (bijective_quotient_inf_to_pi_quotient hf),
  .. quotient_inf_to_pi_quotient f }

end chinese_remainder

section mul_and_radical
variables {R : Type u} [comm_ring R]
variables {I J K L: ideal R}

instance : has_mul (ideal R) := ⟨(•)⟩

theorem mul_mem_mul {r s} (hr : r ∈ I) (hs : s ∈ J) : r * s ∈ I * J :=
submodule.smul_mem_smul hr hs

theorem mul_mem_mul_rev {r s} (hr : r ∈ I) (hs : s ∈ J) : s * r ∈ I * J :=
mul_comm r s ▸ mul_mem_mul hr hs

theorem mul_le : I * J ≤ K ↔ ∀ (r ∈ I) (s ∈ J), r * s ∈ K :=
submodule.smul_le

lemma mul_le_left : I * J ≤ J :=
ideal.mul_le.2 (λ r hr s, ideal.mul_mem_left _)

lemma mul_le_right : I * J ≤ I :=
ideal.mul_le.2 (λ r hr s hs, ideal.mul_mem_right _ hr)

@[simp] lemma sup_mul_right_self : I ⊔ (I * J) = I :=
sup_eq_left.2 ideal.mul_le_right

@[simp] lemma sup_mul_left_self : I ⊔ (J * I) = I :=
sup_eq_left.2 ideal.mul_le_left

@[simp] lemma mul_right_self_sup : (I * J) ⊔ I = I :=
sup_eq_right.2 ideal.mul_le_right

@[simp] lemma mul_left_self_sup : (J * I) ⊔ I = I :=
sup_eq_right.2 ideal.mul_le_left

variables (I J K)
protected theorem mul_comm : I * J = J * I :=
le_antisymm (mul_le.2 $ λ r hrI s hsJ, mul_mem_mul_rev hsJ hrI)
(mul_le.2 $ λ r hrJ s hsI, mul_mem_mul_rev hsI hrJ)

protected theorem mul_assoc : (I * J) * K = I * (J * K) :=
submodule.smul_assoc I J K

theorem span_mul_span (S T : set R) : span S * span T =
  span ⋃ (s ∈ S) (t ∈ T), {s * t} :=
submodule.span_smul_span S T
variables {I J K}

theorem mul_le_inf : I * J ≤ I ⊓ J :=
mul_le.2 $ λ r hri s hsj, ⟨I.mul_mem_right hri, J.mul_mem_left hsj⟩

theorem mul_eq_inf_of_coprime (h : I ⊔ J = ⊤) : I * J = I ⊓ J :=
le_antisymm mul_le_inf $ λ r ⟨hri, hrj⟩,
let ⟨s, hsi, t, htj, hst⟩ := submodule.mem_sup.1 ((eq_top_iff_one _).1 h) in
mul_one r ▸ hst ▸ (mul_add r s t).symm ▸ ideal.add_mem (I * J) (mul_mem_mul_rev hsi hrj) (mul_mem_mul hri htj)

variables (I)
theorem mul_bot : I * ⊥ = ⊥ :=
submodule.smul_bot I

theorem bot_mul : ⊥ * I = ⊥ :=
submodule.bot_smul I

theorem mul_top : I * ⊤ = I :=
ideal.mul_comm ⊤ I ▸ submodule.top_smul I

theorem top_mul : ⊤ * I = I :=
submodule.top_smul I
variables {I}

theorem mul_mono (hik : I ≤ K) (hjl : J ≤ L) : I * J ≤ K * L :=
submodule.smul_mono hik hjl

theorem mul_mono_left (h : I ≤ J) : I * K ≤ J * K :=
submodule.smul_mono_left h

theorem mul_mono_right (h : J ≤ K) : I * J ≤ I * K :=
submodule.smul_mono_right h

variables (I J K)
theorem mul_sup : I * (J ⊔ K) = I * J ⊔ I * K :=
submodule.smul_sup I J K

theorem sup_mul : (I ⊔ J) * K = I * K ⊔ J * K :=
submodule.sup_smul I J K
variables {I J K}

lemma pow_le_pow {m n : ℕ} (h : m ≤ n) :
  I^n ≤ I^m :=
begin
  cases nat.exists_eq_add_of_le h with k hk,
  rw [hk, pow_add],
  exact le_trans (mul_le_inf) (inf_le_left)
end

/-- The radical of an ideal `I` consists of the elements `r` such that `r^n ∈ I` for some `n`. -/
def radical (I : ideal R) : ideal R :=
{ carrier := { r | ∃ n : ℕ, r ^ n ∈ I },
  zero := ⟨1, (pow_one (0:R)).symm ▸ I.zero_mem⟩,
  add := λ x y ⟨m, hxmi⟩ ⟨n, hyni⟩, ⟨m + n,
    (add_pow x y (m + n)).symm ▸ I.sum_mem $
    show ∀ c ∈ finset.range (nat.succ (m + n)), x ^ c * y ^ (m + n - c) * (nat.choose (m + n) c) ∈ I,
    from λ c hc, or.cases_on (le_total c m)
      (λ hcm, I.mul_mem_right $ I.mul_mem_left $ nat.add_comm n m ▸ (nat.add_sub_assoc hcm n).symm ▸
        (pow_add y n (m-c)).symm ▸ I.mul_mem_right hyni)
      (λ hmc, I.mul_mem_right $ I.mul_mem_right $ nat.add_sub_cancel' hmc ▸
        (pow_add x m (c-m)).symm ▸ I.mul_mem_right hxmi)⟩,
  smul := λ r s ⟨n, hsni⟩, ⟨n, show (r * s)^n ∈ I,
    from (mul_pow r s n).symm ▸ I.mul_mem_left hsni⟩ }

theorem le_radical : I ≤ radical I :=
λ r hri, ⟨1, (pow_one r).symm ▸ hri⟩

variables (R)
theorem radical_top : (radical ⊤ : ideal R) = ⊤ :=
(eq_top_iff_one _).2 ⟨0, submodule.mem_top⟩
variables {R}

theorem radical_mono (H : I ≤ J) : radical I ≤ radical J :=
λ r ⟨n, hrni⟩, ⟨n, H hrni⟩

variables (I)
theorem radical_idem : radical (radical I) = radical I :=
le_antisymm (λ r ⟨n, k, hrnki⟩, ⟨n * k, (pow_mul r n k).symm ▸ hrnki⟩) le_radical
variables {I}

theorem radical_eq_top : radical I = ⊤ ↔ I = ⊤ :=
⟨λ h, (eq_top_iff_one _).2 $ let ⟨n, hn⟩ := (eq_top_iff_one _).1 h in
  @one_pow R _ n ▸ hn, λ h, h.symm ▸ radical_top R⟩

theorem is_prime.radical (H : is_prime I) : radical I = I :=
le_antisymm (λ r ⟨n, hrni⟩, H.mem_of_pow_mem n hrni) le_radical

variables (I J)
theorem radical_sup : radical (I ⊔ J) = radical (radical I ⊔ radical J) :=
le_antisymm (radical_mono $ sup_le_sup le_radical le_radical) $
λ r ⟨n, hrnij⟩, let ⟨s, hs, t, ht, hst⟩ := submodule.mem_sup.1 hrnij in
@radical_idem _ _ (I ⊔ J) ▸ ⟨n, hst ▸ ideal.add_mem _
  (radical_mono le_sup_left hs) (radical_mono le_sup_right ht)⟩

theorem radical_inf : radical (I ⊓ J) = radical I ⊓ radical J :=
le_antisymm (le_inf (radical_mono inf_le_left) (radical_mono inf_le_right))
(λ r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩, ⟨m + n, (pow_add r m n).symm ▸ I.mul_mem_right hrm,
(pow_add r m n).symm ▸ J.mul_mem_left hrn⟩)

theorem radical_mul : radical (I * J) = radical I ⊓ radical J :=
le_antisymm (radical_inf I J ▸ radical_mono $ @mul_le_inf _ _ I J)
(λ r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩, ⟨m + n, (pow_add r m n).symm ▸ mul_mem_mul hrm hrn⟩)
variables {I J}

theorem is_prime.radical_le_iff (hj : is_prime J) :
  radical I ≤ J ↔ I ≤ J :=
⟨le_trans le_radical, λ hij r ⟨n, hrni⟩, hj.mem_of_pow_mem n $ hij hrni⟩

theorem radical_eq_Inf (I : ideal R) :
  radical I = Inf { J : ideal R | I ≤ J ∧ is_prime J } :=
le_antisymm (le_Inf $ λ J hJ, hJ.2.radical_le_iff.2 hJ.1) $
λ r hr, classical.by_contradiction $ λ hri,
let ⟨m, (hrm : r ∉ radical m), him, hm⟩ := zorn.zorn_partial_order₀ {K : ideal R | r ∉ radical K}
  (λ c hc hcc y hyc, ⟨Sup c, λ ⟨n, hrnc⟩, let ⟨y, hyc, hrny⟩ :=
      (submodule.mem_Sup_of_directed ⟨y, hyc⟩ hcc.directed_on).1 hrnc in hc hyc ⟨n, hrny⟩,
    λ z, le_Sup⟩) I hri in
have ∀ x ∉ m, r ∈ radical (m ⊔ span {x}) := λ x hxm, classical.by_contradiction $ λ hrmx, hxm $
  hm (m ⊔ span {x}) hrmx le_sup_left ▸ (le_sup_right : _ ≤ m ⊔ span {x}) (subset_span $ set.mem_singleton _),
have is_prime m, from ⟨by rintro rfl; rw radical_top at hrm; exact hrm trivial,
  λ x y hxym, classical.or_iff_not_imp_left.2 $ λ hxm, classical.by_contradiction $ λ hym,
  let ⟨n, hrn⟩ := this _ hxm, ⟨p, hpm, q, hq, hpqrn⟩ := submodule.mem_sup.1 hrn, ⟨c, hcxq⟩ := mem_span_singleton'.1 hq in
  let ⟨k, hrk⟩ := this _ hym, ⟨f, hfm, g, hg, hfgrk⟩ := submodule.mem_sup.1 hrk, ⟨d, hdyg⟩ := mem_span_singleton'.1 hg in
  hrm ⟨n + k, by rw [pow_add, ← hpqrn, ← hcxq, ← hfgrk, ← hdyg, add_mul, mul_add (c*x), mul_assoc c x (d*y), mul_left_comm x, ← mul_assoc];
    refine m.add_mem (m.mul_mem_right hpm) (m.add_mem (m.mul_mem_left hfm) (m.mul_mem_left hxym))⟩⟩,
hrm $ this.radical.symm ▸ (Inf_le ⟨him, this⟩ : Inf {J : ideal R | I ≤ J ∧ is_prime J} ≤ m) hr

instance : comm_semiring (ideal R) := submodule.comm_semiring

@[simp] lemma add_eq_sup : I + J = I ⊔ J := rfl
@[simp] lemma zero_eq_bot : (0 : ideal R) = ⊥ := rfl
@[simp] lemma one_eq_top : (1 : ideal R) = ⊤ :=
by erw [submodule.one_eq_map_top, submodule.map_id]

variables (I)
theorem radical_pow (n : ℕ) (H : n > 0) : radical (I^n) = radical I :=
nat.rec_on n (not.elim dec_trivial) (λ n ih H,
or.cases_on (lt_or_eq_of_le $ nat.le_of_lt_succ H)
  (λ H, calc radical (I^(n+1))
           = radical I ⊓ radical (I^n) : radical_mul _ _
       ... = radical I ⊓ radical I : by rw ih H
       ... = radical I : inf_idem)
  (λ H, H ▸ (pow_one I).symm ▸ rfl)) H

end mul_and_radical

section map_and_comap
variables {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
variables (f : R →+* S)
variables {I J : ideal R} {K L : ideal S}

def map (I : ideal R) : ideal S :=
span (f '' I)

/-- `I.comap f` is the preimage of `I` under `f`. -/
def comap (I : ideal S) : ideal R :=
{ carrier := f ⁻¹' I,
  zero := by simp only [set.mem_preimage, f.map_zero, I.mem_coe, I.zero_mem],
  add := λ x y hx hy, show f (x + y) ∈ I, by { rw f.map_add, exact I.add_mem hx hy },
  smul := λ c x hx, show f (c * x) ∈ I, by { rw f.map_mul, exact I.mul_mem_left hx } }

variables {f}
theorem map_mono (h : I ≤ J) : map f I ≤ map f J :=
span_mono $ set.image_subset _ h

theorem mem_map_of_mem {x} (h : x ∈ I) : f x ∈ map f I :=
subset_span ⟨x, h, rfl⟩

theorem map_le_iff_le_comap :
  map f I ≤ K ↔ I ≤ comap f K :=
span_le.trans set.image_subset_iff

@[simp] theorem mem_comap {x} : x ∈ comap f K ↔ f x ∈ K := iff.rfl

theorem comap_mono (h : K ≤ L) : comap f K ≤ comap f L :=
set.preimage_mono (λ x hx, h hx)
variables (f)

theorem comap_ne_top (hK : K ≠ ⊤) : comap f K ≠ ⊤ :=
(ne_top_iff_one _).2 $ by rw [mem_comap, f.map_one];
  exact (ne_top_iff_one _).1 hK

theorem is_prime.comap [hK : K.is_prime] : (comap f K).is_prime :=
⟨comap_ne_top _ hK.1, λ x y,
  by simp only [mem_comap, f.map_mul]; apply hK.2⟩

variables (I J K L)

theorem map_top : map f ⊤ = ⊤ :=
(eq_top_iff_one _).2 $ subset_span ⟨1, trivial, f.map_one⟩

theorem map_mul : map f (I * J) = map f I * map f J :=
le_antisymm (map_le_iff_le_comap.2 $ mul_le.2 $ λ r hri s hsj,
  show f (r * s) ∈ _, by rw f.map_mul;
  exact mul_mem_mul (mem_map_of_mem hri) (mem_map_of_mem hsj))
(trans_rel_right _ (span_mul_span _ _) $ span_le.2 $
  set.bUnion_subset $ λ i ⟨r, hri, hfri⟩,
  set.bUnion_subset $ λ j ⟨s, hsj, hfsj⟩,
  set.singleton_subset_iff.2 $ hfri ▸ hfsj ▸
  by rw [← f.map_mul];
  exact mem_map_of_mem (mul_mem_mul hri hsj))

variable (f)
lemma gc_map_comap : galois_connection (ideal.map f) (ideal.comap f) :=
λ I J, ideal.map_le_iff_le_comap

@[simp] lemma comap_id : I.comap (ring_hom.id R) = I :=
ideal.ext $ λ _, iff.rfl

@[simp] lemma map_id : I.map (ring_hom.id R) = I :=
(gc_map_comap (ring_hom.id R)).l_unique galois_connection.id comap_id

lemma comap_comap {T : Type*} [comm_ring T] {I : ideal T} (f : R →+* S)
  (g : S →+*T) : (I.comap g).comap f = I.comap (g.comp f) := rfl

lemma map_map {T : Type*} [comm_ring T] {I : ideal R} (f : R →+* S)
  (g : S →+*T) : (I.map f).map g = I.map (g.comp f) :=
((gc_map_comap f).compose _ _ _ _ (gc_map_comap g)).l_unique
  (gc_map_comap (g.comp f)) (λ _, comap_comap _ _)

variables {f I J K L}

lemma map_le_of_le_comap : I ≤ K.comap f → I.map f ≤ K :=
(gc_map_comap f).l_le

lemma le_comap_of_map_le : I.map f ≤ K → I ≤ K.comap f :=
(gc_map_comap f).le_u

lemma le_comap_map : I ≤ (I.map f).comap f :=
(gc_map_comap f).le_u_l _

lemma map_comap_le : (K.comap f).map f ≤ K :=
(gc_map_comap f).l_u_le _

@[simp] lemma comap_top : (⊤ : ideal S).comap f = ⊤ :=
(gc_map_comap f).u_top

@[simp] lemma map_bot : (⊥ : ideal R).map f = ⊥ :=
(gc_map_comap f).l_bot

variables (f I J K L)

@[simp] lemma map_comap_map : ((I.map f).comap f).map f = I.map f :=
congr_fun (gc_map_comap f).l_u_l_eq_l I

@[simp] lemma comap_map_comap : ((K.comap f).map f).comap f = K.comap f :=
congr_fun (gc_map_comap f).u_l_u_eq_u K

lemma map_sup : (I ⊔ J).map f = I.map f ⊔ J.map f :=
(gc_map_comap f).l_sup

theorem comap_inf : comap f (K ⊓ L) = comap f K ⊓ comap f L := rfl

variables {ι : Sort*}

lemma map_supr (K : ι → ideal R) : (supr K).map f = ⨆ i, (K i).map f :=
(gc_map_comap f).l_supr

lemma comap_infi (K : ι → ideal S) : (infi K).comap f = ⨅ i, (K i).comap f :=
(gc_map_comap f).u_infi

lemma map_Sup (s : set (ideal R)): (Sup s).map f = ⨆ I ∈ s, (I : ideal R).map f :=
(gc_map_comap f).l_Sup

lemma comap_Inf (s : set (ideal S)): (Inf s).comap f = ⨅ I ∈ s, (I : ideal S).comap f :=
(gc_map_comap f).u_Inf

theorem comap_radical : comap f (radical K) = radical (comap f K) :=
le_antisymm (λ r ⟨n, hfrnk⟩, ⟨n, show f (r ^ n) ∈ K,
  from (f.map_pow r n).symm ▸ hfrnk⟩)
(λ r ⟨n, hfrnk⟩, ⟨n, f.map_pow r n ▸ hfrnk⟩)

@[simp] lemma map_quotient_self :
  map (quotient.mk_hom I) I = ⊥ :=
eq_bot_iff.2 $ ideal.map_le_iff_le_comap.2 $ λ x hx,
(submodule.mem_bot I.quotient).2 $ ideal.quotient.eq_zero_iff_mem.2 hx

variables {I J K L}

theorem map_inf_le : map f (I ⊓ J) ≤ map f I ⊓ map f J :=
(gc_map_comap f).monotone_l.map_inf_le _ _

theorem map_radical_le : map f (radical I) ≤ radical (map f I) :=
map_le_iff_le_comap.2 $ λ r ⟨n, hrni⟩, ⟨n, f.map_pow r n ▸ mem_map_of_mem hrni⟩

theorem le_comap_sup : comap f K ⊔ comap f L ≤ comap f (K ⊔ L) :=
(gc_map_comap f).monotone_u.le_map_sup _ _

theorem le_comap_mul : comap f K * comap f L ≤ comap f (K * L) :=
map_le_iff_le_comap.1 $ (map_mul f (comap f K) (comap f L)).symm ▸
mul_mono (map_le_iff_le_comap.2 $ le_refl _) (map_le_iff_le_comap.2 $ le_refl _)

section surjective
variables (hf : function.surjective f)
include hf

open function

theorem map_comap_of_surjective (I : ideal S) :
  map f (comap f I) = I :=
le_antisymm (map_le_iff_le_comap.2 (le_refl _))
(λ s hsi, let ⟨r, hfrs⟩ := hf s in
  hfrs ▸ (mem_map_of_mem $ show f r ∈ I, from hfrs.symm ▸ hsi))

/-- `map` and `comap` are adjoint, and the composition `map f ∘ comap f` is the
  identity -/
def gi_map_comap : galois_insertion (map f) (comap f) :=
galois_insertion.monotone_intro
  ((gc_map_comap f).monotone_u)
  ((gc_map_comap f).monotone_l)
  (λ _, le_comap_map)
  (map_comap_of_surjective _ hf)

lemma map_surjective_of_surjective : surjective (map f) :=
(gi_map_comap f hf).l_surjective

lemma comap_injective_of_surjective : injective (comap f) :=
(gi_map_comap f hf).u_injective

lemma map_sup_comap_of_surjective (I J : ideal S) : (I.comap f ⊔ J.comap f).map f = I ⊔ J :=
(gi_map_comap f hf).l_sup_u _ _

lemma map_supr_comap_of_surjective (K : ι → ideal S) : (⨆i, (K i).comap f).map f = supr K :=
(gi_map_comap f hf).l_supr_u _

lemma map_inf_comap_of_surjective (I J : ideal S) : (I.comap f ⊓ J.comap f).map f = I ⊓ J :=
(gi_map_comap f hf).l_inf_u _ _

lemma map_infi_comap_of_surjective (K : ι → ideal S) : (⨅i, (K i).comap f).map f = infi K :=
(gi_map_comap f hf).l_infi_u _

theorem mem_image_of_mem_map_of_surjective {I : ideal R} {y}
  (H : y ∈ map f I) : y ∈ f '' I :=
submodule.span_induction H (λ _, id) ⟨0, I.zero_mem, f.map_zero⟩
(λ y1 y2 ⟨x1, hx1i, hxy1⟩ ⟨x2, hx2i, hxy2⟩, ⟨x1 + x2, I.add_mem hx1i hx2i, hxy1 ▸ hxy2 ▸ f.map_add _ _⟩)
(λ c y ⟨x, hxi, hxy⟩, let ⟨d, hdc⟩ := hf c in ⟨d • x, I.smul_mem _ hxi, hdc ▸ hxy ▸ f.map_mul _ _⟩)

theorem comap_map_of_surjective (I : ideal R) :
  comap f (map f I) = I ⊔ comap f ⊥ :=
le_antisymm (assume r h, let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h in
  submodule.mem_sup.2 ⟨s, hsi, r - s, (submodule.mem_bot S).2 $ by rw [f.map_sub, hfsr, sub_self],
  add_sub_cancel'_right s r⟩)
(sup_le (map_le_iff_le_comap.1 (le_refl _)) (comap_mono bot_le))

/-- Correspondence theorem -/
def order_iso_of_surjective :
  ((≤) : ideal S → ideal S → Prop) ≃o
  ((≤) : { p : ideal R // comap f ⊥ ≤ p } → { p : ideal R // comap f ⊥ ≤ p } → Prop) :=
{ to_fun := λ J, ⟨comap f J, comap_mono bot_le⟩,
  inv_fun := λ I, map f I.1,
  left_inv := λ J, map_comap_of_surjective f hf J,
  right_inv := λ I, subtype.eq $ show comap f (map f I.1) = I.1,
    from (comap_map_of_surjective f hf I).symm ▸ le_antisymm
      (sup_le (le_refl _) I.2) le_sup_left,
  ord' := λ I1 I2, ⟨comap_mono, λ H, map_comap_of_surjective f hf I1 ▸
    map_comap_of_surjective f hf I2 ▸ map_mono H⟩ }

def le_order_embedding_of_surjective :
  ((≤) : ideal S → ideal S → Prop) ≼o ((≤) : ideal R → ideal R → Prop) :=
(order_iso_of_surjective f hf).to_order_embedding.trans (subtype.order_embedding _ _)

def lt_order_embedding_of_surjective :
  ((<) : ideal S → ideal S → Prop) ≼o ((<) : ideal R → ideal R → Prop) :=
(le_order_embedding_of_surjective f hf).lt_embedding_of_le_embedding

end surjective

end map_and_comap

section jacobson
variables {R : Type u} [comm_ring R]

/-- The Jacobson radical of `I` is the infimum of all maximal ideals containing `I`. -/
def jacobson (I : ideal R) : ideal R :=
Inf {J : ideal R | I ≤ J ∧ is_maximal J}

theorem jacobson_eq_top_iff {I : ideal R} : jacobson I = ⊤ ↔ I = ⊤ :=
⟨λ H, classical.by_contradiction $ λ hi, let ⟨M, hm, him⟩ := exists_le_maximal I hi in
  lt_top_iff_ne_top.1 (lt_of_le_of_lt (show jacobson I ≤ M, from Inf_le ⟨him, hm⟩) $ lt_top_iff_ne_top.2 hm.1) H,
λ H, eq_top_iff.2 $ le_Inf $ λ J ⟨hij, hj⟩, H ▸ hij⟩

theorem mem_jacobson_iff {I : ideal R} {x : R} :
  x ∈ jacobson I ↔ ∀ y, ∃ z, x * y * z + z - 1 ∈ I :=
⟨λ hx y, classical.by_cases
  (assume hxy : I ⊔ span {x * y + 1} = ⊤,
    let ⟨p, hpi, q, hq, hpq⟩ := submodule.mem_sup.1 ((eq_top_iff_one _).1 hxy) in
    let ⟨r, hr⟩ := mem_span_singleton.1 hq in
    ⟨r, by rw [← one_mul r, ← mul_assoc, ← add_mul, mul_one, ← hr, ← hpq, ← neg_sub, add_sub_cancel]; exact I.neg_mem hpi⟩)
  (assume hxy : I ⊔ span {x * y + 1} ≠ ⊤,
    let ⟨M, hm1, hm2⟩ := exists_le_maximal _ hxy in
    suffices x ∉ M, from (this $ mem_Inf.1 hx ⟨le_trans le_sup_left hm2, hm1⟩).elim,
    λ hxm, hm1.1 $ (eq_top_iff_one _).2 $ add_sub_cancel' (x * y) 1 ▸ M.sub_mem
      (le_trans le_sup_right hm2 $ mem_span_singleton.2 $ dvd_refl _)
      (M.mul_mem_right hxm)),
λ hx, mem_Inf.2 $ λ M ⟨him, hm⟩, classical.by_contradiction $ λ hxm,
  let ⟨y, hy⟩ := hm.exists_inv hxm, ⟨z, hz⟩ := hx (-y) in
  hm.1 $ (eq_top_iff_one _).2 $ sub_sub_cancel (x * -y * z + z) 1 ▸ M.sub_mem
    (by rw [← one_mul z, ← mul_assoc, ← add_mul, mul_one, mul_neg_eq_neg_mul_symm, neg_add_eq_sub, ← neg_sub,
        neg_mul_eq_neg_mul_symm, neg_mul_eq_mul_neg, mul_comm x y]; exact M.mul_mem_right hy)
    (him hz)⟩

end jacobson

section is_local
variables {R : Type u} [comm_ring R]

/-- An ideal `I` is local iff its Jacobson radical is maximal. -/
@[class] def is_local (I : ideal R) : Prop :=
is_maximal (jacobson I)

theorem is_local_of_is_maximal_radical {I : ideal R} (hi : is_maximal (radical I)) : is_local I :=
have radical I = jacobson I,
from le_antisymm (le_Inf $ λ M ⟨him, hm⟩, hm.is_prime.radical_le_iff.2 him)
  (Inf_le ⟨le_radical, hi⟩),
show is_maximal (jacobson I), from this ▸ hi

theorem is_local.le_jacobson {I J : ideal R} (hi : is_local I) (hij : I ≤ J) (hj : J ≠ ⊤) : J ≤ jacobson I :=
let ⟨M, hm, hjm⟩ := exists_le_maximal J hj in
le_trans hjm $ le_of_eq $ eq.symm $ hi.eq_of_le hm.1 $ Inf_le ⟨le_trans hij hjm, hm⟩

theorem is_local.mem_jacobson_or_exists_inv {I : ideal R} (hi : is_local I) (x : R) :
  x ∈ jacobson I ∨ ∃ y, y * x - 1 ∈ I :=
classical.by_cases
  (assume h : I ⊔ span {x} = ⊤,
    let ⟨p, hpi, q, hq, hpq⟩ := submodule.mem_sup.1 ((eq_top_iff_one _).1 h) in
    let ⟨r, hr⟩ := mem_span_singleton.1 hq in
    or.inr ⟨r, by rw [← hpq, mul_comm, ← hr, ← neg_sub, add_sub_cancel]; exact I.neg_mem hpi⟩)
  (assume h : I ⊔ span {x} ≠ ⊤,
    or.inl $ le_trans le_sup_right (hi.le_jacobson le_sup_left h) $ mem_span_singleton.2 $ dvd_refl x)

end is_local

section is_primary
variables {R : Type u} [comm_ring R]

/-- A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`. -/
def is_primary (I : ideal R) : Prop :=
I ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ radical I

theorem is_primary.to_is_prime (I : ideal R) (hi : is_prime I) : is_primary I :=
⟨hi.1, λ x y hxy, (hi.2 hxy).imp id $ λ hyi, le_radical hyi⟩

theorem mem_radical_of_pow_mem {I : ideal R} {x : R} {m : ℕ} (hx : x ^ m ∈ radical I) : x ∈ radical I :=
radical_idem I ▸ ⟨m, hx⟩

theorem is_prime_radical {I : ideal R} (hi : is_primary I) : is_prime (radical I) :=
⟨mt radical_eq_top.1 hi.1, λ x y ⟨m, hxy⟩, begin
  rw mul_pow at hxy, cases hi.2 hxy,
  { exact or.inl ⟨m, h⟩ },
  { exact or.inr (mem_radical_of_pow_mem h) }
end⟩

theorem is_primary_inf {I J : ideal R} (hi : is_primary I) (hj : is_primary J)
  (hij : radical I = radical J) : is_primary (I ⊓ J) :=
⟨ne_of_lt $ lt_of_le_of_lt inf_le_left (lt_top_iff_ne_top.2 hi.1), λ x y ⟨hxyi, hxyj⟩,
begin
  rw [radical_inf, hij, inf_idem],
  cases hi.2 hxyi with hxi hyi, cases hj.2 hxyj with hxj hyj,
  { exact or.inl ⟨hxi, hxj⟩ },
  { exact or.inr hyj },
  { rw hij at hyi, exact or.inr hyi }
end⟩

theorem is_primary_of_is_maximal_radical {I : ideal R} (hi : is_maximal (radical I)) : is_primary I :=
have radical I = jacobson I,
from le_antisymm (le_Inf $ λ M ⟨him, hm⟩, hm.is_prime.radical_le_iff.2 him)
  (Inf_le ⟨le_radical, hi⟩),
⟨ne_top_of_lt $ lt_of_le_of_lt le_radical (lt_top_iff_ne_top.2 hi.1),
λ x y hxy, ((is_local_of_is_maximal_radical hi).mem_jacobson_or_exists_inv y).symm.imp
  (λ ⟨z, hz⟩, by rw [← mul_one x, ← sub_sub_cancel (z * y) 1, mul_sub, mul_left_comm]; exact
    I.sub_mem (I.mul_mem_left hxy) (I.mul_mem_left hz))
  (this ▸ id)⟩

end is_primary

end ideal

namespace ring_hom

variables {R : Type u} {S : Type v} [comm_ring R]

section comm_ring
variables [comm_ring S] (f : R →+* S)

/-- Kernel of a ring homomorphism as an ideal of the domain. -/
def ker : ideal R := ideal.comap f ⊥

/-- An element is in the kernel if and only if it maps to zero.-/
lemma mem_ker {r} : r ∈ ker f ↔ f r = 0 :=
by rw [ker, ideal.mem_comap, submodule.mem_bot]

lemma ker_eq : ((ker f) : set R) = is_add_group_hom.ker f := rfl

lemma inj_iff_ker_eq_bot : function.injective f ↔ ker f = ⊥ :=
by rw [←submodule.ext'_iff, ker_eq]; exact is_add_group_hom.inj_iff_trivial_ker f

lemma ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ ∀ x, f x = 0 → x = 0 :=
by rw [←submodule.ext'_iff, ker_eq]; exact is_add_group_hom.trivial_ker_iff_eq_zero f

/-- If the target is not the zero ring, then one is not in the kernel.-/
lemma not_one_mem_ker [nonzero S] (f : R →+* S) : (1:R) ∉ ker f :=
by { rw [mem_ker, f.map_one], exact one_ne_zero }

end comm_ring

/-- The kernel of a homomorphism to an integral domain is a prime ideal.-/
lemma ker_is_prime [integral_domain S] (f : R →+* S) :
  (ker f).is_prime :=
⟨by { rw [ne.def, ideal.eq_top_iff_one], exact not_one_mem_ker f },
λ x y, by simpa only [mem_ker, f.map_mul] using @eq_zero_or_eq_zero_of_mul_eq_zero S _ _ _ _ _⟩

end ring_hom

namespace ideal

variables {R : Type*} {S : Type*} [comm_ring R] [comm_ring S]

lemma map_eq_bot_iff_le_ker {I : ideal R} (f : R →+* S) : I.map f = ⊥ ↔ I ≤ f.ker :=
by rw [ring_hom.ker, eq_bot_iff, map_le_iff_le_comap]

end ideal

namespace submodule

variables {R : Type u} {M : Type v}
variables [comm_ring R] [add_comm_group M] [module R M]

-- It is even a semialgebra. But those aren't in mathlib yet.

instance semimodule_submodule : semimodule (ideal R) (submodule R M) :=
{ smul_add := smul_sup,
  add_smul := sup_smul,
  mul_smul := smul_assoc,
  one_smul := by simp,
  zero_smul := bot_smul,
  smul_zero := smul_bot }

end submodule
