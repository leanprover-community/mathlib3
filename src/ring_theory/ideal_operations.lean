/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

More operations on modules and ideals.
-/

import ring_theory.ideals data.nat.choose order.zorn
import linear_algebra.tensor_product
import data.equiv.algebra
import ring_theory.algebra_operations

universes u v w x

open lattice

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

theorem annihilator_supr (ι : Type w) (f : ι → submodule R M) :
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

theorem infi_colon_supr (ι₁ : Type w) (f : ι₁ → submodule R M)
  (ι₂ : Type x) (g : ι₂ → submodule R M) :
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
  (λ r hr s hs, (@smul_eq_mul R _ r s).symm ▸ smul_smul _ r s t ▸ smul_mem_smul hr (smul_mem_smul hs htn))
  ((zero_smul R t).symm ▸ submodule.zero_mem _)
  (λ x y, (add_smul x y t).symm ▸ submodule.add_mem _)
  (λ r s h, (@smul_eq_mul R _ r s).symm ▸ smul_smul _ r s t ▸ submodule.smul_mem _ _ h))
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
  { rw [← quotient.eq, quotient.mk_one, ← finset.prod_hom (quotient.mk (f i))],
    apply finset.prod_eq_one, intros, rw [← quotient.mk_one, quotient.eq], apply hgi },
  intros j hjs hji, rw [← quotient.eq_zero_iff_mem, ← finset.prod_hom (quotient.mk (f j))],
  refine finset.prod_eq_zero (finset.mem_erase_of_ne_of_mem hji hjs) _,
  rw quotient.eq_zero_iff_mem, exact hgj j hjs hji
end

theorem exists_sub_mem [fintype ι] {f : ι → ideal R}
  (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) (g : ι → R) :
  ∃ r : R, ∀ i, r - g i ∈ f i :=
begin
  have : ∃ φ : ι → R, (∀ i, φ i - 1 ∈ f i) ∧ (∀ i j, i ≠ j → φ i ∈ f j),
  { have := exists_sub_one_mem_and_mem (finset.univ : finset ι) (λ i _ j _ hij, hf i j hij),
    choose φ hφ, use λ i, φ i (finset.mem_univ i),
    exact ⟨λ i, (hφ i _).1, λ i j hij, (hφ i _).2 j (finset.mem_univ j) hij.symm⟩ },
  rcases this with ⟨φ, hφ1, hφ2⟩,
  use finset.univ.sum (λ i, g i * φ i),
  intros i,
  rw [← quotient.eq, ← finset.sum_hom (quotient.mk (f i))],
  refine eq.trans (finset.sum_eq_single i _ _) _,
  { intros j _ hji, rw quotient.eq_zero_iff_mem, exact (f i).mul_mem_left (hφ2 j i hji) },
  { intros hi, exact (hi $ finset.mem_univ i).elim },
  specialize hφ1 i, rw [← quotient.eq, quotient.mk_one] at hφ1,
  rw [quotient.mk_mul, hφ1, mul_one]
end

def quotient_inf_to_pi_quotient (f : ι → ideal R) :
  (⨅ i, f i).quotient → Π i, (f i).quotient :=
@@quotient.lift _ _ (⨅ i, f i) (λ r i, ideal.quotient.mk (f i) r)
  (@pi.is_ring_hom_pi ι (λ i, (f i).quotient) _ R _ _ _)
  (λ r hr, funext $ λ i, quotient.eq_zero_iff_mem.2 $ (submodule.mem_infi _).1 hr i)

theorem is_ring_hom_quotient_inf_to_pi_quotient (f : ι → ideal R) :
  is_ring_hom (quotient_inf_to_pi_quotient f) :=
@@quotient.is_ring_hom _ _ _
  (@pi.is_ring_hom_pi ι (λ i, (f i).quotient) _ R _ _ _) _

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
  (⨅ i, f i).quotient ≃r Π i, (f i).quotient :=
{ hom := is_ring_hom_quotient_inf_to_pi_quotient f,
  .. equiv.of_bijective (bijective_quotient_inf_to_pi_quotient hf) }

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
  exact le_trans (mul_le_inf) (lattice.inf_le_left)
end

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
      submodule.mem_Sup_of_directed hrnc y hyc hcc.directed_on in hc hyc ⟨n, hrny⟩,
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

theorem is_prime.mul_le {I J P : ideal R} (hp : is_prime P) :
  I * J ≤ P ↔ I ≤ P ∨ J ≤ P :=
⟨λ h, classical.or_iff_not_imp_left.2 $ λ hip j hj, let ⟨i, hi, hip⟩ := set.not_subset.1 hip in
  (hp.2 $ h $ mul_mem_mul hi hj).resolve_left hip,
λ h, or.cases_on h (le_trans $ le_trans mul_le_inf inf_le_left)
  (le_trans $ le_trans mul_le_inf inf_le_right)⟩

theorem is_prime.inf_le {I J P : ideal R} (hp : is_prime P) :
  I ⊓ J ≤ P ↔ I ≤ P ∨ J ≤ P :=
⟨λ h, hp.mul_le.1 $ le_trans mul_le_inf h,
λ h, or.cases_on h (le_trans inf_le_left) (le_trans inf_le_right)⟩

variables {ι : Type v}

theorem prod_le_inf {s : finset ι} {f : ι → ideal R} : s.prod f ≤ s.inf f :=
begin
  classical, refine s.induction_on _ _,
  { rw [finset.prod_empty, finset.inf_empty], exact le_refl _ },
 intros a s has ih,
  rw [finset.prod_insert has, finset.inf_insert],
  exact le_trans mul_le_inf (inf_le_inf (le_refl _) ih)
end

theorem is_prime.prod_le {s : finset ι} {f : ι → ideal R} {P : ideal R} (hp : is_prime P) :
  s.prod f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
suffices s.prod f ≤ P → ∃ i ∈ s, f i ≤ P,
  from ⟨this, λ ⟨i, his, hip⟩, le_trans prod_le_inf $ le_trans (finset.inf_le his) hip⟩,
begin
  classical, refine s.induction_on _ _,
  { intro h, rw finset.prod_empty at h,
    exact (hp.1 $ eq_top_iff.2 h).elim },
  intros a s has ih h,
  rw [finset.prod_insert has, hp.mul_le] at h, cases h,
  { exact ⟨a, finset.mem_insert_self a s, h⟩ },
  rcases ih h with ⟨i, hi, ih⟩,
  exact ⟨i, finset.mem_insert_of_mem hi, ih⟩
end

theorem is_prime.inf_le' {s : finset ι} {f : ι → ideal R} {P : ideal R} (hp : is_prime P) :
  s.inf f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
⟨λ h, hp.prod_le.1 $ le_trans prod_le_inf h, λ ⟨i, his, hip⟩, le_trans (finset.inf_le his) hip⟩

theorem subset_union {I J K : ideal R} : (I : set R) ⊆ J ∪ K ↔ I ≤ J ∨ I ≤ K :=
⟨λ h, classical.or_iff_not_imp_left.2 $ λ hij s hsi,
  let ⟨r, hri, hrj⟩ := set.not_subset.1 hij in classical.by_contradiction $ λ hsk,
  or.cases_on (h $ I.add_mem hri hsi)
    (λ hj, hrj $ add_sub_cancel r s ▸ J.sub_mem hj ((h hsi).resolve_right hsk))
    (λ hk, hsk $ add_sub_cancel' r s ▸ K.sub_mem hk ((h hri).resolve_left hrj)),
λ h, or.cases_on h (λ h, set.subset.trans h $ set.subset_union_left J K)
  (λ h, set.subset.trans h $ set.subset_union_right J K)⟩

theorem subset_union_prime' {s : finset ι} {f : ι → ideal R} {a b : ι}
  (hp : ∀ i ∈ s, is_prime (f i)) {I : ideal R} :
  (I : set R) ⊆ f a ∪ f b ∪ (⋃ i ∈ (↑s : set ι), f i) ↔ I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i :=
suffices (I : set R) ⊆ f a ∪ f b ∪ (⋃ i ∈ (↑s : set ι), f i) → I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i,
  from ⟨this, λ h, or.cases_on h (λ h, set.subset.trans h $ set.subset.trans
      (set.subset_union_left _ _) (set.subset_union_left _ _)) $
    λ h, or.cases_on h (λ h, set.subset.trans h $ set.subset.trans
      (set.subset_union_right _ _) (set.subset_union_left _ _)) $
    λ ⟨i, his, hi⟩, by refine (set.subset.trans hi $ set.subset.trans _ $ set.subset_union_right _ _);
      exact set.subset_bUnion_of_mem (finset.mem_coe.2 his)⟩,
begin
  generalize hn : s.card = n, unfreezeI, intros h,
  induction n with n ih generalizing a b s,
  case nat.zero { rw finset.card_eq_zero at hn, subst hn,
    rw [finset.coe_empty, set.bUnion_empty, set.union_empty, subset_union] at h,
    simpa only [exists_prop, finset.not_mem_empty, false_and, exists_false, or_false] },
  classical,
  replace hn : ∃ (i : ι) (t : finset ι), i ∉ t ∧ insert i t = s ∧ t.card = n := finset.card_eq_succ.1 hn,
  rcases hn with ⟨i, t, hit, rfl, hn⟩,
  replace hp : is_prime (f i) ∧ ∀ x ∈ t, is_prime (f x) := (t.forall_mem_insert _ _).1 hp,
  by_cases Ht : ∃ j ∈ t, f j ≤ f i,
  { rcases Ht with ⟨j, hjt, hfji⟩,
    have : ∃ u, j ∉ u ∧ insert j u = t,
    { exact ⟨t.erase j, t.not_mem_erase j, finset.insert_erase hjt⟩ },
    rcases this with ⟨u, hju, rfl⟩,
    have hp' : ∀ k ∈ insert i u, is_prime (f k),
    { rw finset.forall_mem_insert at hp ⊢, exact ⟨hp.1, hp.2.2⟩ },
    have hiu : i ∉ u := mt finset.mem_insert_of_mem hit,
    have hn' : (insert i u).card = n,
    { rwa finset.card_insert_of_not_mem at hn ⊢, exacts [hiu, hju] },
    have h' : (I : set R) ⊆ f a ∪ f b ∪ (⋃ k ∈ (↑(insert i u) : set ι), f k),
    { rw finset.coe_insert at h ⊢, rw finset.coe_insert at h,
      simp only [set.bUnion_insert] at h ⊢,
      rwa [← set.union_assoc ↑(f i), set.union_eq_self_of_subset_right hfji] at h },
    specialize @ih a b (insert i u) hp' hn' h',
    refine ih.imp id (or.imp id (exists_imp_exists $ λ k, _)), simp only [exists_prop],
    exact and.imp (λ hk, finset.insert_subset_insert i (finset.subset_insert j u) hk) id },
  by_cases Ha : f a ≤ f i,
  { have h' : (I : set R) ⊆ f i ∪ f b ∪ (⋃ j ∈ (↑t : set ι), f j),
    { rwa [finset.coe_insert, set.bUnion_insert, ← set.union_assoc, set.union_right_comm ↑(f a),
          set.union_eq_self_of_subset_left Ha] at h },
    specialize @ih i b t hp.2 hn h', right,
    rcases ih with ih | ih | ⟨k, hkt, ih⟩,
    { exact or.inr ⟨i, finset.mem_insert_self i t, ih⟩ },
    { exact or.inl ih },
    { exact or.inr ⟨k, finset.mem_insert_of_mem hkt, ih⟩ } },
  by_cases Hb : f b ≤ f i,
  { have h' : (I : set R) ⊆ f a ∪ f i ∪ (⋃ j ∈ (↑t : set ι), f j),
    { rwa [finset.coe_insert, set.bUnion_insert, ← set.union_assoc, set.union_assoc ↑(f a),
          set.union_eq_self_of_subset_left Hb] at h },
    specialize @ih a i t hp.2 hn h',
    rcases ih with ih | ih | ⟨k, hkt, ih⟩,
    { exact or.inl ih },
    { exact or.inr (or.inr ⟨i, finset.mem_insert_self i t, ih⟩) },
    { exact or.inr (or.inr ⟨k, finset.mem_insert_of_mem hkt, ih⟩) } },
  by_cases Hi : I ≤ f i,
  { exact or.inr (or.inr ⟨i, finset.mem_insert_self i t, Hi⟩) },
  have : ¬I ⊓ f a ⊓ f b ⊓ t.inf f ≤ f i,
  { simp only [hp.1.inf_le, hp.1.inf_le', not_or_distrib], exact ⟨⟨⟨Hi, Ha⟩, Hb⟩, Ht⟩ },
  rcases set.not_subset.1 this with ⟨r, ⟨⟨⟨hrI, hra⟩, hrb⟩, hr⟩, hri⟩,
  by_cases HI : (I : set R) ⊆ f a ∪ f b ∪ ⋃ j ∈ (↑t : set ι), f j,
  { specialize ih hp.2 hn HI, rcases ih with ih | ih | ⟨k, hkt, ih⟩,
    { left, exact ih }, { right, left, exact ih },
    { right, right, exact ⟨k, finset.mem_insert_of_mem hkt, ih⟩ } },
  exfalso, rcases set.not_subset.1 HI with ⟨s, hsI, hs⟩,
  rw [finset.coe_insert, set.bUnion_insert] at h,
  have hsi : s ∈ f i := ((h hsI).resolve_left (mt or.inl hs)).resolve_right (mt or.inr hs),
  rcases h (I.add_mem hrI hsI) with ⟨ha | hb⟩ | hi | ht,
  { exact hs (or.inl $ or.inl $ add_sub_cancel' r s ▸ (f a).sub_mem ha hra) },
  { exact hs (or.inl $ or.inr $ add_sub_cancel' r s ▸ (f b).sub_mem hb hrb) },
  { exact hri (add_sub_cancel r s ▸ (f i).sub_mem hi hsi) },
  { rw set.mem_bUnion_iff at ht, rcases ht with ⟨j, hjt, hj⟩,
    simp only [finset.inf_eq_infi, submodule.mem_coe, submodule.mem_infi] at hr,
    exact hs (or.inr $ set.mem_bUnion hjt $ add_sub_cancel' r s ▸ (f j).sub_mem hj $ hr j hjt) }
end

/-- Prime avoidance. Atiyah-Macdonald 1.11, Eisenbud 3.3, Stacks 00DS, Matsumura Ex.1.6. -/
theorem subset_union_prime {s : finset ι} {f : ι → ideal R} (a b : ι)
  (hp : ∀ i ∈ s, i ≠ a → i ≠ b → is_prime (f i)) {I : ideal R} :
  (I : set R) ⊆ (⋃ i ∈ (↑s : set ι), f i) ↔ ∃ i ∈ s, I ≤ f i :=
suffices (I : set R) ⊆ (⋃ i ∈ (↑s : set ι), f i) → ∃ i, i ∈ s ∧ I ≤ f i,
  from ⟨λ h, bex_def.2 $ this h, λ ⟨i, his, hi⟩, set.subset.trans hi $ set.subset_bUnion_of_mem $
    show i ∈ (↑s : set ι), from his⟩,
assume h : (I : set R) ⊆ (⋃ i ∈ (↑s : set ι), f i),
begin
  classical, by_cases has : a ∈ s,
  { have : ∃ t, a ∉ t ∧ insert a t = s :=
      ⟨s.erase a, finset.not_mem_erase a s, finset.insert_erase has⟩,
    rcases this with ⟨t, hat, rfl⟩, by_cases hbt : b ∈ t,
    { have : ∃ u, b ∉ u ∧ insert b u = t :=
        ⟨t.erase b, finset.not_mem_erase b t, finset.insert_erase hbt⟩,
      rcases this with ⟨u, hbu, rfl⟩,
      have hp' : ∀ i ∈ u, is_prime (f i),
      { intros i hiu,
        have hiabu : i ∈ insert a (insert b u) := finset.mem_insert_of_mem (finset.mem_insert_of_mem hiu),
        have hia : i ≠ a, { rintro rfl, exact hat (finset.mem_insert_of_mem hiu) },
        have hib : i ≠ b, { rintro rfl, exact hbu hiu },
        exact hp i hiabu hia hib },
      rw [finset.coe_insert, finset.coe_insert, set.bUnion_insert, set.bUnion_insert,
          ← set.union_assoc, subset_union_prime' hp', bex_def] at h,
      rwa [finset.exists_mem_insert, finset.exists_mem_insert] },
    { have hp' : ∀ j ∈ t, is_prime (f j),
      { intros j hjt,
        have hjat : j ∈ insert a t := finset.mem_insert_of_mem hjt,
        have hja : j ≠ a, { rintro rfl, exact hat hjt },
        have hjb : j ≠ b, { rintro rfl, exact hbt hjt },
        exact hp j hjat hja hjb },
      rw [finset.coe_insert, set.bUnion_insert, ← set.union_self (f a : set R),
          subset_union_prime' hp', ← or_assoc, or_self, bex_def] at h,
      rwa finset.exists_mem_insert } },
  { by_cases hbs : b ∈ s,
    { have : ∃ t, b ∉ t ∧ insert b t = s :=
        ⟨s.erase b, finset.not_mem_erase b s, finset.insert_erase hbs⟩,
      rcases this with ⟨t, hbt, rfl⟩,
      have hp' : ∀ j ∈ t, is_prime (f j),
      { intros j hjt,
        have hjbt : j ∈ insert b t := finset.mem_insert_of_mem hjt,
        have hja : j ≠ a, { rintro rfl, exact has (finset.mem_insert_of_mem hjt) },
        have hjb : j ≠ b, { rintro rfl, exact hbt hjt },
        exact hp j hjbt hja hjb },
      rw [finset.coe_insert, set.bUnion_insert, ← set.union_self (f b : set R),
          subset_union_prime' hp', ← or_assoc, or_self, bex_def] at h,
      rwa finset.exists_mem_insert },
    by_cases hse : s = ∅,
    { subst hse, rw [finset.coe_empty, set.bUnion_empty, set.subset_empty_iff] at h,
      have : (I : set R) ≠ ∅ := set.ne_empty_of_mem I.zero_mem,
      exact absurd h this },
    { cases finset.exists_mem_of_ne_empty hse with i his,
      have : ∃ t, i ∉ t ∧ insert i t = s :=
        ⟨s.erase i, finset.not_mem_erase i s, finset.insert_erase his⟩,
      rcases this with ⟨t, hit, rfl⟩,
      have hp' : ∀ j ∈ t, is_prime (f j),
      { intros j hjt,
        have hjit : j ∈ insert i t := finset.mem_insert_of_mem hjt,
        have hja : j ≠ a, { rintro rfl, exact has (finset.mem_insert_of_mem hjt) },
        have hjb : j ≠ b, { rintro rfl, exact hbs (finset.mem_insert_of_mem hjt) },
        exact hp j hjit hja hjb },
      rw [finset.coe_insert, set.bUnion_insert, ← set.union_self (f i : set R),
          subset_union_prime' hp', ← or_assoc, or_self, bex_def] at h,
      rwa finset.exists_mem_insert } }
end

end mul_and_radical

section map_and_comap
variables {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
variables (f : R → S) [is_ring_hom f]
variables {I J : ideal R} {K L : ideal S}

def map (I : ideal R) : ideal S :=
span (f '' I)

def comap (I : ideal S) : ideal R :=
{ carrier := f ⁻¹' I,
  zero := show f 0 ∈ I, by rw is_ring_hom.map_zero f; exact I.zero_mem,
  add := λ x y hx hy, show f (x + y) ∈ I, by rw is_ring_hom.map_add f; exact I.add_mem hx hy,
  smul := λ c x hx, show f (c * x) ∈ I, by rw is_ring_hom.map_mul f; exact I.mul_mem_left hx }

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
set.preimage_mono h
variables (f)

theorem comap_ne_top (hK : K ≠ ⊤) : comap f K ≠ ⊤ :=
(ne_top_iff_one _).2 $ by rw [mem_comap, is_ring_hom.map_one f];
  exact (ne_top_iff_one _).1 hK

instance is_prime.comap {hK : K.is_prime} : (comap f K).is_prime :=
⟨comap_ne_top _ hK.1, λ x y,
  by simp only [mem_comap, is_ring_hom.map_mul f]; apply hK.2⟩

variables (I J K L)
theorem map_bot : map f ⊥ = ⊥ :=
le_antisymm (map_le_iff_le_comap.2 bot_le) bot_le

theorem map_top : map f ⊤ = ⊤ :=
(eq_top_iff_one _).2 $ subset_span ⟨1, trivial, is_ring_hom.map_one f⟩

theorem comap_top : comap f ⊤ = ⊤ :=
(eq_top_iff_one _).2 trivial

theorem map_sup : map f (I ⊔ J) = map f I ⊔ map f J :=
le_antisymm (map_le_iff_le_comap.2 $ sup_le
  (map_le_iff_le_comap.1 le_sup_left)
  (map_le_iff_le_comap.1 le_sup_right))
(sup_le (map_mono le_sup_left) (map_mono le_sup_right))

theorem map_mul : map f (I * J) = map f I * map f J :=
le_antisymm (map_le_iff_le_comap.2 $ mul_le.2 $ λ r hri s hsj,
  show f (r * s) ∈ _, by rw is_ring_hom.map_mul f;
  exact mul_mem_mul (mem_map_of_mem hri) (mem_map_of_mem hsj))
(trans_rel_right _ (span_mul_span _ _) $ span_le.2 $
  set.bUnion_subset $ λ i ⟨r, hri, hfri⟩,
  set.bUnion_subset $ λ j ⟨s, hsj, hfsj⟩,
  set.singleton_subset_iff.2 $ hfri ▸ hfsj ▸
  by rw [← is_ring_hom.map_mul f];
  exact mem_map_of_mem (mul_mem_mul hri hsj))

theorem comap_inf : comap f (K ⊓ L) = comap f K ⊓ comap f L := rfl

theorem comap_radical : comap f (radical K) = radical (comap f K) :=
le_antisymm (λ r ⟨n, hfrnk⟩, ⟨n, show f (r ^ n) ∈ K,
  from (is_semiring_hom.map_pow f r n).symm ▸ hfrnk⟩)
(λ r ⟨n, hfrnk⟩, ⟨n, is_semiring_hom.map_pow f r n ▸ hfrnk⟩)

@[simp] lemma map_quotient_self :
  map (quotient.mk I) I = ⊥ :=
lattice.eq_bot_iff.2 $ ideal.map_le_iff_le_comap.2 $ λ x hx,
(submodule.mem_bot I.quotient).2 $ ideal.quotient.eq_zero_iff_mem.2 hx

variables {I J K L}

theorem map_inf_le : map f (I ⊓ J) ≤ map f I ⊓ map f J :=
map_le_iff_le_comap.2 $ (comap_inf f (map f I) (map f J)).symm ▸
inf_le_inf (map_le_iff_le_comap.1 $ le_refl _) (map_le_iff_le_comap.1 $ le_refl _)

theorem map_radical_le : map f (radical I) ≤ radical (map f I) :=
map_le_iff_le_comap.2 $ λ r ⟨n, hrni⟩, ⟨n, is_semiring_hom.map_pow f r n ▸ mem_map_of_mem hrni⟩

theorem le_comap_sup : comap f K ⊔ comap f L ≤ comap f (K ⊔ L) :=
map_le_iff_le_comap.1 $ (map_sup f (comap f K) (comap f L)).symm ▸
sup_le_sup (map_le_iff_le_comap.2 $ le_refl _) (map_le_iff_le_comap.2 $ le_refl _)

theorem le_comap_mul : comap f K * comap f L ≤ comap f (K * L) :=
map_le_iff_le_comap.1 $ (map_mul f (comap f K) (comap f L)).symm ▸
mul_mono (map_le_iff_le_comap.2 $ le_refl _) (map_le_iff_le_comap.2 $ le_refl _)

section surjective
variables (hf : function.surjective f)
include hf

theorem map_comap_of_surjective (I : ideal S) :
  map f (comap f I) = I :=
le_antisymm (map_le_iff_le_comap.2 (le_refl _))
(λ s hsi, let ⟨r, hfrs⟩ := hf s in
  hfrs ▸ (mem_map_of_mem $ show f r ∈ I, from hfrs.symm ▸ hsi))

theorem mem_image_of_mem_map_of_surjective {I : ideal R} {y}
  (H : y ∈ map f I) : y ∈ f '' I :=
submodule.span_induction H (λ _, id) ⟨0, I.zero_mem, is_ring_hom.map_zero f⟩
(λ y1 y2 ⟨x1, hx1i, hxy1⟩ ⟨x2, hx2i, hxy2⟩, ⟨x1 + x2, I.add_mem hx1i hx2i, hxy1 ▸ hxy2 ▸ is_ring_hom.map_add f⟩)
(λ c y ⟨x, hxi, hxy⟩, let ⟨d, hdc⟩ := hf c in ⟨d • x, I.smul_mem _ hxi, hdc ▸ hxy ▸ is_ring_hom.map_mul f⟩)

theorem comap_map_of_surjective (I : ideal R) :
  comap f (map f I) = I ⊔ comap f ⊥ :=
le_antisymm (assume r h, let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h in
  submodule.mem_sup.2 ⟨s, hsi, r - s, (submodule.mem_bot S).2 $ by rw [is_ring_hom.map_sub f, hfsr, sub_self],
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
  ord := λ I1 I2, ⟨comap_mono, λ H, map_comap_of_surjective f hf I1 ▸
    map_comap_of_surjective f hf I2 ▸ map_mono H⟩ }

def le_order_embedding_of_surjective :
  ((≤) : ideal S → ideal S → Prop) ≼o ((≤) : ideal R → ideal R → Prop) :=
(order_iso_of_surjective f hf).to_order_embedding.trans (subtype.order_embedding _ _)

def lt_order_embedding_of_surjective :
  ((<) : ideal S → ideal S → Prop) ≼o ((<) : ideal R → ideal R → Prop) :=
(le_order_embedding_of_surjective f hf).lt_embedding_of_le_embedding

end surjective

end map_and_comap

end ideal

namespace is_ring_hom

variables {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
variables (f : R → S) [is_ring_hom f]

def ker : ideal R := ideal.comap f ⊥

lemma ker_eq : ((ker f) : set R) = is_add_group_hom.ker f := rfl

lemma inj_iff_ker_eq_bot : function.injective f ↔ ker f = ⊥ :=
by rw [←submodule.ext'_iff, ker_eq]; exact is_add_group_hom.inj_iff_trivial_ker f

lemma ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ ∀ x, f x = 0 → x = 0 :=
by rw [←submodule.ext'_iff, ker_eq]; exact is_add_group_hom.trivial_ker_iff_eq_zero f

lemma injective_iff : function.injective f ↔ ∀ x, f x = 0 → x = 0 :=
is_add_group_hom.injective_iff f

end is_ring_hom

namespace submodule

variables {R : Type u} {M : Type v}
variables [comm_ring R] [add_comm_group M] [module R M]

-- It is even a semialgebra. But those aren't in mathlib yet.

instance : semimodule (ideal R) (submodule R M) :=
{ smul_add := smul_sup,
  add_smul := sup_smul,
  mul_smul := smul_assoc,
  one_smul := by simp,
  zero_smul := bot_smul,
  smul_zero := smul_bot }

end submodule
