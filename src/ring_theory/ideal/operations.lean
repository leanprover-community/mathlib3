/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.nat.choose.sum
import data.equiv.ring
import algebra.algebra.operations
import ring_theory.ideal.basic
/-!
# More operations on modules and ideals
-/
universes u v w x

open_locale big_operators

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

protected theorem smul_assoc : (I • J) • N = I • (J • N) :=
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

variables {M' : Type w} [add_comm_group M'] [module R M']

theorem map_smul'' (f : M →ₗ[R] M') : (I • N).map f = I • N.map f :=
le_antisymm (map_le_iff_le_comap.2 $ smul_le.2 $ λ r hr n hn, show f (r • n) ∈ I • N.map f,
    from (f.map_smul r n).symm ▸ smul_mem_smul hr (mem_map_of_mem hn)) $
smul_le.2 $ λ r hr n hn, let ⟨p, hp, hfp⟩ := mem_map.1 hn in
hfp ▸ f.map_smul r p ▸ mem_map_of_mem (smul_mem_smul hr hp)

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
  rcases this with ⟨g, hgi, hgj⟩, use (∏ x in s.erase i, g x), split,
  { rw [← quotient.eq, ring_hom.map_one, ring_hom.map_prod],
    apply finset.prod_eq_one, intros, rw [← ring_hom.map_one, quotient.eq], apply hgi },
  intros j hjs hji, rw [← quotient.eq_zero_iff_mem, ring_hom.map_prod],
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
  use ∑ i, g i * φ i,
  intros i,
  rw [← quotient.eq, ring_hom.map_sum],
  refine eq.trans (finset.sum_eq_single i _ _) _,
  { intros j _ hji, rw quotient.eq_zero_iff_mem, exact (f i).mul_mem_left (hφ2 j i hji) },
  { intros hi, exact (hi $ finset.mem_univ i).elim },
  specialize hφ1 i, rw [← quotient.eq, ring_hom.map_one] at hφ1,
  rw [ring_hom.map_mul, hφ1, mul_one]
end

def quotient_inf_to_pi_quotient (f : ι → ideal R) :
  (⨅ i, f i).quotient →+* Π i, (f i).quotient :=
begin
  refine quotient.lift (⨅ i, f i) _ _,
  { convert @@pi.ring_hom (λ i, quotient (f i)) (λ i, ring.to_semiring) ring.to_semiring
      (λ i, quotient.mk (f i)) },
  { intros r hr,
    rw submodule.mem_infi at hr,
    ext i,
    exact quotient.eq_zero_iff_mem.2 (hr i) }
end

theorem quotient_inf_to_pi_quotient_bijective [fintype ι] {f : ι → ideal R}
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
{ .. equiv.of_bijective _ (quotient_inf_to_pi_quotient_bijective hf),
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

lemma span_mul_span' (S T : set R) : span S * span T = span (S*T) :=
by { unfold span, rw submodule.span_mul_span,}

lemma span_singleton_mul_span_singleton (r s : R) : span {r} * span {s} = (span {r * s} : ideal R) :=
by { unfold span, rw [submodule.span_mul_span, set.singleton_mul_singleton],}

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

lemma mul_eq_bot {R : Type*} [integral_domain R] {I J : ideal R} :
  I * J = ⊥ ↔ I = ⊥ ∨ J = ⊥ :=
⟨λ hij, or_iff_not_imp_left.mpr (λ I_ne_bot, J.eq_bot_iff.mpr (λ j hj,
  let ⟨i, hi, ne0⟩ := I.ne_bot_iff.mp I_ne_bot in
    or.resolve_left (mul_eq_zero.mp ((I * J).eq_bot_iff.mp hij _ (mul_mem_mul hi hj))) ne0)),
 λ h, by cases h; rw [← ideal.mul_bot, h, ideal.mul_comm]⟩

/-- The radical of an ideal `I` consists of the elements `r` such that `r^n ∈ I` for some `n`. -/
def radical (I : ideal R) : ideal R :=
{ carrier := { r | ∃ n : ℕ, r ^ n ∈ I },
  zero_mem' := ⟨1, (pow_one (0:R)).symm ▸ I.zero_mem⟩,
  add_mem' := λ x y ⟨m, hxmi⟩ ⟨n, hyni⟩, ⟨m + n,
    (add_pow x y (m + n)).symm ▸ I.sum_mem $
    show ∀ c ∈ finset.range (nat.succ (m + n)), x ^ c * y ^ (m + n - c) * (nat.choose (m + n) c) ∈ I,
    from λ c hc, or.cases_on (le_total c m)
      (λ hcm, I.mul_mem_right $ I.mul_mem_left $ nat.add_comm n m ▸ (nat.add_sub_assoc hcm n).symm ▸
        (pow_add y n (m-c)).symm ▸ I.mul_mem_right hyni)
      (λ hmc, I.mul_mem_right $ I.mul_mem_right $ nat.add_sub_cancel' hmc ▸
        (pow_add x m (c-m)).symm ▸ I.mul_mem_right hxmi)⟩,
  smul_mem' := λ r s ⟨n, hsni⟩, ⟨n, show (r * s)^n ∈ I,
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
  λ x y hxym, or_iff_not_imp_left.2 $ λ hxm, classical.by_contradiction $ λ hym,
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

variables (R)
theorem top_pow (n : ℕ) : (⊤ ^ n : ideal R) = ⊤ :=
nat.rec_on n one_eq_top $ λ n ih, by rw [pow_succ, ih, top_mul]
variables {R}

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
  smul_mem' := λ c x hx, show f (c * x) ∈ I, by { rw f.map_mul, exact I.mul_mem_left hx },
  .. I.to_add_submonoid.comap (f : R →+ S) }

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

@[simp] lemma comap_eq_top_iff {I : ideal S} : I.comap f = ⊤ ↔ I = ⊤ :=
⟨ λ h, I.eq_top_iff_one.mpr (f.map_one ▸ mem_comap.mp ((I.comap f).eq_top_iff_one.mp h)),
  λ h, by rw [h, comap_top] ⟩

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

lemma comap_Inf' (s : set (ideal S)) : (Inf s).comap f = ⨅ I ∈ (comap f '' s), I :=
trans (comap_Inf f s) (by rw infi_image)

theorem comap_radical : comap f (radical K) = radical (comap f K) :=
le_antisymm (λ r ⟨n, hfrnk⟩, ⟨n, show f (r ^ n) ∈ K,
  from (f.map_pow r n).symm ▸ hfrnk⟩)
(λ r ⟨n, hfrnk⟩, ⟨n, f.map_pow r n ▸ hfrnk⟩)

theorem comap_is_prime [H : is_prime K] : is_prime (comap f K) :=
⟨comap_ne_top f H.left,
  λ x y h, H.right (show f x * f y ∈ K, by rwa [mem_comap, ring_hom.map_mul] at h)⟩

@[simp] lemma map_quotient_self :
  map (quotient.mk I) I = ⊥ :=
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

lemma mem_map_iff_of_surjective {I : ideal R} {y} :
  y ∈ map f I ↔ ∃ x, x ∈ I ∧ f x = y :=
⟨λ h, (set.mem_image _ _ _).2 (mem_image_of_mem_map_of_surjective f hf h),
  λ ⟨x, hx⟩, hx.right ▸ (mem_map_of_mem hx.left)⟩

theorem comap_map_of_surjective (I : ideal R) :
  comap f (map f I) = I ⊔ comap f ⊥ :=
le_antisymm (assume r h, let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h in
  submodule.mem_sup.2 ⟨s, hsi, r - s, (submodule.mem_bot S).2 $ by rw [f.map_sub, hfsr, sub_self],
  add_sub_cancel'_right s r⟩)
(sup_le (map_le_iff_le_comap.1 (le_refl _)) (comap_mono bot_le))

lemma le_map_of_comap_le_of_surjective : comap f K ≤ I → K ≤ map f I :=
λ h, (map_comap_of_surjective f hf K) ▸ map_mono h

/-- Correspondence theorem -/
def rel_iso_of_surjective :
  ideal S ≃o { p : ideal R // comap f ⊥ ≤ p } :=
{ to_fun := λ J, ⟨comap f J, comap_mono bot_le⟩,
  inv_fun := λ I, map f I.1,
  left_inv := λ J, map_comap_of_surjective f hf J,
  right_inv := λ I, subtype.eq $ show comap f (map f I.1) = I.1,
    from (comap_map_of_surjective f hf I).symm ▸ le_antisymm
      (sup_le (le_refl _) I.2) le_sup_left,
  map_rel_iff' := λ I1 I2, ⟨comap_mono, λ H, map_comap_of_surjective f hf I1 ▸
    map_comap_of_surjective f hf I2 ▸ map_mono H⟩ }

/-- The map on ideals induced by a surjective map preserves inclusion. -/
def order_embedding_of_surjective : ideal S ↪o ideal R :=
(rel_iso_of_surjective f hf).to_rel_embedding.trans (subtype.rel_embedding _ _)

theorem map_eq_top_or_is_maximal_of_surjective (H : is_maximal I) :
  (map f I) = ⊤ ∨ is_maximal (map f I) :=
begin
  refine or_iff_not_imp_left.2 (λ ne_top, ⟨λ h, ne_top h, λ J hJ, _⟩),
  { refine (rel_iso_of_surjective f hf).injective
      (subtype.ext_iff.2 (eq.trans (H.right (comap f J) (lt_of_le_of_ne _ _)) comap_top.symm)),
    { exact (map_le_iff_le_comap).1 (le_of_lt hJ) },
    { exact λ h, hJ.right (le_map_of_comap_le_of_surjective f hf (le_of_eq h.symm)) } }
end

theorem comap_is_maximal_of_surjective [H : is_maximal K] : is_maximal (comap f K) :=
begin
  refine ⟨comap_ne_top _ H.left, λ J hJ, _⟩,
  suffices : map f J = ⊤,
  { replace this := congr_arg (comap f) this,
    rw [comap_top, comap_map_of_surjective _ hf, eq_top_iff] at this,
    rw eq_top_iff,
    exact le_trans this (sup_le (le_of_eq rfl) (le_trans (comap_mono (bot_le)) (le_of_lt hJ))) },
  refine H.right (map f J) (lt_of_le_of_ne (le_map_of_comap_le_of_surjective _ hf (le_of_lt hJ))
    (λ h, ne_of_lt hJ (trans (congr_arg (comap f) h) _))),
  rw [comap_map_of_surjective _ hf, sup_eq_left],
  exact le_trans (comap_mono bot_le) (le_of_lt hJ)
end

end surjective

lemma mem_quotient_iff_mem (hIJ : I ≤ J) {x : R} :
  quotient.mk I x ∈ J.map (quotient.mk I) ↔ x ∈ J :=
begin
  refine iff.trans (mem_map_iff_of_surjective _ quotient.mk_surjective) _,
  split,
  { rintros ⟨x, x_mem, x_eq⟩,
    simpa using J.add_mem (hIJ (quotient.eq.mp x_eq.symm)) x_mem },
  { intro x_mem,
    exact ⟨x, x_mem, rfl⟩ }
end

section injective
variables (hf : function.injective f)
include hf

open function

lemma comap_bot_le_of_injective : comap f ⊥ ≤ I :=
begin
  refine le_trans (λ x hx, _) bot_le,
  rw [mem_comap, submodule.mem_bot, ← ring_hom.map_zero f] at hx,
  exact eq.symm (hf hx) ▸ (submodule.zero_mem ⊥)
end

end injective

section bijective
variables (hf : function.bijective f)
include hf

open function

/-- Special case of the correspondence theorem for isomorphic rings -/
def rel_iso_of_bijective : ideal S ≃o ideal R :=
{ to_fun := comap f,
  inv_fun := map f,
  left_inv := (rel_iso_of_surjective f hf.right).left_inv,
  right_inv := λ J, subtype.ext_iff.1
    ((rel_iso_of_surjective f hf.right).right_inv ⟨J, comap_bot_le_of_injective f hf.left⟩),
  map_rel_iff' := (rel_iso_of_surjective f hf.right).map_rel_iff' }

lemma comap_le_iff_le_map : comap f K ≤ I ↔ K ≤ map f I :=
⟨λ h, le_map_of_comap_le_of_surjective f hf.right h,
 λ h, ((rel_iso_of_bijective f hf).right_inv I) ▸ comap_mono h⟩

theorem map.is_maximal (H : is_maximal I) : is_maximal (map f I) :=
by refine or_iff_not_imp_left.1
  (map_eq_top_or_is_maximal_of_surjective f hf.right H) (λ h, H.left _);
calc I = comap f (map f I) : ((rel_iso_of_bijective f hf).right_inv I).symm
   ... = comap f ⊤ : by rw h
   ... = ⊤ : by rw comap_top

end bijective

end map_and_comap

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

lemma ker_eq_comap_bot (f : R →+* S) : f.ker = ideal.comap f ⊥ := rfl

lemma injective_iff_ker_eq_bot : function.injective f ↔ ker f = ⊥ :=
by rw [submodule.ext'_iff, ker_eq]; exact is_add_group_hom.injective_iff_trivial_ker f

lemma ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ ∀ x, f x = 0 → x = 0 :=
by rw [submodule.ext'_iff, ker_eq]; exact is_add_group_hom.trivial_ker_iff_eq_zero f

/-- If the target is not the zero ring, then one is not in the kernel.-/
lemma not_one_mem_ker [nontrivial S] (f : R →+* S) : (1:R) ∉ ker f :=
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

@[simp] lemma mk_ker {I : ideal R} : (quotient.mk I).ker = I :=
by ext; rw [ring_hom.ker, mem_comap, submodule.mem_bot, quotient.eq_zero_iff_mem]

lemma ker_le_comap {K : ideal S} (f : R →+* S) : f.ker ≤ comap f K :=
λ x hx, mem_comap.2 (((ring_hom.mem_ker f).1 hx).symm ▸ K.zero_mem)

lemma map_Inf {A : set (ideal R)} {f : R →+* S} (hf : function.surjective f) :
  (∀ J ∈ A, ring_hom.ker f ≤ J) → map f (Inf A) = Inf (map f '' A) :=
begin
  refine λ h, le_antisymm (le_Inf _) _,
  { intros j hj y hy,
    cases (mem_map_iff_of_surjective f hf).1 hy with x hx,
    cases (set.mem_image _ _ _).mp hj with J hJ,
    rw [← hJ.right, ← hx.right],
    exact mem_map_of_mem (Inf_le_of_le hJ.left (le_of_eq rfl) hx.left) },
  { intros y hy,
    cases hf y with x hx,
    refine hx ▸ (mem_map_of_mem _),
    rw Inf_eq_infi at ⊢ hy,
    simp at ⊢ hy,
    intros J hJ,
    cases (mem_map_iff_of_surjective f hf).1 (hy (map f J) J hJ rfl) with x' hx',
    have : x - x' ∈ J,
    { apply h J hJ,
      rw [ring_hom.mem_ker, ring_hom.map_sub, hx, hx'.right, sub_self y], },
    convert J.add_mem this hx'.left,
    ring, }
end

theorem map_is_prime_of_surjective {f : R →+* S} (hf : function.surjective f) {I : ideal R}
  [H : is_prime I] (hk : ring_hom.ker f ≤ I) : is_prime (map f I) :=
begin
  refine ⟨λ h, H.left (eq_top_iff.2 _), λ x y, _⟩,
  { replace h := congr_arg (comap f) h,
    rw [comap_map_of_surjective _ hf, comap_top] at h,
    exact h ▸ sup_le (le_of_eq rfl) hk },
  { refine λ hxy, (hf x).rec_on (λ a ha, (hf y).rec_on (λ b hb, _)),
    rw [← ha, ← hb, ← ring_hom.map_mul, mem_map_iff_of_surjective _ hf] at hxy,
    rcases hxy with ⟨c, hc, hc'⟩,
    rw [← sub_eq_zero, ← ring_hom.map_sub] at hc',
    have : a * b ∈ I,
    { convert I.sub_mem hc (hk (hc' : c - a * b ∈ f.ker)),
      ring },
    exact (H.right this).imp (λ h, ha ▸ mem_map_of_mem h) (λ h, hb ▸ mem_map_of_mem h) }
end

theorem map_radical_of_surjective {f : R →+* S} (hf : function.surjective f) {I : ideal R}
  (h : ring_hom.ker f ≤ I) : map f (I.radical) = (map f I).radical :=
begin
  rw [radical_eq_Inf, radical_eq_Inf],
  have : ∀ J ∈ {J : ideal R | I ≤ J ∧ J.is_prime}, f.ker ≤ J := λ J hJ, le_trans h hJ.left,
  convert map_Inf hf this,
  refine funext (λ j, propext ⟨_, _⟩),
  { rintros ⟨hj, hj'⟩,
    haveI : j.is_prime := hj',
    exact ⟨comap f j, ⟨⟨map_le_iff_le_comap.1 hj, comap_is_prime f j⟩,
      map_comap_of_surjective f hf j⟩⟩ },
  { rintro ⟨J, ⟨hJ, hJ'⟩⟩,
    haveI : J.is_prime := hJ.right,
    refine ⟨hJ' ▸ map_mono hJ.left, hJ' ▸ map_is_prime_of_surjective hf (le_trans h hJ.left)⟩ },
end

section quotient_algebra

/-- The ring hom `R/f⁻¹(I) →+* S/I` induced by a ring hom `f : R →+* S` -/
def quotient_map {I : ideal R} (J : ideal S) (f : R →+* S) (hIJ : I ≤ J.comap f) :
  I.quotient →+* J.quotient :=
(quotient.lift I ((quotient.mk J).comp f) (λ _ ha,
  by simpa [function.comp_app, ring_hom.coe_comp, quotient.eq_zero_iff_mem] using hIJ ha))

variables {I : ideal R} {J: ideal S} [algebra R S]

@[priority 100]
instance quotient_algebra : algebra (J.comap (algebra_map R S)).quotient J.quotient :=
(quotient_map J (algebra_map R S) (le_of_eq rfl)).to_algebra

lemma algebra_map_quotient_injective :
  function.injective (algebra_map (J.comap (algebra_map R S)).quotient J.quotient) :=
begin
  rintros ⟨a⟩ ⟨b⟩ hab,
  replace hab := quotient.eq.mp hab,
  rw ← ring_hom.map_sub at hab,
  exact quotient.eq.mpr hab
end

end quotient_algebra

end ideal

namespace submodule

variables {R : Type u} {M : Type v}
variables [comm_ring R] [add_comm_group M] [module R M]

-- It is even a semialgebra. But those aren't in mathlib yet.

instance semimodule_submodule : semimodule (ideal R) (submodule R M) :=
{ smul_add := smul_sup,
  add_smul := sup_smul,
  mul_smul := submodule.smul_assoc,
  one_smul := by simp,
  zero_smul := bot_smul,
  smul_zero := smul_bot }

end submodule

namespace ring_hom
variables {A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C]
variables (f : A →+* B)

/-- `lift_of_surjective f hf g hg` is the unique ring homomorphism `φ`

* such that `φ.comp f = g` (`lift_of_surjective_comp`),
* where `f : A →+* B` is surjective (`hf`),
* and `g : B →+* C` satisfies `hg : f.ker ≤ g.ker`.

See `lift_of_surjective_eq` for the uniqueness lemma.

```
   A .
   |  \
 f |   \ g
   |    \
   v     \⌟
   B ----> C
      ∃!φ
```
 -/
noncomputable def lift_of_surjective
  (hf : function.surjective f) (g : A →+* C) (hg : f.ker ≤ g.ker) :
  B →+* C :=
{ to_fun := λ b, g (classical.some (hf b)),
  map_one' :=
  begin
    rw [← g.map_one, ← sub_eq_zero, ← g.map_sub, ← g.mem_ker],
    apply hg,
    rw [f.mem_ker, f.map_sub, sub_eq_zero, f.map_one],
    exact classical.some_spec (hf 1)
  end,
  map_mul' :=
  begin
    intros x y,
    rw [← g.map_mul, ← sub_eq_zero, ← g.map_sub, ← g.mem_ker],
    apply hg,
    rw [f.mem_ker, f.map_sub, sub_eq_zero, f.map_mul],
    simp only [classical.some_spec (hf _)],
  end,
  .. add_monoid_hom.lift_of_surjective f.to_add_monoid_hom hf g.to_add_monoid_hom hg }

@[simp] lemma lift_of_surjective_comp_apply
  (hf : function.surjective f) (g : A →+* C) (hg : f.ker ≤ g.ker) (a : A) :
  (f.lift_of_surjective hf g hg) (f a) = g a :=
f.to_add_monoid_hom.lift_of_surjective_comp_apply hf g.to_add_monoid_hom hg a

@[simp] lemma lift_of_surjective_comp (hf : function.surjective f) (g : A →+* C) (hg : f.ker ≤ g.ker) :
  (f.lift_of_surjective hf g hg).comp f = g :=
by { ext, simp only [comp_apply, lift_of_surjective_comp_apply] }

lemma eq_lift_of_surjective (hf : function.surjective f) (g : A →+* C) (hg : f.ker ≤ g.ker)
  (h : B →+* C) (hh : h.comp f = g) :
  h = (f.lift_of_surjective hf g hg) :=
begin
  ext b, rcases hf b with ⟨a, rfl⟩,
  simp only [← comp_apply, hh, f.lift_of_surjective_comp],
end

end ring_hom
