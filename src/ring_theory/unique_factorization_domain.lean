/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson

-/
import algebra.gcd_monoid
import ring_theory.integral_domain
import ring_theory.noetherian

/--

# Unique factorization

## Main Definitions
* `wf_dvd_monoid` holds for `monoid`s for which a strict divisibility relation is
  well-founded.
* `unique_factorization_monoid` holds for `wf_dvd_monoid`s where
  `irreducible` is equivalent to `prime`

## To do
* set up the complete lattice structure on `factor_set`.

-/

variables {α : Type*}
local infix ` ~ᵤ ` : 50 := associated

section prio
set_option default_priority 100 -- see Note [default priority]
/-- Well-foundedness of the strict version of |, which is equivalent to the descending chain
condition on divisibility and to the ascending chain condition on
principal ideals in an integral domain.
  -/
class wf_dvd_monoid (α : Type*) [comm_monoid_with_zero α] : Prop :=
(well_founded_dvd_not_unit : well_founded (@dvd_not_unit α _))

export wf_dvd_monoid (well_founded_dvd_not_unit)

instance is_noetherian_ring.wf_dvd_monoid [integral_domain α] [is_noetherian_ring α] :
  wf_dvd_monoid α :=
⟨by { convert inv_image.wf (λ a, ideal.span ({a} : set α)) (well_founded_submodule_gt _ _),
      ext,
      exact ideal.span_singleton_lt_span_singleton.symm }⟩

end prio

instance polynomial.wf_dvd_monoid [integral_domain α] [wf_dvd_monoid α] : wf_dvd_monoid (polynomial α) :=
{ well_founded_dvd_not_unit := begin
    classical,
    refine rel_hom.well_founded
      ⟨λ p, (if p = 0 then ⊤ else ↑p.degree, p.leading_coeff), _⟩
      (prod.lex_wf (with_top.well_founded_lt $ with_bot.well_founded_lt nat.lt_wf)
        _inst_2.well_founded_dvd_not_unit),
    rintros a b ⟨ane0, ⟨c, ⟨not_unit_c, rfl⟩⟩⟩,
    rw [polynomial.degree_mul, if_neg ane0],
    split_ifs with hac,
    { rw [hac, polynomial.leading_coeff_zero],
      apply prod.lex.left,
      exact lt_of_le_of_ne le_top with_top.coe_ne_top },
    have cne0 : c ≠ 0 := right_ne_zero_of_mul hac,
    simp only [cne0, ane0, polynomial.leading_coeff_mul],
    by_cases hdeg : c.degree = 0,
    { simp only [hdeg, add_zero],
      refine prod.lex.right _ ⟨_, ⟨c.leading_coeff, (λ unit_c, not_unit_c _), rfl⟩⟩,
      { rwa [ne, polynomial.leading_coeff_eq_zero] },
      rw [polynomial.is_unit_iff, polynomial.eq_C_of_degree_eq_zero hdeg],
      use [c.leading_coeff, unit_c],
      rw [polynomial.leading_coeff, polynomial.nat_degree_eq_of_degree_eq_some hdeg] },
    { apply prod.lex.left,
      rw polynomial.degree_eq_nat_degree cne0 at *,
      rw [with_top.coe_lt_coe, polynomial.degree_eq_nat_degree ane0,
          ← with_bot.coe_add, with_bot.coe_lt_coe],
      exact lt_add_of_pos_right _ (nat.pos_of_ne_zero (λ h, hdeg (h.symm ▸ with_bot.coe_zero))) },
  end }

namespace wf_dvd_monoid

variables [comm_monoid_with_zero α]
open associates nat

theorem of_wf_dvd_monoid_associates (h : wf_dvd_monoid (associates α)): wf_dvd_monoid α :=
⟨begin
  haveI := h,
  refine (surjective.well_founded_iff mk_surjective _).2 wf_dvd_monoid.well_founded_dvd_not_unit,
  intros, rw mk_dvd_not_unit_mk_iff
end⟩

variables [wf_dvd_monoid α]

instance wf_dvd_monoid_associates : wf_dvd_monoid (associates α) :=
⟨begin
  refine (surjective.well_founded_iff mk_surjective _).1 wf_dvd_monoid.well_founded_dvd_not_unit,
  intros, rw mk_dvd_not_unit_mk_iff
end⟩

theorem well_founded_associates : well_founded ((<) : associates α → associates α → Prop) :=
subrelation.wf (λ x y, dvd_not_unit_of_lt) wf_dvd_monoid.well_founded_dvd_not_unit

local attribute [elab_as_eliminator] well_founded.fix

lemma exists_irreducible_factor {a : α} (ha : ¬ is_unit a) (ha0 : a ≠ 0) :
  ∃ i, irreducible i ∧ i ∣ a :=
(irreducible_or_factor a ha).elim (λ hai, ⟨a, hai, dvd_refl _⟩)
  (well_founded.fix
    wf_dvd_monoid.well_founded_dvd_not_unit
    (λ a ih ha ha0 ⟨x, y, hx, hy, hxy⟩,
      have hx0 : x ≠ 0, from λ hx0, ha0 (by rw [← hxy, hx0, zero_mul]),
      (irreducible_or_factor x hx).elim
        (λ hxi, ⟨x, hxi, hxy ▸ by simp⟩)
        (λ hxf, let ⟨i, hi⟩ := ih x ⟨hx0, y, hy, hxy.symm⟩ hx hx0 hxf in
          ⟨i, hi.1, dvd.trans hi.2 (hxy ▸ by simp)⟩)) a ha ha0)

@[elab_as_eliminator] lemma induction_on_irreducible {P : α → Prop} (a : α)
  (h0 : P 0) (hu : ∀ u : α, is_unit u → P u)
  (hi : ∀ a i : α, a ≠ 0 → irreducible i → P a → P (i * a)) :
  P a :=
by haveI := classical.dec; exact
well_founded.fix wf_dvd_monoid.well_founded_dvd_not_unit
  (λ a ih, if ha0 : a = 0 then ha0.symm ▸ h0
    else if hau : is_unit a then hu a hau
    else let ⟨i, hii, ⟨b, hb⟩⟩ := exists_irreducible_factor hau ha0 in
      have hb0 : b ≠ 0, from λ hb0, by simp * at *,
      hb.symm ▸ hi _ _ hb0 hii (ih _ ⟨hb0, i,
        hii.1, by rw [hb, mul_comm]⟩))
  a

lemma exists_factors (a : α) : a ≠ 0 →
  ∃f : multiset α, (∀b ∈ f, irreducible b) ∧ associated a f.prod :=
wf_dvd_monoid.induction_on_irreducible a
  (λ h, (h rfl).elim)
  (λ u hu _, ⟨0, by simp [associated_one_iff_is_unit, hu]⟩)
  (λ a i ha0 hii ih hia0,
    let ⟨s, hs⟩ := ih ha0 in
    ⟨i::s, ⟨by clear _let_match; finish,
      by { rw multiset.prod_cons,
           exact associated_mul_mul (by refl) hs.2 }⟩⟩)

end wf_dvd_monoid

theorem wf_dvd_monoid.of_well_founded_associates [comm_cancel_monoid_with_zero α]
  (h : well_founded ((<) : associates α → associates α → Prop)) : wf_dvd_monoid α :=
wf_dvd_monoid.of_wf_dvd_monoid_associates ⟨by { convert h, ext, exact associates.dvd_not_unit_iff_lt }⟩

theorem wf_dvd_monoid.iff_well_founded_associates [comm_cancel_monoid_with_zero α] :
  wf_dvd_monoid α ↔ well_founded ((<) : associates α → associates α → Prop) :=
⟨by apply wf_dvd_monoid.well_founded_associates, wf_dvd_monoid.of_well_founded_associates⟩
section prio
set_option default_priority 100 -- see Note [default priority]
/-- unique factorization monoids.

These are defined as `comm_cancel_monoid_with_zero`s with the descending chain condition on
the divisibility relation, but this is equivalent to more familiar definitions:

Each element (except zero) is uniquely represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

Each element (except zero) is non-uniquely represented as a multiset
of prime factors.

To define a UFD using the definition in terms of multisets
of irreducible factors, use the definition `of_unique_irreducible_factorization`

To define a UFD using the definition in terms of multisets
of prime factors, use the definition `of_exists_prime_factorization`

-/
class unique_factorization_monoid (α : Type*) [comm_cancel_monoid_with_zero α] extends wf_dvd_monoid α :
  Prop :=
(irreducible_iff_prime : ∀ {a : α}, irreducible a ↔ prime a )


instance ufm_of_gcd_of_wf_dvd_monoid [nontrivial α] [comm_cancel_monoid_with_zero α]
  [wf_dvd_monoid α] [gcd_monoid α] : unique_factorization_monoid α :=
{ irreducible_iff_prime := λ _, gcd_monoid.irreducible_iff_prime
  .. ‹wf_dvd_monoid α› }

instance associates.ufm [nontrivial α] [comm_cancel_monoid_with_zero α]
  [unique_factorization_monoid α] : unique_factorization_monoid (associates α) :=
{ irreducible_iff_prime := by { rw ← associates.irreducible_iff_prime_iff,
    apply unique_factorization_monoid.irreducible_iff_prime, }
  .. (wf_dvd_monoid.wf_dvd_monoid_associates : wf_dvd_monoid (associates α)) }

end prio

namespace unique_factorization_monoid
variables [comm_cancel_monoid_with_zero α] [unique_factorization_monoid α]

theorem exists_prime_factors (a : α) : a ≠ 0 →
  ∃ f : multiset α, (∀b ∈ f, prime b) ∧ a ~ᵤ f.prod :=
by { simp_rw ← unique_factorization_monoid.irreducible_iff_prime, apply wf_dvd_monoid.exists_factors a, }

@[elab_as_eliminator] lemma induction_on_prime {P : α → Prop}
  (a : α) (h₁ : P 0) (h₂ : ∀ x : α, is_unit x → P x)
  (h₃ : ∀ a p : α, a ≠ 0 → prime p → P a → P (p * a)) : P a :=
begin
  simp_rw ← unique_factorization_monoid.irreducible_iff_prime at h₃,
  exact wf_dvd_monoid.induction_on_irreducible a h₁ h₂ h₃,
end

lemma factors_unique : ∀{f g : multiset α},
  (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod ~ᵤ g.prod →
  multiset.rel associated f g :=
by haveI := classical.dec_eq α; exact
λ f, multiset.induction_on f
  (λ g _ hg h,
    multiset.rel_zero_left.2 $
      multiset.eq_zero_of_forall_not_mem (λ x hx,
        have is_unit g.prod, by simpa [associated_one_iff_is_unit] using h.symm,
        (hg x hx).1 (is_unit_iff_dvd_one.2 (dvd.trans (multiset.dvd_prod hx)
          (is_unit_iff_dvd_one.1 this)))))
  (λ p f ih g hf hg hfg,
    let ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod
      (irreducible_iff_prime.1 (hf p (by simp)))
      (λ q hq, irreducible_iff_prime.1 (hg _ hq)) $
        (dvd_iff_dvd_of_rel_right hfg).1
          (show p ∣ (p :: f).prod, by simp) in
    begin
      rw ← multiset.cons_erase hbg,
      exact multiset.rel.cons hb (ih (λ q hq, hf _ (by simp [hq]))
        (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq))
        (associated_mul_left_cancel
          (by rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg]) hb
        (hf p (by simp)).ne_zero))
    end)

end unique_factorization_monoid

lemma prime_factors_unique [comm_cancel_monoid_with_zero α] : ∀{f g : multiset α},
  (∀x∈f, prime x) → (∀x∈g, prime x) → f.prod ~ᵤ g.prod →
  multiset.rel associated f g :=
by haveI := classical.dec_eq α; exact
λ f, multiset.induction_on f
  (λ g _ hg h,
    multiset.rel_zero_left.2 $
      multiset.eq_zero_of_forall_not_mem (λ x hx,
        have is_unit g.prod, by simpa [associated_one_iff_is_unit] using h.symm,
        (irreducible_of_prime $ hg x hx).1 (is_unit_iff_dvd_one.2 (dvd.trans (multiset.dvd_prod hx)
          (is_unit_iff_dvd_one.1 this)))))
  (λ p f ih g hf hg hfg,
    let ⟨b, hbg, hb⟩ := exists_associated_mem_of_dvd_prod
      (hf p (by simp)) (λ q hq, hg _ hq) $
        (dvd_iff_dvd_of_rel_right hfg).1
          (show p ∣ (p :: f).prod, by simp) in
    begin
      rw ← multiset.cons_erase hbg,
      exact multiset.rel.cons hb (ih (λ q hq, hf _ (by simp [hq]))
        (λ q (hq : q ∈ g.erase b), hg q (multiset.mem_of_mem_erase hq))
        (associated_mul_left_cancel
          (by rwa [← multiset.prod_cons, ← multiset.prod_cons, multiset.cons_erase hbg]) hb
        (hf p (by simp)).ne_zero))
    end)

lemma prime_factors_irreducible [comm_cancel_monoid_with_zero α] {a : α} {f : multiset α}
  (ha : irreducible a) (pfa : (∀b ∈ f, prime b) ∧ a ~ᵤ f.prod) :
  ∃ p, a ~ᵤ p ∧ f = p :: 0 :=
by haveI := classical.dec_eq α; exact
multiset.induction_on f
  (λ h, (ha.1 (associated_one_iff_is_unit.1 h)).elim)
  (λ p s _ hp hs, let ⟨u, hu⟩ := hp in ⟨p,
    have hs0 : s = 0, from classical.by_contradiction
      (λ hs0, let ⟨q, hq⟩ := multiset.exists_mem_of_ne_zero hs0 in
       (hs q (by simp [hq])).2.1 $
        (ha.2 ((p * ↑(u⁻¹)) * (s.erase q).prod) _
          (by {rw [mul_right_comm _ _ q, mul_assoc, ← multiset.prod_cons, multiset.cons_erase hq,
            mul_comm p _, mul_assoc, ← multiset.prod_cons, hu.symm, mul_comm, mul_assoc],
            simp, })).resolve_left $
              mt is_unit_of_mul_is_unit_left $ mt is_unit_of_mul_is_unit_left
                (hs p (multiset.mem_cons_self _ _)).2.1),
    ⟨(by {clear _let_match; simp * at *}), hs0 ▸ rfl⟩⟩)
  (pfa.2) (pfa.1)

section exists_prime_factors

variables [comm_cancel_monoid_with_zero α]
  (pf : ∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, prime b) ∧ a ~ᵤ f.prod)

include pf

lemma wf_dvd_monoid_of_exists_prime_factors : wf_dvd_monoid α :=
⟨begin
    classical,
    apply rel_hom.well_founded (rel_hom.mk _ _) (with_top.well_founded_lt nat.lt_wf),
    { intro a, by_cases a = 0, exact ⊤, exact (classical.some (pf a h)).card, },
    { intros a b hab, rw dif_neg hab.1, by_cases b = 0, { simp [h, lt_top_iff_ne_top], },
      rw [dif_neg h, with_top.coe_lt_coe],
      cases hab.2 with c hc, have cne0 : c ≠ 0, { intro con, apply h, rw [hc.2, con, mul_zero], },
      rw hc.2 at hab, apply lt_of_lt_of_le,
      apply lt_add_of_pos_right, rw multiset.card_pos, swap, exact (classical.some (pf c cne0)),
      { intro con, apply hc.1, rw is_unit_iff_of_associated, apply is_unit_one,
        convert (classical.some_spec (pf c cne0)).2, simp [con], },
      rw ← multiset.card_add,
      apply le_of_eq (multiset.card_eq_card_of_rel (prime_factors_unique _ (classical.some_spec (pf _ h)).1 _)),
      { intros x hadd, rw multiset.mem_add at hadd,
        cases hadd; apply (classical.some_spec (pf _ _)).1 _ hadd, },
      { rw multiset.prod_add, transitivity a * c,
        { apply associated_mul_mul; apply (classical.some_spec (pf _ _)).2.symm, },
        { rw ← hc.2, apply (classical.some_spec (pf _ _)).2, } } },
end⟩

lemma irreducible_iff_prime_of_exists_prime_factors {p : α} : irreducible p ↔ prime p :=
by letI := classical.dec_eq α; exact
if hp0 : p = 0 then by simp [hp0]
else
  ⟨λ h, begin
    cases pf p hp0 with f hf, cases prime_factors_irreducible h hf with q hq,
    rw prime_iff_of_associated hq.1, apply hf.1 q, rw hq.2, simp,
  end,
    irreducible_of_prime⟩

theorem unique_factorization_monoid_of_exists_prime_factors :
  unique_factorization_monoid α :=
{ irreducible_iff_prime := λ _, irreducible_iff_prime_of_exists_prime_factors pf,
  .. wf_dvd_monoid_of_exists_prime_factors pf }

end exists_prime_factors

theorem unique_factorization_monoid_iff_exists_prime_factors [comm_cancel_monoid_with_zero α] :
  unique_factorization_monoid α ↔
    (∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, prime b) ∧ a ~ᵤ f.prod) :=
⟨λ h, @unique_factorization_monoid.exists_prime_factors _ _ h,
  unique_factorization_monoid_of_exists_prime_factors⟩

theorem irreducible_iff_prime_of_exists_unique_irreducible_factors [comm_cancel_monoid_with_zero α]
  (eif : ∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, irreducible b) ∧ a ~ᵤ f.prod)
  (uif : ∀ (f g : multiset α),
  (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod ~ᵤ g.prod → multiset.rel associated f g) :
  ∀ (p : α), irreducible p ↔ prime p :=
λ p, ⟨by letI := classical.dec_eq α; exact λ hpi,
    ⟨hpi.ne_zero, hpi.1,
      λ a b ⟨x, hx⟩,
      if hab0 : a * b = 0
      then (eq_zero_or_eq_zero_of_mul_eq_zero hab0).elim
        (λ ha0, by simp [ha0])
        (λ hb0, by simp [hb0])
      else
        have hx0 : x ≠ 0, from λ hx0, by simp * at *,
        have ha0 : a ≠ 0, from left_ne_zero_of_mul hab0,
        have hb0 : b ≠ 0, from right_ne_zero_of_mul hab0,
        begin
          cases eif x hx0 with fx hfx,
          cases eif a ha0 with fa hfa,
          cases eif b hb0 with fb hfb,
          have h : multiset.rel associated (p :: fx) (fa + fb),
          { apply uif,
            { exact λ i hi, (multiset.mem_cons.1 hi).elim (λ hip, hip.symm ▸ hpi) (hfx.1 _), },
            { exact λ i hi, (multiset.mem_add.1 hi).elim (hfa.1 _) (hfb.1 _), },
            calc multiset.prod (p :: fx)
                  ~ᵤ a * b : by rw [hx, multiset.prod_cons];
                    exact associated_mul_mul (by refl)
                      (hfx.2.symm)
              ... ~ᵤ (fa).prod * (fb).prod :
                associated_mul_mul hfa.2 hfb.2
              ... = _ : by rw multiset.prod_add, },
          exact let ⟨q, hqf, hq⟩ := multiset.exists_mem_of_rel_of_mem h
          (multiset.mem_cons_self p _) in
        (multiset.mem_add.1 hqf).elim
          (λ hqa, or.inl $ (dvd_iff_dvd_of_rel_left hq).2 $
            (dvd_iff_dvd_of_rel_right hfa.2.symm).1
              (multiset.dvd_prod hqa))
          (λ hqb, or.inr $ (dvd_iff_dvd_of_rel_left hq).2 $
            (dvd_iff_dvd_of_rel_right hfb.2.symm).1
              (multiset.dvd_prod hqb))
        end⟩, irreducible_of_prime⟩

theorem unique_factorization_monoid.of_exists_unique_irreducible_factors
  [comm_cancel_monoid_with_zero α]
  (eif : ∀ (a : α), a ≠ 0 → ∃ f : multiset α, (∀b ∈ f, irreducible b) ∧ a ~ᵤ f.prod)
  (uif : ∀ (f g : multiset α),
  (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod ~ᵤ g.prod → multiset.rel associated f g) :
  unique_factorization_monoid α :=
unique_factorization_monoid_of_exists_prime_factors (by {
  convert eif,
  simp_rw irreducible_iff_prime_of_exists_unique_irreducible_factors eif uif,
})

namespace unique_factorization_monoid
variables [comm_cancel_monoid_with_zero α] [decidable_eq α] [nontrivial α] [normalization_monoid α]
  [unique_factorization_monoid α]

/-- Noncomputably determines the multiset of prime factors -/
noncomputable def factors (a : α) : multiset α := if h : a = 0 then 0 else
multiset.map normalize $ classical.some (unique_factorization_monoid.exists_prime_factors a h)

theorem factors_prod {a : α} (ane0 : a ≠ 0) : associated (factors a).prod a :=
begin
  rw [factors, dif_neg ane0],
  transitivity, swap,
  { exact (classical.some_spec (unique_factorization_monoid.exists_prime_factors a ane0)).2.symm },
  { rw [← associates.mk_eq_mk_iff_associated, ← associates.prod_mk, ← associates.prod_mk,
    multiset.map_map],
    refine congr rfl (congr (congr rfl _) rfl), ext,
    rw [function.comp_apply, associates.mk_eq_mk_iff_associated], apply normalize_associated },
end

theorem prime_factors {a : α} : ∀ (x : α), x ∈ factors a → prime x :=
begin
  rw [factors],
  by_cases ane0 : a = 0, {simp [ane0]},
  rw dif_neg ane0,
  intros x hx, rcases multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩,
  rw prime_iff_of_associated (normalize_associated),
  exact (classical.some_spec (unique_factorization_monoid.exists_prime_factors a ane0)).1 y hy,
end

theorem irreducible_factors {a : α} : ∀ (x : α), x ∈ factors a → irreducible x :=
λ x h, irreducible_of_prime (prime_factors x h)

theorem normalize_factors {a : α} : ∀ (x : α), x ∈ factors a → normalize x = x :=
begin
  rw [factors],
  by_cases a = 0, {simp [h]}, rw dif_neg h,
  intros x hx, rcases multiset.mem_map.1 hx with ⟨y, ⟨hy, rfl⟩⟩,
  apply normalize_idem,
end

lemma factors_irreducible {a : α} (ha : irreducible a) :
  factors a = normalize a :: 0 :=
begin
  cases prime_factors_irreducible ha ⟨prime_factors, (factors_prod ha.ne_zero).symm⟩ with p hp,
  convert hp.2, rw [← normalize_factors p, normalize_eq_normalize_iff, dvd_dvd_iff_associated],
  {apply hp.1}, rw hp.2, simp,
end

lemma exists_mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) : p ∣ a →
  ∃ q ∈ factors a, p ~ᵤ q :=
λ ⟨b, hb⟩,
have hb0 : b ≠ 0, from λ hb0, by simp * at *,
have multiset.rel associated (p :: factors b) (factors a),
  from factors_unique
    (λ x hx, (multiset.mem_cons.1 hx).elim (λ h, h.symm ▸ hp)
      (irreducible_factors _))
    irreducible_factors
    (associated.symm $ calc multiset.prod (factors a) ~ᵤ a : factors_prod ha0
      ... = p * b : hb
      ... ~ᵤ multiset.prod (p :: factors b) :
        by rw multiset.prod_cons; exact associated_mul_mul
          (associated.refl _)
          (associated.symm (factors_prod hb0))),
multiset.exists_mem_of_rel_of_mem this (by simp)

end unique_factorization_monoid

namespace unique_factorization_monoid

variables {R : Type*} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R]

lemma no_factors_of_no_prime_factors {a b : R} (ha : a ≠ 0)
  (h : (∀ {d}, d ∣ a → d ∣ b → ¬ prime d)) : ∀ {d}, d ∣ a → d ∣ b → is_unit d :=
λ d, induction_on_prime d
  (by { simp only [zero_dvd_iff], intros, contradiction })
  (λ x hx _ _, hx)
  (λ d q hp hq ih dvd_a dvd_b,
    absurd hq (h (dvd_of_mul_right_dvd dvd_a) (dvd_of_mul_right_dvd dvd_b)))

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `c` have no common prime factors, `a ∣ b`.
Compare `is_coprime.dvd_of_dvd_mul_left`. -/
lemma dvd_of_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a ≠ 0) :
  (∀ {d}, d ∣ a → d ∣ c → ¬ prime d) → a ∣ b * c → a ∣ b :=
begin
  refine induction_on_prime c _ _ _,
  { intro no_factors,
    simp only [dvd_zero, mul_zero, forall_prop_of_true],
    haveI := classical.prop_decidable,
    exact is_unit_iff_forall_dvd.mp
      (no_factors_of_no_prime_factors ha @no_factors (dvd_refl a) (dvd_zero a)) _ },
  { rintros _ ⟨x, rfl⟩ _ a_dvd_bx,
    apply units.dvd_mul_right.mp a_dvd_bx },
  { intros c p hc hp ih no_factors a_dvd_bpc,
    apply ih (λ q dvd_a dvd_c hq, no_factors dvd_a (dvd_mul_of_dvd_right dvd_c _) hq),
    rw mul_left_comm at a_dvd_bpc,
    refine or.resolve_left (left_dvd_or_dvd_right_of_dvd_prime_mul hp a_dvd_bpc) (λ h, _),
    exact no_factors h (dvd_mul_right p c) hp }
end

/-- Euclid's lemma: if `a ∣ b * c` and `a` and `b` have no common prime factors, `a ∣ c`.
Compare `is_coprime.dvd_of_dvd_mul_right`. -/
lemma dvd_of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a ≠ 0)
  (no_factors : ∀ {d}, d ∣ a → d ∣ b → ¬ prime d) : a ∣ b * c → a ∣ c :=
by simpa [mul_comm b c] using dvd_of_dvd_mul_left_of_no_prime_factors ha @no_factors

/-- If `a ≠ 0, b` are elements of a unique factorization domain, then dividing
out their common factor `c'` gives `a'` and `b'` with no factors in common. -/
lemma exists_reduced_factors : ∀ (a ≠ (0 : R)) b,
  ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → is_unit d) ∧ c' * a' = a ∧ c' * b' = b :=
begin
  haveI := classical.prop_decidable,
  intros a,
  refine induction_on_prime a _ _ _,
  { intros, contradiction },
  { intros a a_unit a_ne_zero b,
    use [a, b, 1],
    split,
    { intros p p_dvd_a _,
      exact is_unit_of_dvd_unit p_dvd_a a_unit },
    { simp } },
  { intros a p a_ne_zero p_prime ih_a pa_ne_zero b,
    by_cases p ∣ b,
    { rcases h with ⟨b, rfl⟩,
      obtain ⟨a', b', c', no_factor, ha', hb'⟩ := ih_a a_ne_zero b,
      refine ⟨a', b', p * c', @no_factor, _, _⟩,
      { rw [mul_assoc, ha'] },
      { rw [mul_assoc, hb'] } },
    { obtain ⟨a', b', c', coprime, rfl, rfl⟩ := ih_a a_ne_zero b,
      refine ⟨p * a', b', c', _, mul_left_comm _ _ _, rfl⟩,
      intros q q_dvd_pa' q_dvd_b',
      cases left_dvd_or_dvd_right_of_dvd_prime_mul p_prime q_dvd_pa' with p_dvd_q q_dvd_a',
      { have : p ∣ c' * b' := dvd_mul_of_dvd_right (dvd_trans p_dvd_q q_dvd_b') _,
        contradiction },
      exact coprime q_dvd_a' q_dvd_b'  } }
end

lemma exists_reduced_factors' (a b : R) (hb : b ≠ 0) :
  ∃ a' b' c', (∀ {d}, d ∣ a' → d ∣ b' → is_unit d) ∧ c' * a' = a ∧ c' * b' = b :=
let ⟨b', a', c', no_factor, hb, ha⟩ := exists_reduced_factors b hb a
in ⟨a', b', c', λ _ hpb hpa, no_factor hpa hpb, ha, hb⟩

end unique_factorization_monoid


namespace associates
open unique_factorization_monoid associated multiset
variables [comm_cancel_monoid_with_zero α] [nontrivial α]

/-- `factor_set α` representation elements of unique factorization domain as multisets.
`multiset α` produced by `factors` are only unique up to associated elements, while the multisets in
`factor_set α` are unqiue by equality and restricted to irreducible elements. This gives us a
representation of each element as a unique multisets (or the added ⊤ for 0), which has a complete
lattice struture. Infimum is the greatest common divisor and supremum is the least common multiple.
-/
@[reducible] def {u} factor_set (α : Type u) [comm_cancel_monoid_with_zero α] [nontrivial α] :
  Type u :=
with_top (multiset { a : associates α // irreducible a })

local attribute [instance] associated.setoid

theorem factor_set.coe_add {a b : multiset { a : associates α // irreducible a }} :
  (↑(a + b) : factor_set α) = a + b :=
by norm_cast

lemma factor_set.sup_add_inf_eq_add [decidable_eq (associates α)] :
  ∀(a b : factor_set α), a ⊔ b + a ⊓ b = a + b
| none     b        := show ⊤ ⊔ b + ⊤ ⊓ b = ⊤ + b, by simp
| a        none     := show a ⊔ ⊤ + a ⊓ ⊤ = a + ⊤, by simp
| (some a) (some b) := show (a : factor_set α) ⊔ b + a ⊓ b = a + b, from
  begin
    rw [← with_top.coe_sup, ← with_top.coe_inf, ← with_top.coe_add, ← with_top.coe_add,
      with_top.coe_eq_coe],
    exact multiset.union_add_inter _ _
  end

def factor_set.prod : factor_set α → associates α
| none     := 0
| (some s) := (s.map coe).prod

@[simp] theorem prod_top : (⊤ : factor_set α).prod = 0 := rfl

@[simp] theorem prod_coe {s : multiset { a : associates α // irreducible a }} :
  (s : factor_set α).prod = (s.map coe).prod :=
rfl

@[simp] theorem prod_add : ∀(a b : factor_set α), (a + b).prod = a.prod * b.prod
| none b    := show (⊤ + b).prod = (⊤:factor_set α).prod * b.prod, by simp
| a    none := show (a + ⊤).prod = a.prod * (⊤:factor_set α).prod, by simp
| (some a) (some b) :=
  show (↑a + ↑b:factor_set α).prod = (↑a:factor_set α).prod * (↑b:factor_set α).prod,
    by rw [← factor_set.coe_add, prod_coe, prod_coe, prod_coe, multiset.map_add, multiset.prod_add]

theorem prod_mono : ∀{a b : factor_set α}, a ≤ b → a.prod ≤ b.prod
| none b h := have b = ⊤, from top_unique h, by rw [this, prod_top]; exact le_refl _
| a none h := show a.prod ≤ (⊤ : factor_set α).prod, by simp; exact le_top
| (some a) (some b) h := prod_le_prod $ multiset.map_le_map $ with_top.coe_le_coe.1 $ h

variable [unique_factorization_monoid α]

theorem unique' {p q : multiset (associates α)} :
  (∀a∈p, irreducible a) → (∀a∈q, irreducible a) → p.prod = q.prod → p = q :=
begin
  apply multiset.induction_on_multiset_quot p,
  apply multiset.induction_on_multiset_quot q,
  assume s t hs ht eq,
  refine multiset.map_mk_eq_map_mk_of_rel (unique_factorization_monoid.factors_unique _ _ _),
  { exact assume a ha, ((irreducible_mk _).1 $ hs _ $ multiset.mem_map_of_mem _ ha) },
  { exact assume a ha, ((irreducible_mk _).1 $ ht _ $ multiset.mem_map_of_mem _ ha) },
  simpa [quot_mk_eq_mk, prod_mk, mk_eq_mk_iff_associated] using eq
end

variables [decidable_eq α] [normalization_monoid α]

private theorem forall_map_mk_factors_irreducible (x : α) (hx : x ≠ 0) :
  ∀(a : associates α), a ∈ multiset.map associates.mk (factors x) → irreducible a :=
begin
  assume a ha,
  rcases multiset.mem_map.1 ha with ⟨c, hc, rfl⟩,
  exact (irreducible_mk c).2 (irreducible_factors _ hc)
end

theorem prod_le_prod_iff_le {p q : multiset (associates α)}
  (hp : ∀a∈p, irreducible a) (hq : ∀a∈q, irreducible a) :
  p.prod ≤ q.prod ↔ p ≤ q :=
iff.intro
  begin
    rintros ⟨⟨c⟩, eqc⟩,
    have : c ≠ 0, from (mt mk_eq_zero.2 $
      assume (hc : quot.mk setoid.r c = 0),
      have (0 : associates α) ∈ q, from prod_eq_zero_iff.1 $ eqc.symm ▸ hc.symm ▸ mul_zero _,
      not_irreducible_zero ((irreducible_mk 0).1 $ hq _ this)),
    have : associates.mk (factors c).prod = quot.mk setoid.r c,
      from mk_eq_mk_iff_associated.2 (factors_prod this),

    refine multiset.le_iff_exists_add.2 ⟨(factors c).map associates.mk, unique' hq _ _⟩,
    { assume x hx,
      rcases multiset.mem_add.1 hx with h | h,
      exact hp x h,
      exact forall_map_mk_factors_irreducible c ‹c ≠ 0› _ h },
    { simp [multiset.prod_add, prod_mk, *] at * }
  end
  prod_le_prod

noncomputable def factors' (a : α) (ha : a ≠ 0) : multiset { a : associates α // irreducible a } :=
(factors a).pmap (λa ha, ⟨associates.mk a, (irreducible_mk _).2 ha⟩)
  (irreducible_factors)

@[simp] theorem map_subtype_coe_factors' {a : α} (ha : a ≠ 0) :
  (factors' a ha).map coe = (factors a).map associates.mk :=
by simp [factors', multiset.map_pmap, multiset.pmap_eq_map]

theorem factors'_cong {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) (h : a ~ᵤ b) :
  factors' a ha = factors' b hb :=
have multiset.rel associated (factors a) (factors b), from
  factors_unique irreducible_factors irreducible_factors
    ((factors_prod ha).trans $ h.trans $ (factors_prod hb).symm),
by simpa [(multiset.map_eq_map subtype.coe_injective).symm, rel_associated_iff_map_eq_map.symm]

variable [dec : decidable_eq (associates α)]
include dec

noncomputable def factors (a : associates α) : factor_set α :=
begin
  refine (if h : a = 0 then ⊤ else
    quotient.hrec_on a (λx h, some $ factors' x (mt mk_eq_zero.2 h)) _ h),

  assume a b hab,
  apply function.hfunext,
  { have : a ~ᵤ 0 ↔ b ~ᵤ 0, from
      iff.intro (assume ha0, hab.symm.trans ha0) (assume hb0, hab.trans hb0),
    simp only [associated_zero_iff_eq_zero] at this,
    simp only [quotient_mk_eq_mk, this, mk_eq_zero] },
  exact (assume ha hb eq, heq_of_eq $ congr_arg some $ factors'_cong _ _ hab)
end

@[simp] theorem factors_0 : (0 : associates α).factors = ⊤ :=
dif_pos rfl

@[simp] theorem factors_mk (a : α) (h : a ≠ 0) : (associates.mk a).factors = factors' a h :=
dif_neg (mt mk_eq_zero.1 h)

theorem prod_factors : ∀(s : factor_set α), s.prod.factors = s
| none     := by simp [factor_set.prod]; refl
| (some s) :=
  begin
    unfold factor_set.prod,
    generalize eq_a : (s.map coe).prod = a,
    rcases a with ⟨a⟩,
    rw quot_mk_eq_mk at *,

    have : (s.map (coe : _ → associates α)).prod ≠ 0, from assume ha,
      let ⟨⟨a, ha⟩, h, eq⟩ := multiset.mem_map.1 (prod_eq_zero_iff.1 ha) in
      have irreducible (0 : associates α), from eq ▸ ha,
      not_irreducible_zero ((irreducible_mk _).1 this),
    have ha : a ≠ 0, by simp [*] at *,
    suffices : (unique_factorization_monoid.factors a).map associates.mk = s.map coe,
    { rw [factors_mk a ha],
      apply congr_arg some _,
      simpa [(multiset.map_eq_map subtype.coe_injective).symm] },

    refine unique'
      (forall_map_mk_factors_irreducible _ ha)
      (assume a ha, let ⟨⟨x, hx⟩, ha, eq⟩ := multiset.mem_map.1 ha in eq ▸ hx)
      _,
    rw [prod_mk, eq_a, mk_eq_mk_iff_associated],
    exact factors_prod ha
  end

theorem factors_prod (a : associates α) : a.factors.prod = a :=
quotient.induction_on a $ assume a, decidable.by_cases
  (assume : associates.mk a = 0, by simp [quotient_mk_eq_mk, this])
  (assume : associates.mk a ≠ 0,
    have a ≠ 0, by simp * at *,
    by simp [this, quotient_mk_eq_mk, prod_mk, mk_eq_mk_iff_associated.2 (factors_prod this)])

theorem eq_of_factors_eq_factors {a b : associates α} (h : a.factors = b.factors) : a = b :=
have a.factors.prod = b.factors.prod, by rw h,
by rwa [factors_prod, factors_prod] at this

omit dec

theorem eq_of_prod_eq_prod {a b : factor_set α} (h : a.prod = b.prod) : a = b :=
begin
  classical,
  have : a.prod.factors = b.prod.factors, by rw h,
  rwa [prod_factors, prod_factors] at this
end

include dec


@[simp] theorem factors_mul (a b : associates α) : (a * b).factors = a.factors + b.factors :=
eq_of_prod_eq_prod $ eq_of_factors_eq_factors $
  by rw [prod_add, factors_prod, factors_prod, factors_prod]

theorem factors_mono : ∀{a b : associates α}, a ≤ b → a.factors ≤ b.factors
| s t ⟨d, rfl⟩ := by rw [factors_mul] ; exact le_add_of_nonneg_right bot_le

theorem factors_le {a b : associates α} : a.factors ≤ b.factors ↔ a ≤ b :=
iff.intro
  (assume h, have a.factors.prod ≤ b.factors.prod, from prod_mono h,
    by rwa [factors_prod, factors_prod] at this)
  factors_mono

omit dec

theorem prod_le {a b : factor_set α} : a.prod ≤ b.prod ↔ a ≤ b :=
begin
  classical,
  exact iff.intro
  (assume h, have a.prod.factors ≤ b.prod.factors, from factors_mono h,
    by rwa [prod_factors, prod_factors] at this)
  prod_mono
end

include dec

noncomputable instance : has_sup (associates α) := ⟨λa b, (a.factors ⊔ b.factors).prod⟩
noncomputable instance : has_inf (associates α) := ⟨λa b, (a.factors ⊓ b.factors).prod⟩

noncomputable instance : bounded_lattice (associates α) :=
{ sup          := (⊔),
  inf          := (⊓),
  sup_le       :=
    assume a b c hac hbc, factors_prod c ▸ prod_mono (sup_le (factors_mono hac) (factors_mono hbc)),
  le_sup_left  := assume a b,
    le_trans (le_of_eq (factors_prod a).symm) $ prod_mono $ le_sup_left,
  le_sup_right := assume a b,
    le_trans (le_of_eq (factors_prod b).symm) $ prod_mono $ le_sup_right,
  le_inf :=
    assume a b c hac hbc, factors_prod a ▸ prod_mono (le_inf (factors_mono hac) (factors_mono hbc)),
  inf_le_left  := assume a b,
    le_trans (prod_mono inf_le_left) (le_of_eq (factors_prod a)),
  inf_le_right := assume a b,
    le_trans (prod_mono inf_le_right) (le_of_eq (factors_prod b)),
  .. associates.partial_order,
  .. associates.order_top,
  .. associates.order_bot }

lemma sup_mul_inf (a b : associates α) : (a ⊔ b) * (a ⊓ b) = a * b :=
show (a.factors ⊔ b.factors).prod * (a.factors ⊓ b.factors).prod = a * b,
begin
  refine eq_of_factors_eq_factors _,
  rw [← prod_add, prod_factors, factors_mul, factor_set.sup_add_inf_eq_add]
end

end associates

section
open associates unique_factorization_monoid

/-- `to_gcd_monoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain. -/
noncomputable def unique_factorization_monoid.to_gcd_monoid
  (α : Type*) [integral_domain α] [unique_factorization_monoid α] [normalization_monoid α]
  [decidable_eq (associates α)] [decidable_eq α] : gcd_monoid α :=
{ gcd := λa b, (associates.mk a ⊓ associates.mk b).out,
  lcm := λa b, (associates.mk a ⊔ associates.mk b).out,
  gcd_dvd_left := assume a b, (out_dvd_iff a (associates.mk a ⊓ associates.mk b)).2 $ inf_le_left,
  gcd_dvd_right := assume a b, (out_dvd_iff b (associates.mk a ⊓ associates.mk b)).2 $ inf_le_right,
  dvd_gcd := assume a b c hac hab, show a ∣ (associates.mk c ⊓ associates.mk b).out,
    by rw [dvd_out_iff, le_inf_iff, mk_le_mk_iff_dvd_iff, mk_le_mk_iff_dvd_iff]; exact ⟨hac, hab⟩,
  lcm_zero_left := assume a, show (⊤ ⊔ associates.mk a).out = 0, by simp,
  lcm_zero_right := assume a, show (associates.mk a ⊔ ⊤).out = 0, by simp,
  gcd_mul_lcm := assume a b,
    show (associates.mk a ⊓ associates.mk b).out * (associates.mk a ⊔ associates.mk b).out =
      normalize (a * b),
    by rw [← out_mk, ← out_mul, mul_comm, sup_mul_inf]; refl,
  normalize_gcd := assume a b, by convert normalize_out _,
  .. ‹normalization_monoid α› }

end
