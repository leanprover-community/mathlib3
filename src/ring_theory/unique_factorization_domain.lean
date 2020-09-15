/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker

Theory of unique factorization domains.

@TODO: setup the complete lattice structure on `factor_set`.
-/
import algebra.gcd_monoid
import ring_theory.integral_domain

variables {α : Type*}
local infix ` ~ᵤ ` : 50 := associated

/-- Unique factorization domains.

In a unique factorization domain each element (except zero) is uniquely
represented as a multiset of irreducible factors.
Uniqueness is only up to associated elements.

This is equivalent to defining a unique factorization domain as a domain in
which each element (except zero) is non-uniquely represented as a multiset
of prime factors. This definition is used.

To define a UFD using the traditional definition in terms of multisets
of irreducible factors, use the definition `of_unique_irreducible_factorization`

-/
class unique_factorization_domain (α : Type*) [integral_domain α] :=
(factors : α → multiset α)
(factors_prod : ∀{a : α}, a ≠ 0 → (factors a).prod ~ᵤ a)
(prime_factors : ∀{a : α}, a ≠ 0 → ∀x∈factors a, prime x)

namespace unique_factorization_domain

variables [integral_domain α] [unique_factorization_domain α]

@[elab_as_eliminator] lemma induction_on_prime {P : α → Prop}
  (a : α) (h₁ : P 0) (h₂ : ∀ x : α, is_unit x → P x)
  (h₃ : ∀ a p : α, a ≠ 0 → prime p → P a → P (p * a)) : P a :=
by haveI := classical.dec_eq α; exact
if ha0 : a = 0 then ha0.symm ▸ h₁
else @multiset.induction_on _
  (λ s : multiset α, ∀ (a : α), a ≠ 0 → s.prod ~ᵤ a → (∀ p ∈ s, prime p) →  P a)
  (factors a)
  (λ _ _ h _, h₂ _ ((is_unit_iff_of_associated h.symm).2 is_unit_one))
  (λ p s ih a ha0 ⟨u, hu⟩ hsp,
    have ha : a = (p * u) * s.prod, by simp [hu.symm, mul_comm, mul_assoc],
    have hs0 : s.prod ≠ 0, from λ _ : s.prod = 0, by simp * at *,
    ha.symm ▸ h₃ _ _ hs0
      (prime_of_associated ⟨u, rfl⟩ (hsp p (multiset.mem_cons_self _ _)))
      (ih _ hs0 (by refl) (λ p hp, hsp p (multiset.mem_cons.2 (or.inr hp)))))
  _
  ha0
  (factors_prod ha0)
  (prime_factors ha0)

lemma factors_irreducible {a : α} (ha : irreducible a) :
  ∃ p, a ~ᵤ p ∧ factors a = p :: 0 :=
by haveI := classical.dec_eq α; exact
multiset.induction_on (factors a)
  (λ h, (ha.1 (associated_one_iff_is_unit.1 h.symm)).elim)
  (λ p s _ hp hs, let ⟨u, hu⟩ := hp in ⟨p,
    have hs0 : s = 0, from classical.by_contradiction
      (λ hs0, let ⟨q, hq⟩ := multiset.exists_mem_of_ne_zero hs0 in
       (hs q (by simp [hq])).2.1 $
        (ha.2 ((p * u) * (s.erase q).prod) _
          (by rw [mul_right_comm _ _ q, mul_assoc, ← multiset.prod_cons,
            multiset.cons_erase hq]; simp [hu.symm, mul_comm, mul_assoc])).resolve_left $
              mt is_unit_of_mul_is_unit_left $ mt is_unit_of_mul_is_unit_left
                (hs p (multiset.mem_cons_self _ _)).2.1),
    ⟨associated.symm (by clear _let_match; simp * at *), hs0 ▸ rfl⟩⟩)
  (factors_prod ha.ne_zero)
  (prime_factors ha.ne_zero)

lemma irreducible_iff_prime {p : α} : irreducible p ↔ prime p :=
by letI := classical.dec_eq α; exact
if hp0 : p = 0 then by simp [hp0]
else
  ⟨λ h, let ⟨q, hq⟩ := factors_irreducible h in
      have prime q, from hq.2 ▸ prime_factors hp0 _ (by simp [hq.2]),
      suffices prime (factors p).prod,
        from prime_of_associated (factors_prod hp0) this,
      hq.2.symm ▸ by simp [this],
    irreducible_of_prime⟩

lemma irreducible_factors : ∀{a : α}, a ≠ 0 → ∀x∈factors a, irreducible x :=
by simp only [irreducible_iff_prime]; exact @prime_factors _ _ _

lemma unique : ∀{f g : multiset α},
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

end unique_factorization_domain

/-- Definition of a UFD as an integral domain in which each non-zero element can be uniquely
represented by a multisets of irreducible factors. Uniqueness is only up to associated elements. -/
structure unique_irreducible_factorization (α : Type*) [integral_domain α] :=
(factors : α → multiset α)
(factors_prod : ∀{a : α}, a ≠ 0 → (factors a).prod ~ᵤ a)
(irreducible_factors : ∀{a : α}, a ≠ 0 →  ∀x∈factors a, irreducible x)
(unique : ∀{f g : multiset α},
  (∀x∈f, irreducible x) → (∀x∈g, irreducible x) → f.prod ~ᵤ g.prod → multiset.rel associated f g)

namespace unique_factorization_domain
open unique_factorization_domain associated
variables [integral_domain α] [unique_factorization_domain α]

lemma exists_mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) : p ∣ a →
  ∃ q ∈ factors a, p ~ᵤ q :=
λ ⟨b, hb⟩,
have hb0 : b ≠ 0, from λ hb0, by simp * at *,
have multiset.rel associated (p :: factors b) (factors a),
  from unique
    (λ x hx, (multiset.mem_cons.1 hx).elim (λ h, h.symm ▸ hp)
      (irreducible_factors hb0 _))
    (irreducible_factors ha0)
    (associated.symm $ calc multiset.prod (factors a) ~ᵤ a : factors_prod ha0
      ... = p * b : hb
      ... ~ᵤ multiset.prod (p :: factors b) :
        by rw multiset.prod_cons; exact associated_mul_mul
          (associated.refl _)
          (associated.symm (factors_prod hb0))),
multiset.exists_mem_of_rel_of_mem this (by simp)

/-- Go from unique factorization defined in terms of non-unique multisets of prime factors to the
more traditional definition in terms of unique (up to association) multisets of irreducible factors.
-/
def of_unique_irreducible_factorization {α : Type*} [integral_domain α]
  (o : unique_irreducible_factorization α) : unique_factorization_domain α :=
{ prime_factors := by letI := classical.dec_eq α; exact λ a h p (hpa : p ∈ o.factors a),
    have hpi : irreducible p, from o.irreducible_factors h _ hpa,
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
        have multiset.rel associated  (p :: o.factors x) (o.factors a + o.factors b),
          from o.unique
            (λ i hi, (multiset.mem_cons.1 hi).elim
              (λ hip, hip.symm ▸ hpi)
              (o.irreducible_factors hx0 _))
            (show ∀ x ∈ o.factors a + o.factors b, irreducible x,
              from λ x hx, (multiset.mem_add.1 hx).elim
                (o.irreducible_factors ha0 _)
                (o.irreducible_factors hb0 _)) $
              calc multiset.prod (p :: o.factors x)
                  ~ᵤ a * b : by rw [hx, multiset.prod_cons];
                    exact associated_mul_mul (by refl)
                      (o.factors_prod hx0)
              ... ~ᵤ (o.factors a).prod * (o.factors b).prod :
                associated_mul_mul
                  (o.factors_prod ha0).symm
                  (o.factors_prod hb0).symm
              ... = _ : by rw multiset.prod_add,
        let ⟨q, hqf, hq⟩ := multiset.exists_mem_of_rel_of_mem this
          (multiset.mem_cons_self p _) in
        (multiset.mem_add.1 hqf).elim
          (λ hqa, or.inl $ (dvd_iff_dvd_of_rel_left hq).2 $
            (dvd_iff_dvd_of_rel_right (o.factors_prod ha0)).1
              (multiset.dvd_prod hqa))
          (λ hqb, or.inr $ (dvd_iff_dvd_of_rel_left hq).2 $
            (dvd_iff_dvd_of_rel_right (o.factors_prod hb0)).1
              (multiset.dvd_prod hqb))⟩,
  ..o }

end unique_factorization_domain

namespace associates
open unique_factorization_domain associated
variables [integral_domain α]

/-- `factor_set α` representation elements of unique factorization domain as multisets.

`multiset α` produced by `factors` are only unique up to associated elements, while the multisets in
`factor_set α` are unqiue by equality and restricted to irreducible elements. This gives us a
representation of each element as a unique multisets (or the added ⊤ for 0), which has a complete
lattice struture. Infimum is the greatest common divisor and supremum is the least common multiple.
-/
@[reducible] def {u} factor_set (α : Type u) [integral_domain α] :
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

/-- The product of the elements of a factor_set -/
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

/-- `count p s` is the multiplicity of `p` in the factor_set `s`. -/
def count [decidable_eq (associates α)] (p : {a : associates α // irreducible a}) :
  factor_set α → ℕ
| none := 0
| (some s) := s.count p

@[simp] lemma count_some [decidable_eq (associates α)] (p : {a : associates α // irreducible a})
  (s : multiset _) : count p (some s) = s.count p := rfl

@[simp] lemma count_zero [decidable_eq (associates α)] (p : {a : associates α // irreducible a}) :
  count p (0 : factor_set α) = 0 := rfl

variable [unique_factorization_domain α]

theorem unique' {p q : multiset (associates α)} :
  (∀a∈p, irreducible a) → (∀a∈q, irreducible a) → p.prod = q.prod → p = q :=
begin
  apply multiset.induction_on_multiset_quot p,
  apply multiset.induction_on_multiset_quot q,
  assume s t hs ht eq,
  refine multiset.map_mk_eq_map_mk_of_rel (unique_factorization_domain.unique _ _ _),
  { exact assume a ha, ((irreducible_mk_iff _).1 $ hs _ $ multiset.mem_map_of_mem _ ha) },
  { exact assume a ha, ((irreducible_mk_iff _).1 $ ht _ $ multiset.mem_map_of_mem _ ha) },
  simpa [quot_mk_eq_mk, prod_mk, mk_eq_mk_iff_associated] using eq
end

private theorem forall_map_mk_factors_irreducible (x : α) (hx : x ≠ 0) :
  ∀(a : associates α), a ∈ multiset.map associates.mk (factors x) → irreducible a :=
begin
  assume a ha,
  rcases multiset.mem_map.1 ha with ⟨c, hc, rfl⟩,
  exact (irreducible_mk_iff c).2 (irreducible_factors hx _ hc)
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
      not_irreducible_zero ((irreducible_mk_iff 0).1 $ hq _ this)),
    have : associates.mk (factors c).prod = quot.mk setoid.r c,
      from mk_eq_mk_iff_associated.2 (factors_prod this),

    refine le_iff_exists_add.2 ⟨(factors c).map associates.mk, unique' hq _ _⟩,
    { assume x hx,
      rcases multiset.mem_add.1 hx with h | h,
      exact hp x h,
      exact forall_map_mk_factors_irreducible c ‹c ≠ 0› _ h },
    { simp [multiset.prod_add, prod_mk, *] at * }
  end
  prod_le_prod

/-- The multiset of associates of irreducible factors of a non-zero element. -/
def factors' (a : α) (ha : a ≠ 0) : multiset { a : associates α // irreducible a } :=
(factors a).pmap (λa ha, ⟨associates.mk a, (irreducible_mk_iff _).2 ha⟩)
  (irreducible_factors $ ha)

@[simp] theorem map_subtype_coe_factors' {a : α} (ha : a ≠ 0) :
  (factors' a ha).map coe = (factors a).map associates.mk :=
by simp [factors', multiset.map_pmap, multiset.pmap_eq_map]

theorem factors'_cong {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) (h : a ~ᵤ b) :
  factors' a ha = factors' b hb :=
have multiset.rel associated (factors a) (factors b), from
  unique (irreducible_factors ha) (irreducible_factors hb)
    ((factors_prod ha).trans $ h.trans $ (factors_prod hb).symm),
by simpa [(multiset.map_eq_map subtype.coe_injective).symm, rel_associated_iff_map_eq_map.symm]

variable [dec : decidable_eq (associates α)]
include dec

/-- The factor_set of irreducible factors of an element -/
def factors (a : associates α) : factor_set α :=
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

def factor_set_mem : {a : associates α // irreducible a} → (factor_set α) → Prop
| _ ⊤ := true
| p (some l) := p ∈ l

instance : has_mem {a : associates α // irreducible a} (factor_set α) := ⟨factor_set_mem⟩

lemma mem_factor_set_top {p : associates α} {hp : irreducible p} :
  subtype.mk p hp ∈ (⊤ : factor_set α) := by unfold has_mem.mem

lemma mem_factor_set_some' {p : associates α} {hp : irreducible p}
  {l : multiset {a : associates α // irreducible a }} {ll : factor_set α} (h : ll = some l):
  subtype.mk p hp ∈ ll ↔ subtype.mk p hp ∈ l :=
begin
  rw h, refl
end

lemma mem_factor_set_some'' {p : associates α} {hp : irreducible p}
  {l : multiset {a : associates α // irreducible a }} :
  factor_set_mem (subtype.mk p hp) ((some l) : factor_set α) ↔ subtype.mk p hp ∈ l := by refl

lemma mem_factor_set_some {p : associates α} {hp : irreducible p}
  {l : multiset {a : associates α // irreducible a }}:
  subtype.mk p hp ∈ ((some l) : factor_set α) ↔ subtype.mk p hp ∈ l :=
begin
  refl
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
      not_irreducible_zero ((irreducible_mk_iff _).1 this),
    have ha : a ≠ 0, by simp [*] at *,
    suffices : (unique_factorization_domain.factors a).map associates.mk = s.map coe,
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

instance : has_sup (associates α) := ⟨λa b, (a.factors ⊔ b.factors).prod⟩
instance : has_inf (associates α) := ⟨λa b, (a.factors ⊓ b.factors).prod⟩

instance : bounded_lattice (associates α) :=
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

lemma dvd_of_mem_factors {a p : associates α} {hp : irreducible p}
  (hm : subtype.mk p hp ∈ factors a) : p ∣ a :=
begin
  by_cases ha0 : a = 0, { rw ha0, exact dvd_zero p},
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha0,
  rw [← associates.factors_prod a],
  rw [← ha', factors_mk a0 nza] at hm ⊢,
  erw prod_coe,
  apply multiset.dvd_prod, apply multiset.mem_map.mpr,
  exact ⟨⟨p, hp⟩, hm, rfl⟩
end

omit dec

lemma dvd_of_mem_factors' {a : α} {p : associates α} {hp : irreducible p} {hz : a ≠ 0}
  (h_mem : subtype.mk p hp ∈ factors' a hz) : p ∣ associates.mk a :=
by { classical, apply @dvd_of_mem_factors _ _ _ _ _ _ hp, rw factors_mk _ hz, exact h_mem }

lemma mem_factors'_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) (hd : p ∣ a) :
  subtype.mk (associates.mk p) ((irreducible_mk_iff _).2 hp) ∈ factors' a ha0 :=
begin
  obtain ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd ha0 hp hd,
  apply multiset.mem_pmap.mpr, use q, use hq,
  exact subtype.eq (eq.symm (mk_eq_mk_iff_associated.mpr hpq))
end

lemma mem_factors'_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) :
  subtype.mk (associates.mk p) ((irreducible_mk_iff _).2 hp) ∈ factors' a ha0 ↔ p ∣ a :=
begin
  split,
  { rw ← mk_dvd_mk, exact dvd_of_mem_factors' },
  { apply mem_factors'_of_dvd }
end

lemma associates_irreducible_iff_prime : ∀{p : associates α}, irreducible p ↔ prime p :=
associates.forall_associated.2 $ assume a,
by rw [associates.irreducible_mk_iff, associates.prime_mk, irreducible_iff_prime]

include dec

lemma mem_factors_of_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) (hd : p ∣ a) :
  subtype.mk (associates.mk p) ((irreducible_mk_iff _).2 hp) ∈ factors (associates.mk a) :=
begin
  rw factors_mk _ ha0, exact mem_factors'_of_dvd ha0 hp hd
end

lemma mem_factors_iff_dvd {a p : α} (ha0 : a ≠ 0) (hp : irreducible p) :
  subtype.mk (associates.mk p) ((irreducible_mk_iff _).2 hp) ∈ factors (associates.mk a) ↔ p ∣ a :=
begin
  split,
  { rw ← mk_dvd_mk, exact dvd_of_mem_factors },
  { apply mem_factors_of_dvd ha0 }
end

lemma exists_prime_dvd_of_not_inf_one {a b : α}
  (ha : a ≠ 0) (hb : b ≠ 0) (h : (associates.mk a) ⊓ (associates.mk b) ≠ 1)  :
  ∃ (p : α), prime p ∧ p ∣ a ∧ p ∣ b :=
begin
  have hz : (factors (associates.mk a)) ⊓ (factors (associates.mk b)) ≠ 0,
  { contrapose! h with hf,
    change ((factors (associates.mk a)) ⊓ (factors (associates.mk b))).prod = 1,
    rw hf,
    exact multiset.prod_zero },
  rw [factors_mk a ha, factors_mk b hb, ← with_top.coe_inf] at hz,
  obtain ⟨⟨p0, p0_irr⟩, p0_mem⟩ := multiset.exists_mem_of_ne_zero ((mt with_top.coe_eq_coe.mpr) hz),
  rw multiset.inf_eq_inter at p0_mem,
  obtain ⟨p, rfl⟩ : ∃ p, associates.mk p = p0 := quot.exists_rep p0,
  refine ⟨p, _, _, _⟩,
  { rw [← irreducible_iff_prime, ← irreducible_mk_iff],
    exact p0_irr },
  { apply dvd_of_mk_le_mk,
    exact dvd_of_mem_factors' (multiset.mem_inter.mp p0_mem).left },
  { apply dvd_of_mk_le_mk,
    exact dvd_of_mem_factors' (multiset.mem_inter.mp p0_mem).right }
end

theorem coprime_iff_inf_one {a b : α} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
  (associates.mk a) ⊓ (associates.mk b) = 1 ↔ ∀ {d : α}, d ∣ a → d ∣ b → ¬ prime d :=
begin
  split,
  { intros hg p ha hb hp,
    refine ((associates.prime_mk _).mpr hp).not_unit (is_unit_of_dvd_one _ _),
    rw ← hg,
    exact le_inf (mk_le_mk_of_dvd ha) (mk_le_mk_of_dvd hb) },
  { contrapose,
    intros hg hc,
    obtain ⟨p, hp, hpa, hpb⟩ := exists_prime_dvd_of_not_inf_one ha0 hb0 hg,
    exact hc hpa hpb hp }
end

theorem factors_prime_pow {p : associates α} (hp : irreducible p)
  (k : ℕ) : factors (p ^ k) = some (multiset.repeat ⟨p, hp⟩ k) :=
eq_of_prod_eq_prod (by rw [associates.factors_prod, factor_set.prod, multiset.map_repeat,
                           multiset.prod_repeat, subtype.coe_mk])

theorem prime_pow_dvd_iff_le {m p : associates α} (h₁ : m ≠ 0)
  (h₂ : irreducible p) {k : ℕ} : p ^ k ≤ m ↔ k ≤ count ⟨p, h₂⟩ m.factors :=
begin
  obtain ⟨a, nz, rfl⟩ := associates.exists_non_zero_rep h₁,
  rw [factors_mk _ nz, ← with_top.some_eq_coe, count_some, multiset.le_count_iff_repeat_le,
      ← factors_le, factors_prime_pow h₂, factors_mk _ nz],
  exact with_top.coe_le_coe
end

theorem count_mul {a : associates α} (ha : a ≠ 0) {b : associates α} (hb : b ≠ 0)
  {p : { a : associates α // irreducible a }} :
  count p (factors (a * b)) = count p a.factors + count p b.factors :=
begin
  obtain ⟨a0, nza, ha'⟩ := exists_non_zero_rep ha,
  obtain ⟨b0, nzb, hb'⟩ := exists_non_zero_rep hb,
  rw [factors_mul, ← ha', ← hb', factors_mk a0 nza, factors_mk b0 nzb, ← factor_set.coe_add,
      ← with_top.some_eq_coe, ← with_top.some_eq_coe, ← with_top.some_eq_coe, count_some,
      multiset.count_add],
  refl
end

theorem count_of_coprime {a : associates α} (ha : a ≠ 0) {b : associates α} (hb : b ≠ 0)
  (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d) (p : { a : associates α // irreducible a }) :
  count p a.factors = 0 ∨ count p b.factors = 0 :=
begin
  rw [or_iff_not_imp_left, ← ne.def, ← nat.pos_iff_ne_zero],
  intro hca,
  contrapose! hab with hcb,
  rw ← nat.pos_iff_ne_zero at hcb,
  have hpa : p.val ∣ a,
  { rw [← pow_one p.val],
    apply (prime_pow_dvd_iff_le ha p.2).2,
    simpa only [subtype.eta] },
  have hpb : p.val ∣ b,
  { rw [← pow_one p.val],
    apply (prime_pow_dvd_iff_le hb p.2).2,
    simpa only [subtype.eta] },
  exact ⟨p, hpa, hpb, (associates_irreducible_iff_prime.mp p.2)⟩,
end

theorem coprime_product {a : associates α} (ha : a ≠ 0) {b : associates α} (hb : b ≠ 0)
  (p : { a : associates α // irreducible a }) (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d) :
  count p a.factors = 0 ∨ count p a.factors = count p (a * b).factors :=
begin
  cases count_of_coprime ha hb hab p with hz hb0, { tauto },
  apply or.intro_right,
  rw [count_mul ha hb, hb0, add_zero]
end

theorem dvd_count_of_dvd_count_mul {a b : associates α} (ha : a ≠ 0) (hb : b ≠ 0)
  {p : { a : associates α // irreducible a }} (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d)
  {k : ℕ} (habk : k ∣ count p (a * b).factors) : k ∣ count p a.factors :=
begin
  cases count_of_coprime ha hb hab p with hz h,
  { rw hz, exact dvd_zero k },
  { rw [count_mul ha hb, h] at habk, exact habk }
end

lemma factors_one : factors (1 : associates α) = 0 :=
begin
  apply eq_of_prod_eq_prod,
  rw associates.factors_prod,
  exact multiset.prod_zero,
end

theorem pow_factors {a : associates α} {k : ℕ} : (a ^ k).factors = k •ℕ a.factors :=
begin
  induction k with n h,
  { rw [zero_nsmul, pow_zero], exact factors_one },
  { rw [pow_succ, succ_nsmul, factors_mul, h] }
end

lemma count_pow {a : associates α} (ha : a ≠ 0) (p : { a : associates α // irreducible a })
  (k : ℕ) : count p (a ^ k).factors = k * count p a.factors :=
begin
  induction k with n h,
  { rw [pow_zero, factors_one, zero_mul, count_zero] },
  { rw [pow_succ, count_mul ha (pow_ne_zero' _ ha), h, nat.succ_eq_add_one], ring }
end

theorem dvd_count_pow {a : associates α} (ha : a ≠ 0) (p : { a : associates α // irreducible a })
  (k : ℕ) : k ∣ count p (a ^ k).factors := by { rw count_pow ha, apply dvd_mul_right }

theorem is_pow_of_dvd_count {a : associates α} (ha : a ≠ 0) {k : ℕ}
  (hp : ∀ (p : { a : associates α // irreducible a }), k ∣ count p a.factors) :
  ∃ (b : associates α), a = b ^ k :=
begin
  obtain ⟨a0, hz, rfl⟩ := exists_non_zero_rep ha,
  rw factors_mk a0 hz at hp,
  obtain ⟨u, hu⟩ := multiset.exists_smul_of_dvd_count _ hp,
  use (u : factor_set α).prod,
  apply eq_of_factors_eq_factors,
  rw [pow_factors, prod_factors, factors_mk a0 hz, ← with_top.some_eq_coe, hu],
  exact with_bot.coe_nsmul u k
end

omit dec

theorem eq_pow_of_mul_eq_pow {a b c : associates α} (ha : a ≠ 0) (hb : b ≠ 0)
  (hab : ∀ d, d ∣ a → d ∣ b → ¬ prime d) {k : ℕ} (h : a * b = c ^ k) :
  ∃ (d : associates α), a = d ^ k :=
begin
  classical,
  by_cases hk0 : k = 0,
  { use 1,
    rw [hk0, pow_zero] at h ⊢,
    apply (mul_eq_one_iff.1 h).1 },
  { refine is_pow_of_dvd_count ha (λ p, dvd_count_of_dvd_count_mul ha hb hab _),
    rw h,
    apply dvd_count_pow,
    rintros rfl,
    rw zero_pow' _ hk0 at h,
    cases mul_eq_zero.mp h; contradiction }
end

end associates

section
open associates unique_factorization_domain

/-- `to_gcd_monoid` constructs a GCD monoid out of a normalization on a
  unique factorization domain. -/
def unique_factorization_domain.to_gcd_monoid
  (α : Type*) [integral_domain α] [unique_factorization_domain α] [normalization_monoid α]
  [decidable_eq (associates α)] : gcd_monoid α :=
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

namespace unique_factorization_domain

variables {R : Type*} [integral_domain R] [unique_factorization_domain R]

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

end unique_factorization_domain

open unique_factorization_domain associated lattice associates

variables [integral_domain α] [nontrivial α] [gcd_monoid α] [unique_factorization_domain α]
local attribute [instance] associated.setoid

lemma exists_prime_dvd_of_gcd_ne_one {a b : α}
  (h : gcd a b ≠ 1) (ha : a ≠ 0) : ∃ (p : α), prime p ∧ p ∣ a ∧ p ∣ b :=
begin
  have hz : gcd a b ≠ 0, { apply mt (gcd_eq_zero_iff a b).mp, tauto },
  have hg : associated (factors (gcd a b)).prod (gcd a b) := factors_prod hz,
  have h : factors (gcd a b) ≠ 0,
  { contrapose! h with hz2,
    rw [hz2, multiset.prod_zero] at hg,
    rw [← normalize_gcd, ← normalize_one, ← out_mk, ← out_mk],
    exact congr_arg _ (mk_eq_mk_iff_associated.mpr hg.symm) },
  cases multiset.exists_mem_of_ne_zero h with p hp,
  exact ⟨p,
         prime_factors hz p hp,
         (dvd_gcd_iff p a b).mp (dvd_trans (multiset.dvd_prod hp) (dvd_of_associated hg))⟩
end

theorem coprime_iff_gcd_eq_one {a b : α} (ha : a ≠ 0) :
  gcd a b = 1 ↔ ∀ {d}, d ∣ a → d ∣ b → ¬ prime d :=
begin
  split,
  { intro hg, intros p ha hb hp,
    have hpg : p ∣ gcd a b := (dvd_gcd_iff p a b).mpr (and.intro ha hb),
    rw hg at hpg,
    exact hp.not_unit (is_unit_of_dvd_one p hpg) },
  { haveI := classical.prop_decidable,
    contrapose!,
    intro hg,
    obtain ⟨p, hp, hpa, hpb⟩ := exists_prime_dvd_of_gcd_ne_one hg ha,
    exact ⟨p, hpa, hpb, hp⟩ }
end
