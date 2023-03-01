/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.list.prime
import data.polynomial.field_division
import data.polynomial.lifts

/-!
# Split polynomials

A polynomial `f : K[X]` splits over a field extension `L` of `K` if it is zero or all of its
irreducible factors over `L` have degree `1`.

## Main definitions

* `polynomial.splits i f`: A predicate on a homomorphism `i : K →+* L` from a commutative ring to a
  field and a polynomial `f` saying that `f.map i` is zero or all of its irreducible factors over
  `L` have degree `1`.

## Main statements

* `lift_of_splits`: If `K` and `L` are field extensions of a field `F` and for some finite subset
  `S` of `K`, the minimal polynomial of every `x ∈ K` splits as a polynomial with coefficients in
  `L`, then `algebra.adjoin F S` embeds into `L`.

-/

noncomputable theory
open_locale classical big_operators polynomial

universes u v w

variables {F : Type u} {K : Type v} {L : Type w}

namespace polynomial

open polynomial

section splits

section comm_ring
variables [comm_ring K] [field L] [field F]
variables (i : K →+* L)

/-- A polynomial `splits` iff it is zero or all of its irreducible factors have `degree` 1. -/
def splits (f : K[X]) : Prop :=
f.map i = 0 ∨ ∀ {g : L[X]}, irreducible g → g ∣ f.map i → degree g = 1

@[simp] lemma splits_zero : splits i (0 : K[X]) := or.inl (polynomial.map_zero i)

lemma splits_of_map_eq_C {f : K[X]} {a : L} (h : f.map i = C a) : splits i f :=
if ha : a = 0 then or.inl (h.trans (ha.symm ▸ C_0))
else or.inr $ λ g hg ⟨p, hp⟩, absurd hg.1 $ not_not.2 $ is_unit_iff_degree_eq_zero.2 $
begin
  have := congr_arg degree hp,
  rw [h, degree_C ha, degree_mul, @eq_comm (with_bot ℕ) 0, nat.with_bot.add_eq_zero_iff] at this,
  exact this.1,
end

@[simp] lemma splits_C (a : K) : splits i (C a) := splits_of_map_eq_C i (map_C i)

lemma splits_of_map_degree_eq_one {f : K[X]} (hf : degree (f.map i) = 1) : splits i f :=
or.inr $ λ g hg ⟨p, hp⟩,
  by have := congr_arg degree hp;
  simp [nat.with_bot.add_eq_one_iff, hf, @eq_comm (with_bot ℕ) 1,
    mt is_unit_iff_degree_eq_zero.2 hg.1] at this;
  clear _fun_match; tauto

lemma splits_of_degree_le_one {f : K[X]} (hf : degree f ≤ 1) : splits i f :=
if hif : degree (f.map i) ≤ 0 then splits_of_map_eq_C i (degree_le_zero_iff.mp hif)
else begin
  push_neg at hif,
  rw [← order.succ_le_iff, ← with_bot.coe_zero, with_bot.succ_coe, nat.succ_eq_succ] at hif,
  exact splits_of_map_degree_eq_one i (le_antisymm ((degree_map_le i _).trans hf) hif),
end

lemma splits_of_degree_eq_one {f : K[X]} (hf : degree f = 1) : splits i f :=
splits_of_degree_le_one i hf.le

lemma splits_of_nat_degree_le_one {f : K[X]} (hf : nat_degree f ≤ 1) : splits i f :=
splits_of_degree_le_one i (degree_le_of_nat_degree_le hf)

lemma splits_of_nat_degree_eq_one {f : K[X]} (hf : nat_degree f = 1) : splits i f :=
splits_of_nat_degree_le_one i (le_of_eq hf)

lemma splits_mul {f g : K[X]} (hf : splits i f) (hg : splits i g) : splits i (f * g) :=
if h : (f * g).map i = 0 then or.inl h
else or.inr $ λ p hp hpf, ((principal_ideal_ring.irreducible_iff_prime.1 hp).2.2 _ _
    (show p ∣ map i f * map i g, by convert hpf; rw polynomial.map_mul)).elim
  (hf.resolve_left (λ hf, by simpa [hf] using h) hp)
  (hg.resolve_left (λ hg, by simpa [hg] using h) hp)

lemma splits_of_splits_mul' {f g : K[X]} (hfg : (f * g).map i ≠ 0) (h : splits i (f * g)) :
  splits i f ∧ splits i g :=
⟨or.inr $ λ g hgi hg, or.resolve_left h hfg hgi
   (by rw polynomial.map_mul; exact hg.trans (dvd_mul_right _ _)),
 or.inr $ λ g hgi hg, or.resolve_left h hfg hgi
   (by rw polynomial.map_mul; exact hg.trans (dvd_mul_left _ _))⟩

lemma splits_map_iff (j : L →+* F) {f : K[X]} :
  splits j (f.map i) ↔ splits (j.comp i) f :=
by simp [splits, polynomial.map_map]

theorem splits_one : splits i 1 :=
splits_C i 1

theorem splits_of_is_unit [is_domain K] {u : K[X]} (hu : is_unit u) : u.splits i :=
(is_unit_iff.mp hu).some_spec.2 ▸ splits_C _ _

theorem splits_X_sub_C {x : K} : (X - C x).splits i :=
splits_of_degree_le_one _ $ degree_X_sub_C_le _

theorem splits_X : X.splits i :=
splits_of_degree_le_one _ degree_X_le

theorem splits_prod {ι : Type u} {s : ι → K[X]} {t : finset ι} :
  (∀ j ∈ t, (s j).splits i) → (∏ x in t, s x).splits i :=
begin
  refine finset.induction_on t (λ _, splits_one i) (λ a t hat ih ht, _),
  rw finset.forall_mem_insert at ht, rw finset.prod_insert hat,
  exact splits_mul i ht.1 (ih ht.2)
end

lemma splits_pow {f : K[X]} (hf : f.splits i) (n : ℕ) : (f ^ n).splits i :=
begin
  rw [←finset.card_range n, ←finset.prod_const],
  exact splits_prod i (λ j hj, hf),
end

lemma splits_X_pow (n : ℕ) : (X ^ n).splits i := splits_pow i (splits_X i) n

theorem splits_id_iff_splits {f : K[X]} :
  (f.map i).splits (ring_hom.id L) ↔ f.splits i :=
by rw [splits_map_iff, ring_hom.id_comp]

lemma exists_root_of_splits' {f : K[X]} (hs : splits i f) (hf0 : degree (f.map i) ≠ 0) :
  ∃ x, eval₂ i x f = 0 :=
if hf0' : f.map i = 0 then by simp [eval₂_eq_eval_map, hf0']
else
  let ⟨g, hg⟩ := wf_dvd_monoid.exists_irreducible_factor
    (show ¬ is_unit (f.map i), from mt is_unit_iff_degree_eq_zero.1 hf0) hf0' in
  let ⟨x, hx⟩ := exists_root_of_degree_eq_one (hs.resolve_left hf0' hg.1 hg.2) in
  let ⟨i, hi⟩ := hg.2 in
  ⟨x, by rw [← eval_map, hi, eval_mul, show _ = _, from hx, zero_mul]⟩

lemma roots_ne_zero_of_splits' {f : K[X]} (hs : splits i f) (hf0 : nat_degree (f.map i) ≠ 0) :
  (f.map i).roots ≠ 0 :=
let ⟨x, hx⟩ := exists_root_of_splits' i hs (λ h, hf0 $ nat_degree_eq_of_degree_eq_some h) in
λ h, by { rw ← eval_map at hx,
  cases h.subst ((mem_roots _).2 hx), exact ne_zero_of_nat_degree_gt (nat.pos_of_ne_zero hf0) }

/-- Pick a root of a polynomial that splits. See `root_of_splits` for polynomials over a field
which has simpler assumptions. -/
def root_of_splits' {f : K[X]} (hf : f.splits i) (hfd : (f.map i).degree ≠ 0) : L :=
classical.some $ exists_root_of_splits' i hf hfd

theorem map_root_of_splits' {f : K[X]} (hf : f.splits i) (hfd) :
  f.eval₂ i (root_of_splits' i hf hfd) = 0 :=
classical.some_spec $ exists_root_of_splits' i hf hfd

lemma nat_degree_eq_card_roots' {p : K[X]} {i : K →+* L}
  (hsplit : splits i p) : (p.map i).nat_degree = (p.map i).roots.card :=
begin
  by_cases hp : p.map i = 0,
  { rw [hp, nat_degree_zero, roots_zero, multiset.card_zero] },
  obtain ⟨q, he, hd, hr⟩ := exists_prod_multiset_X_sub_C_mul (p.map i),
  rw [← splits_id_iff_splits, ← he] at hsplit,
  rw ← he at hp,
  have hq : q ≠ 0 := λ h, hp (by rw [h, mul_zero]),
  rw [← hd, add_right_eq_self],
  by_contra,
  have h' : (map (ring_hom.id L) q).nat_degree ≠ 0, { simp [h], },
  have := roots_ne_zero_of_splits' (ring_hom.id L) (splits_of_splits_mul' _ _ hsplit).2 h',
  { rw map_id at this, exact this hr },
  { rw [map_id], exact mul_ne_zero monic_prod_multiset_X_sub_C.ne_zero hq },
end

lemma degree_eq_card_roots' {p : K[X]} {i : K →+* L} (p_ne_zero : p.map i ≠ 0)
  (hsplit : splits i p) : (p.map i).degree = (p.map i).roots.card :=
by rw [degree_eq_nat_degree p_ne_zero, nat_degree_eq_card_roots' hsplit]

end comm_ring

variables [field K] [field L] [field F]
variables (i : K →+* L)

/-- This lemma is for polynomials over a field. -/
lemma splits_iff (f : K[X]) :
  splits i f ↔ f = 0 ∨ ∀ {g : L[X]}, irreducible g → g ∣ f.map i → degree g = 1 :=
by rw [splits, map_eq_zero]

/-- This lemma is for polynomials over a field. -/
lemma splits.def {i : K →+* L} {f : K[X]} (h : splits i f) :
  f = 0 ∨ ∀ {g : L[X]}, irreducible g → g ∣ f.map i → degree g = 1 :=
(splits_iff i f).mp h

lemma splits_of_splits_mul {f g : K[X]} (hfg : f * g ≠ 0) (h : splits i (f * g)) :
  splits i f ∧ splits i g :=
splits_of_splits_mul' i (map_ne_zero hfg) h

lemma splits_of_splits_of_dvd {f g : K[X]} (hf0 : f ≠ 0) (hf : splits i f) (hgf : g ∣ f) :
  splits i g :=
by { obtain ⟨f, rfl⟩ := hgf, exact (splits_of_splits_mul i hf0 hf).1 }

lemma splits_of_splits_gcd_left {f g : K[X]} (hf0 : f ≠ 0) (hf : splits i f) :
  splits i (euclidean_domain.gcd f g) :=
polynomial.splits_of_splits_of_dvd i hf0 hf (euclidean_domain.gcd_dvd_left f g)

lemma splits_of_splits_gcd_right {f g : K[X]} (hg0 : g ≠ 0) (hg : splits i g) :
  splits i (euclidean_domain.gcd f g) :=
polynomial.splits_of_splits_of_dvd i hg0 hg (euclidean_domain.gcd_dvd_right f g)

theorem splits_mul_iff {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) :
  (f * g).splits i ↔ f.splits i ∧ g.splits i :=
⟨splits_of_splits_mul i (mul_ne_zero hf hg), λ ⟨hfs, hgs⟩, splits_mul i hfs hgs⟩

theorem splits_prod_iff {ι : Type u} {s : ι → K[X]} {t : finset ι} :
  (∀ j ∈ t, s j ≠ 0) → ((∏ x in t, s x).splits i ↔ ∀ j ∈ t, (s j).splits i) :=
begin
  refine finset.induction_on t (λ _, ⟨λ _ _ h, h.elim, λ _, splits_one i⟩) (λ a t hat ih ht, _),
  rw finset.forall_mem_insert at ht ⊢,
  rw [finset.prod_insert hat, splits_mul_iff i ht.1 (finset.prod_ne_zero_iff.2 ht.2), ih ht.2]
end

lemma degree_eq_one_of_irreducible_of_splits {p : K[X]}
  (hp : irreducible p) (hp_splits : splits (ring_hom.id K) p) :
  p.degree = 1 :=
begin
  rcases hp_splits,
  { exfalso, simp * at *, },
  { apply hp_splits hp, simp }
end

lemma exists_root_of_splits {f : K[X]} (hs : splits i f) (hf0 : degree f ≠ 0) :
  ∃ x, eval₂ i x f = 0 :=
exists_root_of_splits' i hs ((f.degree_map i).symm ▸ hf0)

lemma roots_ne_zero_of_splits {f : K[X]} (hs : splits i f) (hf0 : nat_degree f ≠ 0) :
  (f.map i).roots ≠ 0 :=
roots_ne_zero_of_splits' i hs (ne_of_eq_of_ne (nat_degree_map i) hf0)

/-- Pick a root of a polynomial that splits. This version is for polynomials over a field and has
simpler assumptions. -/
def root_of_splits {f : K[X]} (hf : f.splits i) (hfd : f.degree ≠ 0) : L :=
root_of_splits' i hf ((f.degree_map i).symm ▸ hfd)

/-- `root_of_splits'` is definitionally equal to `root_of_splits`. -/
lemma root_of_splits'_eq_root_of_splits {f : K[X]} (hf : f.splits i) (hfd) :
  root_of_splits' i hf hfd = root_of_splits i hf (f.degree_map i ▸ hfd) := rfl

theorem map_root_of_splits {f : K[X]} (hf : f.splits i) (hfd) :
  f.eval₂ i (root_of_splits i hf hfd) = 0 :=
map_root_of_splits' i hf (ne_of_eq_of_ne (degree_map f i) hfd)

lemma nat_degree_eq_card_roots {p : K[X]} {i : K →+* L}
  (hsplit : splits i p) : p.nat_degree = (p.map i).roots.card :=
(nat_degree_map i).symm.trans $ nat_degree_eq_card_roots' hsplit

lemma degree_eq_card_roots {p : K[X]} {i : K →+* L} (p_ne_zero : p ≠ 0)
  (hsplit : splits i p) : p.degree = (p.map i).roots.card :=
by rw [degree_eq_nat_degree p_ne_zero, nat_degree_eq_card_roots hsplit]

theorem roots_map {f : K[X]} (hf : f.splits $ ring_hom.id K) :
  (f.map i).roots = f.roots.map i :=
(roots_map_of_injective_of_card_eq_nat_degree i.injective $
  by { convert (nat_degree_eq_card_roots hf).symm, rw map_id }).symm

lemma image_root_set [algebra F K] [algebra F L] {p : F[X]} (h : p.splits (algebra_map F K))
  (f : K →ₐ[F] L) : f '' p.root_set K = p.root_set L :=
begin
  classical,
  rw [root_set, ←finset.coe_image, ←multiset.to_finset_map, ←f.coe_to_ring_hom, ←roots_map ↑f
      ((splits_id_iff_splits (algebra_map F K)).mpr h), map_map, f.comp_algebra_map, ←root_set],
end

lemma adjoin_root_set_eq_range [algebra F K] [algebra F L] {p : F[X]}
  (h : p.splits (algebra_map F K)) (f : K →ₐ[F] L) :
  algebra.adjoin F (p.root_set L) = f.range ↔ algebra.adjoin F (p.root_set K) = ⊤ :=
begin
  rw [←image_root_set h f, algebra.adjoin_image, ←algebra.map_top],
  exact (subalgebra.map_injective f.to_ring_hom.injective).eq_iff,
end

lemma eq_prod_roots_of_splits {p : K[X]} {i : K →+* L} (hsplit : splits i p) :
  p.map i = C (i p.leading_coeff) * ((p.map i).roots.map (λ a, X - C a)).prod :=
begin
  rw ← leading_coeff_map, symmetry,
  apply C_leading_coeff_mul_prod_multiset_X_sub_C,
  rw nat_degree_map, exact (nat_degree_eq_card_roots hsplit).symm,
end

lemma eq_prod_roots_of_splits_id {p : K[X]}
  (hsplit : splits (ring_hom.id K) p) :
  p = C p.leading_coeff * (p.roots.map (λ a, X - C a)).prod :=
by simpa using eq_prod_roots_of_splits hsplit

lemma eq_prod_roots_of_monic_of_splits_id {p : K[X]}
  (m : monic p) (hsplit : splits (ring_hom.id K) p) :
  p = (p.roots.map (λ a, X - C a)).prod :=
begin
  convert eq_prod_roots_of_splits_id hsplit,
  simp [m],
end

lemma eq_X_sub_C_of_splits_of_single_root {x : K} {h : K[X]} (h_splits : splits i h)
  (h_roots : (h.map i).roots = {i x}) : h = C h.leading_coeff * (X - C x) :=
begin
  apply polynomial.map_injective _ i.injective,
  rw [eq_prod_roots_of_splits h_splits, h_roots],
  simp,
end

theorem mem_lift_of_splits_of_roots_mem_range (R : Type*) [comm_ring R] [algebra R K] {f : K[X]}
  (hs : f.splits (ring_hom.id K)) (hm : f.monic)
  (hr : ∀ a ∈ f.roots, a ∈ (algebra_map R K).range) : f ∈ polynomial.lifts (algebra_map R K) :=
begin
  rw [eq_prod_roots_of_monic_of_splits_id hm hs, lifts_iff_lifts_ring],
  refine subring.multiset_prod_mem _ _ (λ P hP, _),
  obtain ⟨b, hb, rfl⟩ := multiset.mem_map.1 hP,
  exact subring.sub_mem _ (X_mem_lifts _) (C'_mem_lifts (hr _ hb))
end

section UFD

local attribute [instance, priority 10] principal_ideal_ring.to_unique_factorization_monoid
local infix ` ~ᵤ ` : 50 := associated

open unique_factorization_monoid associates

lemma splits_of_exists_multiset {f : K[X]} {s : multiset L}
  (hs : f.map i = C (i f.leading_coeff) * (s.map (λ a : L, X - C a)).prod) :
  splits i f :=
if hf0 : f = 0 then hf0.symm ▸ splits_zero i
else or.inr $ λ p hp hdp, begin
  rw irreducible_iff_prime at hp,
  rw [hs, ← multiset.prod_to_list] at hdp,
  obtain (hd|hd) := hp.2.2 _ _ hdp,
  { refine (hp.2.1 $ is_unit_of_dvd_unit hd _).elim,
    exact is_unit_C.2 ((leading_coeff_ne_zero.2 hf0).is_unit.map i) },
  { obtain ⟨q, hq, hd⟩ := hp.dvd_prod_iff.1 hd,
    obtain ⟨a, ha, rfl⟩ := multiset.mem_map.1 (multiset.mem_to_list.1 hq),
    rw degree_eq_degree_of_associated ((hp.dvd_prime_iff_associated $ prime_X_sub_C a).1 hd),
    exact degree_X_sub_C a },
end

lemma splits_of_splits_id {f : K[X]} : splits (ring_hom.id K) f → splits i f :=
unique_factorization_monoid.induction_on_prime f (λ _, splits_zero _)
  (λ _ hu _, splits_of_degree_le_one _
    ((is_unit_iff_degree_eq_zero.1 hu).symm ▸ dec_trivial))
  (λ a p ha0 hp ih hfi, splits_mul _
    (splits_of_degree_eq_one _
      ((splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).1.def.resolve_left
        hp.1 hp.irreducible (by rw map_id)))
    (ih (splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).2))

end UFD

lemma splits_iff_exists_multiset {f : K[X]} : splits i f ↔
  ∃ (s : multiset L), f.map i = C (i f.leading_coeff) * (s.map (λ a : L, X - C a)).prod :=
⟨λ hf, ⟨(f.map i).roots, eq_prod_roots_of_splits hf⟩, λ ⟨s, hs⟩, splits_of_exists_multiset i hs⟩

lemma splits_comp_of_splits (j : L →+* F) {f : K[X]}
  (h : splits i f) : splits (j.comp i) f :=
begin
  change i with ((ring_hom.id _).comp i) at h,
  rw [← splits_map_iff],
  rw [← splits_map_iff i] at h,
  exact splits_of_splits_id _ h
end

/-- A polynomial splits if and only if it has as many roots as its degree. -/
lemma splits_iff_card_roots {p : K[X]} :
  splits (ring_hom.id K) p ↔ p.roots.card = p.nat_degree :=
begin
  split,
  { intro H, rw [nat_degree_eq_card_roots H, map_id] },
  { intro hroots,
    rw splits_iff_exists_multiset (ring_hom.id K),
    use p.roots,
    simp only [ring_hom.id_apply, map_id],
    exact (C_leading_coeff_mul_prod_multiset_X_sub_C hroots).symm },
end

lemma aeval_root_derivative_of_splits [algebra K L] {P : K[X]} (hmo : P.monic)
  (hP : P.splits (algebra_map K L)) {r : L} (hr : r ∈ (P.map (algebra_map K L)).roots) :
  aeval r P.derivative = (((P.map $ algebra_map K L).roots.erase r).map (λ a, r - a)).prod :=
begin
  replace hmo := hmo.map (algebra_map K L),
  replace hP := (splits_id_iff_splits (algebra_map K L)).2 hP,
  rw [aeval_def, ← eval_map, ← derivative_map],
  nth_rewrite 0 [eq_prod_roots_of_monic_of_splits_id hmo hP],
  rw [eval_multiset_prod_X_sub_C_derivative hr]
end

/-- If `P` is a monic polynomial that splits, then `coeff P 0` equals the product of the roots. -/
lemma prod_roots_eq_coeff_zero_of_monic_of_split {P : K[X]} (hmo : P.monic)
  (hP : P.splits (ring_hom.id K)) : coeff P 0 = (-1) ^ P.nat_degree * P.roots.prod :=
begin
  nth_rewrite 0 [eq_prod_roots_of_monic_of_splits_id hmo hP],
  rw [coeff_zero_eq_eval_zero, eval_multiset_prod, multiset.map_map],
  simp_rw [function.comp_app, eval_sub, eval_X, zero_sub, eval_C],
  conv_lhs { congr, congr, funext,
    rw [neg_eq_neg_one_mul] },
  rw [multiset.prod_map_mul, multiset.map_const, multiset.prod_replicate, multiset.map_id',
    splits_iff_card_roots.1 hP]
end

/-- If `P` is a monic polynomial that splits, then `P.next_coeff` equals the sum of the roots. -/
lemma sum_roots_eq_next_coeff_of_monic_of_split {P : K[X]} (hmo : P.monic)
  (hP : P.splits (ring_hom.id K)) : P.next_coeff = - P.roots.sum :=
begin
  nth_rewrite 0 [eq_prod_roots_of_monic_of_splits_id hmo hP],
  rw [monic.next_coeff_multiset_prod _ _ (λ a ha, _)],
  { simp_rw [next_coeff_X_sub_C, multiset.sum_map_neg'] },
  { exact monic_X_sub_C a }
end

end splits

end polynomial
