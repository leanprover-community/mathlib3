/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

Definition of splitting fields, and definition of homomorphism into any field that splits
-/
import ring_theory.adjoin_root
import ring_theory.algebra_tower
import ring_theory.polynomial
import field_theory.minimal_polynomial

universes u v w

variables {α : Type u} {β : Type v} {γ : Type w}

namespace polynomial

noncomputable theory
open_locale classical big_operators
variables [field α] [field β] [field γ]
open polynomial

section splits

variables (i : α →+* β)

/-- a polynomial `splits` iff it is zero or all of its irreducible factors have `degree` 1 -/
def splits (f : polynomial α) : Prop :=
f = 0 ∨ ∀ {g : polynomial β}, irreducible g → g ∣ f.map i → degree g = 1

@[simp] lemma splits_zero : splits i (0 : polynomial α) := or.inl rfl

@[simp] lemma splits_C (a : α) : splits i (C a) :=
if ha : a = 0 then ha.symm ▸ (@C_0 α _).symm ▸ splits_zero i
else
have hia : i a ≠ 0, from mt ((is_add_group_hom.injective_iff i).1
  i.injective _) ha,
or.inr $ λ g hg ⟨p, hp⟩, absurd hg.1 (classical.not_not.2 (is_unit_iff_degree_eq_zero.2 $
  by have := congr_arg degree hp;
    simp [degree_C hia, @eq_comm (with_bot ℕ) 0,
      nat.with_bot.add_eq_zero_iff] at this; clear _fun_match; tautology))

lemma splits_of_degree_eq_one {f : polynomial α} (hf : degree f = 1) : splits i f :=
or.inr $ λ g hg ⟨p, hp⟩,
  by have := congr_arg degree hp;
  simp [nat.with_bot.add_eq_one_iff, hf, @eq_comm (with_bot ℕ) 1,
    mt is_unit_iff_degree_eq_zero.2 hg.1] at this;
  clear _fun_match; tauto

lemma splits_of_degree_le_one {f : polynomial α} (hf : degree f ≤ 1) : splits i f :=
begin
  cases h : degree f with n,
  { rw [degree_eq_bot.1 h]; exact splits_zero i },
  { cases n with n,
    { rw [eq_C_of_degree_le_zero (trans_rel_right (≤) h (le_refl _))];
      exact splits_C _ _ },
    { have hn : n = 0,
      { rw h at hf,
        cases n, { refl }, { exact absurd hf dec_trivial } },
      exact splits_of_degree_eq_one _ (by rw [h, hn]; refl) } }
end

lemma splits_mul {f g : polynomial α} (hf : splits i f) (hg : splits i g) : splits i (f * g) :=
if h : f * g = 0 then by simp [h]
else or.inr $ λ p hp hpf, ((principal_ideal_ring.irreducible_iff_prime.1 hp).2.2 _ _
    (show p ∣ map i f * map i g, by convert hpf; rw polynomial.map_mul)).elim
  (hf.resolve_left (λ hf, by simpa [hf] using h) hp)
  (hg.resolve_left (λ hg, by simpa [hg] using h) hp)

lemma splits_of_splits_mul {f g : polynomial α} (hfg : f * g ≠ 0) (h : splits i (f * g)) :
  splits i f ∧ splits i g :=
⟨or.inr $ λ g hgi hg, or.resolve_left h hfg hgi (by rw map_mul; exact dvd.trans hg (dvd_mul_right _ _)),
 or.inr $ λ g hgi hg, or.resolve_left h hfg hgi (by rw map_mul; exact dvd.trans hg (dvd_mul_left _ _))⟩

lemma splits_of_splits_of_dvd {f g : polynomial α} (hf0 : f ≠ 0) (hf : splits i f) (hgf : g ∣ f) :
  splits i g :=
by { obtain ⟨f, rfl⟩ := hgf, exact (splits_of_splits_mul i hf0 hf).1 }

lemma splits_map_iff (j : β →+* γ) {f : polynomial α} :
  splits j (f.map i) ↔ splits (j.comp i) f :=
by simp [splits, polynomial.map_map]

theorem splits_one : splits i 1 :=
splits_C i 1

theorem splits_X_sub_C {x : α} : (X - C x).splits i :=
splits_of_degree_eq_one _ $ degree_X_sub_C x

theorem splits_id_iff_splits {f : polynomial α} :
  (f.map i).splits (ring_hom.id β) ↔ f.splits i :=
by rw [splits_map_iff, ring_hom.id_comp]

theorem splits_mul_iff {f g : polynomial α} (hf : f ≠ 0) (hg : g ≠ 0) :
  (f * g).splits i ↔ f.splits i ∧ g.splits i :=
⟨splits_of_splits_mul i (mul_ne_zero hf hg), λ ⟨hfs, hgs⟩, splits_mul i hfs hgs⟩

theorem splits_prod {ι : Type w} {s : ι → polynomial α} {t : finset ι} :
  (∀ j ∈ t, (s j).splits i) → (∏ x in t, s x).splits i :=
begin
  refine finset.induction_on t (λ _, splits_one i) (λ a t hat ih ht, _),
  rw finset.forall_mem_insert at ht, rw finset.prod_insert hat,
  exact splits_mul i ht.1 (ih ht.2)
end

theorem splits_prod_iff {ι : Type w} {s : ι → polynomial α} {t : finset ι} :
  (∀ j ∈ t, s j ≠ 0) → ((∏ x in t, s x).splits i ↔ ∀ j ∈ t, (s j).splits i) :=
begin
  refine finset.induction_on t (λ _, ⟨λ _ _ h, h.elim, λ _, splits_one i⟩) (λ a t hat ih ht, _),
  rw finset.forall_mem_insert at ht ⊢,
  rw [finset.prod_insert hat, splits_mul_iff i ht.1 (finset.prod_ne_zero_iff.2 ht.2), ih ht.2]
end

-- MOVE
theorem map_ne_zero {i : α →+* β} {p : polynomial α} (hp : p ≠ 0) : p.map i ≠ 0 :=
mt (map_eq_zero i).1 hp

lemma exists_root_of_splits {f : polynomial α} (hs : splits i f) (hf0 : degree f ≠ 0) :
  ∃ x, eval₂ i x f = 0 :=
if hf0 : f = 0 then ⟨37, by simp [hf0]⟩
else
  let ⟨g, hg⟩ := is_noetherian_ring.exists_irreducible_factor
    (show ¬ is_unit (f.map i), from mt is_unit_iff_degree_eq_zero.1 (by rwa degree_map))
    (map_ne_zero hf0) in
  let ⟨x, hx⟩ := exists_root_of_degree_eq_one (hs.resolve_left hf0 hg.1 hg.2) in
  let ⟨i, hi⟩ := hg.2 in
  ⟨x, by rw [← eval_map, hi, eval_mul, show _ = _, from hx, zero_mul]⟩

lemma exists_multiset_of_splits {f : polynomial α} : splits i f →
  ∃ (s : multiset β), f.map i = C (i f.leading_coeff) *
  (s.map (λ a : β, (X : polynomial β) - C a)).prod :=
suffices splits (ring_hom.id _) (f.map i) → ∃ s : multiset β, f.map i =
  (C (f.map i).leading_coeff) * (s.map (λ a : β, (X : polynomial β) - C a)).prod,
by rwa [splits_map_iff, leading_coeff_map i] at this,
is_noetherian_ring.irreducible_induction_on (f.map i)
  (λ _, ⟨{37}, by simp [i.map_zero]⟩)
  (λ u hu _, ⟨0,
    by conv_lhs { rw eq_C_of_degree_eq_zero (is_unit_iff_degree_eq_zero.1 hu) };
      simp [leading_coeff, nat_degree_eq_of_degree_eq_some (is_unit_iff_degree_eq_zero.1 hu)]⟩)
  (λ f p hf0 hp ih hfs,
    have hpf0 : p * f ≠ 0, from mul_ne_zero hp.ne_zero hf0,
    let ⟨s, hs⟩ := ih (splits_of_splits_mul _ hpf0 hfs).2 in
    ⟨-(p * norm_unit p).coeff 0 :: s,
      have hp1 : degree p = 1, from hfs.resolve_left hpf0 hp (by simp),
      begin
        rw [multiset.map_cons, multiset.prod_cons, leading_coeff_mul, C_mul, mul_assoc,
          mul_left_comm (C f.leading_coeff), ← hs, ← mul_assoc, mul_left_inj' hf0],
        conv_lhs {rw eq_X_add_C_of_degree_eq_one hp1},
        simp only [mul_add, coe_norm_unit hp.ne_zero, mul_comm p, coeff_neg,
          C_neg, sub_eq_add_neg, neg_neg, coeff_C_mul, (mul_assoc _ _ _).symm, C_mul.symm,
          mul_inv_cancel (show p.leading_coeff ≠ 0, from mt leading_coeff_eq_zero.1
            hp.ne_zero), one_mul],
      end⟩)

-- MOVE
theorem roots_zero {R : Type*} [integral_domain R] : (0 : polynomial R).roots = ∅ :=
dif_pos rfl

-- MOVE
theorem roots_C {R : Type*} [integral_domain R] (x : R) : (C x).roots = ∅ :=
if H : x = 0 then by rw [H, C_0, roots_zero] else finset.ext $ λ r,
have h : C x ≠ 0, from λ h, H $ C_inj.1 $ h.symm ▸ C_0.symm,
by rw [mem_roots h, is_root.def, eval_C, eq_false_intro H, eq_false_intro (finset.not_mem_empty r)]

-- MOVE
theorem roots_one {R : Type*} [integral_domain R] : (1 : polynomial R).roots = ∅ :=
roots_C 1

-- MOVE
theorem map_list_prod {R S : Type*} [semiring R] [semiring S] (f : R →+* S) (L : list (polynomial R)) :
  L.prod.map f = (L.map $ map f).prod :=
list.rec_on L (map_one f) $ λ hd tl ih,
by rw [list.prod_cons, map_mul, ih, list.map_cons, list.prod_cons]

-- MOVE
theorem map_multiset_prod {R S : Type*} [comm_semiring R] [comm_semiring S] (f : R →+* S) (m : multiset (polynomial R)) :
  m.prod.map f = (m.map $ map f).prod :=
multiset.induction_on m (map_one f) $ λ hd tl ih,
by rw [multiset.prod_cons, map_mul, ih, multiset.map_cons, multiset.prod_cons]

-- MOVE
theorem map_prod {R S : Type*} [comm_semiring R] [comm_semiring S] (f : R →+* S) {ι : Type*} (g : ι → polynomial R) (s : finset ι) :
  (∏ i in s, g i).map f = ∏ i in s, (g i).map f :=
by { rw [finset.prod, map_multiset_prod, multiset.map_map], refl }

-- MOVE
theorem list.prod_ne_zero {R : Type*} [domain R] {L : list R} :
  (∀ x ∈ L, (x : _) ≠ 0) → L.prod ≠ 0 :=
list.rec_on L (λ _, one_ne_zero) $ λ hd tl ih H, by { rw list.forall_mem_cons at H,
rw list.prod_cons, exact mul_ne_zero H.1 (ih H.2) }

-- MOVE
theorem multiset.forall_mem_cons {α : Sort*} {p : α → Prop} {a : α} {m : multiset α} :
  (∀ x ∈ (a :: m), p x) ↔ p a ∧ ∀ x ∈ m, p x :=
quotient.induction_on' m $ λ L, list.forall_mem_cons

-- MOVE
theorem multiset.prod_ne_zero {R : Type*} [integral_domain R] {m : multiset R} :
  (∀ x ∈ m, (x : _) ≠ 0) → m.prod ≠ 0 :=
multiset.induction_on m (λ _, one_ne_zero) $ λ hd tl ih H, by { rw multiset.forall_mem_cons at H,
rw multiset.prod_cons, exact mul_ne_zero H.1 (ih H.2) }

-- MOVE
theorem roots_list_prod {R : Type*} [integral_domain R] (L : list (polynomial R)) :
  (∀ p ∈ L, (p : _) ≠ 0) → L.prod.roots = L.to_finset.bind roots :=
list.rec_on L (λ _, roots_one) $ λ hd tl ih H,
begin
  rw list.forall_mem_cons at H,
  rw [list.prod_cons, roots_mul (mul_ne_zero H.1 $ list.prod_ne_zero H.2)],
  rw [list.to_finset_cons, finset.bind_insert, ih H.2]
end

-- MOVE
theorem roots_multiset_prod {R : Type*} [integral_domain R] (m : multiset (polynomial R)) :
  (∀ p ∈ m, (p : _) ≠ 0) → m.prod.roots = m.to_finset.bind roots :=
multiset.induction_on m (λ _, roots_one) $ λ hd tl ih H,
begin
  rw multiset.forall_mem_cons at H,
  rw [multiset.prod_cons, roots_mul (mul_ne_zero H.1 $ multiset.prod_ne_zero H.2)],
  rw [multiset.to_finset_cons, finset.bind_insert, ih H.2]
end

-- MOVE
theorem multiset.to_finset_map {α β : Sort*} [decidable_eq α] [decidable_eq β] (f : α → β) (m : multiset α) :
  (m.map f).to_finset = m.to_finset.image f :=
finset.val_inj.1 $ (multiset.erase_dup_map_erase_dup_eq _ _).symm

-- MOVE
theorem multiset.forall_mem_map_iff {α β : Sort*} {p : β → Prop} {m : multiset α} {f : α → β} :
  (∀ y ∈ m.map f, p y) ↔ (∀ x ∈ m, p (f x)) :=
quotient.induction_on' m $ λ L, list.forall_mem_map_iff

theorem roots_map {f : polynomial α} (hf : f.splits $ ring_hom.id α) :
  (f.map i).roots = (f.roots).image i :=
if hf0 : f = 0 then by rw [hf0, map_zero, roots_zero, roots_zero, finset.image_empty] else
have hmf0 : f.map i ≠ 0 := map_ne_zero hf0,
let ⟨m, hm⟩ := exists_multiset_of_splits _ hf in
have h1 : ∀ p ∈ m.map (λ r, X - C r), (p : _) ≠ 0,
  from multiset.forall_mem_map_iff.2 $ λ _ _, X_sub_C_ne_zero _,
have h2 : ∀ p ∈ m.map (λ r, X - C (i r)), (p : _) ≠ 0,
  from multiset.forall_mem_map_iff.2 $ λ _ _, X_sub_C_ne_zero _,
begin
  rw map_id at hm, rw hm at hf0 hmf0 ⊢, rw map_mul at hmf0 ⊢,
  rw [roots_mul hf0, roots_mul hmf0, map_C, roots_C, finset.empty_union, roots_C, finset.empty_union,
      map_multiset_prod, multiset.map_map], simp_rw [(∘), map_sub, map_X, map_C],
  rw [roots_multiset_prod _ h2, multiset.to_finset_map, finset.image_bind,
      roots_multiset_prod _ h1, multiset.to_finset_map, finset.image_bind],
  simp_rw roots_X_sub_C, rw [finset.bind_singleton, finset.bind_singleton], erw finset.image_id
end

section UFD

local attribute [instance, priority 10] principal_ideal_ring.to_unique_factorization_domain
local infix ` ~ᵤ ` : 50 := associated

open unique_factorization_domain associates

lemma splits_of_exists_multiset {f : polynomial α} {s : multiset β}
  (hs : f.map i = C (i f.leading_coeff) * (s.map (λ a : β, (X : polynomial β) - C a)).prod) :
  splits i f :=
if hf0 : f = 0 then or.inl hf0
else
  or.inr $ λ p hp hdp,
    have ht : multiset.rel associated
      (factors (f.map i)) (s.map (λ a : β, (X : polynomial β) - C a)) :=
    unique
      (λ p hp, irreducible_factors (map_ne_zero hf0) _ hp)
      (λ p' m, begin
          obtain ⟨a,m,rfl⟩ := multiset.mem_map.1 m,
          exact irreducible_of_degree_eq_one (degree_X_sub_C _),
        end)
      (associated.symm $ calc _ ~ᵤ f.map i :
        ⟨(units.map' C : units β →* units (polynomial β)) (units.mk0 (f.map i).leading_coeff
            (mt leading_coeff_eq_zero.1 (map_ne_zero hf0))),
          by conv_rhs {rw [hs, ← leading_coeff_map i, mul_comm]}; refl⟩
        ... ~ᵤ _ : associated.symm (unique_factorization_domain.factors_prod (by simpa using hf0))),
  let ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd (by simpa) hp hdp in
  let ⟨q', hq', hqq'⟩ := multiset.exists_mem_of_rel_of_mem ht hq in
  let ⟨a, ha⟩ := multiset.mem_map.1 hq' in
  by rw [← degree_X_sub_C a, ha.2];
    exact degree_eq_degree_of_associated (hpq.trans hqq')

lemma splits_of_splits_id {f : polynomial α} : splits (ring_hom.id _) f → splits i f :=
unique_factorization_domain.induction_on_prime f (λ _, splits_zero _)
  (λ _ hu _, splits_of_degree_le_one _
    ((is_unit_iff_degree_eq_zero.1 hu).symm ▸ dec_trivial))
  (λ a p ha0 hp ih hfi, splits_mul _
    (splits_of_degree_eq_one _
      ((splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).1.resolve_left
        hp.1 (irreducible_of_prime hp) (by rw map_id)))
    (ih (splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).2))

end UFD

lemma splits_iff_exists_multiset {f : polynomial α} : splits i f ↔
  ∃ (s : multiset β), f.map i = C (i f.leading_coeff) *
  (s.map (λ a : β, (X : polynomial β) - C a)).prod :=
⟨exists_multiset_of_splits i, λ ⟨s, hs⟩, splits_of_exists_multiset i hs⟩

lemma splits_comp_of_splits (j : β →+* γ) {f : polynomial α}
  (h : splits i f) : splits (j.comp i) f :=
begin
  change i with ((ring_hom.id _).comp i) at h,
  rw [← splits_map_iff],
  rw [← splits_map_iff i] at h,
  exact splits_of_splits_id _ h
end

end splits

section splitting_field

/-- Non-computably choose an irreducible factor from a polynomial. -/
def factor (f : polynomial α) : polynomial α :=
if H : ∃ g, irreducible g ∧ g ∣ f then classical.some H else X

instance irreducible_factor (f : polynomial α) : irreducible (factor f) :=
begin
  rw factor, split_ifs with H, { exact (classical.some_spec H).1 }, { exact irreducible_X }
end

theorem factor_dvd_of_not_is_unit {f : polynomial α} (hf1 : ¬is_unit f) : factor f ∣ f :=
begin
  by_cases hf2 : f = 0, { rw hf2, exact dvd_zero _ },
  rw [factor, dif_pos (is_noetherian_ring.exists_irreducible_factor hf1 hf2)],
  exact (classical.some_spec $ is_noetherian_ring.exists_irreducible_factor hf1 hf2).2
end

theorem factor_dvd_of_degree_ne_zero {f : polynomial α} (hf : f.degree ≠ 0) : factor f ∣ f :=
factor_dvd_of_not_is_unit (mt degree_eq_zero_of_is_unit hf)

theorem factor_dvd_of_nat_degree_ne_zero {f : polynomial α} (hf : f.nat_degree ≠ 0) : factor f ∣ f :=
factor_dvd_of_degree_ne_zero (mt nat_degree_eq_of_degree_eq_some hf)

/-- Divide a polynomial f by X - C r where r is a root of f in a bigger field extension. -/
def remove_factor (f : polynomial α) : polynomial (adjoin_root $ factor f) :=
map (adjoin_root.of f.factor) f /ₘ (X - C (adjoin_root.root f.factor))

theorem X_sub_C_mul_remove_factor (f : polynomial α) (hf : f.nat_degree ≠ 0) :
  (X - C (adjoin_root.root f.factor)) * f.remove_factor = map (adjoin_root.of f.factor) f :=
let ⟨g, hg⟩ := factor_dvd_of_nat_degree_ne_zero hf in
mul_div_by_monic_eq_iff_is_root.2 $ by rw [is_root.def, eval_map, hg, eval₂_mul, ← hg,
    adjoin_root.eval₂_root, zero_mul]

theorem nat_degree_remove_factor (f : polynomial α) :
  f.remove_factor.nat_degree = f.nat_degree - 1 :=
by rw [remove_factor, nat_degree_div_by_monic _ (monic_X_sub_C _), nat_degree_map, nat_degree_X_sub_C]

theorem nat_degree_remove_factor' {f : polynomial α} {n : ℕ} (hfn : f.nat_degree = n+1) :
  f.remove_factor.nat_degree = n :=
by rw [nat_degree_remove_factor, hfn, n.add_sub_cancel]

/-- Auxiliary construction to a splitting field of a polynomial. Uses induction on the degree. -/
def splitting_field_aux (n : ℕ) : Π {α : Type u} [field α], by exactI Π (f : polynomial α),
  f.nat_degree = n → Type u :=
nat.rec_on n (λ α _ _ _, α) $ λ n ih α _ f hf, by exactI
ih f.remove_factor (nat_degree_remove_factor' hf)

namespace splitting_field_aux

theorem succ (n : ℕ) (f : polynomial α) (hfn : f.nat_degree = n + 1) :
  splitting_field_aux (n+1) f hfn =
    splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn) := rfl

instance field (n : ℕ) : Π {α : Type u} [field α], by exactI
  Π {f : polynomial α} (hfn : f.nat_degree = n), field (splitting_field_aux n f hfn) :=
nat.rec_on n (λ α _ _ _, ‹field α›) $ λ n ih α _ f hf, ih _

instance inhabited {n : ℕ} {f : polynomial α} (hfn : f.nat_degree = n) :
  inhabited (splitting_field_aux n f hfn) := ⟨37⟩

instance algebra (n : ℕ) : Π {α : Type u} [field α], by exactI
  Π {f : polynomial α} (hfn : f.nat_degree = n), algebra α (splitting_field_aux n f hfn) :=
nat.rec_on n (λ α _ _ _, by exactI algebra.id α) $ λ n ih α _ f hfn,
by exactI @@algebra.comap.algebra _ _ _ _ _ _ _ (ih _)

instance algebra' {n : ℕ} {f : polynomial α} (hfn : f.nat_degree = n + 1) :
  algebra (adjoin_root f.factor) (splitting_field_aux _ _ hfn) :=
splitting_field_aux.algebra n _

instance algebra'' {n : ℕ} {f : polynomial α} (hfn : f.nat_degree = n + 1) :
  algebra α (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)) :=
splitting_field_aux.algebra (n+1) hfn

instance algebra''' {n : ℕ} {f : polynomial α} (hfn : f.nat_degree = n + 1) :
  algebra (adjoin_root f.factor)
    (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)) :=
splitting_field_aux.algebra n _

instance algebra_tower {n : ℕ} {f : polynomial α} (hfn : f.nat_degree = n + 1) :
  is_algebra_tower α (adjoin_root f.factor) (splitting_field_aux _ _ hfn) :=
is_algebra_tower.of_algebra_map_eq $ λ x, rfl

instance algebra_tower' {n : ℕ} {f : polynomial α} (hfn : f.nat_degree = n + 1) :
  is_algebra_tower α (adjoin_root f.factor)
    (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)) :=
is_algebra_tower.of_algebra_map_eq $ λ x, rfl

theorem algebra_map_succ (n : ℕ) (f : polynomial α) (hfn : f.nat_degree = n + 1) :
  by exact algebra_map α (splitting_field_aux _ _ hfn) =
    (algebra_map (adjoin_root f.factor)
        (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn))).comp
      (adjoin_root.of f.factor) :=
rfl

protected theorem splits (n : ℕ) : ∀ {α : Type u} [field α], by exactI
  ∀ (f : polynomial α) (hfn : f.nat_degree = n),
    splits (algebra_map α $ splitting_field_aux n f hfn) f :=
nat.rec_on n (λ α _ _ hf, by exactI splits_of_degree_le_one _
  (le_trans degree_le_nat_degree $ hf.symm ▸ with_bot.coe_le_coe.2 zero_le_one)) $ λ n ih α _ f hf,
by { resetI, rw [← splits_id_iff_splits, algebra_map_succ, ← map_map, splits_id_iff_splits,
    ← X_sub_C_mul_remove_factor f (λ h, by { rw h at hf, cases hf })],
exact splits_mul _ (splits_X_sub_C _) (ih _ _) }

theorem exists_lift (n : ℕ) : ∀ {α : Type u} [field α], by exactI
  ∀ (f : polynomial α) (hfn : f.nat_degree = n) {β : Type*} [field β], by exactI
    ∀ (j : α →+* β) (hf : splits j f), ∃ k : splitting_field_aux n f hfn →+* β,
      k.comp (algebra_map _ _) = j :=
nat.rec_on n (λ α _ _ _ β _ j _, by exactI ⟨j, j.comp_id⟩) $ λ n ih α _ f hf β _ j hj, by exactI
have hndf : f.nat_degree ≠ 0, by { intro h, rw h at hf, cases hf },
have hfn0 : f ≠ 0, by { intro h, rw h at hndf, exact hndf rfl },
let ⟨r, hr⟩ := exists_root_of_splits _ (splits_of_splits_of_dvd j hfn0 hj
  (factor_dvd_of_nat_degree_ne_zero hndf)) (mt is_unit_iff_degree_eq_zero.2 f.irreducible_factor.1) in
have hmf0 : map (adjoin_root.of f.factor) f ≠ 0, from map_ne_zero hfn0,
have hsf : splits (adjoin_root.lift j r hr) f.remove_factor,
by { rw ← X_sub_C_mul_remove_factor _ hndf at hmf0, refine (splits_of_splits_mul _ hmf0 _).2,
  rwa [X_sub_C_mul_remove_factor _ hndf, ← splits_id_iff_splits, map_map, adjoin_root.lift_comp_of,
      splits_id_iff_splits] },
let ⟨k, hk⟩ := ih f.remove_factor (nat_degree_remove_factor' hf) (adjoin_root.lift j r hr) hsf in
⟨k, by rw [algebra_map_succ, ← ring_hom.comp_assoc, hk, adjoin_root.lift_comp_of]⟩

theorem adjoin_roots (n : ℕ) : ∀ {α : Type u} [field α], by exactI
  ∀ (f : polynomial α) (hfn : f.nat_degree = n),
    algebra.adjoin α (↑(f.map $ algebra_map α $ splitting_field_aux n f hfn).roots :
      set (splitting_field_aux n f hfn)) = ⊤ :=
nat.rec_on n (λ α _ f hf, by exactI algebra.eq_top_iff.2 (λ x, subalgebra.range_le _ ⟨x, rfl⟩)) $
λ n ih α _ f hfn, by exactI
have hndf : f.nat_degree ≠ 0, by { intro h, rw h at hfn, cases hfn },
have hfn0 : f ≠ 0, by { intro h, rw h at hndf, exact hndf rfl },
have hmf0 : map (algebra_map α (splitting_field_aux n.succ f hfn)) f ≠ 0 := map_ne_zero hfn0,
by { rw [algebra_map_succ, ← map_map, ← X_sub_C_mul_remove_factor _ hndf, map_mul] at hmf0 ⊢,
rw [roots_mul hmf0, map_sub, map_X, map_C, roots_X_sub_C, finset.coe_union, finset.coe_singleton,
    algebra.adjoin_union, ← set.image_singleton, algebra.adjoin_algebra_map α (adjoin_root f.factor)
      (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)),
    adjoin_root.adjoin_root_eq_top, algebra.map_top,
    is_algebra_tower.range_under_adjoin α (adjoin_root f.factor)
      (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)),
    ih, is_algebra_tower.subalgebra_comap_top] }

end splitting_field_aux

/-- A splitting field of a polynomial. -/
def splitting_field (f : polynomial α) :=
splitting_field_aux _ f rfl

namespace splitting_field

variables (f : polynomial α)

instance : field (splitting_field f) :=
splitting_field_aux.field _ _

instance inhabited : inhabited (splitting_field f) := ⟨37⟩

instance : algebra α (splitting_field f) :=
splitting_field_aux.algebra _ _

protected theorem splits : splits (algebra_map α (splitting_field f)) f :=
splitting_field_aux.splits _ _ _

variables [algebra α β] (hb : splits (algebra_map α β) f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : splitting_field f →ₐ[α] β :=
{ commutes' := λ r, by { have := classical.some_spec (splitting_field_aux.exists_lift _ _ _ _ hb),
    exact ring_hom.ext_iff.1 this r },
  .. classical.some (splitting_field_aux.exists_lift _ _ _ _ hb) }

theorem adjoin_roots : algebra.adjoin α
    (↑(f.map (algebra_map α $ splitting_field f)).roots : set (splitting_field f)) = ⊤ :=
splitting_field_aux.adjoin_roots _ _ _

end splitting_field

variables (α β) [algebra α β]
/-- Typeclass characterising splitting fields. -/
class is_splitting_field (f : polynomial α) : Prop :=
(splits [] : splits (algebra_map α β) f)
(adjoin_roots [] : algebra.adjoin α (↑(f.map (algebra_map α β)).roots : set β) = ⊤)

namespace is_splitting_field

variables {α}
instance splitting_field (f : polynomial α) : is_splitting_field α (splitting_field f) f :=
⟨splitting_field.splits f, splitting_field.adjoin_roots f⟩

variables {α β γ} [algebra β γ] [algebra α γ] [is_algebra_tower α β γ]

-- MOVE, REFACTOR
variables (α)
theorem subalgebra.mem_res {U : subalgebra β γ} {x : γ} : x ∈ is_algebra_tower.subalgebra_comap α β γ U ↔ x ∈ U :=
iff.rfl

-- MOVE, REFACTOR
variables (α)
theorem subalgebra.res_inj {U V : subalgebra β γ} (H : is_algebra_tower.subalgebra_comap α β γ U = is_algebra_tower.subalgebra_comap α β γ V) : U = V :=
subalgebra.ext $ λ x, by rw [← subalgebra.mem_res α, H, subalgebra.mem_res]

variables {α}
instance map (f : polynomial α) [is_splitting_field α γ f] :
  is_splitting_field β γ (f.map $ algebra_map α β) :=
⟨by { rw [splits_map_iff, ← is_algebra_tower.algebra_map_eq], exact splits γ f },
subalgebra.res_inj α $ by { rw [map_map, ← is_algebra_tower.algebra_map_eq, is_algebra_tower.subalgebra_comap_top, eq_top_iff, ← adjoin_roots γ f, algebra.adjoin_le_iff],
  exact λ x hx, @algebra.subset_adjoin β _ _ _ _ _ _ hx }⟩

-- MOVE
theorem surjective_algbera_map_iff {α β : Type*} [comm_semiring α] [semiring β] [algebra α β] :
  function.surjective (algebra_map α β) ↔ (⊤ : subalgebra α β) = ⊥ :=
⟨λ h, eq_bot_iff.2 $ λ y _, let ⟨x, hx⟩ := h y in hx ▸ subalgebra.algebra_map_mem _ _,
λ h y, algebra.mem_bot.1 $ eq_bot_iff.1 h (algebra.mem_top : y ∈ _)⟩

-- MOVE
theorem bijective_algbera_map_iff :
  function.bijective (algebra_map α β) ↔ (⊤ : subalgebra α β) = ⊥ :=
⟨λ h, surjective_algbera_map_iff.1 h.2,
λ h, ⟨(algebra_map α β).injective, surjective_algbera_map_iff.2 h⟩⟩

variables {α} (β)
theorem splits_iff (f : polynomial α) [is_splitting_field α β f] :
  polynomial.splits (ring_hom.id α) f ↔ (⊤ : subalgebra α β) = ⊥ :=
⟨λ h, eq_bot_iff.2 $ adjoin_roots β f ▸ (roots_map (algebra_map α β) h).symm ▸
  algebra.adjoin_le_iff.2 (λ y hy, let ⟨x, hxs, hxy⟩ := finset.mem_image.1 hy in hxy ▸
  subalgebra.algebra_map_mem _ _),
λ h, @ring_equiv.to_ring_hom_refl α _ ▸
  ring_equiv.trans_symm (ring_equiv.of_bijective _ $ bijective_algbera_map_iff.2 h) ▸
  by { rw ring_equiv.to_ring_hom_trans, exact splits_comp_of_splits _ _ (splits β f) }⟩

theorem mul (f g : polynomial α) (hf : f ≠ 0) (hg : g ≠ 0) [is_splitting_field α β f]
  [is_splitting_field β γ (g.map $ algebra_map α β)] :
  is_splitting_field α γ (f * g) :=
⟨(is_algebra_tower.algebra_map_eq α β γ).symm ▸ splits_mul _
  (splits_comp_of_splits _ _ (splits β f))
  ((splits_map_iff _ _).1 (splits γ $ g.map $ algebra_map α β)),
by rw [map_mul, roots_mul (mul_ne_zero (map_ne_zero hf : f.map (algebra_map α γ) ≠ 0)
        (map_ne_zero hg)), finset.coe_union, algebra.adjoin_union,
      is_algebra_tower.algebra_map_eq α β γ, ← map_map,
      roots_map (algebra_map β γ) ((splits_id_iff_splits $ algebra_map α β).2 $ splits β f),
      finset.coe_image, algebra.adjoin_algebra_map, adjoin_roots, algebra.map_top,
      is_algebra_tower.range_under_adjoin, ← map_map, adjoin_roots, is_algebra_tower.subalgebra_comap_top]⟩

end is_splitting_field

end splitting_field

end polynomial
