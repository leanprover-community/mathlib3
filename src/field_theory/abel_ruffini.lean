import group_theory.solvable
import field_theory.polynomial_galois_group
import ring_theory.roots_of_unity

noncomputable theory
open_locale classical

open polynomial intermediate_field

--todo: remove hypothesis in `nat_degree_X_pow_sub_C`
lemma leading_coeff_X_pow_sub_C {R : Type*} [ring R] [nontrivial R] {n : ℕ} (hn : 0 < n) (a : R) :
  (X ^ n - C a).leading_coeff = 1 :=
begin
  rw [leading_coeff, nat_degree_X_pow_sub_C hn, coeff_sub, coeff_X_pow_self,
      coeff_C, if_neg (pos_iff_ne_zero.mp hn), sub_zero],
  assumption,
end

lemma leading_coeff_X_pow_sub_one {R : Type*} [ring R] [nontrivial R] {n : ℕ} (hn : 0 < n) :
  (X ^ n - 1 : polynomial R).leading_coeff = 1 :=
begin
  rw [←C_1, leading_coeff_X_pow_sub_C hn],
  assumption,
end

lemma splits_C_mul_iff {F : Type*} [field F] {E : Type*} [field E] (i : F →+* E)
  {p : polynomial F} {a : F} (ha : a ≠ 0) : (C a * p).splits i ↔ p.splits i :=
begin
  by_cases hp : p = 0,
  { rw [hp, mul_zero] },
  { rw [splits_mul_iff i (mt C_eq_zero.mp ha) hp, and_iff_right (splits_C i a)] },
end

lemma prod_comp {R : Type*} [comm_semiring R] (s : multiset (polynomial R)) (p : polynomial R) :
  s.prod.comp p = (s.map (λ q : polynomial R, q.comp p)).prod :=
(s.prod_hom (monoid_hom.mk (λ q : polynomial R, q.comp p) one_comp (λ q r, mul_comp q r p))).symm

section abel_ruffini

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

lemma gal_zero_is_solvable : is_solvable (gal (0 : polynomial F)) :=
by apply_instance

lemma gal_one_is_solvable : is_solvable (gal (1 : polynomial F)) :=
by apply_instance

lemma gal_C_is_solvable (x : F) : is_solvable (gal (C x)) :=
by apply_instance

lemma gal_X_is_solvable : is_solvable (gal (X : polynomial F)) :=
by apply_instance

lemma gal_X_sub_C_is_solvable (x : F) : is_solvable (gal (X - C x)) :=
by apply_instance

lemma gal_X_pow_is_solvable (n : ℕ) : is_solvable (gal (X ^ n : polynomial F)) :=
by apply_instance

lemma gal_mul_is_solvable {p q : polynomial F}
  (hp : is_solvable (gal p)) (hq : is_solvable (gal q)) : is_solvable (gal (p * q)) :=
solvable_of_solvable_injective (gal.restrict_prod_injective p q)

lemma gal_prod_is_solvable {s : multiset (polynomial F)}
  (hs : ∀ p ∈ s, is_solvable (gal p)) : is_solvable (gal s.prod) :=
begin
  apply multiset.induction_on' s,
  { rw [multiset.empty_eq_zero, multiset.prod_zero],
    exact gal_one_is_solvable },
  { intros p t hps hts ht,
    rw [multiset.insert_eq_cons, multiset.prod_cons],
    exact gal_mul_is_solvable (hs p hps) ht },
end

lemma lemma2 {p q : polynomial F} (hpq : fact (splits (algebra_map F q.splitting_field) p))
  (hq : is_solvable (gal q)) : is_solvable (gal p) :=
begin
  haveI : is_solvable (q.splitting_field ≃ₐ[F] q.splitting_field) := hq,
  exact solvable_of_surjective (alg_equiv.restrict_normal_hom_surjective q.splitting_field),
end

lemma lemma3 (p q : polynomial F)
  (hpq : p.splits (algebra_map F q.splitting_field))
  (hp : is_solvable (gal p))
  (hq : is_solvable (gal (q.map (algebra_map F p.splitting_field)))) :
  is_solvable (gal q) :=
begin
  let K := p.splitting_field,
  let L := q.splitting_field,
  haveI : fact (p.splits (algebra_map F L)) := hpq,
  have iso : L ≃ₐ[K] (q.map (algebra_map F p.splitting_field)).splitting_field,
  { exact is_splitting_field.alg_equiv L (q.map (algebra_map F K)) },
  haveI : is_solvable (K ≃ₐ[F] K) := hp,
  haveI : is_solvable (L ≃ₐ[K] L) := by
  { /- transfer solvability along isomorphism -/
    sorry },
  exact is_solvable_of_is_scalar_tower F p.splitting_field q.splitting_field,
end

section gal_X_pow_sub_C

lemma gal_X_pow_sub_one_is_solvable (n : ℕ) : is_solvable (X ^ n - 1 : polynomial F).gal :=
begin
  suffices : ∀ σ τ : (X ^ n - 1 : polynomial F).gal, σ * τ = τ * σ,
  { sorry },
  intros σ τ,
  ext a ha,
  rw [mem_root_set, alg_hom.map_sub, aeval_X_pow, aeval_one, sub_eq_zero_iff_eq] at ha,
  have key1 : ∀ σ : (X ^ n - 1 : polynomial F).gal, ∃ m : ℕ, σ a = a ^ m,
  { intro σ,
    sorry },
  obtain ⟨c, hc⟩ := key1 σ,
  obtain ⟨d, hd⟩ := key1 τ,
  change σ (τ a) = τ (σ a),
  rw [hc, hd, σ.map_pow, τ.map_pow, hc, hd, ←pow_mul, pow_mul'],
  sorry,
end

lemma gal_X_pow_sub_C_is_solvable_aux (n : ℕ) (a : F)
  (h : (X ^ n - 1 : polynomial F).splits (ring_hom.id F)) : is_solvable (X ^ n - C a).gal :=
begin
  by_cases ha : a = 0,
  { rw [ha, C_0, sub_zero],
    exact gal_X_pow_is_solvable n },
  have ha' : algebra_map F (X ^ n - C a).splitting_field a ≠ 0 :=
    mt ((ring_hom.injective_iff _).mp (ring_hom.injective _) a) ha,
  by_cases hn : n = 0,
  { rw [hn, pow_zero, ←C_1, ←C_sub],
    exact gal_C_is_solvable (1 - a) },
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn,
  have hn'' : (X ^ n - C a).degree ≠ 0,
  { rwa [degree_X_pow_sub_C hn', ne, with_bot.coe_eq_zero],
    apply_instance },
  have hn''' : X ^ n - C a ≠ 0,
  { intro h,
    replace h := congr_arg (eval 0) h,
    rw [eval_sub, eval_zero, sub_eq_zero_iff_eq, eval_pow, eval_X, eval_C, zero_pow hn'] at h,
    exact ha h.symm },
  have key0 : ∀ {c}, c ^ n = 1 → ∃ d, algebra_map F (X ^ n - C a).splitting_field d = c,
  { intros c hc,
    rw [←ring_hom.mem_range],
    apply minpoly.mem_range_of_degree_eq_one,
    refine or.resolve_left h _ _ _,
    { intro h,
      replace h := congr_arg nat_degree h,
      rw [←C_1, nat_degree_X_pow_sub_C hn', nat_degree_zero] at h,
      exact hn h,
      apply_instance },
    { exact minpoly.irreducible ((splitting_field.normal (X ^ n - C a)).is_integral c) },
    { apply minpoly.dvd,
      rwa [map_id, alg_hom.map_sub, aeval_X_pow, aeval_one, sub_eq_zero_iff_eq] } },
  suffices : ∀ σ τ : (X ^ n - C a).gal, σ * τ = τ * σ,
  { sorry },
  intros σ τ,
  ext b hb,
  rw [mem_root_set hn''', alg_hom.map_sub, aeval_X_pow, aeval_C, sub_eq_zero_iff_eq] at hb,
  have hb' : b ≠ 0,
  { intro hb',
    rw [hb', zero_pow hn'] at hb,
    exact ha' hb.symm },
  have key2 : ∀ σ : (X ^ n - C a).gal, ∃ c, σ b = b * algebra_map F _ c,
  { intro σ,
    have key : (σ b / b) ^ n = 1,
    { rw [div_pow, ←σ.map_pow, hb, σ.commutes, div_self ha'] },
    obtain ⟨c, hc⟩ := key0 key,
    use c,
    rw [hc, mul_div_cancel' (σ b) hb'] },
  obtain ⟨c, hc⟩ := key2 σ,
  obtain ⟨d, hd⟩ := key2 τ,
  change σ (τ b) = τ (σ b),
  rw [hc, hd, σ.map_mul, τ.map_mul, hc, hd, σ.commutes, τ.commutes],
  ring,
end

lemma splits_X_pow_sub_one_of_X_pow_sub_C {F : Type*} [field F] {E : Type*} [field E]
  (i : F →+* E) (n : ℕ) {a : F} (ha : a ≠ 0) (h : (X ^ n - C a).splits i) : (X ^ n - 1).splits i :=
begin
  have ha' : i a ≠ 0 := mt (i.injective_iff.mp (i.injective) a) ha,
  by_cases hn : n = 0,
  { rw [hn, pow_zero, sub_self],
    exact splits_zero i },
  have hn' : 0 < n := pos_iff_ne_zero.mpr hn,
  have hn'' : (X ^ n - C a).degree ≠ 0,
  { rwa [degree_X_pow_sub_C hn', ne, with_bot.coe_eq_zero],
    apply_instance },
  obtain ⟨b, hb⟩ := exists_root_of_splits i h hn'',
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero_iff_eq] at hb,
  have hb' : b ≠ 0,
  { intro hb',
    rw [hb', zero_pow hn'] at hb,
    exact ha' hb.symm },
  let s := ((X ^ n - C a).map i).roots,
  have hs : _ = _ * (s.map _).prod := eq_prod_roots_of_splits h,
  have hs' : s.card = n,
  { rw [splits_iff_card_roots.mp ((splits_id_iff_splits i).mpr h), nat_degree_map],
    exact nat_degree_X_pow_sub_C hn' },
  rw [leading_coeff_X_pow_sub_C hn', ring_hom.map_one, C_1, one_mul] at hs,
  apply @splits_of_exists_multiset F E _ _ i (X ^ n - 1) (s.map (λ c : E, c / b)),
  rw [leading_coeff_X_pow_sub_one hn', ring_hom.map_one, C_1, one_mul],
  have key : (X ^ n - 1).map i = C (i a⁻¹) * ((X ^ n - C a).map i).comp (C b * X),
  { rw [map_sub, map_sub, map_pow, map_X, map_C, map_one, sub_comp, pow_comp, X_comp, C_comp,
        mul_pow, ←C_pow, hb, mul_sub, ←mul_assoc, ←C_mul, ←ring_hom.map_mul, inv_mul_cancel ha,
        ring_hom.map_one, C_1, one_mul] },
  rw [key, hs, prod_comp, multiset.map_map, multiset.map_map],
  have key' : (λ q : polynomial E, q.comp (C b * X)) ∘ (λ c : E, X - C c) =
    (λ c : E, C b * (X - C (c / b))),
  { ext1 c,
    change (X - C c).comp (C b * X) = C b * (X - C (c / b)),
    rw [sub_comp, X_comp, C_comp, mul_sub, ←C_mul, mul_div_cancel' c hb'] },
  rw [key', multiset.prod_map_mul, multiset.map_const, multiset.prod_repeat, hs', ←C_pow, hb,
      ←mul_assoc, ←C_mul, ←ring_hom.map_mul, inv_mul_cancel ha, ring_hom.map_one, C_1, one_mul],
  exact field.to_nontrivial F,
  exact field.to_nontrivial F,
end

lemma gal_X_pow_sub_C_is_solvable (n : ℕ) (x : F) : is_solvable (X ^ n - C x).gal :=
begin
  by_cases hx : x = 0,
  { rw [hx, C_0, sub_zero],
    exact gal_X_pow_is_solvable n },
  apply lemma3 (X ^ n - 1) (X ^ n - C x),
  { exact splits_X_pow_sub_one_of_X_pow_sub_C _ n hx (splitting_field.splits _) },
  { exact gal_X_pow_sub_one_is_solvable n },
  { rw [map_sub, map_pow, map_X, map_C],
    apply gal_X_pow_sub_C_is_solvable_aux,
    have key := splitting_field.splits (X ^ n - 1 : polynomial F),
    rwa [←splits_id_iff_splits, map_sub, map_pow, map_X, map_one] at key },
end

end gal_X_pow_sub_C

variables (F)

inductive is_SBR : E → Prop
| base (a : F) : is_SBR (algebra_map F E a)
| add (a b : E) : is_SBR a → is_SBR b → is_SBR (a + b)
| neg (α : E) : is_SBR α → is_SBR (-α)
| mul (α β : E) : is_SBR α → is_SBR β → is_SBR (α * β)
| inv (α : E) : is_SBR α → is_SBR α⁻¹
| rad (α : E) (n : ℕ) (hn : n ≠ 0) : is_SBR (α^n) → is_SBR α

variables (E)

def SBR : intermediate_field F E :=
{ carrier := is_SBR F,
  zero_mem' := by { convert is_SBR.base (0 : F), rw ring_hom.map_zero },
  add_mem' := is_SBR.add,
  neg_mem' := is_SBR.neg,
  one_mem' := by { convert is_SBR.base (1 : F), rw ring_hom.map_one },
  mul_mem' := is_SBR.mul,
  inv_mem' := is_SBR.inv,
  algebra_map_mem' := is_SBR.base }

namespace SBR

variables {F} {E} {α : E}

lemma induction (P : SBR F E → Prop)
(base : ∀ α : F, P (algebra_map F (SBR F E) α))
(add : ∀ α β : SBR F E, P α → P β → P (α + β))
(neg : ∀ α : SBR F E, P α → P (-α))
(mul : ∀ α β : SBR F E, P α → P β → P (α * β))
(inv : ∀ α : SBR F E, P α → P α⁻¹)
(rad : ∀ α : SBR F E, ∀ n : ℕ, n ≠ 0 → P (α^n) → P α)
(α : SBR F E) : P α :=
begin
  revert α,
  suffices : ∀ (α : E), is_SBR F α → (∃ β : SBR F E, ↑β = α ∧ P β),
  { intro α,
    obtain ⟨α₀, hα₀, Pα⟩ := this α (subtype.mem α),
    convert Pα,
    exact subtype.ext hα₀.symm },
  apply is_SBR.rec,
  { exact λ α, ⟨algebra_map F (SBR F E) α, rfl, base α⟩ },
  { intros α β hα hβ Pα Pβ,
    obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := ⟨Pα, Pβ⟩,
    exact ⟨α₀ + β₀, by {rw [←hα₀, ←hβ₀], refl }, add α₀ β₀ Pα Pβ⟩ },
  { intros α hα Pα,
    obtain ⟨α₀, hα₀, Pα⟩ := Pα,
    exact ⟨-α₀, by {rw ←hα₀, refl }, neg α₀ Pα⟩ },
  { intros α β hα hβ Pα Pβ,
    obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := ⟨Pα, Pβ⟩,
    exact ⟨α₀ * β₀, by {rw [←hα₀, ←hβ₀], refl }, mul α₀ β₀ Pα Pβ⟩ },
  { intros α hα Pα,
    obtain ⟨α₀, hα₀, Pα⟩ := Pα,
    exact ⟨α₀⁻¹, by {rw ←hα₀, refl }, inv α₀ Pα⟩ },
  { intros α n hn hα Pα,
    obtain ⟨α₀, hα₀, Pα⟩ := Pα,
    refine ⟨⟨α, is_SBR.rad α n hn hα⟩, rfl, rad _ n hn _⟩,
    convert Pα,
    exact subtype.ext (eq.trans ((SBR F E).coe_pow _ n) hα₀.symm) }
end

theorem is_integral (α : SBR F E) : is_integral F α :=
begin
  revert α,
  apply SBR.induction,
  { exact λ _, is_integral_algebra_map },
  { exact λ _ _, is_integral_add },
  { exact λ _, is_integral_neg },
  { exact λ _ _, is_integral_mul },
  { exact λ α hα, subalgebra.inv_mem_of_algebraic (integral_closure F (SBR F E))
      (show is_algebraic F ↑(⟨α, hα⟩ : integral_closure F (SBR F E)),
        by exact (is_algebraic_iff_is_integral F).mpr hα) },
  { intros α n hn hα,
    obtain ⟨p, h1, h2⟩ := (is_algebraic_iff_is_integral F).mpr hα,
    refine (is_algebraic_iff_is_integral F).mp ⟨p.comp (X ^ n),
      ⟨λ h, h1 (leading_coeff_eq_zero.mp _), by rw [aeval_comp, aeval_X_pow, h2]⟩⟩,
    rwa [←leading_coeff_eq_zero, leading_coeff_comp, leading_coeff_X_pow, one_pow, mul_one] at h,
    rwa nat_degree_X_pow }
end

def P (α : SBR F E) : Prop := is_solvable (minpoly F α).gal

lemma induction3 {α : SBR F E} {n : ℕ} (hn : n ≠ 0) (hα : P (α ^ n)) : P α :=
begin
  let p := minpoly F (α ^ n),
  have hp : p.comp (X ^ n) ≠ 0,
  { intro h,
    cases (comp_eq_zero_iff.mp h) with h' h',
    { exact minpoly.ne_zero (is_integral (α ^ n)) h' },
    { exact hn (by rw [←nat_degree_C _, ←h'.2, nat_degree_X_pow]) } },
  apply lemma2,
  { apply splits_of_splits_of_dvd,
    { exact hp },
    { exact splitting_field.splits (p.comp (X ^ n)) },
    { apply minpoly.dvd,
      rw [aeval_comp, aeval_X_pow, minpoly.aeval] } },
  { apply lemma3 p (p.comp (X ^ n)),
    { exact gal.splits_in_splitting_field_of_comp _ _ (by rwa [nat_degree_X_pow]) },
    { exact hα },
    { obtain ⟨s, hs⟩ := exists_multiset_of_splits _ (splitting_field.splits p),
      rw [map_comp, map_pow, map_X, hs, mul_comp, C_comp],
      apply gal_mul_is_solvable,
      { exact gal_C_is_solvable _ },
      { rw prod_comp,
        apply gal_prod_is_solvable,
        intros q hq,
        rw multiset.mem_map at hq,
        obtain ⟨q, hq, rfl⟩ := hq,
        rw multiset.mem_map at hq,
        obtain ⟨q, hq, rfl⟩ := hq,
        rw [sub_comp, X_comp, C_comp],
        exact gal_X_pow_sub_C_is_solvable n q } } },
end

--todo: clean up
lemma induction2 {α β γ : SBR F E} (hγ : γ ∈ F⟮α, β⟯) (hα : P α) (hβ : P β) : P γ :=
begin
  let p := (minpoly F α),
  let q := (minpoly F β),
  have hpq := polynomial.splits_of_splits_mul _ (mul_ne_zero (minpoly.ne_zero (is_integral α))
    (minpoly.ne_zero (is_integral β))) (splitting_field.splits (p * q)),
  let f : F⟮α, β⟯ →ₐ[F] (p * q).splitting_field := classical.choice (alg_hom_mk_adjoin_splits
  begin
    intros x hx,
    cases hx,
    rw hx,
    exact ⟨is_integral α, hpq.1⟩,
    cases hx,
    exact ⟨is_integral β, hpq.2⟩,
  end),
  have key : minpoly F γ = minpoly F (f ⟨γ, hγ⟩) := minpoly.unique' (normal.is_integral
    (splitting_field.normal _) _) (minpoly.irreducible (is_integral γ)) begin
      suffices : aeval (⟨γ, hγ⟩ : F ⟮α, β⟯) (minpoly F γ) = 0,
      { rw [aeval_alg_hom_apply, this, alg_hom.map_zero] },
      apply (algebra_map F⟮α, β⟯ (SBR F E)).injective,
      rw [ring_hom.map_zero, is_scalar_tower.algebra_map_aeval],
      exact minpoly.aeval F γ,
    end (minpoly.monic (is_integral γ)),
  rw [P, key],
  exact lemma2 (normal.splits (splitting_field.normal _) _) (gal_mul_is_solvable hα hβ),
end

lemma induction1 {α β : SBR F E} (hβ : β ∈ F⟮α⟯) (hα : P α) : P β :=
induction2 (adjoin.mono F _ _ (ge_of_eq (set.pair_eq_singleton α)) hβ) hα hα

theorem solvable_gal_of_SBR (α : SBR F E) :
  is_solvable (minpoly F α).gal :=
begin
  revert α,
  apply SBR.induction,
  { exact λ α, by { rw minpoly.eq_X_sub_C, exact gal_X_sub_C_is_solvable α } },
  { exact λ α β, induction2 (add_mem _ (subset_adjoin F _ (set.mem_insert α _))
      (subset_adjoin F _ (set.mem_insert_of_mem α (set.mem_singleton β)))) },
  { exact λ α, induction1 (neg_mem _ (mem_adjoin_simple_self F α)) },
  { exact λ α β, induction2 (mul_mem _ (subset_adjoin F _ (set.mem_insert α _))
      (subset_adjoin F _ (set.mem_insert_of_mem α (set.mem_singleton β)))) },
  { exact λ α, induction1 (inv_mem _ (mem_adjoin_simple_self F α)) },
  { exact λ α n, induction3 },
end

end SBR

end abel_ruffini
