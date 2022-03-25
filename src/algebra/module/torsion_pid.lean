import ring_theory.principal_ideal_domain
import algebra.direct_sum.module
import ring_theory.finiteness
import algebra.module.torsion

universes u v
open_locale big_operators

namespace associates
theorem finset_prod_mk {α β : Type*} [comm_monoid α] {p : finset β} {f : β → α} :
  ∏ i in p, associates.mk (f i) = associates.mk (∏ i in p, f i) :=
by rw [finset.prod_eq_multiset_prod, ← multiset.map_map, prod_mk, ← finset.prod_eq_multiset_prod]

lemma count_le_count_of_le
  {α : Type*} [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]
  {a b p : associates α} (ha : a ≠ 0) (hb : b ≠ 0) (hp : irreducible p) [decidable_eq α]
  [decidable_eq (associates α)] [Π p : associates α, decidable (irreducible p)]
  (h : a.factors ≤ b.factors) : p.count a.factors ≤ p.count b.factors :=
begin
  obtain ⟨sa, h_sa⟩ := factors_eq_some_iff_ne_zero.mpr ha,
  obtain ⟨sb, h_sb⟩ := factors_eq_some_iff_ne_zero.mpr hb,
  rw [h_sa, h_sb] at h ⊢,
  rw [count_some hp, count_some hp], rw with_top.some_le_some at h,
  exact multiset.count_le_of_le _ h
end

lemma count_eq_zero_of_ne
  {α : Type*} [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]
  {p q : associates α} (hp : irreducible p) (hq : irreducible q) [decidable_eq α]
  [decidable_eq (associates α)] [Π p : associates α, decidable (irreducible p)]
  (h : p ≠ q) : p.count q.factors = 0 :=
not_ne_iff.mp $ λ h', h $ associated_iff_eq.mp $ hp.associated_of_dvd hq $
by { nontriviality α, exact le_of_count_ne_zero hq.ne_zero hp h' }

lemma eq_pow_find_of_dvd_irreducible_pow
  {α : Type*} [cancel_comm_monoid_with_zero α] [unique_factorization_monoid α]
  {a p : associates α} (hp : irreducible p) [∀ n : ℕ, decidable (a ∣ p ^ n)]
  (h : ∃ n : ℕ, a ∣ p ^ n) :
  a = p ^ nat.find h :=
begin
  have := nat.find_spec h,
  have b_ne_zero := pow_ne_zero _ hp.ne_zero,
  have a_ne_zero := ne_zero_of_dvd_ne_zero b_ne_zero (nat.find_spec h),
  haveI : decidable_eq α := by { classical, apply_instance },
  haveI : decidable_eq (associates α) := by { classical, apply_instance },
  haveI : ∀ p : associates α, decidable (irreducible p) := by { classical, apply_instance },
  apply eq_of_eq_counts a_ne_zero b_ne_zero,
  change a ≤ _ at this, nontriviality α, rw ← factors_le at this,
  have count_le := λ q hq, count_le_count_of_le a_ne_zero b_ne_zero hq this,
  have eq_zero_of_ne : ∀ (q : associates α), irreducible q → q ≠ p → _ = 0 :=
  λ q hq h, nat.eq_zero_of_le_zero $ by
  { convert count_le q hq, symmetry,
    rw [count_pow hp.ne_zero hq, count_eq_zero_of_ne hq hp h, mul_zero] },
  intros q hq,
  apply le_antisymm (count_le q hq),
  rw count_pow hp.ne_zero hq,
  by_cases h : q = p,
  { rw [h, count_self hp, mul_one],
    refine nat.find_le ⟨1, _⟩, rw mul_one,
    nth_rewrite 1 ← factors_prod a,
    obtain ⟨s, hs⟩ := factors_eq_some_iff_ne_zero.mpr a_ne_zero, rw hs at eq_zero_of_ne ⊢,
    rw [count_some hp, ← s.count_map_eq_count' _ subtype.coe_injective],
    change _  = (s.map coe).prod,
    convert multiset.pow_count p,
    refine (multiset.filter_eq_self.mpr $ λ q hq, _).symm,
    rw multiset.mem_map at hq, obtain ⟨⟨q, hq⟩, hqs, rfl⟩ := hq,
    symmetry, rw ← not_ne_iff, intro h,
    have := eq_zero_of_ne q hq h, rw count_some hq at this,
    exact multiset.count_ne_zero.mpr hqs this },
  { rw [count_eq_zero_of_ne hq hp h, mul_zero], exact zero_le _ }
end
end associates

namespace multiset
lemma le_bind {α β : Type*} {f : α → multiset β} (S : multiset α) {x : α} (hx : x ∈ S) :
  f x ≤ S.bind f :=
begin
  classical,
  rw le_iff_count, intro a,
  rw count_bind, apply le_sum_of_mem,
  rw mem_map, exact ⟨x, hx, rfl⟩
end
end multiset

namespace dfinsupp
variables {ι : Type*} {α β : ι → Type*} [Π i, has_zero (β i)]
instance [is_empty ι] : subsingleton (Π₀ i, β i) := ⟨λ a b, by { ext, exact is_empty_elim i }⟩
lemma dfinsupp_sigma {β : (Σ i, α i) → Type*} [Π i, has_zero (β i)] :
  (Π₀ i, β i) ≃ Π₀ i j, β ⟨i, j⟩ := sorry

end dfinsupp

namespace direct_sum
open_locale direct_sum
variables {ι : Type*} {β : ι → Type*} [Π i, add_comm_monoid (β i)]
instance [is_empty ι] : subsingleton (⨁ i, β i) := dfinsupp.subsingleton
end direct_sum

namespace set
lemma insert_image_compl_eq_range {A B : Type*} (f : A → B) (x : A) :
  insert (f x) (f '' {x}ᶜ) = range f :=
begin
  ext y, rw [mem_range, mem_insert_iff, mem_image],
  split,
  { rintro (h | ⟨x', hx', h⟩),
    { exact ⟨x, h.symm⟩ },
    { exact ⟨x', h⟩ } },
  { rintro ⟨x', h⟩,
    by_cases hx : x' = x,
    { left, rw [← h, hx] },
    { right, refine ⟨_, _, h⟩, rw mem_compl_singleton_iff, exact hx } }
end
end set

namespace module
open linear_map
variables  {R A M B : Type*} [semiring R] [add_comm_monoid A] [module R A]
  [add_comm_group B] [module R B] [add_comm_group M] [module R M]

noncomputable lemma equiv_prod_of_split_exact (j : A →ₗ[R] M) (g : M →ₗ[R] B) (f : B →ₗ[R] M)
  (hj : function.injective j) (exac : j.range = g.ker) (h : g.comp f = linear_map.id) :
  (A × B) ≃ₗ[R] M :=
begin
  have : ∀ x, ∃ a, j a = x - f (g x) := λ x, by
    rw [← mem_range, exac, mem_ker, map_sub, ← comp_apply g f, h, id_apply, sub_eq_zero],
  refine equiv.to_linear_equiv ⟨_, pi.prod (λ x, (this x).some) g, λ x, _, λ x, _⟩
    (j.coprod f).is_linear,
  { obtain ⟨a, b⟩ := x, simp only [pi.prod, prod.mk.inj_iff],
    have gj : g (j a) = 0 := by { rw [← mem_ker, ← exac, mem_range], exact ⟨a, rfl⟩ },
    have gf : g (f b) = b := by rw [← comp_apply, h, id_apply],
    split,
    { apply hj, rw (this _).some_spec,
      simp only [coe_comp, pi.add_apply, function.comp_app, fst_apply, snd_apply, map_add],
      rw [gj, gf, map_zero, zero_add, add_sub_cancel] },
    { simp only [coe_comp, pi.add_apply, function.comp_app, fst_apply, snd_apply, map_add],
      rw [gj, gf, zero_add] } },
  { simp only [pi.prod, coe_comp, pi.add_apply, function.comp_app, fst_apply, snd_apply],
    rw [(this x).some_spec, sub_add_cancel] }
end
end module

namespace submodule
variables {R M R₂ M₂ : Type*} [ring R] [add_comm_group M] [module R M]
  [ring R₂] [add_comm_group M₂] [module R₂ M₂] {τ₁₂ : R →+* R₂}
def liftq_span_singleton (x : M) (f : M →ₛₗ[τ₁₂] M₂) (h : f x = 0) : (M ⧸ R ∙ x) →ₛₗ[τ₁₂] M₂ :=
(R ∙ x).liftq f $ by rw [span_singleton_le_iff_mem, linear_map.mem_ker, h]
end submodule

/-section pid
open_locale direct_sum
open submodule

variables {R : Type u} [comm_ring R] [is_domain R] [is_principal_ideal_ring R]
  {M : Type v} [add_comm_group M] [module R M]
section
open dfinsupp
variables [decidable_eq R] [decidable_eq (associates R)]

noncomputable instance inst : gcd_monoid R := unique_factorization_monoid.to_gcd_monoid _

lemma coprime_of_irreducible_pow {ι : Type*} [fintype ι] (p : ι → R)
  (irred : ∀ i, irreducible (p i)) (assoc : ∀ i j, associated (p i) (p j) → i = j)
  (e : ι → ℕ) : pairwise (is_coprime on λ i, p i ^ e i) :=
λ i j h, ((irred i).coprime_iff_not_dvd.mpr
  (λ h', h (assoc _ _ ((irred i).associated_of_dvd (irred j) h')))).pow_left.pow_right

open finset multiset

theorem is_internal_prime_power_torsion [module.finite R M] (hM : module.is_torsion R M) :
  ∃ (ι : Type u) [fintype ι] [decidable_eq ι] (p : ι → R) [∀ i, irreducible (p i)] (e : ι → ℕ),
  by exactI direct_sum.submodule_is_internal (λ i, torsion_by R M ((p i) ^ e i)) :=
begin
  cases (module.finite_def.mp (by apply_instance) : (⊤ : submodule R M).fg) with S h,
  let P : multiset (associates R) :=
    S.val.bind (λ s, map associates.mk $
      principal_ideal_ring.factors ↑(classical.some $ mem_torsion_of_is_torsion hM s)),
  let ι := P.to_finset,
  let p : _ → R := λ i, classical.some $ associates.mk_surjective i,
  have hp : ∀ i, associates.mk (p i) = i := λ i, classical.some_spec $ associates.mk_surjective i,
  have irred : ∀ i : ι, irreducible (p i) := λ i, begin
    have hi := i.prop, rw [mem_to_finset, mem_bind] at hi,
    obtain ⟨s, hs, hi⟩ := hi, rw multiset.mem_map at hi, obtain ⟨q, hq, hi⟩ := hi,
    rw [← associates.irreducible_mk, hp i, ← hi, associates.irreducible_mk],
    apply (principal_ideal_ring.factors_spec _ _).left _ hq,
    exact non_zero_divisors.coe_ne_zero _
  end,
  refine ⟨ι, by apply_instance, by apply_instance, λ i, p i, irred, λ i, P.count i, _⟩,
  have coprime : pairwise (is_coprime on λ i : ι, p i ^ P.count i) :=
    coprime_of_irreducible_pow _ irred (λ i j assoc, subtype.coe_injective
      (by { rw [← hp ↑i, ← hp ↑j, associates.mk_eq_mk_iff_associated], exact assoc })) _,
  apply @torsion_is_internal _ _ _ _ _ _ (λ i, p i ^ P.count i) _ coprime,
  rw [eq_top_iff, ← h, span_le], intros s hs, rw set_like.mem_coe,
  refine torsion_le_torsion_of_dvd ↑_ _ _ (classical.some_spec $ mem_torsion_of_is_torsion hM s),
  rw [← (principal_ideal_ring.factors_spec (_ : R)
    (non_zero_divisors.coe_ne_zero _)).right.dvd_iff_dvd_left,
  ← associates.mk_dvd_mk, ← associates.prod_mk, ← associates.finset_prod_mk],
  convert prod_dvd_prod_of_le (S.val.le_bind hs),
  change _ = P.prod, rw prod_multiset_count,
  congr', ext i, rw [associates.mk_pow, hp],
end
end

section p_torsion
variables {p : R} [hp : irreducible p] (hM : ∀ x : M, ∃ N : ℕ, p ^ N • x = 0) [decidable_eq M]

open ideal submodule.is_principal
include hp hM
lemma torsion_of_eq_span_pow_find (x : M) : torsion_of R M x = span {p ^ nat.find (hM x)} :=
begin
  rw [← (torsion_of R M x).span_singleton_generator, span_singleton_eq_span_singleton,
    ← associates.mk_eq_mk_iff_associated, associates.mk_pow],
  have : (λ n : ℕ, p ^ n • x = 0) =
    λ n : ℕ, (associates.mk $ generator $ torsion_of R M x) ∣ associates.mk p ^ n,
  { ext n, rw [← associates.mk_pow, associates.mk_dvd_mk, ← mem_iff_generator_dvd], refl },
  convert associates.eq_pow_find_of_dvd_irreducible_pow ((associates.irreducible_mk p).mpr hp) _,
  { classical, apply_instance },
  rw ← this, exact hM x
end

lemma p_pow_smul_lift {x y : M} {k : ℕ} (hM' : ∀ x : M, p ^ nat.find (hM y) • x = 0)
  (h : p ^ k • x ∈ R ∙ y) : ∃ a : R, p ^ k • x = p ^ k • a • y :=
begin
  by_cases hk : k ≤ nat.find (hM y),
  { let f := ((R ∙ p ^ (nat.find (hM y) - k) * p ^ k).quot_equiv_of_eq _ _).trans
      (quot_torsion_of_equiv_span_singleton R M y),
    have : f.symm ⟨p ^ k • x, h⟩ ∈
      R ∙ ideal.quotient.mk (R ∙ p ^ (nat.find (hM y) - k) * p ^ k) (p ^ k),
    { rw [← quotient.torsion_by_eq_span_singleton, mem_torsion_by_iff, ← f.symm.map_smul],
      convert f.symm.map_zero, ext,
      rw [coe_smul_of_tower, coe_mk, coe_zero, smul_smul, ← pow_add, nat.sub_add_cancel hk, hM' x],
      { exact mem_non_zero_divisors_of_ne_zero (pow_ne_zero _ hp.ne_zero) } },
    rw submodule.mem_span_singleton at this, obtain ⟨a, ha⟩ := this, use a,
    rw [f.eq_symm_apply, ← ideal.quotient.mk_eq_mk, ← quotient.mk_smul] at ha,
    dsimp only [smul_eq_mul, f, linear_equiv.trans_apply, submodule.quot_equiv_of_eq_mk,
      quot_torsion_of_equiv_span_singleton_apply_mk] at ha,
    rw [smul_smul, mul_comm], exact congr_arg coe ha.symm,
    { symmetry, convert torsion_of_eq_span_pow_find hM y,
      rw [← pow_add, nat.sub_add_cancel hk] } },
  { use 0, rw [zero_smul, smul_zero, ← nat.sub_add_cancel (le_of_not_le hk),
      pow_add, mul_smul, hM', smul_zero] }
end

open finset multiset submodule.quotient

theorem torsion_by_prime_power_decomposition' (d : ℕ) (s : fin d → M)
  (hs : span R (set.range s) = ⊤) :
  ∃ (k : fin d → ℕ), nonempty $ M ≃ₗ[R] ⨁ (i : fin d), R ⧸ R ∙ (p ^ (k i : ℕ)) :=
begin
  unfreezingI { induction d with d IH generalizing M },
  { use λ i, fin_zero_elim i,
    rw [set.range_eq_empty, submodule.span_empty] at hs,
    haveI : unique M := ⟨⟨0⟩, λ x, by { rw [← mem_bot _, hs], trivial }⟩,
    exact ⟨0⟩ },
  { let oj := list.argmax (λ i, nat.find $ hM $ s i) (list.fin_range d.succ),
    have hoj : oj.is_some := (option.ne_none_iff_is_some.mp $ λ eq_none, d.succ_ne_zero $
      list.fin_range_eq_nil.mp $ list.argmax_eq_none.mp eq_none),
    let j := option.get hoj,
    let s' : fin d → M ⧸ R ∙ s j := mk ∘ s ∘ j.succ_above,
    haveI : decidable_eq (M ⧸ R ∙ s j) := by { classical, apply_instance },
    obtain ⟨k, ⟨f⟩⟩ := IH _ s' _,
    { have : ∀ i : fin d, ∃ x : M, p ^ k i • x = 0 ∧ f (mk x) = direct_sum.lof R _ _ i 1,
      { intro i,
        let fi := f.symm.to_linear_map.comp (direct_sum.lof _ _ _ i),
        have fi1 := mk_surjective (R ∙ s j) (fi 1),
        have : p ^ k i • fi1.some ∈ R ∙ s j,
        { rw [← quotient.mk_eq_zero, mk_smul, fi1.some_spec, ← fi.map_smul],
          convert fi.map_zero, change _ • submodule.quotient.mk _ = _,
          rw [← mk_smul, quotient.mk_eq_zero, algebra.id.smul_eq_mul, mul_one],
          exact mem_span_singleton_self _ },
        obtain ⟨a, ha⟩ := p_pow_smul_lift hM sorry this,
        refine ⟨fi1.some - a • s j, by rw [smul_sub, sub_eq_zero, ha], _⟩,
        rw [mk_sub, mk_smul, (quotient.mk_eq_zero _).mpr $ mem_span_singleton_self _,
          smul_zero, sub_zero, fi1.some_spec],
        simp only [linear_map.coe_comp, f.symm.coe_to_linear_map, f.apply_symm_apply] },
      use fin.cons (nat.find $ hM $ s j) k,
      refine ⟨linear_equiv.of_linear
        (direct_sum.to_module R (fin d.succ) M $ fin.cons
          ((R ∙ s j).subtype.comp
            ((quot_equiv_of_eq _ _ (torsion_of_eq_span_pow_find hM _).symm).trans
            $ quot_torsion_of_equiv_span_singleton R M $ s j).to_linear_map)
          $ λ i, liftq_span_singleton _
            (linear_map.to_span_singleton R M $ classical.some $ this i) _)
        sorry
        _ _⟩,
      { rw fin.cons_succ, exact (classical.some_spec $ this i).left },
      { sorry },
      { sorry } },
    { rintro ⟨x⟩, obtain ⟨N, hN⟩ := hM x, use N,
      rw [quotient.quot_mk_eq_mk, ← quotient.mk_smul, hN, quotient.mk_zero] },
    { have hs' := congr_arg (submodule.map $ mkq $ R ∙ s j) hs,
      rw [submodule.map_span, submodule.map_top, range_mkq] at hs', simp only [mkq_apply] at hs',
      simp only [s'], rw [set.range_comp (mk ∘ s), fin.range_succ_above], simp only at hs',
      rw [← set.range_comp, ← set.insert_image_compl_eq_range _ j, function.comp_apply,
        (quotient.mk_eq_zero _).mpr (mem_span_singleton_self _), span_insert_zero] at hs',
      exact hs' } }
end
end p_torsion

end pid-/
