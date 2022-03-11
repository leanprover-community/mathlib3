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
instance {ι : Type*} [is_empty ι] {β : ι → Type*} [Π i, has_zero (β i)] :
  subsingleton (Π₀ i, β i) :=
  ⟨λ a b, by { ext, exact is_empty_elim i }⟩
end dfinsupp

namespace direct_sum
open_locale direct_sum
instance {ι : Type*} [is_empty ι] {β : ι → Type*} [Π i, add_comm_monoid (β i)] :
  subsingleton (⨁ i, β i) := dfinsupp.subsingleton
end direct_sum

namespace linear_equiv
variables {R M N : Type*} [semiring R] [add_comm_monoid M] [add_comm_monoid N]
  [module R M] [module R N]
def of_subsingleton_of_subsingleton [subsingleton M] [subsingleton N] : M ≃ₗ[R] N :=
{ .. equiv_of_subsingleton_of_subsingleton 0 0,
  .. (0 : M →ₗ[R] N)}
end linear_equiv

section pid
open_locale direct_sum
open submodule dfinsupp

variables {R : Type u} [comm_ring R] [is_domain R] [is_principal_ideal_ring R]
  {M : Type v} [add_comm_group M] [module R M]
section
variables [decidable_eq R] [decidable_eq (associates R)]

noncomputable instance i : gcd_monoid R := unique_factorization_monoid.to_gcd_monoid _

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
  apply torsion_is_internal coprime,
  rw [eq_top_iff, ← h, span_le], intros s hs, rw set_like.mem_coe,
  refine torsion_le_torsion_of_dvd ↑_ _ _ (classical.some_spec $ mem_torsion_of_is_torsion hM s),
  rw [← (principal_ideal_ring.factors_spec (_ : R)
    (non_zero_divisors.coe_ne_zero _)).right.dvd_iff_dvd_left,
  ← associates.mk_dvd_mk, ← associates.prod_mk, ← associates.finset_prod_mk],
  convert prod_dvd_prod_of_le (S.val.le_bind hs),
  change _ = P.prod, rw [prod_multiset_count, ← prod_finset_coe _ ι],
  congr', ext i, rw [associates.mk_pow, hp],
end
end

section p_torsion
variables {p : R} [hp : irreducible p] {N : ℕ} (hM : ∀ x : M, p ^ N • x = 0) [decidable_eq M]
def p_order (x : M) := nat.find ⟨N, hM x⟩

open associates ideal
include hp hM
variables {p}
lemma torsion_of_eq_p_order (x : M) : torsion_of R M x = span {p ^ p_order hM x} :=
begin
  rw [← (torsion_of R M x).span_singleton_generator, span_singleton_eq_span_singleton,
    ← mk_eq_mk_iff_associated],
  have := (is_principal.mem_iff_generator_dvd _).mp
    ((mem_torsion_of_iff x $ p ^ p_order hM x).mpr _),
  { sorry },
  {
    sorry }
end

open finset multiset list submodule.quotient

noncomputable lemma torsion_by_prime_power_decomposition' (d : ℕ) (s : fin d → M)
  (hs : span R ((map s univ.val).to_finset : set M) = ⊤) :
  Σ (k : fin d → ℕ), M ≃ₗ[R] ⨁ (i : fin d), R ⧸ R ∙ (p ^ (k i : ℕ)) :=
begin
  unfreezingI { induction d with d IH generalizing M },
  { use λ i, fin_zero_elim i,
    rw [univ_eq_empty, empty_val, multiset.map_zero, to_finset_zero, coe_empty,
      submodule.span_empty] at hs,
    haveI : unique M := ⟨⟨0⟩, λ x, by { rw [← mem_bot _, hs], trivial }⟩,
    exact linear_equiv.of_subsingleton_of_subsingleton },
  { let oj := argmax (λ i, p_order hM $ s i) (fin_range d.succ),
    have hoj : oj.is_some := (option.ne_none_iff_is_some.mp $ λ eq_none, d.succ_ne_zero $
      fin_range_eq_nil.mp $ argmax_eq_none.mp eq_none),
    let j := option.get hoj,
    let s' : fin d → M ⧸ R ∙ s j := λ i, mk $ s $ j.succ_above i,
    haveI : decidable_eq (M ⧸ R ∙ s j) := by { classical, apply_instance },
    obtain ⟨k, f⟩ := IH _ s' _,
    { use j.insert_nth (p_order hM $ s j) k,
      sorry },
    { sorry },
    { sorry } }
end
end p_torsion

end pid
