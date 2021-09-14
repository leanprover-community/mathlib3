import ring_theory.adjoin.basic
import linear_algebra.linear_independent
import ring_theory.mv_polynomial.basic
import data.mv_polynomial.supported
import ring_theory.algebraic
import data.mv_polynomial.equiv

noncomputable theory

open function set subalgebra mv_polynomial algebra
open_locale classical big_operators

universes u v w x

variables {ι : Type*} {ι' : Type*} (R : Type*) {K : Type*}
variables {A : Type*} {A' A'' : Type*} {V : Type u} {V' : Type*}

section

variables (v : ι → A)
variables [comm_ring R] [comm_ring A] [comm_ring A'] [comm_ring A'']
variables [algebra R A] [algebra R A'] [algebra R A'']
variables {a b : R} {x y : A}

/-- `algebraic_independent R v` states the family of vectors `v`
  is algebraically independent over `R`. -/
def algebraic_independent : Prop :=
injective (mv_polynomial.aeval v : mv_polynomial ι R →ₐ[R] A)

variables {R} {v}

theorem algebraic_independent_iff_ker_eq_bot : algebraic_independent R v ↔
  (mv_polynomial.aeval v : mv_polynomial ι R →ₐ[R] A).to_ring_hom.ker = ⊥ :=
ring_hom.injective_iff_ker_eq_bot _

theorem algebraic_independent_iff : algebraic_independent R v ↔
  ∀p : mv_polynomial ι R, mv_polynomial.aeval (v : ι → A) p = 0 → p = 0 :=
ring_hom.injective_iff _

theorem algebraic_independent_iff_injective_aeval :
  algebraic_independent R v ↔ injective (mv_polynomial.aeval v : mv_polynomial ι R →ₐ[R] A) :=
iff.rfl

@[simp] lemma algebraic_independent_empty_type_iff [is_empty ι] :
  algebraic_independent R v ↔ injective (algebra_map R A) :=
have aeval v = (algebra.of_id R A).comp (@is_empty_alg_equiv R ι _ _).to_alg_hom,
  by { ext i, exact is_empty.elim' ‹is_empty ι› i },
begin
  rw [algebraic_independent, this,
    ← injective.of_comp_iff' _ (@is_empty_alg_equiv R ι _ _).bijective],
  refl
end

namespace algebraic_independent

variables (hv : algebraic_independent R v)

include hv

lemma algebra_map_injective : injective (algebra_map R A) :=
by simpa [← mv_polynomial.algebra_map_eq, function.comp] using
    (injective.of_comp_iff
      (algebraic_independent_iff_injective_aeval.1 hv) (mv_polynomial.C)).2
    (mv_polynomial.C_injective _ _)

lemma linear_independent : linear_independent R v :=
begin
  rw [linear_independent_iff_injective_total],
  have : finsupp.total ι A R v =
    (mv_polynomial.aeval v).to_linear_map.comp (finsupp.total ι _ R X),
  { ext, simp },
  rw this,
  refine hv.comp _,
  rw [← linear_independent_iff_injective_total],
  exact linear_independent_X _ _
end

lemma ne_zero [nontrivial R] (i : ι) : v i ≠ 0 :=
hv.linear_independent.ne_zero i

lemma comp (f : ι' → ι) (hf : function.injective f) : algebraic_independent R (v ∘ f) :=
λ p q, by simpa [aeval_rename, (rename_injective f hf).eq_iff] using @hv (rename f p) (rename f q)

lemma coe_range : algebraic_independent R (coe : range v → A) :=
by simpa using hv.comp _ (range_splitting_injective v)

lemma map {f : A →ₐ[R] A'} (hf_inj : set.inj_on f (adjoin R (range v))) :
  algebraic_independent R (f ∘ v) :=
have aeval (f ∘ v) = f.comp (aeval v), by ext; simp,
have h : ∀ x : mv_polynomial ι R, aeval v x ∈ (@aeval R _ _ _ _ (coe : range v → A) _).range,
  { intro x,
    rw [alg_hom.mem_range],
    refine ⟨mv_polynomial.rename (cod_restrict v (range v) (mem_range_self)) x, _⟩,
    simp [function.comp, aeval_rename] },
begin
  intros x y hxy,
  rw [this] at hxy,
  rw [adjoin_eq_range] at hf_inj,
  exact hv (hf_inj (h x) (h y) hxy)
end

lemma map' {f : A →ₐ[R] A'} (hf_inj : injective f) : algebraic_independent R (f ∘ v) :=
hv.map (inj_on_of_injective hf_inj _)

omit hv

lemma of_comp (f : A →ₐ[R] A') (hfv : algebraic_independent R (f ∘ v)) :
  algebraic_independent R v :=
have aeval (f ∘ v) = f.comp (aeval v), by ext; simp,
by rw [algebraic_independent, this] at hfv; exact hfv.of_comp

end algebraic_independent

open algebraic_independent

lemma alg_hom.algebraic_independent_iff (f : A →ₐ[R] A') (hf : injective f) :
  algebraic_independent R (f ∘ v) ↔ algebraic_independent R v :=
⟨λ h, h.of_comp f, λ h, h.map (inj_on_of_injective hf _)⟩

-- TODO uncomment when required instance is added to master
@[nontriviality]
lemma algebraic_independent_of_subsingleton [subsingleton R] : algebraic_independent R v := sorry
-- algebraic_independent_iff.2 (λ l hl, subsingleton.elim _ _)

theorem algebraic_independent_equiv (e : ι ≃ ι') {f : ι' → A} :
  algebraic_independent R (f ∘ e) ↔ algebraic_independent R f :=
⟨λ h, function.comp.right_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
λ h, h.comp _ e.injective⟩

theorem algebraic_independent_equiv' (e : ι ≃ ι') {f : ι' → A} {g : ι → A} (h : f ∘ e = g) :
  algebraic_independent R g ↔ algebraic_independent R f :=
h ▸ algebraic_independent_equiv e

theorem algebraic_independent_subtype_range {ι} {f : ι → A} (hf : injective f) :
  algebraic_independent R (coe : range f → A) ↔ algebraic_independent R f :=
iff.symm $ algebraic_independent_equiv' (equiv.of_injective f hf) rfl

alias algebraic_independent_subtype_range ↔ algebraic_independent.of_subtype_range _

theorem algebraic_independent_image {ι} {s : set ι} {f : ι → A} (hf : set.inj_on f s) :
  algebraic_independent R (λ x : s, f x) ↔ algebraic_independent R (λ x : f '' s, (x : A)) :=
algebraic_independent_equiv' (equiv.set.image_of_inj_on _ _ hf) rfl

lemma algebraic_independent_adjoin (hs : algebraic_independent R v) :
  @algebraic_independent ι R (adjoin R (range v))
      (λ i : ι, ⟨v i, subset_adjoin (mem_range_self i)⟩) _ _ _ :=
algebraic_independent.of_comp (adjoin R (range v)).val hs

/-- A set of algebraically independent vectors in an algebra `A` over a ring `K` is also
algebraically independent over a subring `R` of `K`.
The implementation uses minimal assumptions about the relationship between `R`, `K` and `A`.
The version where `K` is an `R`-algebra is `algebraic_independent.restrict_scalars_algebras`.
 -/
lemma algebraic_independent.restrict_scalars {K : Type*} [comm_ring K] [algebra R K]
   [algebra K A] [is_scalar_tower R K A]
  (hinj : function.injective (algebra_map R K)) (ai : algebraic_independent K v) :
  algebraic_independent R v :=
have (aeval v : mv_polynomial ι K →ₐ[K] A).to_ring_hom.comp
    (mv_polynomial.map (algebra_map R K)) =
    (aeval v : mv_polynomial ι R →ₐ[R] A).to_ring_hom,
  by { ext; simp [algebra_map_eq_smul_one] },
begin
  show injective (aeval v).to_ring_hom,
  rw [← this],
  exact injective.comp ai (mv_polynomial.map_injective _ hinj)
end

/-- Every finite subset of an algebraically independent set is algebraically independent. -/
lemma algebraic_independent_finset_map_embedding_subtype
  (s : set A) (li : algebraic_independent R (coe : s → A)) (t : finset s) :
  algebraic_independent R (coe : (finset.map (embedding.subtype s) t) → A) :=
begin
  let f : t.map (embedding.subtype s) → s := λ x, ⟨x.1, begin
    obtain ⟨x, h⟩ := x,
    rw [finset.mem_map] at h,
    obtain ⟨a, ha, rfl⟩ := h,
    simp only [subtype.coe_prop, embedding.coe_subtype],
  end⟩,
  convert algebraic_independent.comp li f _,
  rintros ⟨x, hx⟩ ⟨y, hy⟩,
  rw [finset.mem_map] at hx hy,
  obtain ⟨a, ha, rfl⟩ := hx,
  obtain ⟨b, hb, rfl⟩ := hy,
  simp only [imp_self, subtype.mk_eq_mk],
end

/--
If every finite set of algebraically independent element has cardinality at most `n`,
then the same is true for arbitrary sets of algebraically independent element.
-/
lemma algebraic_independent_bounded_of_finset_algebraic_independent_bounded {n : ℕ}
  (H : ∀ s : finset A, algebraic_independent R (λ i : s, (i : A)) → s.card ≤ n) :
  ∀ s : set A, algebraic_independent R (coe : s → A) → cardinal.mk s ≤ n :=
begin
  intros s li,
  apply cardinal.card_le_of,
  intro t,
  rw ← finset.card_map (embedding.subtype s),
  apply H,
  apply algebraic_independent_finset_map_embedding_subtype _ li,
end

section subtype

lemma algebraic_independent.restrict_of_comp_subtype {s : set ι}
  (hs : algebraic_independent R (v ∘ coe : s → A)) :
  algebraic_independent R (s.restrict v) :=
hs

variables (R A)
lemma algebraic_independent_empty_iff : algebraic_independent R (λ x, x : (∅ : set A) → A) ↔
  injective (algebra_map R A) :=
by simp
variables {R A}

lemma algebraic_independent.mono {t s : set A} (h : t ⊆ s)
  (hv : algebraic_independent R (λ x, x : s → A)) : algebraic_independent R (λ x, x : t → A) :=
by simpa [function.comp] using hv.comp (inclusion h) (inclusion_injective h)

end subtype

/-! ### Properties which require `ring R` -/

section module

lemma algebraic_independent.injective [nontrivial R] (hv : algebraic_independent R v) :
  injective v :=
hv.linear_independent.injective

theorem algebraic_independent.to_subtype_range {ι} {f : ι → A} (hf : algebraic_independent R f) :
  algebraic_independent R (coe : range f → A) :=
if hι : nonempty ι
then if hR : nontrivial R
then
have by exactI (aeval (coe : range f → A) : mv_polynomial (range f) R →ₐ[R] A).to_ring_hom =
    (aeval f).to_ring_hom.comp (mv_polynomial.rename
      (equiv.of_injective f hf.injective).symm).to_ring_hom,
  begin
    resetI,
    ext,
    { simp },
    { intro _,
      simp only [rename_X, alg_hom.coe_to_ring_hom, aeval_X, comp_app, ring_hom.coe_comp,
        alg_hom.to_ring_hom_eq_coe, equiv.apply_of_injective_symm f] }
  end,
begin
  resetI,
  show injective (aeval coe).to_ring_hom,
  rw [this],
  exact injective.comp hf (mv_polynomial.rename_injective _ (equiv.injective _))
end
else by { haveI : subsingleton R := not_nontrivial_iff_subsingleton.1 hR,
  exact algebraic_independent_of_subsingleton }
else by { haveI hι : is_empty ι := not_nonempty_iff.1 hι,
  haveI : is_empty (range f) := ⟨λ ⟨_, ⟨x, _⟩⟩, is_empty.elim' hι x⟩,
  simp * at * }

theorem algebraic_independent.to_subtype_range' {ι} {f : ι → A} (hf : algebraic_independent R f)
  {t} (ht : range f = t) :
  algebraic_independent R (coe : t → A) :=
ht ▸ hf.to_subtype_range

theorem algebraic_independent_comp_subtype {s : set ι} :
  algebraic_independent R (v ∘ coe : s → A) ↔
  ∀ p ∈ (mv_polynomial.supported R s), aeval v p = 0 → p = 0 :=
have (aeval (v ∘ coe : s → A) : _ →ₐ[R] _) =
  (aeval v).comp (rename coe), by ext; simp,
have ∀ p : mv_polynomial s R, rename (coe : s → ι) p = 0 ↔ p = 0,
  from (ring_hom.injective_iff' (rename (coe : s → ι) : mv_polynomial s R →ₐ[R] _).to_ring_hom).1
    (rename_injective _ subtype.val_injective),
by simp [algebraic_independent_iff, supported_eq_range_rename, *]

theorem algebraic_independent_subtype {s : set A} :
  algebraic_independent R (λ x, x : s → A) ↔
  ∀ (p : mv_polynomial A R), p ∈ mv_polynomial.supported R s → aeval id p = 0 → p = 0 :=
by apply @algebraic_independent_comp_subtype _ _ _ id

lemma algebraic_independent_of_finite (s : set A)
  (H : ∀ t ⊆ s, finite t → algebraic_independent R (λ x, x : t → A)) :
  algebraic_independent R (λ x, x : s → A) :=
algebraic_independent_subtype.2 $
  λ p hp, algebraic_independent_subtype.1 (H _ (mem_supported.1 hp) (finset.finite_to_set _)) _
    (by simp)

theorem algebraic_independent.image_of_comp {ι ι'} (s : set ι) (f : ι → ι') (g : ι' → A)
  (hs : algebraic_independent R (λ x : s, g (f x))) :
  algebraic_independent R (λ x : f '' s, g x) :=
begin
  nontriviality R,
  have : inj_on f s, from inj_on_iff_injective.2 hs.injective.of_comp,
  exact (algebraic_independent_equiv' (equiv.set.image_of_inj_on f s this) rfl).1 hs
end

theorem algebraic_independent.image {ι} {s : set ι} {f : ι → A}
  (hs : algebraic_independent R (λ x : s, f x)) : algebraic_independent R (λ x : f '' s, (x : A)) :=
by convert algebraic_independent.image_of_comp s f id hs

-- section maximal
-- universes v w

-- /--
-- An alternative characterization of a maximal algebraically independent family,
-- quantifying over types (in the same universe as `A`) into which the indexing family injects.
-- -/
-- lemma algebraic_independent.maximal_iff {ι : Type w} {R : Type u} [comm_ring R] [nontrivial R]
--   {A : Type v} [comm_ring A] [algebra R A] {v : ι → A} (i : algebraic_independent R v) :
--   i.maximal ↔ ∀ (κ : Type v) (w : κ → A) (i' : algebraic_independent R w)
--     (j : ι → κ) (h : w ∘ j = v), surjective j :=
-- begin
--   fsplit,
--   { rintros p κ w i' j rfl,
--     specialize p (range w) i'.coe_range (range_comp_subset_range _ _),
--     rw [range_comp, ←@image_univ _ _ w] at p,
--     exact range_iff_surjective.mp (image_injective.mpr i'.injective p), },
--   { intros p w i' h,
--     specialize p w (coe : w → A) i'
--       (λ i, ⟨v i, range_subset_iff.mp h i⟩)
--       (by { ext, simp, }),
--     have q := congr_arg (λ s, (coe : w → A) '' s) p.range_eq,
--     dsimp at q,
--     rw [←image_univ, image_image] at q,
--     simpa using q, },
-- end

-- end maximal

lemma algebraic_independent_Union_of_directed {η : Type*} [nonempty η]
  {s : η → set A} (hs : directed (⊆) s)
  (h : ∀ i, algebraic_independent R (λ x, x : s i → A)) :
  algebraic_independent R (λ x, x : (⋃ i, s i) → A) :=
begin
  refine algebraic_independent_of_finite (⋃ i, s i) (λ t ht ft, _),
  rcases finite_subset_Union ft ht with ⟨I, fi, hI⟩,
  rcases hs.finset_le fi.to_finset with ⟨i, hi⟩,
  exact (h i).mono (subset.trans hI $ bUnion_subset $
    λ j hj, hi j (fi.mem_to_finset.2 hj))
end

lemma algebraic_independent_sUnion_of_directed {s : set (set A)}
  (hsn : s.nonempty)
  (hs : directed_on (⊆) s)
  (h : ∀ a ∈ s, algebraic_independent R (λ x, x : (a : set A) → A)) :
  algebraic_independent R (λ x, x : (⋃₀ s) → A) :=
by letI : nonempty s := nonempty.to_subtype hsn;
rw sUnion_eq_Union; exact
algebraic_independent_Union_of_directed hs.directed_coe (by simpa using h)

lemma exists_maximal_algebraic_independent
  (s t : set A) (hst : s ⊆ t)
  (hs : algebraic_independent R (coe : s → A)) :
  ∃ u : set A, algebraic_independent R (coe : u → A) ∧ s ⊆ u ∧ u ⊆ t ∧
    ∀ v : set A, algebraic_independent R (coe : v → A) →
      u ⊆ v → v ⊆ t → v = u :=
begin
  rcases zorn.zorn_subset_nonempty
      { u : set A | algebraic_independent R (coe : u → A) ∧ s ⊆ u ∧ u ⊆ t }
    (λ c hc chainc hcn, ⟨⋃₀ c, begin
      refine ⟨⟨algebraic_independent_sUnion_of_directed hcn
        chainc.directed_on
        (λ a ha, (hc ha).1), _, _⟩, _⟩,
      { cases hcn with v hv,
        exact subset_sUnion_of_subset _ v (hc hv).2.1 hv },
      { exact sUnion_subset (λ v hv, (hc hv).2.2) },
      { intros s,
        exact subset_sUnion_of_mem }
    end⟩)
  s ⟨hs, set.subset.refl s, hst⟩ with ⟨u, ⟨huai, hsu, hut⟩, hsu, hv⟩,
  use [u, huai, hsu, hut],
  intros v hvai huv hvt,
  exact hv _ ⟨hvai, trans hsu huv, hvt⟩ huv,
end

section repr
variables (hv : algebraic_independent R v)

/-- Canonical isomorphism between polynomial and the subalgebra generated by
  algebraically independent elements. -/
@[simps] def algebraic_independent.aeval_equiv (hv : algebraic_independent R v) :
  (mv_polynomial ι R) ≃ₐ[R] algebra.adjoin R (range v) :=
begin
  apply alg_equiv.of_bijective
    (alg_hom.cod_restrict (@aeval R A ι _ _ v _) (algebra.adjoin R (range v)) _),
  swap,
  { intros x,
    rw [adjoin_range_eq_range_aeval],
    exact alg_hom.mem_range_self _ _ },
  { split,
    { exact (alg_hom.injective_cod_restrict _ _ _).2 hv },
    { rintros ⟨x, hx⟩,
      rw [adjoin_range_eq_range_aeval] at hx,
      rcases hx with ⟨y, rfl⟩,
      use y,
      ext,
      simp } }
end

def algebraic_independent.repr (hv : algebraic_independent R v) :
  algebra.adjoin R (range v) →ₐ[R] mv_polynomial ι R := hv.aeval_equiv.symm

@[simp] lemma algebraic_independent.aeval_repr (x) : aeval v (hv.repr x) = x :=
subtype.ext_iff.1 (alg_equiv.apply_symm_apply hv.aeval_equiv x)

lemma algebraic_independent.aeval_comp_repr :
  (aeval v).comp hv.repr = subalgebra.val _ :=
alg_hom.ext $ hv.aeval_repr

lemma algebraic_independent.repr_ker :
  (hv.repr : adjoin R (range v) →+* mv_polynomial ι R).ker = ⊥ :=
(ring_hom.injective_iff_ker_eq_bot _).1 (alg_equiv.injective _)

end repr

variable (R)
/--
  A family is a transcendence basis if it is a maximal algebraically independent subset.
-/
def is_transcendence_basis (v : ι → A) : Prop :=
algebraic_independent R v ∧
  ∀ (s : set A) (i' : algebraic_independent R (coe : s → A)) (h : range v ≤ s), range v = s

variable {R}
lemma algebraic_independent.is_transcendence_basis_iff
  {ι : Type w} {R : Type u} [comm_ring R] [nontrivial R]
  {A : Type v} [comm_ring A] [algebra R A] {v : ι → A} (i : algebraic_independent R v) :
  is_transcendence_basis R v ↔ ∀ (κ : Type v) (w : κ → A) (i' : algebraic_independent R w)
    (j : ι → κ) (h : w ∘ j = v), surjective j :=
begin
  fsplit,
  { rintros p κ w i' j rfl,
    have p := p.2 (range w) i'.coe_range (range_comp_subset_range _ _),
    rw [range_comp, ←@image_univ _ _ w] at p,
    exact range_iff_surjective.mp (image_injective.mpr i'.injective p) },
  { intros p,
    use i,
    intros w i' h,
    specialize p w (coe : w → A) i'
      (λ i, ⟨v i, range_subset_iff.mp h i⟩)
      (by { ext, simp, }),
    have q := congr_arg (λ s, (coe : w → A) '' s) p.range_eq,
    dsimp at q,
    rw [←image_univ, image_image] at q,
    simpa using q, },
end

example {R S A : Type} [comm_ring R] [comm_ring S] [comm_ring A]
  [algebra R A] [algebra R S] (f : S →ₐ[R] A) (x : A) : polynomial S →ₐ[R] A :=
sorry

example {R A ι : Type*} [comm_ring R] [comm_ring A] [algebra R A]
  (f : mv_polynomial (option ι) R ≃ₐ[R] polynomial (mv_polynomial ι R))
  (p : mv_polynomial (option ι) R) :
  (option_equiv_left R ι) p = ((option_equiv_left R ι :
    mv_polynomial (option ι) R →ₐ[R] polynomial (mv_polynomial ι R))
    : mv_polynomial (option ι) R →+* polynomial (mv_polynomial ι R)) p :=
by simp

lemma is_trancendence_basis.is_algebraic_aux
  {ι : Type v} {R : Type u} [comm_ring R] [nontrivial R]
  {A : Type v} [comm_ring A] [algebra R A] {v : ι → A}
  (h : is_transcendence_basis R v) : is_algebraic (adjoin R (range v)) A :=
begin
  have ai : algebraic_independent R v := h.1,
  --rw ai.is_transcendence_basis_iff.{w w u} at h,
  intros x,
  have : ¬ algebraic_independent R (λ o : option ι, o.elim x v),
  { have := not_imp_not.2 (ai.is_transcendence_basis_iff.1 h (option ι)
      (λ o, option.elim o x v)),
    simp only [not_exists, and_imp, exists_prop, forall_exists_index, not_forall] at this,
    exact this some rfl none (by simp) },
  simp only [algebraic_independent_iff, not_forall, exists_prop] at this,
  rcases this with ⟨p, hpx, hp0⟩,
  use (mv_polynomial.option_equiv_left R ι p).map ai.aeval_equiv.to_alg_hom,
  split,
  { admit },
  { have : ((aeval (λ o : option ι, o.elim x v) :
      mv_polynomial (option ι) R →ₐ[R] A) : mv_polynomial (option ι) R →+* A)  =
      ring_hom.comp ((polynomial.aeval x : polynomial R →ₐ[R] A) : polynomial R →+* A)
        ((polynomial.map_ring_hom ↑ai.aeval_equiv.to_alg_hom).comp
          ↑(mv_polynomial.option_equiv_left R ι).to_alg_hom),
    { admit },
    { conv_rhs { rw [← hpx, ← alg_hom.coe_to_ring_hom (aeval (λ o : option ι, o.elim x v) :
        mv_polynomial (option ι) R →ₐ[R] A)] },
      rw [this],
      simp,
      rw [alg_equiv.coe_to_alg_hom], } }
end

lemma exists_is_transcendence_basis (h : function.injective (algebra_map R A)) :
  ∃ s : set A, is_transcendence_basis R (coe : s → A) :=
begin
  rcases exists_maximal_algebraic_independent ∅ set.univ (set.empty_subset _)
    ((algebraic_independent_empty_iff _ _).2 h) with ⟨u, huai, -, -, hu⟩,
  use [u, huai],
  intros v hvai hv,
  rw hu v hvai (by simpa using hv) (set.subset_univ _),
  simp
end

#exit
section subtype
/-! The following lemmas use the subtype defined by a set in `A` as the index set `ι`. -/

lemma algebraic_independent.disjoint_adjoin_image (hv : algebraic_independent R v) {s t : set ι}
  (hs : disjoint s t) : disjoint (algebra.adjoin R $ v '' s) (algebra.adjoin R $ v '' t) :=
begin
  rw [disjoint_iff, eq_bot_iff],
  rintros x ⟨hxs, hxt⟩,
  rw [set_like.mem_coe, adjoin_eq_range] at hxs hxt,
  rcases hxs with ⟨p, rfl⟩,
  rcases hxt with ⟨q, hpq⟩,
  rw [← algebraic_independent_subtype_range] at hv,
  have := @hv (mv_polynomial.rename (set.inclusion (image_subset_range v s)) p)
              (mv_polynomial.rename (set.inclusion (image_subset_range v t)) q),
  simp only [aeval_rename, aeval_rename, function.comp, set.coe_inclusion] at this,
  have := this hpq.symm,

end

lemma algebraic_independent.not_mem_span_image [nontrivial R] (hv : algebraic_independent R v) {s : set ι}
  {x : ι} (h : x ∉ s) : v x ∉ submodule.span R (v '' s) :=
begin
  have h' : v x ∈ submodule.span R (v '' {x}),
  { rw set.image_singleton,
    exact mem_span_singleton_self (v x), },
  intro w,
  apply algebraic_independent.ne_zero x hv,
  refine disjoint_def.1 (hv.disjoint_span_image _) (v x) h' w,
  simpa using h,
end

lemma algebraic_independent.total_ne_of_not_mem_support [nontrivial R] (hv : algebraic_independent R v)
  {x : ι} (f : ι →₀ R) (h : x ∉ f.support) :
  finsupp.total ι A R v f ≠ v x :=
begin
  replace h : x ∉ (f.support : set ι) := h,
  have p := hv.not_mem_span_image h,
  intro w,
  rw ←w at p,
  rw finsupp.span_image_eq_map_total at p,
  simp only [not_exists, not_and, mem_map] at p,
  exact p f (f.mem_supported_support R) rfl,
end

lemma algebraic_independent_sum {v : ι ⊕ ι' → A} :
  algebraic_independent R v ↔ algebraic_independent R (v ∘ sum.inl) ∧
    algebraic_independent R (v ∘ sum.inr) ∧
      disjoint (submodule.span R (range (v ∘ sum.inl))) (submodule.span R (range (v ∘ sum.inr))) :=
begin
  rw [range_comp v, range_comp v],
  refine ⟨λ h, ⟨h.comp _ sum.inl_injective, h.comp _ sum.inr_injective,
    h.disjoint_span_image is_compl_range_inl_range_inr.1⟩, _⟩,
  rintro ⟨hl, hr, hlr⟩,
  rw [algebraic_independent_iff'] at *,
  intros s g hg i hi,
  have : ∑ i in s.preimage sum.inl (sum.inl_injective.inj_on _), (λ x, g x • v x) (sum.inl i) +
    ∑ i in s.preimage sum.inr (sum.inr_injective.inj_on _), (λ x, g x • v x) (sum.inr i) = 0,
  { rw [finset.sum_preimage', finset.sum_preimage', ← finset.sum_union, ← finset.filter_or],
    { simpa only [← mem_union, range_inl_union_range_inr, mem_univ, finset.filter_true] },
    { exact finset.disjoint_filter.2 (λ x hx, disjoint_left.1 is_compl_range_inl_range_inr.1) } },
  { rw ← eq_neg_iff_add_eq_zero at this,
    rw [disjoint_def'] at hlr,
    have A := hlr _ (sum_mem _ $ λ i hi, _) _ (neg_mem _ $ sum_mem _ $ λ i hi, _) this,
    { cases i with i i,
      { exact hl _ _ A i (finset.mem_preimage.2 hi) },
      { rw [this, neg_eq_zero] at A,
        exact hr _ _ A i (finset.mem_preimage.2 hi) } },
    { exact smul_mem _ _ (subset_span ⟨sum.inl i, mem_range_self _, rfl⟩) },
    { exact smul_mem _ _ (subset_span ⟨sum.inr i, mem_range_self _, rfl⟩) } }
end

lemma algebraic_independent.sum_type {v' : ι' → A} (hv : algebraic_independent R v)
  (hv' : algebraic_independent R v')
  (h : disjoint (submodule.span R (range v)) (submodule.span R (range v'))) :
  algebraic_independent R (sum.elim v v') :=
algebraic_independent_sum.2 ⟨hv, hv', h⟩

lemma algebraic_independent.union {s t : set A}
  (hs : algebraic_independent R (λ x, x : s → A)) (ht : algebraic_independent R (λ x, x : t → A))
  (hst : disjoint (span R s) (span R t)) :
  algebraic_independent R (λ x, x : (s ∪ t) → A) :=
(hs.sum_type ht $ by simpa).to_subtype_range' $ by simp

lemma algebraic_independent_Union_finite_subtype {ι : Type*} {f : ι → set A}
  (hl : ∀i, algebraic_independent R (λ x, x : f i → A))
  (hd : ∀i, ∀t:set ι, finite t → i ∉ t → disjoint (span R (f i)) (⨆i∈t, span R (f i))) :
  algebraic_independent R (λ x, x : (⋃i, f i) → A) :=
begin
  rw [Union_eq_Union_finset f],
  apply algebraic_independent_Union_of_directed,
  { apply directed_of_sup,
    exact (λ t₁ t₂ ht, Union_subset_Union $ λ i, Union_subset_Union_const $ λ h, ht h) },
  assume t,
  induction t using finset.induction_on with i s his ih,
  { refine (algebraic_independent_empty _ _).mono _,
    simp },
  { rw [finset.set_bUnion_insert],
    refine (hl _).union ih _,
    refine (hd i s s.finite_to_set his).mono_right _,
    simp only [(span_Union _).symm],
    refine span_mono (@supr_le_supr2 (set A) _ _ _ _ _ _),
    exact λ i, ⟨i, le_rfl⟩ }
end

lemma algebraic_independent_Union_finite {η : Type*} {ιs : η → Type*}
  {f : Π j : η, ιs j → A}
  (hindep : ∀j, algebraic_independent R (f j))
  (hd : ∀i, ∀t:set η, finite t → i ∉ t →
      disjoint (span R (range (f i))) (⨆i∈t, span R (range (f i)))) :
  algebraic_independent R (λ ji : Σ j, ιs j, f ji.1 ji.2) :=
begin
  nontriviality R,
  apply algebraic_independent.of_subtype_range,
  { rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy,
    by_cases h_cases : x₁ = y₁,
    subst h_cases,
    { apply sigma.eq,
      rw algebraic_independent.injective (hindep _) hxy,
      refl },
    { have h0 : f x₁ x₂ = 0,
      { apply disjoint_def.1 (hd x₁ {y₁} (finite_singleton y₁)
          (λ h, h_cases (eq_of_mem_singleton h))) (f x₁ x₂) (subset_span (mem_range_self _)),
        rw supr_singleton,
        simp only at hxy,
        rw hxy,
        exact (subset_span (mem_range_self y₂)) },
      exact false.elim ((hindep x₁).ne_zero _ h0) } },
  rw range_sigma_eq_Union_range,
  apply algebraic_independent_Union_finite_subtype (λ j, (hindep j).to_subtype_range) hd,
end

end subtype

section repr
variables (hv : algebraic_independent R v)

/-- Canonical isomorphism between algebraic combinations and the span of algebraicly independent vectors.
-/
@[simps] def algebraic_independent.total_equiv (hv : algebraic_independent R v) :
  (ι →₀ R) ≃ₗ[R] span R (range v) :=
begin
apply algebraic_equiv.of_bijective
  (algebraic_map.cod_restrict (span R (range v)) (finsupp.total ι A R v) _),
{ rw [← algebraic_map.ker_eq_bot, algebraic_map.ker_cod_restrict],
  apply hv },
{ rw [← algebraic_map.range_eq_top, algebraic_map.range_eq_map, algebraic_map.map_cod_restrict,
    ← algebraic_map.range_le_iff_comap, range_subtype, map_top],
  rw finsupp.range_total,
  apply le_refl (span R (range v)) },
{ intro l,
  rw ← finsupp.range_total,
  rw algebraic_map.mem_range,
  apply mem_range_self l }
end

/-- Linear combination representing a vector in the span of algebraicly independent vectors.

Given a family of algebraicly independent vectors, we can represent any vector in their span as
a algebraic combination of these vectors. These are provided by this algebraic map.
It is simply one direction of `algebraic_independent.total_equiv`. -/
def algebraic_independent.repr (hv : algebraic_independent R v) :
  span R (range v) →ₗ[R] ι →₀ R := hv.total_equiv.symm

@[simp] lemma algebraic_independent.total_repr (x) : finsupp.total ι A R v (hv.repr x) = x :=
subtype.ext_iff.1 (algebraic_equiv.apply_symm_apply hv.total_equiv x)

lemma algebraic_independent.total_comp_repr :
  (finsupp.total ι A R v).comp hv.repr = submodule.subtype _ :=
algebraic_map.ext $ hv.total_repr

lemma algebraic_independent.repr_ker : hv.repr.ker = ⊥ :=
by rw [algebraic_independent.repr, algebraic_equiv.ker]

lemma algebraic_independent.repr_range : hv.repr.range = ⊤ :=
by rw [algebraic_independent.repr, algebraic_equiv.range]

lemma algebraic_independent.repr_eq
  {l : ι →₀ R} {x} (eq : finsupp.total ι A R v l = ↑x) :
  hv.repr x = l :=
begin
  have : ↑((algebraic_independent.total_equiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l)
      = finsupp.total ι A R v l := rfl,
  have : (algebraic_independent.total_equiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l = x,
  { rw eq at this,
    exact subtype.ext_iff.2 this },
  rw ←algebraic_equiv.symm_apply_apply hv.total_equiv l,
  rw ←this,
  refl,
end

lemma algebraic_independent.repr_eq_single (i) (x) (hx : ↑x = v i) :
  hv.repr x = finsupp.single i 1 :=
begin
  apply hv.repr_eq,
  simp [finsupp.total_single, hx]
end

lemma algebraic_independent.span_repr_eq [nontrivial R] (x) :
  span.repr R (set.range v) x = (hv.repr x).equiv_map_domain (equiv.of_injective _ hv.injective) :=
begin
  have p : (span.repr R (set.range v) x).equiv_map_domain (equiv.of_injective _ hv.injective).symm =
    hv.repr x,
  { apply (algebraic_independent.total_equiv hv).injective,
    ext,
    simp, },
  ext ⟨_, ⟨i, rfl⟩⟩,
  simp [←p],
end

-- TODO: why is this so slow?
lemma algebraic_independent_iff_not_smul_mem_span :
  algebraic_independent R v ↔ (∀ (i : ι) (a : R), a • (v i) ∈ span R (v '' (univ \ {i})) → a = 0) :=
⟨ λ hv i a ha, begin
  rw [finsupp.span_image_eq_map_total, mem_map] at ha,
  rcases ha with ⟨l, hl, e⟩,
  rw sub_eq_zero.1 (algebraic_independent_iff.1 hv (l - finsupp.single i a) (by simp [e])) at hl,
  by_contra hn,
  exact (not_mem_of_mem_diff (hl $ by simp [hn])) (mem_singleton _),
end, λ H, algebraic_independent_iff.2 $ λ l hl, begin
  ext i, simp only [finsupp.zero_apply],
  by_contra hn,
  refine hn (H i _ _),
  refine (finsupp.mem_span_image_iff_total _).2 ⟨finsupp.single i (l i) - l, _, _⟩,
  { rw finsupp.mem_supported',
    intros j hj,
    have hij : j = i :=
      not_not.1
          (λ hij : j ≠ i, hj ((mem_diff _).2 ⟨mem_univ _, λ h, hij (eq_of_mem_singleton h)⟩)),
    simp [hij] },
  { simp [hl] }
end⟩

variable (R)

lemma exists_maximal_independent' (s : ι → A) :
  ∃ I : set ι, algebraic_independent R (λ x : I, s x) ∧
    ∀ J : set ι, I ⊆ J → algebraic_independent R (λ x : J, s x) → I = J :=
begin
  let indep : set ι → Prop := λ I, algebraic_independent R (s ∘ coe : I → A),
  let X := { I : set ι // indep I },
  let r : X → X → Prop := λ I J, I.1 ⊆ J.1,
  have key : ∀ c : set X, zorn.chain r c → indep (⋃ (I : X) (H : I ∈ c), I),
  { intros c hc,
    dsimp [indep],
    rw [algebraic_independent_comp_subtype],
    intros f hsupport hsum,
    rcases eq_empty_or_nonempty c with rfl | ⟨a, hac⟩,
    { simpa using hsupport },
    haveI : is_refl X r := ⟨λ _, set.subset.refl _⟩,
    obtain ⟨I, I_mem, hI⟩ : ∃ I ∈ c, (f.support : set ι) ⊆ I :=
      finset.exists_mem_subset_of_subset_bUnion_of_directed_on hac hc.directed_on hsupport,
    exact algebraic_independent_comp_subtype.mp I.2 f hI hsum },
  have trans : transitive r := λ I J K, set.subset.trans,
  obtain ⟨⟨I, hli : indep I⟩, hmax : ∀ a, r ⟨I, hli⟩ a → r a ⟨I, hli⟩⟩ :=
    @zorn.exists_maximal_of_chains_bounded _ r
    (λ c hc, ⟨⟨⋃ I ∈ c, (I : set ι), key c hc⟩, λ I, set.subset_bUnion_of_mem⟩) trans,
  exact ⟨I, hli, λ J hsub hli, set.subset.antisymm hsub (hmax ⟨J, hli⟩ hsub)⟩,
end

lemma exists_maximal_independent (s : ι → A) : ∃ I : set ι, algebraic_independent R (λ x : I, s x) ∧
  ∀ i ∉ I, ∃ a : R, a ≠ 0 ∧ a • s i ∈ span R (s '' I) :=
begin
  classical,
  rcases exists_maximal_independent' R s with ⟨I, hIlinind, hImaximal⟩,
  use [I, hIlinind],
  intros i hi,
  specialize hImaximal (I ∪ {i}) (by simp),
  set J := I ∪ {i} with hJ,
  have memJ : ∀ {x}, x ∈ J ↔ x = i ∨ x ∈ I, by simp [hJ],
  have hiJ : i ∈ J := by simp,
  have h := mt hImaximal _, swap,
  { intro h2,
    rw h2 at hi,
    exact absurd hiJ hi },
  obtain ⟨f, supp_f, sum_f, f_ne⟩ := algebraic_dependent_comp_subtype.mp h,
  have hfi : f i ≠ 0,
  { contrapose hIlinind,
    refine algebraic_dependent_comp_subtype.mpr ⟨f, _, sum_f, f_ne⟩,
    simp only [finsupp.mem_supported, hJ] at ⊢ supp_f,
    rintro x hx,
    refine (memJ.mp (supp_f hx)).resolve_left _,
    rintro rfl,
    exact hIlinind (finsupp.mem_support_iff.mp hx) },
  use [f i, hfi],
  have hfi' : i ∈ f.support := finsupp.mem_support_iff.mpr hfi,
  rw [← finset.insert_erase hfi', finset.sum_insert (finset.not_mem_erase _ _),
      add_eq_zero_iff_eq_neg] at sum_f,
  rw sum_f,
  refine neg_mem _ (sum_mem _ (λ c hc, smul_mem _ _ (subset_span ⟨c, _, rfl⟩))),
  exact (memJ.mp (supp_f (finset.erase_subset _ _ hc))).resolve_left (finset.ne_of_mem_erase hc),
end
end repr

lemma surjective_of_algebraic_independent_of_span [nontrivial R]
  (hv : algebraic_independent R v) (f : ι' ↪ ι)
  (hss : range v ⊆ span R (range (v ∘ f))) :
  surjective f :=
begin
  intros i,
  let repr : (span R (range (v ∘ f)) : Type*) → ι' →₀ R := (hv.comp f f.injective).repr,
  let l := (repr ⟨v i, hss (mem_range_self i)⟩).map_domain f,
  have h_total_l : finsupp.total ι A R v l = v i,
  { dsimp only [l],
    rw finsupp.total_map_domain,
    rw (hv.comp f f.injective).total_repr,
    { refl },
    { exact f.injective } },
  have h_total_eq : (finsupp.total ι A R v) l = (finsupp.total ι A R v) (finsupp.single i 1),
    by rw [h_total_l, finsupp.total_single, one_smul],
  have l_eq : l = _ := algebraic_map.ker_eq_bot.1 hv h_total_eq,
  dsimp only [l] at l_eq,
  rw ←finsupp.emb_domain_eq_map_domain at l_eq,
  rcases finsupp.single_of_emb_domain_single (repr ⟨v i, _⟩) f i (1 : R) zero_ne_one.symm l_eq
    with ⟨i', hi'⟩,
  use i',
  exact hi'.2
end

lemma eq_of_algebraic_independent_of_span_subtype [nontrivial R] {s t : set A}
  (hs : algebraic_independent R (λ x, x : s → A)) (h : t ⊆ s) (hst : s ⊆ span R t) : s = t :=
begin
  let f : t ↪ s := ⟨λ x, ⟨x.1, h x.2⟩, λ a b hab, subtype.coe_injective (subtype.mk.inj hab)⟩,
  have h_surj : surjective f,
  { apply surjective_of_algebraic_independent_of_span hs f _,
    convert hst; simp [f, comp], },
  show s = t,
  { apply subset.antisymm _ h,
    intros x hx,
    rcases h_surj ⟨x, hx⟩ with ⟨y, hy⟩,
    convert y.mem,
    rw ← subtype.mk.inj hy,
    refl }
end

open algebraic_map

lemma algebraic_independent.image_subtype {s : set A} {f : A →ₗ[R] A'}
  (hs : algebraic_independent R (λ x, x : s → A))
  (hf_inj : disjoint (span R s) f.ker) : algebraic_independent R (λ x, x : f '' s → A') :=
begin
  rw [← @subtype.range_coe _ s] at hf_inj,
  refine (hs.map hf_inj).to_subtype_range' _,
  simp [set.range_comp f]
end

lemma algebraic_independent.inl_union_inr {s : set A} {t : set A'}
  (hs : algebraic_independent R (λ x, x : s → A))
  (ht : algebraic_independent R (λ x, x : t → A')) :
  algebraic_independent R (λ x, x : inl R A A' '' s ∪ inr R A A' '' t → A × A') :=
begin
  refine (hs.image_subtype _).union (ht.image_subtype _) _; [simp, simp, skip],
  simp only [span_image],
  simp [disjoint_iff, prod_inf_prod]
end

lemma algebraic_independent_inl_union_inr' {v : ι → A} {v' : ι' → A'}
  (hv : algebraic_independent R v) (hv' : algebraic_independent R v') :
  algebraic_independent R (sum.elim (inl R A A' ∘ v) (inr R A A' ∘ v')) :=
(hv.map' (inl R A A') ker_inl).sum_type (hv'.map' (inr R A A') ker_inr) $
begin
  refine is_compl_range_inl_inr.disjoint.mono _ _;
    simp only [span_le, range_coe, range_comp_subset_range],
end

/-- Dedekind's algebraic independence of characters -/
-- See, for example, Keith Conrad's note
--  <https://kconrad.math.uconn.edu/blurbs/galoistheory/algebraicchar.pdf>
theorem algebraic_independent_monoid_hom (G : Type*) [monoid G] (L : Type*) [comm_ring L]
  [no_zero_divisors L] :
  @algebraic_independent _ L (G → L) (λ f, f : (G →* L) → (G → L)) _ _ _ :=
by letI := classical.dec_eq (G →* L);
   letI : mul_action L L := distrib_mul_action.to_mul_action;
-- We prove algebraic independence by showing that only the trivial algebraic combination vanishes.
exact algebraic_independent_iff'.2
-- To do this, we use `finset` induction,
(λ s, finset.induction_on s (λ g hg i, false.elim) $ λ a s has ih g hg,
-- Here
-- * `a` is a new character we will insert into the `finset` of characters `s`,
-- * `ih` is the fact that only the trivial algebraic combination of characters in `s` is zero
-- * `hg` is the fact that `g` are the coefficients of a algebraic combination summing to zero
-- and it remains to prove that `g` vanishes on `insert a s`.

-- We now make the key calculation:
-- For any character `i` in the original `finset`, we have `g i • i = g i • a` as functions on the
-- monoid `G`.
have h1 : ∀ i ∈ s, (g i • i : G → L) = g i • a, from λ i his, funext $ λ x : G,
  -- We prove these expressions are equal by showing
  -- the differences of their values on each monoid element `x` is zero
  eq_of_sub_eq_zero $ ih (λ j, g j * j x - g j * a x)
    (funext $ λ y : G, calc
    -- After that, it's just a chase scene.
          (∑ i in s, ((g i * i x - g i * a x) • i : G → L)) y
        = ∑ i in s, (g i * i x - g i * a x) * i y : finset.sum_apply _ _ _
    ... = ∑ i in s, (g i * i x * i y - g i * a x * i y) : finset.sum_congr rfl
      (λ _ _, sub_mul _ _ _)
    ... = ∑ i in s, g i * i x * i y - ∑ i in s, g i * a x * i y : finset.sum_sub_distrib
    ... = (g a * a x * a y + ∑ i in s, g i * i x * i y)
          - (g a * a x * a y + ∑ i in s, g i * a x * i y) : by rw add_sub_add_left_eq_sub
    ... = ∑ i in insert a s, g i * i x * i y - ∑ i in insert a s, g i * a x * i y :
      by rw [finset.sum_insert has, finset.sum_insert has]
    ... = ∑ i in insert a s, g i * i (x * y) - ∑ i in insert a s, a x * (g i * i y) :
      congr (congr_arg has_sub.sub (finset.sum_congr rfl $ λ i _, by rw [i.map_mul, mul_assoc]))
        (finset.sum_congr rfl $ λ _ _, by rw [mul_assoc, mul_left_comm])
    ... = (∑ i in insert a s, (g i • i : G → L)) (x * y)
          - a x * (∑ i in insert a s, (g i • i : G → L)) y :
      by rw [finset.sum_apply, finset.sum_apply, finset.mul_sum]; refl
    ... = 0 - a x * 0 : by rw hg; refl
    ... = 0 : by rw [mul_zero, sub_zero])
    i
    his,
-- On the other hand, since `a` is not already in `s`, for any character `i ∈ s`
-- there is some element of the monoid on which it differs from `a`.
have h2 : ∀ i : G →* L, i ∈ s → ∃ y, i y ≠ a y, from λ i his,
  classical.by_contradiction $ λ h,
  have hia : i = a, from monoid_hom.ext $ λ y, classical.by_contradiction $ λ hy, h ⟨y, hy⟩,
  has $ hia ▸ his,
-- From these two facts we deduce that `g` actually vanishes on `s`,
have h3 : ∀ i ∈ s, g i = 0, from λ i his, let ⟨y, hy⟩ := h2 i his in
  have h : g i • i y = g i • a y, from congr_fun (h1 i his) y,
  or.resolve_right (mul_eq_zero.1 $ by rw [mul_sub, sub_eq_zero]; exact h) (sub_ne_zero_of_ne hy),
-- And so, using the fact that the algebraic combination over `s` and over `insert a s` both vanish,
-- we deduce that `g a = 0`.
have h4 : g a = 0, from calc
  g a = g a * 1 : (mul_one _).symm
  ... = (g a • a : G → L) 1 : by rw ← a.map_one; refl
  ... = (∑ i in insert a s, (g i • i : G → L)) 1 : begin
      rw finset.sum_eq_single a,
      { intros i his hia, rw finset.mem_insert at his,
        rw [h3 i (his.resolve_left hia), zero_smul] },
      { intros haas, exfalso, apply haas, exact finset.mem_insert_self a s }
    end
  ... = 0 : by rw hg; refl,
-- Now we're done; the last two facts together imply that `g` vanishes on every element
-- of `insert a s`.
(finset.forall_mem_insert _ _ _).2 ⟨h4, h3⟩)

lemma le_of_span_le_span [nontrivial R] {s t u: set A}
  (hl : algebraic_independent R (coe : u → A )) (hsu : s ⊆ u) (htu : t ⊆ u)
  (hst : span R s ≤ span R t) : s ⊆ t :=
begin
  have := eq_of_algebraic_independent_of_span_subtype
    (hl.mono (set.union_subset hsu htu))
    (set.subset_union_right _ _)
    (set.union_subset (set.subset.trans subset_span hst) subset_span),
  rw ← this, apply set.subset_union_left
end

lemma span_le_span_iff [nontrivial R] {s t u: set A}
  (hl : algebraic_independent R (coe : u → A)) (hsu : s ⊆ u) (htu : t ⊆ u) :
  span R s ≤ span R t ↔ s ⊆ t :=
⟨le_of_span_le_span hl hsu htu, span_mono⟩

end module

section nontrivial

variables [ring R] [nontrivial R] [add_comm_group A] [add_comm_group A']
variables [module R A] [no_zero_smul_divisors R A] [module R A']
variables {v : ι → A} {s t : set A} {x y z : A}

lemma algebraic_independent_unique_iff
  (v : ι → A) [unique ι] :
  algebraic_independent R v ↔ v (default ι) ≠ 0 :=
begin
  simp only [algebraic_independent_iff, finsupp.total_unique, smul_eq_zero],
  refine ⟨λ h hv, _, λ hv l hl, finsupp.unique_ext $ hl.resolve_right hv⟩,
  have := h (finsupp.single (default ι) 1) (or.inr hv),
  exact one_ne_zero (finsupp.single_eq_zero.1 this)
end

alias algebraic_independent_unique_iff ↔ _ algebraic_independent_unique

lemma algebraic_independent_singleton {x : A} (hx : x ≠ 0) :
  algebraic_independent R (λ x, x : ({x} : set A) → A) :=
algebraic_independent_unique coe hx

end nontrivial

/-!
### Properties which require `division_ring K`

These can be considered generalizations of properties of algebraic independence in vector spaces.
-/

section module

variables [division_ring K] [add_comm_group V] [add_comm_group V']
variables [module K V] [module K V']
variables {v : ι → V} {s t : set V} {x y z : V}

open submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type class) -/

lemma mem_span_insert_exchange : x ∈ span K (insert y s) → x ∉ span K s → y ∈ span K (insert x s) :=
begin
  simp [mem_span_insert],
  rintro a z hz rfl h,
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, _⟩,
  have a0 : a ≠ 0, {rintro rfl, simp * at *},
  simp [a0, smul_add, smul_smul]
end

lemma algebraic_independent_iff_not_mem_span :
  algebraic_independent K v ↔ (∀i, v i ∉ span K (v '' (univ \ {i}))) :=
begin
  apply algebraic_independent_iff_not_smul_mem_span.trans,
  split,
  { intros h i h_in_span,
    apply one_ne_zero (h i 1 (by simp [h_in_span])) },
  { intros h i a ha,
    by_contradiction ha',
    exact false.elim (h _ ((smul_mem_iff _ ha').1 ha)) }
end

lemma algebraic_independent.insert (hs : algebraic_independent K (λ b, b : s → V)) (hx : x ∉ span K s) :
  algebraic_independent K (λ b, b : insert x s → V) :=
begin
  rw ← union_singleton,
  have x0 : x ≠ 0 := mt (by rintro rfl; apply zero_mem _) hx,
  apply hs.union (algebraic_independent_singleton x0),
  rwa [disjoint_span_singleton' x0]
end

lemma algebraic_independent_option' :
  algebraic_independent K (λ o, option.cases_on' o x v : option ι → V) ↔
    algebraic_independent K v ∧ (x ∉ submodule.span K (range v)) :=
begin
  rw [← algebraic_independent_equiv (equiv.option_equiv_sum_punit ι).symm, algebraic_independent_sum,
    @range_unique _ punit, @algebraic_independent_unique_iff punit, disjoint_span_singleton],
  dsimp [(∘)],
  refine ⟨λ h, ⟨h.1, λ hx, h.2.1 $ h.2.2 hx⟩, λ h, ⟨h.1, _, λ hx, (h.2 hx).elim⟩⟩,
  rintro rfl,
  exact h.2 (zero_mem _)
end

lemma algebraic_independent.option (hv : algebraic_independent K v)
  (hx : x ∉ submodule.span K (range v)) :
  algebraic_independent K (λ o, option.cases_on' o x v : option ι → V) :=
algebraic_independent_option'.2 ⟨hv, hx⟩

lemma algebraic_independent_option {v : option ι → V} :
  algebraic_independent K v ↔
    algebraic_independent K (v ∘ coe : ι → V) ∧ v none ∉ submodule.span K (range (v ∘ coe : ι → V)) :=
by simp only [← algebraic_independent_option', option.cases_on'_none_coe]

theorem algebraic_independent_insert' {ι} {s : set ι} {a : ι} {f : ι → V} (has : a ∉ s) :
  algebraic_independent K (λ x : insert a s, f x) ↔
  algebraic_independent K (λ x : s, f x) ∧ f a ∉ submodule.span K (f '' s) :=
by { rw [← algebraic_independent_equiv ((equiv.option_equiv_sum_punit _).trans
  (equiv.set.insert has).symm), algebraic_independent_option], simp [(∘), range_comp f] }

theorem algebraic_independent_insert (hxs : x ∉ s) :
  algebraic_independent K (λ b : insert x s, (b : V)) ↔
  algebraic_independent K (λ b : s, (b : V)) ∧ x ∉ submodule.span K s :=
(@algebraic_independent_insert' _ _ _ _ _ _ _ _ id hxs).trans $ by simp

lemma algebraic_independent_pair {x y : V} (hx : x ≠ 0) (hy : ∀ a : K, a • x ≠ y) :
  algebraic_independent K (coe : ({x, y} : set V) → V) :=
pair_comm y x ▸ (algebraic_independent_singleton hx).insert $ mt mem_span_singleton.1
  (not_exists.2 hy)

lemma algebraic_independent_fin_cons {n} {v : fin n → V} :
  algebraic_independent K (fin.cons x v : fin (n + 1) → V) ↔
    algebraic_independent K v ∧ x ∉ submodule.span K (range v) :=
begin
  rw [← algebraic_independent_equiv (fin_succ_equiv n).symm, algebraic_independent_option],
  convert iff.rfl,
  { ext,
    -- TODO: why doesn't simp use `fin_succ_equiv_symm_coe` here?
    rw [comp_app, comp_app, fin_succ_equiv_symm_coe, fin.cons_succ] },
  { ext,
    rw [comp_app, comp_app, fin_succ_equiv_symm_coe, fin.cons_succ] }
end

lemma algebraic_independent_fin_snoc {n} {v : fin n → V} :
  algebraic_independent K (fin.snoc v x : fin (n + 1) → V) ↔
    algebraic_independent K v ∧ x ∉ submodule.span K (range v) :=
by rw [fin.snoc_eq_cons_rotate, algebraic_independent_equiv, algebraic_independent_fin_cons]

/-- See `algebraic_independent.fin_cons'` for an uglier version that works if you
only have a module over a semiring. -/
lemma algebraic_independent.fin_cons {n} {v : fin n → V} (hv : algebraic_independent K v)
  (hx : x ∉ submodule.span K (range v)) :
  algebraic_independent K (fin.cons x v : fin (n + 1) → V) :=
algebraic_independent_fin_cons.2 ⟨hv, hx⟩

lemma algebraic_independent_fin_succ {n} {v : fin (n + 1) → V} :
  algebraic_independent K v ↔
    algebraic_independent K (fin.tail v) ∧ v 0 ∉ submodule.span K (range $ fin.tail v) :=
by rw [← algebraic_independent_fin_cons, fin.cons_self_tail]

lemma algebraic_independent_fin_succ' {n} {v : fin (n + 1) → V} :
  algebraic_independent K v ↔
    algebraic_independent K (fin.init v) ∧ v (fin.last _) ∉ submodule.span K (range $ fin.init v) :=
by rw [← algebraic_independent_fin_snoc, fin.snoc_init_self]

lemma algebraic_independent_fin2 {f : fin 2 → V} :
  algebraic_independent K f ↔ f 1 ≠ 0 ∧ ∀ a : K, a • f 1 ≠ f 0 :=
by rw [algebraic_independent_fin_succ, algebraic_independent_unique_iff, range_unique,
  mem_span_singleton, not_exists,
  show fin.tail f (default (fin 1)) = f 1, by rw ← fin.succ_zero_eq_one; refl]

lemma exists_algebraic_independent (hs : algebraic_independent K (λ x, x : s → V)) (hst : s ⊆ t) :
  ∃b⊆t, s ⊆ b ∧ t ⊆ span K b ∧ algebraic_independent K (λ x, x : b → V) :=
begin
  rcases zorn.zorn_subset_nonempty {b | b ⊆ t ∧ algebraic_independent K (λ x, x : b → V)} _ _
    ⟨hst, hs⟩ with ⟨b, ⟨bt, bi⟩, sb, h⟩,
  { refine ⟨b, bt, sb, λ x xt, _, bi⟩,
    by_contra hn,
    apply hn,
    rw ← h _ ⟨insert_subset.2 ⟨xt, bt⟩, bi.insert hn⟩ (subset_insert _ _),
    exact subset_span (mem_insert _ _) },
  { refine λ c hc cc c0, ⟨⋃₀ c, ⟨_, _⟩, λ x, _⟩,
    { exact sUnion_subset (λ x xc, (hc xc).1) },
    { exact algebraic_independent_sUnion_of_directed cc.directed_on (λ x xc, (hc xc).2) },
    { exact subset_sUnion_of_mem } }
end

/-- `algebraic_independent.extend` adds vectors to a algebraic independent set `s ⊆ t` until it spans
all elements of `t`. -/
noncomputable def algebraic_independent.extend (hs : algebraic_independent K (λ x, x : s → V))
  (hst : s ⊆ t) : set V :=
classical.some (exists_algebraic_independent hs hst)

lemma algebraic_independent.extend_subset (hs : algebraic_independent K (λ x, x : s → V))
  (hst : s ⊆ t) : hs.extend hst ⊆ t :=
let ⟨hbt, hsb, htb, hli⟩ := classical.some_spec (exists_algebraic_independent hs hst) in hbt

lemma algebraic_independent.subset_extend (hs : algebraic_independent K (λ x, x : s → V))
  (hst : s ⊆ t) : s ⊆ hs.extend hst :=
let ⟨hbt, hsb, htb, hli⟩ := classical.some_spec (exists_algebraic_independent hs hst) in hsb

lemma algebraic_independent.subset_span_extend (hs : algebraic_independent K (λ x, x : s → V))
  (hst : s ⊆ t) : t ⊆ span K (hs.extend hst) :=
let ⟨hbt, hsb, htb, hli⟩ := classical.some_spec (exists_algebraic_independent hs hst) in htb

lemma algebraic_independent.algebraic_independent_extend (hs : algebraic_independent K (λ x, x : s → V))
  (hst : s ⊆ t) : algebraic_independent K (coe : hs.extend hst → V) :=
let ⟨hbt, hsb, htb, hli⟩ := classical.some_spec (exists_algebraic_independent hs hst) in hli

variables {K V}

-- TODO(Aario): rewrite?
lemma exists_of_algebraic_independent_of_finite_span {t : finset V}
  (hs : algebraic_independent K (λ x, x : s → V)) (hst : s ⊆ (span K ↑t : submodule K V)) :
  ∃t':finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card :=
have ∀t, ∀(s' : finset V), ↑s' ⊆ s → s ∩ ↑t = ∅ → s ⊆ (span K ↑(s' ∪ t) : submodule K V) →
  ∃t':finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
assume t, finset.induction_on t
  (assume s' hs' _ hss',
    have s = ↑s',
      from eq_of_algebraic_independent_of_span_subtype hs hs' $
          by simpa using hss',
    ⟨s', by simp [this]⟩)
  (assume b₁ t hb₁t ih s' hs' hst hss',
    have hb₁s : b₁ ∉ s,
      from assume h,
      have b₁ ∈ s ∩ ↑(insert b₁ t), from ⟨h, finset.mem_insert_self _ _⟩,
      by rwa [hst] at this,
    have hb₁s' : b₁ ∉ s', from assume h, hb₁s $ hs' h,
    have hst : s ∩ ↑t = ∅,
      from eq_empty_of_subset_empty $ subset.trans
        (by simp [inter_subset_inter, subset.refl]) (le_of_eq hst),
    classical.by_cases
      (assume : s ⊆ (span K ↑(s' ∪ t) : submodule K V),
        let ⟨u, hust, hsu, eq⟩ := ih _ hs' hst this in
        have hb₁u : b₁ ∉ u, from assume h, (hust h).elim hb₁s hb₁t,
        ⟨insert b₁ u, by simp [insert_subset_insert hust],
          subset.trans hsu (by simp), by simp [eq, hb₁t, hb₁s', hb₁u]⟩)
      (assume : ¬ s ⊆ (span K ↑(s' ∪ t) : submodule K V),
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this in
        have hb₂t' : b₂ ∉ s' ∪ t, from assume h, hb₂t $ subset_span h,
        have s ⊆ (span K ↑(insert b₂ s' ∪ t) : submodule K V), from
          assume b₃ hb₃,
          have ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : set V),
            by simp [insert_eq, -singleton_union, -union_singleton, union_subset_union, subset.refl,
              subset_union_right],
          have hb₃ : b₃ ∈ span K (insert b₁ (insert b₂ ↑(s' ∪ t) : set V)),
            from span_mono this (hss' hb₃),
          have s ⊆ (span K (insert b₁ ↑(s' ∪ t)) : submodule K V),
            by simpa [insert_eq, -singleton_union, -union_singleton] using hss',
          have hb₁ : b₁ ∈ span K (insert b₂ ↑(s' ∪ t)),
            from mem_span_insert_exchange (this hb₂s) hb₂t,
          by rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃,
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset, hb₂s, hs']) hst this in
        ⟨u, subset.trans hust $ union_subset_union (subset.refl _) (by simp [subset_insert]),
          hsu, by simp [eq, hb₂t', hb₁t, hb₁s']⟩)),
begin
  have eq : t.filter (λx, x ∈ s) ∪ t.filter (λx, x ∉ s) = t,
  { ext1 x,
    by_cases x ∈ s; simp * },
  apply exists.elim (this (t.filter (λx, x ∉ s)) (t.filter (λx, x ∈ s))
    (by simp [set.subset_def]) (by simp [set.ext_iff] {contextual := tt}) (by rwa [eq])),
  intros u h,
  exact ⟨u, subset.trans h.1 (by simp [subset_def, and_imp, or_imp_distrib] {contextual:=tt}),
    h.2.1, by simp only [h.2.2, eq]⟩
end

lemma exists_finite_card_le_of_finite_of_algebraic_independent_of_span
  (ht : finite t) (hs : algebraic_independent K (λ x, x : s → V)) (hst : s ⊆ span K t) :
  ∃h : finite s, h.to_finset.card ≤ ht.to_finset.card :=
have s ⊆ (span K ↑(ht.to_finset) : submodule K V), by simp; assumption,
let ⟨u, hust, hsu, eq⟩ := exists_of_algebraic_independent_of_finite_span hs this in
have finite s, from u.finite_to_set.subset hsu,
⟨this, by rw [←eq]; exact (finset.card_le_of_subset $ finset.coe_subset.mp $ by simp [hsu])⟩

end module


end
