import data.finset
import combinatorics.simple_graph.basic
import algebra.module.submodule.basic
import linear_algebra.finite_dimensional
import linear_algebra.finrank
import linear_algebra.finsupp
import data.setoid.partition
import linear_algebra.projective_space.basic
import linear_algebra.span

universes u v w

open finset

variables {α : Type u} [decidable_eq α]



variables [fintype α]

/- A matroid M is an ordered pair `(E, ℐ)` consisting of a finite set `E` and
a collection `ℐ` of subsets of `E` having the following three properties:
  (I1) `∅ ∈ ℐ`.
  (I2) If `I ∈ ℐ` and `I' ⊆ I`, then `I' ∈ ℐ`.
  (I3) If `I₁` and `I₂` are in `I` and `|I₁| < |I₂|`, then there is an element `e` of `I₂ − I₁`
    such that `I₁ ∪ {e} ∈ I`.-/

def can_exchange (ℐ : finset α → Prop) : Prop :=
∀ I₁ I₂, ℐ I₁ ∧ ℐ I₂ → finset.card I₁ < finset.card I₂ → ∃ (e ∈ I₂ \ I₁), (ℐ (insert e I₁))

@[ext]
structure matroid (α : Type u) [fintype α] [decidable_eq α] :=
(ℐ : finset α → Prop)
(empty : ℐ ∅) -- (I1)
(hereditary : ∀ (I₁ : finset α), ℐ I₁ → ∀ (I₂ : finset α), I₂ ⊆ I₁ → ℐ I₂) -- (I2)
(ind : can_exchange ℐ) -- (I3)


namespace matroid

variables (M : matroid α) [decidable_pred M.ℐ]

/- A subset of `E` that is not in `ℐ` is called dependent. -/
def dependent_sets : finset (finset α) := filter (λ s, ¬ M.ℐ s) univ.powerset

-- (C1)
lemma empty_not_dependent : ∅ ∉ M.dependent_sets :=
begin

  sorry,
end

variables [decidable_pred (λ (D : finset α), can_exchange (λ (_x : finset α), _x ∈ D.powerset.erase D))]

def circuit : finset (finset α) :=
  finset.filter (λ (D : finset α), (∀ (S ∈ (erase D.powerset D)), M.ℐ S)) (M.dependent_sets)


@[simp]
lemma mem_circuit (C₁ : finset α) :
  C₁ ∈ M.circuit ↔ C₁ ∈ M.dependent_sets ∧ (∀ (C₂ ∈ (erase C₁.powerset C₁)), M.ℐ C₂) :=
begin
  sorry,
end

/- `(C2)` if C₁ and C₂ are members of C and C₁ ⊆ C₂, then C₂ = C₂.
In other words, C forms an antichain. -/
lemma circuit_antichain (C₁ C₂ : finset α) (h₁ : C₁ ∈ M.circuit) (h₂ : C₂ ∈ M.circuit) : C₁ ⊆ C₂ → C₁ = C₂ :=
begin
  sorry,
end

/- `(C3)` If C₁ and C₂ are distinct members of M.circuit and e ∈ C₁ ∩ C₂, then
there is a member C₃ of M.circuit such that C₃ ⊆ (C₁ ∪ C₂) - e.   -/
lemma circuit_dependence (C₁ C₂ : finset α) (h₁ : C₁ ∈ M.circuit) (h₂ : C₂ ∈ M.circuit) (h : C₁ ≠ C₂) (e : α) :
  e ∈ C₁ ∩ C₂ → ∃ C₃ ∈ M.circuit, C₃ ⊆ (C₁ ∪ C₂) \ {e} :=
begin
  sorry,
end


-- for this i think we need a lemma along the lines of, if α is fintype and p : finset α → Prop
-- is a function where ∀ y ⊆ x, p x → p y, then there are "maximal" x : finset α
-- or maybe we can define this w.r.t rank function?
/- A maximal member of `ℐ` is called a basis. -/
-- def bases : finset (finset α) := filter (λ s, M.ℐ s) univ.powerset


-- this is broken because of some missing instance somewhere, lean doesn't seem to
-- get that if V is finite then a simple graph on V will have finite edge set so
-- uncomment at your own peril (jk if you're feeling up for the challenge you can
-- probably figure out how to fix it)
/- variables (V : Type u) (G : simple_graph V) [fintype V] [decidable_eq V] [fintype G.edge_set]
namespace simple_graph
instance : fintype G.edge_set :=
{ elems := _,
  complete := _ }
end simple_graph
def graphic_matroid (G : simple_graph V) : matroid G.edge_set := _-/



-- coercing x from fintype ↑s to fintype α is proving very annoying
/- @[ext]
def restriction {V : Type u} (M : matroid α) (s : finset α) : matroid s :=
{ ℐ := λ x, M.ℐ _,
  empty := _,
  hereditary := _,
  ind := _ }-/


-- probably need instance saying subspace of fintype is fintype


-- any d-dimensional vector space over GF(q) has exactly (q^d-1) / (q - 1) 1-dimensional subspaces
-- do i count it as fintype.card or do i try to do set of subspaces?
-- fintype.card {x : subspace α V | findim x = 1} = (q^d-1) / (q - 1)
variables (K : Type u) (V : Type v) [field K] [add_comm_group V] [module K V] [fintype K]
variables [finite_dimensional K V] (q d : ℕ)
variables [fintype (module K V)]
variables [fintype {S : submodule K V | finite_dimensional.finrank K S = 1}]
-- size of K should be q
-- we get [fintype V] from finite_dimensional K V and fintype K

instance fintype_subspaces : fintype {x : subspace K V | finite_dimensional.finrank x = 1} :=
begin
  simp,
  sorry,
end

-- lemma num_basis_vectors :

-- use basis_unique, basis_singleton

-- some kind of lemma stating that if c ⬝ x = d ⬝ y then their respective subspaces are the same
-- do we have some kind of map from basis to subspace?
-- i think the notation here is K ∙ x = K ∙ y
-- this is just span_singleton_eq_span_singleton
lemma subspace_eq_of_basis_scalar (x y : V) (b : K) (h2 : b ≠ 0) :
  x = (b • y) → (K ∙ x) = (K ∙ y) :=
begin
  intros h,
  ext v;
  rw submodule.mem_span_singleton,
  rw submodule.mem_span_singleton,
  split,
  rintros ⟨n, hn⟩,
  rw [← hn, h, smul_smul],
  use (n * b),
  rintros ⟨n, hn⟩,
  use (n * b⁻¹),
  rw [← hn, h, smul_smul, mul_assoc, inv_mul_cancel h2, mul_one],
end

--lemma subspace_inter (x y : V) : ¬ ∃ (a : K), x = a • y → (K ∙ x) ∩ (K ∙ y) = {0 : V}

instance fintype_span (x : V) : fintype (K ∙ x) :=
begin
  -- have disjoint_span_singleton
  sorry,
end

lemma mem_span_singleton_smul (a : K) (x : V) : a • x ∈ K ∙ x :=
begin
  apply submodule.mem_span_singleton.2,
  use a,
end

-- use span.coord
lemma card_set_scalar_mul (x : V) : fintype.card (K ∙ x) = fintype.card K :=
begin
  sorry,
end

open_locale classical

-- only true if V & K nontrivial
-- use this for principal of inclusion-exclusion?
lemma sUnion_dimone_univ (hV : nontrivial V) :
  set.sUnion {x : set V | ∃ (m : submodule K V), x = m.carrier ∧ finite_dimensional.finrank K m = 1} = set.univ :=
begin
  ext;
  split,
  intros h,
  simp at h,
  simp,
  by_cases h : x ≠ 0,
  use (K ∙ x).carrier,
  use (K ∙ x),
  refine ⟨rfl, _⟩,
  apply finrank_span_singleton h,
  simp,
  exact submodule.mem_span_singleton_self x,
  push_neg at h,
  have e := (nontrivial_iff_exists_ne x).1 hV,
  cases e with v hv,
  rw h at hv,
  use (K ∙ v).carrier,
  use (K ∙ v),
  refine ⟨rfl, _⟩,
  apply finrank_span_singleton hv,
  rw h,
  simp,
end

-- lemma subspaces_dim_one : {S : subspace K V | finite_dimensional.finrank S = 1} =
variables {ι : Type*}
lemma nonzero_elems [fintype ι] (b : basis ι K V) [fintype V] :
 ({0}ᶜ : finset V).card = fintype.card K ^ fintype.card ι - 1 :=
begin
  rw [← module.card_fintype b, ← card_singleton (0 : V), card_compl],
end

--lemma projective_mk_is_partition : setoid.is_partition (projectivization.submodule (projectivization.mk' K _)) :=

/-lemma dim_one_is_partition : setoid.is_partition
  ({λ (x : { H : submodule K V // finite_dimensional.finrank K H = 1 }), x.1.carrier} : set (set V)) :=
begin
  rw setoid.is_partition,
  split,
  simp,
  intros x hx,
  have h2 : finite_dimensional.finrank K x = 0,
  rw finrank_zero_iff_forall_zero,
  intros x1,
  sorry,
end-/

variables {K V} [fintype V]
def subspace_rem_zero (S : submodule K V) : set V := S.carrier \ {0}

noncomputable def subspace_rem_zero_finset (S : submodule K V) : finset V := (subspace_rem_zero S).to_finset

-- i don't know why the lemma doesn't see the instances
variables [nontrivial K] (p : submodule K V) [no_zero_smul_divisors K p]
lemma span_singleton_eq_iff_mem_dim_one (m : V) (hk : m ≠ 0) : (K ∙ m) = p ↔ m ∈ p ∧ finite_dimensional.finrank K p = 1 :=
begin
  have h1 := submodule.span_singleton_le_iff_mem m p,
  split,
  intros h2,
  rw ← h2,
  refine ⟨submodule.mem_span_singleton_self m, finrank_span_singleton hk⟩,
  intros h2,
  ext;
  split,
  intros h3,
  have h4 := h1.2 h2.1,
  rw submodule.mem_span at h3,
  apply h3,
  simp,
  apply h2.1,

  intros h4,
  have h3 := h2.2,
  have h5 := finite_dimensional.basis_singleton (fin 1) h3,
  specialize h5 ⟨m, h2.1⟩,
  have h6 : (⟨m, h2.1⟩ : p) ≠ 0,
  simp,
  exact hk,
  specialize h5 h6,

  have h9 := (basis.basis_singleton_iff (fin 1)).1,
  have h10 : nonempty (basis (fin 1) K p),
  use h5,
  specialize h9 h10,
  rcases h9 with ⟨a, ⟨ha, hb⟩⟩,
  have h11 := hb ⟨x, h4⟩,
  cases h11 with r hr,
  by_cases x = 0,
  rw h,
  simp,
  have h14 : r ≠ 0,
  have h21 : (⟨x, h4⟩ : p) ≠ 0,
  simp only [ne.def, submodule.mk_eq_zero],
  exact h,
  rw ←hr at h21,
  have h20 := smul_ne_zero_iff.1 h21,
  exact h20.1,
  have h15 : x = r • ↑a,
  rw ← submodule.coe_smul,
  rw hr,
  simp,
  have h12 := hb ⟨m, h2.1⟩,
  cases h12 with s hs,
  have h16 : s ≠ 0,
  have h21 : (⟨m, h2.1⟩ : p) ≠ 0,
  simp only [ne.def, submodule.mk_eq_zero],
  exact hk,
  rw ← hs at h21,
  have h22 := smul_ne_zero_iff.1 h21,
  exact h22.1,
  have h17 : m = s • ↑a,
  rw ← submodule.coe_smul,
  rw hs,
  simp,
  have h13 := subspace_eq_of_basis_scalar K V m a s h16 h17,
  rw h13,
  rw submodule.mem_span_singleton,
  use r,
  rw h15,
  -- x ∈ K a
  -- y ∈ K a
  sorry,
  sorry,
end

noncomputable def of_span : finpartition ({0}ᶜ : finset V) :=
{ parts := finset.image subspace_rem_zero_finset ({S : submodule K V | finite_dimensional.finrank K S = 1}.to_finset),
  sup_indep := λ S h a ha hna,
    begin
      simp,
      simp at ha,
      rcases ha with ⟨H, ⟨hH1, hH2⟩⟩,
      rw disjoint_iff_ne,
      intros x hx y hy,
      rw mem_sup at hy,
      rcases hy with ⟨Y, ⟨hY1, hY2⟩⟩,
      have h2 := mem_of_subset h hY1,
      simp at h2,
      rcases h2 with ⟨P, ⟨hP1, hP2⟩⟩,
      have h3 : x ∈ H,
      rw ← hH2 at hx,
      rw subspace_rem_zero_finset at hx,
      rw subspace_rem_zero at hx,
      simp at hx,
      exact hx.1,
      have h4 : y ∈ P,
      simp at hY2,
      rw ← hP2 at hY2,
      rw subspace_rem_zero_finset at hY2,
      rw subspace_rem_zero at hY2,
      simp at hY2,
      exact hY2.1,
      by_contra hc,

      have h10 : x ≠ 0,
      rw ← hH2 at hx,
      rw subspace_rem_zero_finset at hx,
      rw subspace_rem_zero at hx,
      simp at hx,
      exact hx.2,

      rw ← hc at h4,
      have h5 := (span_singleton_eq_iff_mem_dim_one H x h10).2 ⟨h3, hH1⟩,
      have h11 : y ≠ 0,
      rw ← hc,
      exact h10,
      rw hc at h4,
      have h6 := (span_singleton_eq_iff_mem_dim_one P y h11).2 ⟨h4, hP1⟩,
      have h7 : H = P,
      rw ← h5,
      rw ← h6,
      rw hc,
      have h8 : a = Y,
      rw ← hP2,
      rw h7 at hH2,
      rw ← hH2,
      rw ← h8 at hY1,
      apply hna,
      exact hY1,
    end,
  sup_parts :=
    begin
      ext a;
      split,
      intros h,
      simp,
      rw mem_sup at h,
      rcases h with ⟨f, ⟨h1, h2⟩⟩,
      rw mem_image at h1,
      rcases h1 with ⟨S, ⟨h4, h5⟩⟩,
      rw subspace_rem_zero_finset at h5,
      rw subspace_rem_zero at h5,
      rw ← h5 at h2,
      simp at h2,
      exact h2.2,
      intros h,
      rw mem_sup,
      simp at h,
      use subspace_rem_zero_finset (K ∙ a),
      split,
      simp,
      use (K ∙ a),
      refine ⟨_, rfl⟩,
      rw ← finrank_span_singleton h,
      simp,
      rw subspace_rem_zero_finset,
      rw subspace_rem_zero,
      rw set.mem_to_finset,
      simp,
      refine ⟨_, h⟩,
      apply submodule.mem_span_singleton_self,
    end,
  not_bot_mem :=
    begin
      by_contra,
      simp at h,
      rcases h with ⟨a, ⟨ha1, ha2⟩⟩,
      rw subspace_rem_zero_finset at ha2,
      rw subspace_rem_zero at ha2,
      simp at ha2,
      have h2 : finite_dimensional.finrank K a = 0,
      rw finrank_zero_iff_forall_zero,
      intros x,
      specialize ha2 x x.2,
      simp at ha2,
      apply ha2,
      apply nat.one_ne_zero,
      rw ← ha1,
      rw ← h2,
    end }

lemma card_subspace [nontrivial V] : (∀ (x : finset V), x ∈ finset.image subspace_rem_zero_finset ({S : submodule K V | finite_dimensional.finrank K S = 1}.to_finset) → finset.card x = q - 1) :=
begin
  intros x h,
  rw mem_image at h,
  rcases h with ⟨h, ⟨ha, hb⟩⟩,
  rw set.mem_to_finset at ha,
  simp at ha,
  rw subspace_rem_zero_finset at hb,
  rw subspace_rem_zero at hb,
  rw ← hb,
  rw set.to_finset_diff,
  rw card_sdiff,
  have h2 : h.carrier.to_finset.card = q,
  have h4 := exists_ne (0 : V),
  have B := finite_dimensional.fin_basis K h,
  rw ha at B,

  have h6 : 0 < finite_dimensional.finrank K ↥h,
  rw ha,
  simp,
  haveI := finite_dimensional.finrank_pos_iff.1 h6,
  have h7 := exists_ne (0 : h),
  cases h7 with y hy,
  have hy' : y.1 ≠ 0,
  simp,
  exact hy,
  have h8 := (span_singleton_eq_iff_mem_dim_one h y hy').2 ⟨y.2, ha⟩,
  have h9 := linear_equiv.to_span_nonzero_singleton K h y hy,
  rw ← h8,
  have h10 := equiv.of_bijective h9.to_equiv sorry,
  have h11 := finset.card,
  sorry,
  simp,
end

noncomputable lemma num_subspaces_dim_one (h : finite_dimensional.finrank K V = d) (h2 : fintype.card K = q) :
  ({S : subspace K V | finite_dimensional.finrank S = 1}.to_finset).card * (q - 1) = q^d - 1 :=
begin
  have B := finite_dimensional.fin_basis K V,
  haveI := module.fintype_of_fintype B,
  rw h at B,
  rw ← fintype.card_fin d,
  rw ← h2,
  rw ← nonzero_elems K V B,
  rw ← card_singleton {(0 : K)},
  rw ← card_compl,
  -- rw add_subgroup.card_dvd_of_injective,

  --have h5 := sum_const_nat,
  -- the argument is there are q^d-1 nonzero vectors
  -- and then divide by q - 1 to remove scalar multiples
  -- use big operators for this
  sorry,
end

-- be careful with disjoint of submodules because it means they share the zero element
-- in order to count the number of subspaces we need disjoint of their carriers

end matroid
