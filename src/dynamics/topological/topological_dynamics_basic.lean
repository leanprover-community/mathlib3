import dynamics.topological.compact_metrizable
import topology.uniform_space.basic
import dynamics.topological.baire_refactor

/-!
# Topological dynamics, basic

We introduce some central concepts of topological dynamics :
- the class of topological dynamical systems (data : a compact metrizable space X,
  and a continuous map T : X → X).
- the notion of invariant closed subset, with constructors (intersection, finite union, etc.)
  and a few instances.
- minimal (sub-)systems.
- topologically transitive and mixing systems.
- dynamical relations (orbit, recurrence, nonwandering relations).
  Relationship with minimality and topological transitiveness.
- periodicity, quasi- and almost-periodicity. Relationship with previous notions.

## Main results

- `exists_minimal_in_inv_clos`: existence of a minimal subset in any invariant closed set.
  The most frequent proof uses Zorn's lemma; the statement below uses the second countability
  of the phase space, but does not rely on the axiom of choice.
- `minimal_iff_almost_periodic`: a characterization of almost-periodicity of a point as
  minimality of the closure of its orbit (Birkhoff, 1912).
- `exists_almost_periodic`: the two theorems above yield the existence of almost periodic points.

## Notation

## References

Most of the implementation rely on
  [K] Petr Kurka, Topological and symbolic dynamics, SMF, Cours spécialisés, 2003
with a few modifications, pointed out in the file.
-/


namespace topological_dynamics_basic

/- Lemme suivant à mettre dans topology.basic ? -/

lemma closure_inter_open {α : Type*} [topological_space α] {s t : set α} (h : is_open t) :
  (closure s ∩ t).nonempty ↔ (s ∩ t).nonempty :=
begin
  split,
  { intro clos_st_nonempty,
    cases clos_st_nonempty with x x_in_clos_st,
    rw set.inter_comm,
    exact mem_closure_iff.1 x_in_clos_st.1 t h x_in_clos_st.2 },
  { intro st_nonempty,
    exact set.nonempty.mono (set.inter_subset_inter_left t subset_closure) st_nonempty }
end


class top_dyn_sys (X : Type*) (T : X → X) :=
  ( top : topological_space X )
  ( compact_metrizable : compact_metrizable.compact_metrizable_space X )
  ( continuous : continuous T )


attribute [instance]
  top_dyn_sys.top
  top_dyn_sys.compact_metrizable


variables {X : Type*} (T : X → X) [top_dyn_sys X T]


instance : baire_space X := @baire_category_theorem_locally_compact X _inst_1.top _ _

instance : uniform_space X :=
  @uniform_space_of_compact_t2 X _ _inst_1.compact_metrizable.compact _inst_1.compact_metrizable.t2

localized "notation `𝓤` := uniformity" in uniformity


lemma uniform_continuous_transformation :
  uniform_continuous T :=
@compact_space.uniform_continuous_of_continuous X X _ _ _ (separated_iff_t2.2 _inst_1.compact_metrizable.t2) T _inst_1.continuous


/- A subset F is said to be invariant and closed if it is closed and sub-invariant
(its image is included in itself). Invariant closed sets are the closed subsets of
a topology on X. We prove the stability under finite unions and arbitrary intersections.
  In addition, invariant_closed is stated as a class, of which we give two instances
for now : the empty set and the universe. -/


class invariant_closed (F : set X) :
  Prop :=
  ( is_closed : is_closed F )
  ( is_invariant : F ⊆ T⁻¹' F )


lemma inv_def (F : set X) [invariant_closed T F] :
  ∀ (x : X), x ∈ F → T x ∈ F :=
begin
  intros x x_in_F,
  apply _inst_2.is_invariant,
  exact x_in_F
end


lemma univ_is_inv_clos :
  invariant_closed T set.univ :=
{ is_closed := is_closed_univ,
  is_invariant := by rw set.preimage_univ }


lemma empty_set_is_inv_clos :
  invariant_closed T ∅ :=
{ is_closed := is_closed_empty,
  is_invariant := by rw set.preimage_empty, }


lemma inter_of_inv_clos_is_inv_clos (F : set X) (G : set X)
  [invariant_closed T F] [invariant_closed T G] :
  invariant_closed T (F ∩ G) :=
{ is_closed := is_closed.inter _inst_2.is_closed _inst_3.is_closed,
  is_invariant :=
  begin
    rw set.preimage_inter,
    exact set.inter_subset_inter _inst_2.is_invariant _inst_3.is_invariant,
  end }


lemma Inter_of_inv_clos_is_inv_clos {ι : Sort*} {s : ι → set X}
  [h : ∀ (i : ι), invariant_closed T (s i)] :
  invariant_closed T (⋂ (i : ι), s i) :=
{ is_closed := is_closed_Inter (λ (i : ι), (h i).is_closed),
  is_invariant :=
  begin
    rw set.preimage_Inter,
    apply set.Inter_mono,
    intro i,
    exact (h i).is_invariant,
  end }


lemma sInter_of_inv_clos_is_inv_clos (A : set(set X))
  [h : ∀ (F : set X), (F ∈ A) → invariant_closed T F] :
  invariant_closed T (⋂₀ A) :=
{ is_closed :=
  begin
    apply is_closed_sInter,
    intros F F_in_A,
    specialize h F F_in_A,
    exact h.is_closed,
  end,
  is_invariant :=
  begin
    intros x x_in_sInter,
    simp,
    intros F F_in_A,
    haveI F_inv_clos := h F F_in_A,
    exact inv_def T F x (set.mem_sInter.1 x_in_sInter F F_in_A),
  end }


lemma union_of_inv_clos_is_inv_clos (F : set X) (G : set X)
  [invariant_closed T F] [invariant_closed T G] :
  invariant_closed T (F ∪ G) :=
{ is_closed := is_closed.union _inst_2.is_closed _inst_3.is_closed,
  is_invariant :=
  begin
    rw set.preimage_union,
    exact set.union_subset_union _inst_2.is_invariant _inst_3.is_invariant,
  end }


def topology_of_invariants (X : Type) (T : X → X) [top_dyn_sys X T] :
  topological_space X :=
begin
  apply topological_space.of_closed { F : set X | invariant_closed T F } (empty_set_is_inv_clos T),
  { simp,
    intros A h,
    have this : ∀ (F : set X), F ∈ A → invariant_closed T F := by { intros F F_in_A, exact h F_in_A },
    exact @sInter_of_inv_clos_is_inv_clos X T _ A this},
  { simp,
    introsI F F_inv_clos G G_inv_clos,
    exact union_of_inv_clos_is_inv_clos T F G },
end


def Inter_of_preorbit_of_clos (F : set X) : set X := ⋂ (n : ℕ), T^[n]⁻¹' F


lemma Inter_of_preorbit_of_clos_is_inv_clos (F : set X) [is_closed F] :
  invariant_closed T (Inter_of_preorbit_of_clos T F) :=
begin
  split,
  { apply is_closed_sInter,
    simp,
    exact λ (n : ℕ), is_closed.preimage (continuous.iterate _inst_1.continuous n) _inst_2 },
  { unfold Inter_of_preorbit_of_clos,
    rw set.preimage_Inter,
    apply set.Inter_mono',
    intro n,
    use n+1,
    rw [function.iterate_add T n 1, function.iterate_one, set.preimage_comp] },
end

instance : invariant_closed T set.univ := univ_is_inv_clos T
instance : invariant_closed T ∅ := empty_set_is_inv_clos T
instance (F : set X) (G : set X) [invariant_closed T F] [invariant_closed T G] :
  invariant_closed T (F ∩ G) :=
  inter_of_inv_clos_is_inv_clos T F G
instance (F : set X) (G : set X) [invariant_closed T F] [invariant_closed T G] :
  invariant_closed T (F ∪ G) :=
  union_of_inv_clos_is_inv_clos T F G
instance (F : set X) [is_closed F] :
  invariant_closed T (Inter_of_preorbit_of_clos T F) :=
  Inter_of_preorbit_of_clos_is_inv_clos T F


lemma iter_of_inv_clos_in_inv_clos (F : set X) [invariant_closed T F] (n : ℕ) :
  F ⊆ (T^[n])⁻¹' F :=
begin
  induction n,
  { rw [function.iterate_zero T, set.preimage_id] },
  { rw [function.iterate_succ T n_n, set.preimage_comp],
    exact set.subset.trans _inst_2.is_invariant (set.preimage_mono n_ih) },
end


/- Minimal closed invariant subsets and minimal systems.
  Deviation from [K] : we define not only minimal systems, but more generally minimal
invariant closed subsets. This yields more general statements, while bypassing induced subsystems.
  The dynamical system `(X, T)` is minimal on an invariant closed subset `F` if `F` is irreducible:
  any smaller invariant clsoed subset is either the whole of `F` or empty. -/
def minimal_on (F : set X) :
  Prop :=
∀ (G : set X) [G_inv_clos : invariant_closed T G] (G_sub_F : G ⊆ F), G = ∅ ∨ G = F


/- The dynamical system `(X, T)` is minimal if it is irreducible,
  i.e. if it is minimal on `set.univ`. -/
def minimal :
  Prop :=
∀ (F : set X) [F_inv_clos : invariant_closed T F], F = ∅ ∨ F = set.univ


lemma minimal_iff_minimal_on_univ :
  minimal T ↔ minimal_on T set.univ :=
begin
  split,
  { introsI XT_minimal F F_inv_clos F_sub_univ,
    exact XT_minimal F },
  { introsI minimal_on_univ F F_inv_clos,
    exact minimal_on_univ F (set.subset_univ F) },
end


/-- Existence of a minimal subset in any invariant closed set. The most frequent proof uses
  Zorn's lemma; see e.g. [K]. The statement below uses the second countability of the phase space,
  but does not rely on the axiom of choice.
  The strategy is as follow. Take a countable topological basis (U n) of the space. For
any open set (U n), the complement G n of V n := ⋃ (k : ℕ) (T^[k]⁻¹' (U n)) is invariant closed.
  Start from the invariant closed set F in which we want to find a minimal subsystem.
Construct inductively a closed invariant subset F (n+1) by taking:
    - F (n+1) = F n if F n ⊆ (G n)ᶜ ;
    - F (n+1) = (F n) ∩ (G n) otherwise.
  Then ⋂ (n : ℕ), F n is a closed invariant subset, which is nonempty as the limit of a
nonincreasing sequence of compact subsets.
  In addition, ⋂ (n : ℕ), F n is also minimal: if it were not, there would be a non-trivial
closed invariant subset, whose complement would contains some V k. This contradicts the
construction of the sequence (F n), and in particular the step from F k to F (k+1). -/
theorem exists_minimal_in_inv_clos (F : set X) [invariant_closed T F] :
  F.nonempty → ∃ (G ⊆ F) (G_inv_clos : invariant_closed T G),
  G.nonempty ∧ minimal_on T G :=
begin
  classical,
  /- We begin by translating the second-countability property of the compact_metrizable space
    into an enumeration of a countable open basis. -/
  intro F_nonempty,
  have countable_basis :=
    @topological_space.exists_countable_basis X _ _inst_1.compact_metrizable.second_countable,
  rcases countable_basis with ⟨ open_basis, ⟨ countable_basis, no_nonempty_open, top_basis ⟩ ⟩,
  haveI nonempty_basis : open_basis.nonempty :=
  begin
    apply set.nonempty.of_sUnion,
    rw top_basis.sUnion_eq,
    exact set.nonempty.mono (set.subset_univ F) F_nonempty,
  end,
  replace countable_basis :=
    (set.countable_iff_exists_surjective_to_subtype nonempty_basis).1 countable_basis,
  cases countable_basis with basis_enum surjective_enum,
  clear no_nonempty_open nonempty_basis,
  /- We define the nonincreasing sequence subset_seq of invariant closed subsets
  which will converge to a minimal subset.
    (G n) is the (invariant, closed) subset of points
  which never visit the nth open set in the enumeration.
    subset_seq is defined recursively: start from F. If subset_seq n ⊆ (G n)ᶜ, keep subset_seq n.
  Otherwise, replace subset_seq n by (subset_seq n) ∩ (G n). -/
  let G := λ (n : ℕ), Inter_of_preorbit_of_clos T (basis_enum n)ᶜ,
  let subset_seq : ℕ → set X :=
    λ (n : ℕ), nat.rec_on n F (λ (n : ℕ) (A : set X), if (A ∩ G n).nonempty then (A ∩ G n) else A),
  /- We check by induction that subset_seq n is indeed invariant and closed. -/
  have is_inv_clos_subset_seq : ∀ (n : ℕ), invariant_closed T (subset_seq n) :=
  begin
    intro n,
    induction n with n h_n,
    { assumption },
    { change invariant_closed T (if ((subset_seq n) ∩ G n).nonempty then ((subset_seq n) ∩ G n) else (subset_seq n)),
      split_ifs,
      { haveI := (@Inter_of_preorbit_of_clos_is_inv_clos X T _ (basis_enum n)ᶜ (is_closed_compl_iff.2 (topological_space.is_topological_basis.is_open top_basis (basis_enum n).2))),
        apply inter_of_inv_clos_is_inv_clos T (subset_seq n) },
      { exact h_n } },
  end,
  /- Our candidate for the limit is the limit (or intersection) of the subset_seq n.
  We check that the limit is invariant and closed, then that it is nonempty and minimal. -/
  use ⋂ (n : ℕ), subset_seq n,
  haveI candidate_is_inv_clos := @Inter_of_inv_clos_is_inv_clos X T _ _ _ is_inv_clos_subset_seq,
  split, use set.Inter_subset subset_seq 0,
  split, swap,
  split,
  /- First, the candidate is not empty, as the intersection of a nonincreasing sequence of compact subsets.
  Compactness is free (we already know that (subset_seq n) is closed), we have to prove recursively that (subset_seq n)
  is nonincreasing and nonempty. -/
  { apply is_compact.nonempty_Inter_of_sequence_nonempty_compact_closed subset_seq _ _ _ (λ (n : ℕ), (is_inv_clos_subset_seq n).is_closed),
    { intro n,
      change (if ((subset_seq n) ∩ G n).nonempty then ((subset_seq n) ∩ G n) else (subset_seq n)) ⊆ subset_seq n,
      split_ifs,
      { exact set.inter_subset_left (subset_seq n) _ },
      { trivial } },
    { intro n,
      induction n with n h_n,
      { exact F_nonempty },
      { change (if ((subset_seq n) ∩ G n).nonempty then ((subset_seq n) ∩ G n) else (subset_seq n)).nonempty,
        split_ifs,
        { exact h },
        { exact h_n } } },
    { exact is_closed.is_compact _inst_2.is_closed } },
  /- Now the main dish: the minimality of the limit! Take an nonempty invariant closed subset H in the limit.
  We use a proof by contradiction. If H is not the full candidate, we can find a point y outside H.
  Then, we use the separation (X is normal) to find an open neighbourhood V of y disjoint from H, and from there a smaller open
  neighborhood W of y which belongs to the topological basis. Let k be its index.
  Then the recursive definition of subset_seq fails at stage k, which brings us the contradiction we need. -/
  { introsI H H_inv_clos H_sub_candidate,
    rw or_iff_not_imp_left,
    intro H_not_empty,
    replace H_not_empty := set.nonempty_def.1 (set.ne_empty_iff_nonempty.1 H_not_empty),
    cases H_not_empty with x x_in_H,
    apply subset_antisymm H_sub_candidate,
    intros y y_in_candidate,
    rw set.mem_Inter at y_in_candidate,
    by_contra y_not_in_H,
    have normal_space := (@compact_metrizable.comp_met_is_normal _ _ _inst_1.compact_metrizable).normal,
    specialize normal_space H {y} H_inv_clos.is_closed is_closed_singleton (set.disjoint_singleton_right.2 y_not_in_H),
    rcases normal_space with ⟨ U, V, U_open, V_open, H_sub_U, y_in_V, separation ⟩,
    simp at y_in_V,
    have := (@topological_space.is_topological_basis.is_open_iff X _ V open_basis top_basis).1 V_open y y_in_V,
    rcases this with ⟨ W, ⟨W_in_basis, y_in_W, W_sub_V ⟩ ⟩,
    specialize surjective_enum ⟨ W, W_in_basis ⟩,
    cases surjective_enum with n h_n,
    specialize y_in_candidate (n+1),
    change y ∈ (if ((subset_seq n) ∩ G n).nonempty then ((subset_seq n) ∩ G n) else (subset_seq n)) at y_in_candidate,
    split_ifs at y_in_candidate,
    { replace y_in_candidate := set.mem_Inter.1 (set.mem_of_mem_inter_right y_in_candidate),
      specialize y_in_candidate 0,
      simp [h_n] at y_in_candidate,
      exact y_in_candidate y_in_W },
    { apply h,
      use x,
      simp [Inter_of_preorbit_of_clos, G],
      simp at H_sub_candidate,
      specialize H_sub_candidate n,
      use H_sub_candidate x_in_H,
      intro k,
      simp [h_n],
      apply set.not_mem_subset W_sub_V,
      apply set.disjoint_left.1 separation,
      apply H_sub_U,
      apply iter_of_inv_clos_in_inv_clos T H k,
      exact x_in_H } },
  { exact candidate_is_inv_clos },
end


lemma exists_minimal :
  nonempty X → ∃ (G : set X) (G_inv_clos : invariant_closed T G), G.nonempty ∧ minimal_on T G :=
begin
  introI nonempty_X,
  have := exists_minimal_in_inv_clos T set.univ,
  simp at this,
  simp,
  exact this,
end


/- Topologically transitive and topologically mixing systems.
  We begin with relative versions of these notions:
  topologically transitive or mixing invariant closed subsets. -/

def top_transitive_on (F : set X) :
  Prop :=
∀ (U V : set X), is_open U → is_open V → (U ∩ F).nonempty → (V ∩ F).nonempty
  → ∃ (n ≥ 1), (U ∩ (T^[n]⁻¹' V) ∩ F).nonempty


def top_mixing_on (F : set X) :
  Prop :=
∀ (U V : set X), is_open U → is_open V → (U ∩ F).nonempty → (V ∩ F).nonempty
  → ∃ (N : ℕ), ∀ (n ≥ N), (U ∩ (T^[n]⁻¹' V) ∩ F).nonempty


lemma top_mixing_on_is_top_transitive_on (F : set X) :
  top_mixing_on T F → top_transitive_on T F :=
begin
  intros XT_top_mixing U V U_open V_open U_nonempty V_nonempty,
  specialize XT_top_mixing U V U_open V_open U_nonempty V_nonempty,
  cases XT_top_mixing with N h_N,
  use N+1,
  specialize h_N (N+1),
  simp at h_N,
  simp [h_N],
end


lemma top_transitive_on_has_unbounded_hitting_times (F : set X) :
  top_transitive_on T F
  ↔ ∀ (U V : set X), is_open U → is_open V → (U ∩ F).nonempty → (V ∩ F).nonempty
  → ∀ (N : ℕ), ∃ (n ≥ N), (U ∩ (T^[n]⁻¹' V) ∩ F).nonempty :=
begin
  split,
  { intros XT_trans U V U_open V_open U_nonempty V_nonempty N,
    induction N,
    { specialize XT_trans U V U_open V_open U_nonempty V_nonempty,
      rcases XT_trans with ⟨ n, n_spos, nonempty_inter ⟩,
      use n,
      simp,
      exact nonempty_inter },
    { rcases N_ih with ⟨ n, n_ge_Nih, nonempty_inter ⟩,
      rw set.inter_assoc at nonempty_inter,
      specialize XT_trans U (T^[n]⁻¹' V)
        U_open (is_open.preimage (continuous.iterate _inst_1.continuous n) V_open)
        U_nonempty (set.nonempty.right nonempty_inter),
      rcases XT_trans with ⟨ k, k_spos, nonempty_new_inter ⟩,
      use (n+k),
      split,
      { rw ← (nat.add_one N_n),
        exact add_le_add n_ge_Nih k_spos },
      { rw [← set.preimage_comp, ← function.iterate_add T n k] at nonempty_new_inter,
      exact nonempty_new_inter } } },
  { intros XT_strong_trans U V U_open V_open U_nonempty V_nonempty,
    specialize XT_strong_trans U V U_open V_open U_nonempty V_nonempty 1,
    rcases XT_strong_trans with ⟨ N, N_spos, h_N ⟩,
    exact ⟨N, N_spos, h_N⟩ },
end


/- Now, the same definitions, but for the whole system (X, T). -/

def top_transitive :
  Prop :=
∀ (U V : set X), is_open U → is_open V → U.nonempty → V.nonempty
  → ∃ (n ≥ 1), (U ∩ (T^[n]⁻¹' V)).nonempty


def top_mixing :
  Prop :=
∀ (U V : set X), is_open U → is_open V → U.nonempty → V.nonempty
  → ∃ (N : ℕ), ∀ (n ≥ N), (U ∩ (T^[n]⁻¹' V)).nonempty


lemma top_transitive_iff_top_trans_on_univ :
  top_transitive T ↔ top_transitive_on T set.univ :=
by simp [top_transitive, top_transitive_on]


lemma top_mixing_iff_top_mixing_on_univ :
  top_mixing T ↔ top_mixing_on T set.univ :=
by simp [top_mixing, top_mixing_on]


lemma top_mixing_is_top_transitive :
  top_mixing T → top_transitive T :=
begin
  rw [top_transitive_iff_top_trans_on_univ T, top_mixing_iff_top_mixing_on_univ T],
  exact top_mixing_on_is_top_transitive_on T set.univ,
end


lemma top_transitive_has_unbounded_hitting_times :
  top_transitive T ↔ ∀ (U V : set X), is_open U → is_open V → U.nonempty → V.nonempty
  → ∀ (N : ℕ), ∃ (n ≥ N), (U ∩ (T^[n]⁻¹' V)).nonempty :=
begin
  rw top_transitive_iff_top_trans_on_univ T,
  have := top_transitive_on_has_unbounded_hitting_times T set.univ,
  simp at this,
  simp [this],
end


/- Orbit of a point x under T.
  Deviation from [K] : we define the orbit as starting from time 0, in accordance with common definitions
involving the action of (semi-)groups. We do not define trajectories.
  When we need orbits starting from time 1, we make them start from T x instead of x. -/

def orbit (x : X) :
  set X :=
{ y : X | ∃ (n : ℕ), y = (T^[n] x) }


lemma image_of_orbit_eq_orbit_of_image (x : X) (n : ℕ) :
  T^[n] '' (orbit T x) = orbit T (T^[n] x) :=
begin
  ext y,
  split,
  { intro h,
    rcases h with ⟨ z, ⟨ k, h_k ⟩, Tnz_eq_y ⟩,
    use k,
    rw [← function.iterate_add_apply, add_comm, function.iterate_add_apply, ← h_k, Tnz_eq_y] },
  { intro h,
    cases h with k Tnkx_eq_y,
    use [(T^[k] x), k],
    rw [← function.iterate_add_apply, add_comm, function.iterate_add_apply, Tnkx_eq_y] },
end


lemma orbit_is_inv (x : X) :
  (orbit T x) ⊆ T⁻¹' (orbit T x) :=
begin
  have this := image_of_orbit_eq_orbit_of_image T x 1,
  rw [function.iterate_one T] at this,
  apply @set.subset.trans X (orbit T x) _ (T⁻¹' (orbit T x)) (set.subset_preimage_image T (orbit T x)),
  rw this,
  apply set.preimage_mono,
  intros y y_in_orbit_x,
  cases y_in_orbit_x with n TnTx_eq_y,
  use n+1,
  simp [TnTx_eq_y],
end


lemma orbit_clos_is_inv_clos (x : X) :
  invariant_closed T (closure (orbit T x)) :=
{ is_closed := is_closed_closure,
  is_invariant :=
  begin
    have := (@closure_subset_preimage_closure_image X X _ _ T (orbit T x) _inst_1.continuous),
    apply @set.subset.trans _ _ _ (T⁻¹' (closure (orbit T x)) ) this,
    apply @set.preimage_mono X X T _ (closure (orbit T x)),
    apply closure_mono,
    apply (@set.image_subset_iff X X (orbit T x) (orbit T x) T).2,
    exact orbit_is_inv T x,
  end }


instance (x : X) : invariant_closed T (closure (orbit T x)) := orbit_clos_is_inv_clos T x


lemma orbit_clos_in_inv_clos (x : X) (F : set X) [invariant_closed T F] :
  x ∈ F → closure (orbit T x) ⊆ F :=
begin
  intro x_in_F,
  apply closure_minimal _ _inst_2.is_closed,
  intros y y_in_trajectory,
  cases y_in_trajectory with n Tnx_eq_y,
  rw Tnx_eq_y,
  apply iter_of_inv_clos_in_inv_clos T F n,
  exact x_in_F,
end


/- Dynamical relations and their inclusions. -/

def trajectory_relation :
  set (X × X) :=
{ xy : X × X | xy.2 ∈ orbit T (T xy.1) }


def recurrence_relation :
  set (X × X) :=
{ xy : X × X | xy.2 ∈ closure (orbit T (T xy.1)) }


def nonwandering_relation :
  set (X × X) :=
closure (trajectory_relation T)


def chain_relation :
  set (X × X) :=
{ xy : X × X | ∀ V ∈ 𝓤 X, ∃ (n ≥ 1) (u : ℕ → X),
(u 0) = xy.1 ∧ (u n) = xy.2 ∧ ∀ (k < n), (T (u k), u (k+1)) ∈ V }


/- These dynamical relations, as ordered above, are nondecreasing for the inclusion.
The proof for the first two is fairly straighforward. -/

lemma trajectory_sub_recurrence :
  trajectory_relation T ⊆ recurrence_relation T :=
λ _ h, subset_closure h

lemma recurrence_sub_nonwandering :
  recurrence_relation T ⊆ nonwandering_relation T :=
begin
  intros xy xy_recurr,
  apply mem_closure_iff.2,
  intros W W_open xy_in_W,
  have := is_open_prod_iff.1 W_open xy.1 xy.2,
  simp at this,
  specialize this xy_in_W,
  rcases this with ⟨ U, U_open, V, V_open, x_in_U, y_in_V, UV_in_W ⟩,
  have := mem_closure_iff.1 xy_recurr V V_open y_in_V,
  rcases this with ⟨ z, z_in_V, z_in_trajectory ⟩,
  use (xy.1, z),
  apply set.inter_subset_inter_left (trajectory_relation T) UV_in_W,
  exact ⟨ ⟨ x_in_U, z_in_V ⟩, z_in_trajectory ⟩,
end


/- The proof for the third inclusion is more painful, and uses the uniform continuity of T. -/

/- Récurrence sur le type des chaînes ? + changet la définition de façon adéquate (cloture transitive
de ce qui va bien)-/

lemma nonwandering_sub_chain_recurrent :
  nonwandering_relation T ⊆ chain_relation T :=
begin
  /- Start with a nonwandering pair (x, y) and a uniform neighborhood. Define suitables uniform neighborhoods. -/
  intros xy xy_nonwandering U U_in_UX,
  have := comp_open_symm_mem_uniformity_sets U_in_UX,
  rcases this with ⟨V, V_in_UX, ⟨ V_open, V_symm, VoV_sub_U ⟩ ⟩,
  have V_sub_U : V ⊆ U := set.subset.trans (subset_comp_self_of_mem_uniformity V_in_UX) VoV_sub_U,
  have uniform_continuous_T := uniform_continuous_transformation T,
  set W := V ∩ { α : X × X | (T α.1, T α.2) ∈ V } with W_def,
  have W_in_UX := filter.inter_mem (V_in_UX) (uniform_continuous_def.1 uniform_continuous_T V V_in_UX),
  rw ← W_def at W_in_UX,
  have W_sub_V : W ⊆ V := (set.inter_subset_left V { α : X × X | (T α.1, T α.2) ∈ V }),
  have W_open : is_open W :=
  begin
    apply is_open.inter V_open,
    apply @is_open.preimage (X × X) (X × X) _ _ (λ (α : X × X), (T α.1, T α.2)) _ V V_open,
    exact (continuous.prod_map _inst_1.continuous _inst_1.continuous),
  end,
  /- By closure, we can find a true piece of orbit z, T z, ..., T^[n+1] z = w in the smaller neighborhood. -/
  have key : (closure (trajectory_relation T) ∩ (uniform_space.ball xy.1 W) ×ˢ (uniform_space.ball xy.2 W)).nonempty :=
  begin
    use [xy, xy_nonwandering],
    simp,
    exact ⟨ uniform_space.mem_ball_self xy.1 W_in_UX, uniform_space.mem_ball_self xy.2 W_in_UX⟩,
  end,
  have close_orbit := (closure_inter_open (is_open.prod (uniform_space.is_open_ball xy.1 W_open) (uniform_space.is_open_ball xy.2 W_open))).1 key,
  rcases close_orbit with ⟨ zw, ⟨ w_in_orbit_z, zw_in_ball ⟩ ⟩,
  rw set.mem_prod_eq at zw_in_ball,
  clear key xy_nonwandering W_def uniform_continuous_T V_open V_in_UX W_open,
  cases w_in_orbit_z with n Tn1_z_eq_w,
  use n+1,
  simp,
  /- As a chain from To y, we use the sequence starting from x,
    taking value y at time n+1, and value T^[k] w in between. -/
  use (λ (k : ℕ), if k = 0 then xy.1 else if k < n+1 then T^[k] zw.1 else xy.2),
  simp,
  /- All is left is to wrap up the proof, i.e. to check that this is a suitable chain.
  Nothing surprising, but four distinct cases to work on separately:
  the cases (k = 0), (0 < k < n), (k = n), as well as an annoying edge case with (k = 0) and (n = 1). -/
  intros k k_le_n,
  simp [k_le_n],
  by_cases k_eq_zero : k = 0,
  { simp [k_eq_zero],
    by_cases n_eq_zero : n = 0,
    { simp [n_eq_zero],
      simp [n_eq_zero] at Tn1_z_eq_w,
      apply VoV_sub_U,
      change xy.2 ∈ uniform_space.ball (T xy.1) (comp_rel V V),
      apply @mem_ball_comp X V V (T xy.1) zw.2 xy.2,
      { rw Tn1_z_eq_w,
        exact zw_in_ball.1.2 },
      { rw mem_ball_symmetry V_symm,
        apply W_sub_V,
        exact zw_in_ball.2 } },
    { simp [nat.pos_of_ne_zero n_eq_zero],
      apply V_sub_U,
      change (xy.1, zw.1) ∈ { α : X × X | (T α.1, T α.2) ∈ V },
      apply set.inter_subset_right V _,
      exact zw_in_ball.1 } },
  { simp [k_eq_zero],
    by_cases k_eq_n : k = n,
    { simp [k_eq_n],
      rw [function.commute.self_iterate T n, ← Tn1_z_eq_w],
      apply V_sub_U,
      change xy.2 ∈ uniform_space.ball zw.2 V,
      rw mem_ball_symmetry V_symm,
      exact zw_in_ball.2.1 },
    { have : k < n := by { rw [nat.lt_succ_iff, le_iff_lt_or_eq, or_iff_not_imp_right] at k_le_n, exact k_le_n k_eq_n },
      simp [this],
      rw function.commute.self_iterate T k,
      exact refl_mem_uniformity U_in_UX } },
end


/- Characterization of minimality in terms of dense orbits and recurrence relation;
characterization of topological transitivity in terms of nonwandering relation. -/

lemma minimal_on_iff_dense_orbits_in (F : set X) [invariant_closed T F] :
  minimal_on T F ↔ ∀ (x : X), x ∈ F → closure (orbit T x) = F :=
begin
  split,
  { intros XT_minimal x x_in_F,
    specialize XT_minimal (closure (orbit T x)) (orbit_clos_in_inv_clos T x F x_in_F),
    cases XT_minimal with orbit_empty orbit_full,
    { exfalso,
      replace orbit_empty := (closure_empty_iff (orbit T x)).1 orbit_empty,
      rw [← (set.mem_empty_eq (T x)), ← orbit_empty ],
      use 1,
      simp },
    { exact orbit_full } },
  { introsI dense_orbits G G_inv_clos G_sub_F,
    apply or_iff_not_imp_left.2,
    intro G_not_empty,
    replace G_not_empty := set.nonempty_def.1 (set.ne_empty_iff_nonempty.1 G_not_empty),
    cases G_not_empty with x x_in_G,
    specialize dense_orbits x (G_sub_F x_in_G),
    have key := orbit_clos_in_inv_clos T x G x_in_G,
    rw dense_orbits at key,
    exact set.subset.antisymm G_sub_F key },
end


lemma minimal_iff_dense_orbits :
  minimal T ↔ ∀ (x : X), closure (orbit T x) = set.univ :=
begin
  rw [minimal_iff_minimal_on_univ T, minimal_on_iff_dense_orbits_in T set.univ],
  simp,
end


lemma minimal_on_iff_square_in_recurrent (F : set X) [invariant_closed T F] :
  minimal_on T F ↔ F ×ˢ F ⊆ recurrence_relation T :=
begin
  split,
  { intros F_minimal xy,
    simp [recurrence_relation],
    intros x_in_F y_in_F,
    specialize F_minimal (closure (orbit T (T xy.1))) (orbit_clos_in_inv_clos T (T xy.1) F (inv_def T F xy.1 x_in_F)),
    cases F_minimal with trajectory_empty trajectory_full,
    { exfalso,
      rw [← set.mem_empty_eq (T xy.1), ← trajectory_empty],
      apply subset_closure,
      use 0,
      simp },
    { rw trajectory_full,
      exact y_in_F } },
  { introsI rec_FxF G G_inv_clos G_sub_F,
    rw or_iff_not_imp_left,
    intro G_nonempty,
    replace G_nonempty := set.nonempty_def.1 (set.ne_empty_iff_nonempty.1 G_nonempty),
    cases G_nonempty with x x_in_G,
    apply set.subset.antisymm G_sub_F,
    intros y y_in_F,
    specialize rec_FxF (set.mk_mem_prod (G_sub_F x_in_G) y_in_F),
    simp [recurrence_relation] at rec_FxF,
    exact orbit_clos_in_inv_clos T (T x) G (inv_def T G x x_in_G) rec_FxF },
end


lemma minimal_iff_recurrent_full :
  minimal T ↔ recurrence_relation T = set.univ :=
begin
  rw [minimal_iff_minimal_on_univ T, minimal_on_iff_square_in_recurrent T set.univ],
  simp,
  rw set.univ_subset_iff,
end


/- The reciprocal of `transitive_if_exists_dense_trajectory` is true if `X` is nonempty.
However, the proof relies on Baire theory, and at the moment the implementation of the Baire theorems
are not suitable for this setting; they assume the existence of a pseudo_emetric structure,
which is stronger that the uniform_space structure we have at our disposal and for which we have no instance. -/

/- The simpler statement `(∃ (x : X), closure (orbit T x)= set.univ) → top_transitive T` holds
if `X` is additionally a perfect space. -/

lemma transitive_if_exists_dense_trajectory :
  (∃ (x : X), closure (orbit T (T x)) = set.univ) → top_transitive T :=
begin
  intro point_with_dense_orbit,
  cases point_with_dense_orbit with x x_dense_orbit,
  intros U V U_open V_open U_nonempty V_nonempty,
  /- We want to check that the system can go from U to V, and by density we have and orbit intersecting both U and V. -/
  have : (orbit T (T x) ∩ U).nonempty := by { apply (closure_inter_open U_open).1, rw x_dense_orbit, simp [U_nonempty] },
  rcases this with ⟨ y, ⟨ ⟨ m, Tm1_x_eq_y ⟩, y_in_U ⟩ ⟩,
  have : (orbit T (T x) ∩ V).nonempty := by { apply (closure_inter_open V_open).1, rw x_dense_orbit, simp [V_nonempty] },
  rcases this with ⟨ z, ⟨ ⟨ n, Tn1_x_eq_z ⟩, z_in_V ⟩ ⟩,
  clear U_nonempty V_nonempty U_open,
  by_cases m_lt_n : m < n,
  /- If the orbit intersects U before V, there is little to do. -/
  { rcases (exists_pos_add_of_lt m_lt_n) with ⟨ k, k_spos, h_k ⟩,
    use [k, k_spos, y, y_in_U],
    rw Tm1_x_eq_y,
    simp,
    rw [← function.iterate_add_apply, add_comm, h_k, ← Tn1_x_eq_z],
    exact z_in_V },
  /- Otherwise, the situation is more complex. We can go from V to U, and no we have to construct, somehow, a path from U to V. -/
  { rw not_lt at m_lt_n,
    by_cases x_periodic : x ∈ orbit T (T x),
    /- If x is periodic, by density the whole system is actually a single periodic orbit, so we can go from any point to any other.
    The congruences to work it out explicitely are more irritating than they have any right to be. -/
    { cases x_periodic with k Tk1x_eq_x,
      rw le_iff_exists_add at m_lt_n,
      cases m_lt_n with r h_r,
      let N := n + (k+1)*(r+1),
      use (k*r + k + 1),
      simp,
      have lock : (T^[N] (T x) = z) :=
      begin
        simp [N],
        rw [← function.iterate_succ_apply, nat.succ_eq_add_one k, eq_comm] at Tk1x_eq_x,
        calc T^[n + (k + 1) * (r + 1)] (T x)
              = (T^[n]) (T^[(k + 1) * (r + 1)] (T x)) : by rw function.iterate_add_apply
          ... = (T^[n]) (T (T^[(k + 1) * (r + 1)] x)) : by rw function.commute.iterate_self
          ... = (T^[n]) (T (T^[(k + 1)]^[(r + 1)] x)) : by rw function.iterate_mul
          ... = (T^[n]) (T x)                         : by rw function.iterate_fixed Tk1x_eq_x (r+1)
          ... = z                                     : by rw Tn1_x_eq_z,
      end,
      use [y, y_in_U],
      rw [Tm1_x_eq_y, set.mem_preimage, ← function.iterate_succ T (k*r+k), ← function.iterate_add_apply, ← nat.add_one, h_r],
      simp [N] at lock,
      have key : n + (k + 1) * (r + 1) = k * r + k + 1 + (n + r) := by linarith,
      rw [← key, lock],
      exact z_in_V },
    /- If x is not periodic, since x is in the closure of its orbit, the system must go back infinitely many times
    close to x (this is where it is important to start the orbit at T x !), in particular after having visited V,
    and from there we can travel forward to U.
      This is formalized by defining an explicit open neighborhood W of x which is suitable for this construction
    (it is mapped into V, and not visited before U). By density, we can find a point in the orbit of x which is in W,
    i.e. visited after U and before V. -/
    { let W := (T^[n+1])⁻¹' V ∩ (⋂ (k ∈ set.Icc 1 (m+1)), {T^[k] x}ᶜ),
      have W_open : is_open W :=
      begin
        apply is_open.inter,
        { exact is_open.preimage (continuous.iterate _inst_1.continuous (n+1)) V_open },
        { apply is_open_bInter (set.finite.intro (set.fintype_Icc 1 (m+1))),
          intros k h_k,
          rw is_open_compl_iff,
          apply is_closed_singleton },
      end,
      have W_nonempty : W.nonempty :=
      begin
        use x,
        split,
        { simp,
          rw ← Tn1_x_eq_z,
          exact z_in_V },
        { simp,
          intros k k_spos k_lt_m Tk_x_eq_x,
          apply x_periodic,
          use k.pred,
          rw [← function.iterate_succ_apply, nat.succ_pred_eq_of_pos k_spos, ← Tk_x_eq_x] },
      end,
      have : (orbit T (T x) ∩ W).nonempty := by { apply (closure_inter_open W_open).1, rw x_dense_orbit, simp [W_nonempty] },
      rcases this with ⟨ w, ⟨ ⟨ r, Tr1_x_eq_w ⟩, w_in_W ⟩ ⟩,
      have r_lt_n : r > m :=
      begin
        by_contra,
        simp at h,
        replace w_in_W := w_in_W.2,
        simp at w_in_W,
        specialize w_in_W (r+1),
        simp [h] at w_in_W,
        exact w_in_W Tr1_x_eq_w,
      end,
      rcases (exists_pos_add_of_lt r_lt_n) with ⟨ k, k_spos, h_k ⟩,
      have kn_ge_1 : k+n+1 ≥ 1 := by linarith,
      use [k+n+1, kn_ge_1, y, y_in_U],
      rw Tm1_x_eq_y,
      simp,
      apply set.mem_of_eq_of_mem _ (set.mem_preimage.1 w_in_W.1),
      calc T^[k+n] (T (T^[m] (T x)))
            = T (T^[k+n] (T^[m] (T x))) : by rw function.commute.iterate_self T (k+n)
        ... = T (T^[k+n+m] (T x))       : by rw ← function.iterate_add_apply T (k+n) m (T x)
        ... = T (T^[m+(k+n)] (T x))     : by rw add_comm (k+n) m
        ... = T (T^[m+k+n] (T x))       : by rw ← add_assoc m k n
        ... = T (T^[r+n] (T x))         : by rw h_k
        ... = T (T^[n+r] (T x))         : by rw add_comm r n
        ... = T (T^[n] (T^[r] (T x)))   : by rw function.iterate_add_apply T n r (T x)
        ... = T (T^[n] w)               : by rw ← Tr1_x_eq_w
        ... = (T^[n.succ]) w            : by rw ← function.iterate_succ_apply' T n w
        ... = (T^[n+1]) w               : by rw ← nat.add_one n } },
end

/- Peut etre tourné autrement : top trans ssi l'ensemble des points dont l'orbite est tout
est un Gdelta-dense. D'où densité, et non vite ssi X est non vide ; existe x -> l'ensemble
des x est un Gdelta-dense, etc.-/

lemma nonempty_transitive_iff_exists_dense_trajectory :
  nonempty X → ( top_transitive T ↔ (∃ (x : X), closure (orbit T (T x)) = set.univ)  ) :=
begin
  intro X_nonempty,
  split, swap, exact transitive_if_exists_dense_trajectory T,
  intro XT_top_trans,
  have countable_basis := @topological_space.exists_countable_basis X _ _inst_1.compact_metrizable.second_countable,
  rcases countable_basis with ⟨ open_basis, ⟨ countable_basis, no_nonempty_open, top_basis ⟩ ⟩,
  haveI nonempty_basis : open_basis.nonempty := by { apply set.nonempty.of_sUnion, rw top_basis.sUnion_eq, exact set.nonempty_iff_univ_nonempty.1 X_nonempty },
  have basis_enum_is_open : ∀ V ∈ open_basis, is_open V :=
  begin
    intro V,
    apply topological_space.is_topological_basis.is_open top_basis,
  end,
  have basis_enum_is_nonempty : ∀ (V : set X), V ∈ open_basis → V.nonempty :=
  begin
    intros V h,
    by_contra h',
    rw set.not_nonempty_iff_eq_empty at h',
    rw ← h' at no_nonempty_open,
    exact no_nonempty_open h,
  end,
  let open_seq := λ (V : set X), ⋃ (n : ℕ) (n_spos : n > 0), (T^[n])⁻¹' V,
  have open_seq_is_open : ∀ (V : set X), V ∈ open_basis → is_open (open_seq V) :=
  begin
    intros V h,
    apply is_open_Union,
    intro n,
    apply is_open_Union,
    intro n_spos,
    exact is_open.preimage (continuous.iterate _inst_1.continuous n) (basis_enum_is_open V h),
  end,
  have open_seq_is_dense : ∀ (V : set X), V ∈ open_basis → dense (open_seq V) :=
  begin
    intros V h,
    rw dense_iff_inter_open,
    intros U U_open U_nonempty,
    specialize XT_top_trans U V U_open (basis_enum_is_open V h) U_nonempty (basis_enum_is_nonempty V h),
    rcases XT_top_trans with ⟨n, n_spos, ⟨x, h_x⟩⟩,
    use [x, h_x.1],
    simp,
    use [n, n_spos, h_x.2],
  end,
  have key := @dense_bInter_of_open X (set X) _ _ open_basis open_seq open_seq_is_open countable_basis open_seq_is_dense,
  rw dense_iff_inter_open at key,
  specialize key set.univ is_open_univ (set.nonempty_iff_univ_nonempty.1 X_nonempty),
  simp at key,
  cases key with x h_x,
  use x,
  rw [← dense_iff_closure_eq, topological_space.is_topological_basis.dense_iff top_basis],
  intros U U_open_basis U_nonempty,
  specialize h_x U U_open_basis,
  rcases h_x with ⟨n, n_spos, Tnx_in_U⟩,
  use [T^[n] x, Tnx_in_U, n.pred],
  rw [← function.iterate_succ_apply T n.pred x, nat.succ_pred_eq_of_pos n_spos],
end



lemma transitive_iff_nonwandering_full :
  top_transitive T ↔ nonwandering_relation T = set.univ :=
begin
  split,
  { intro XT_top_trans,
    apply set.eq_univ_iff_forall.2,
    intro xy,
    simp [nonwandering_relation],
    apply mem_closure_iff.2,
    intros W W_open xy_in_W,
    have := is_open_prod_iff.1 W_open xy.1 xy.2,
    simp at this,
    specialize this xy_in_W,
    rcases this with ⟨ U, U_open, V, V_open, x_in_U, y_in_V, UV_in_W ⟩,
    apply set.nonempty_def.2,
    specialize XT_top_trans U V U_open V_open (set.nonempty_of_mem x_in_U) (set.nonempty_of_mem y_in_V),
    rcases XT_top_trans with ⟨ n, n_spos, h_n ⟩,
    replace h_n := set.nonempty_def.1 h_n,
    cases h_n with z h_z,
    use (z, T^[n] z),
    split,
    { apply UV_in_W,
      exact h_z },
    { use n.pred,
      simp,
      rw [← function.iterate_succ_apply, nat.succ_pred_eq_of_pos n_spos] } },
  { intro nonwandering_full,
    simp [nonwandering_relation] at nonwandering_full,
    intros U V U_open V_open U_nonempty V_nonempty,
    have UV_open := by { apply is_open_prod_iff'.2, left, exact ⟨ U_open, V_open ⟩ },
    have key := (closure_inter_open UV_open).1,
    rw [nonwandering_full, set.univ_inter] at key,
    specialize key (set.nonempty.prod U_nonempty V_nonempty),
    rcases key with ⟨ xy, ⟨ n, h_n ⟩, xy_in_UV ⟩,
    use n+1,
    simp [set.nonempty_def],
    use [xy.1, xy_in_UV.1],
    rw ← h_n,
    exact xy_in_UV.2 },
end


lemma minimal_is_top_transitive :
  minimal T → top_transitive T :=
begin
  rw [minimal_iff_recurrent_full T, transitive_iff_nonwandering_full T],
  intro XT_minimal,
  rw [ ← set.univ_subset_iff, ← XT_minimal],
  exact recurrence_sub_nonwandering T,
end


/- Since minimality is equivalent to a full recurrence relation, and topological transitivity to
a full nonwandering relation, we introduce a third notion -- chain transitivity -- corresponding
to a full chain relation. -/

def chain_transitive : Prop := chain_relation T = set.univ


lemma top_transitive_is_chain_transitive :
  top_transitive T → chain_transitive T :=
begin
  unfold chain_transitive,
  rw transitive_iff_nonwandering_full T,
  intro XT_top_trans,
  rw [ ← set.univ_subset_iff, ← XT_top_trans],
  exact nonwandering_sub_chain_recurrent T,
end


lemma chain_transitive_is_surjective :
  chain_transitive T → function.surjective T :=
begin
  contrapose,
  unfold chain_transitive chain_relation,
  push_neg,
  intro T_not_surj,
  cases T_not_surj with x x_not_in_image,
  rw set.ne_univ_iff_exists_not_mem,
  use (x, x),
  simp,
  let U := (T '' set.univ)ᶜ,
  have x_in_U : x ∈ U := by { simp [x_not_in_image] },
  have U_open : is_open U := by { rw is_open_compl_iff, apply is_compact.is_closed (is_compact.image _ _inst_1.continuous), apply is_compact_univ_iff.2, apply_instance },
  rw is_open_iff_ball_subset at U_open,
  specialize U_open x x_in_U,
  rcases U_open with ⟨ V, V_in_UX, V_ball_in_U ⟩,
  have := comp_open_symm_mem_uniformity_sets V_in_UX,
  rcases this with ⟨ W, W_in_UX, ⟨ W_open, W_symm, W_sub_V ⟩ ⟩,
  replace W_sub_V := set.subset.trans (subset_comp_self_of_mem_uniformity W_in_UX) W_sub_V,
  use [W, W_in_UX],
  intros n n_spos u u0_eq_x un_eq_x,
  use [n-1, (nat.sub_lt_of_pos_le 1 n) nat.zero_lt_one n_spos],
  rw [nat.sub_add_cancel n_spos, un_eq_x],
  change x ∉ uniform_space.ball (T (u (n - 1))) W,
  rw [mem_ball_symmetry W_symm],
  apply set.not_mem_subset (ball_mono W_sub_V x),
  apply set.not_mem_subset V_ball_in_U,
  simp [U],
end


/- Diagonals of the 4 relations. This give 4 properties of points in (X, T).
We add convenient characterizations of periodicity and recurrence, as well as two
properties -- quasi-periodicity and almost-periodicity -- which lie between
periodicity and recurrence. These are essentially quantitative versions of recurrence. -/

def is_periodic (x : X) :
  Prop :=
(x, x) ∈ trajectory_relation T


def is_recurrent (x : X) :
  Prop :=
(x, x) ∈ recurrence_relation T


def is_nonwandering (x : X) :
  Prop :=
(x, x) ∈ nonwandering_relation T


def is_chain_recurrent (x : X) :
  Prop :=
(x, x) ∈ chain_relation T


lemma is_periodic_iff (x : X) :
  is_periodic T x ↔ ∃ (n ≥ 1), x = (T^[n] x) :=
begin
  split,
  { intros x_is_periodic,
    cases x_is_periodic with n h_n,
    use n+1,
    simp,
    simp at h_n,
    exact h_n },
  { intro h_n,
    rcases h_n with ⟨ n, n_spos, Tnx_eq_x ⟩,
    use n.pred,
    simp,
    rw [<- function.iterate_succ_apply, nat.succ_pred_eq_of_pos n_spos],
    exact Tnx_eq_x },
end


lemma is_recurrent_iff (x : X) :
  is_recurrent T x ↔ ( ∀ (U : set X), is_open U → x ∈ U → ∃ (n ≥ 1), T^[n] x ∈ U ) :=
begin
  simp [is_recurrent, recurrence_relation],
  split,
  { intros h_x U U_open x_in_U,
    have := mem_closure_iff.1 h_x U U_open x_in_U,
    rcases this with ⟨ y, y_in_U, n, h_n ⟩,
    use n+1,
    simp,
    rw ← h_n,
    exact y_in_U },
  { intro h_x,
    apply mem_closure_iff.2,
    intros U U_open x_in_U,
    specialize h_x U U_open x_in_U,
    rcases h_x with ⟨ n, n_spos, Tn_x_in_U ⟩,
    use [(T^[n] x), Tn_x_in_U, n.pred],
    rw [← function.iterate_succ_apply, nat.succ_pred_eq_of_pos n_spos] },
end


def is_quasi_periodic (x : X) :
  Prop :=
∀ (U : set X), is_open U → x ∈ U → ∃ (p ≥ 1), ∀ (n : ℕ), T^[n*p] x ∈ U


def is_almost_periodic (x : X) :
  Prop :=
∀ (U : set X), is_open U → x ∈ U → ∃ (p ≥ 1), ∀ (n : ℕ), ∃ (k < p), T^[n+k] x ∈ U


lemma periodic_is_quasi_periodic (x : X) :
  is_periodic T x → is_quasi_periodic T x :=
begin
  intros x_periodic U U_open x_in_U,
  cases x_periodic with n h_n,
  use n+1,
  simp at h_n,
  rw [← function.iterate_succ_apply, ← nat.add_one, eq_comm] at h_n,
  simp,
  intro m,
  rw [ mul_comm, function.iterate_mul T (n+1) m, function.iterate_fixed h_n m],
  exact x_in_U,
end


lemma quasi_periodic_is_almost_periodic (x : X) :
  is_quasi_periodic T x → is_almost_periodic T x :=
begin
  intros x_quasi_periodic U U_open x_in_U,
  specialize x_quasi_periodic U U_open x_in_U,
  rcases x_quasi_periodic with ⟨ p, p_spos, h_p ⟩,
  use [p, p_spos],
  intro n,
  have this : n ≤ p * n := by { apply le_mul_of_one_le_left (zero_le n) p_spos },
  replace this := nat.exists_eq_add_of_le this,
  cases this with k h_k,
  use (k % p),
  split,
  { apply nat.mod_lt,
    exact p_spos },
  { have key := nat.mod_add_div (n + k % p) p,
    have : (n + k % p) % p = 0 := by { rw [nat.add_mod_mod, ← h_k], exact nat.mul_mod_right p n },
    simp [this] at key,
    rw ← key,
    specialize h_p ((n + k % p) / p),
    rw mul_comm,
    exact h_p },
end


lemma almost_periodic_is_recurrent (x : X) :
  is_almost_periodic T x → is_recurrent T x :=
begin
  intro x_almost_periodic,
  apply (is_recurrent_iff T x).2,
  intros U U_open x_in_U,
  specialize x_almost_periodic U U_open x_in_U,
  rcases x_almost_periodic with ⟨ p, p_spos, h_p ⟩,
  specialize h_p 1,
  rcases h_p with ⟨ k, k_sle_n, h_k ⟩,
  use 1+k,
  simp [h_k],
end


lemma recurrent_is_nonwandering (x : X) :
  is_recurrent T x → is_nonwandering T x :=
by { intro x_recurrent, exact (recurrence_sub_nonwandering T) x_recurrent }


lemma nonwandering_is_chain_recurrent (x : X) :
  is_nonwandering T x → is_chain_recurrent T x :=
by { intro x_nonwandering, exact (nonwandering_sub_chain_recurrent T) x_nonwandering }





/- Birkhoff's theorem -/
/- G.D. Birkhoff, Quelques théorèmes sur les mouvements des systèmes dynamiques,
Bulletin de la Société Mathématique de France, no. 40 (1912), pp. 305--312-/

/- We correct a mistake into the statement found in [K, Theorem 2.19].
  The reference claims that x is almost periodic if and only if the closure of the orbit of T x is minimal.
However, x needs not belong to the orbit of T x, nor to its closure. As a consequence, considerations
on the closure of the orbit of T x alone cannot give any information on the recurrence to x.
Counter-examples are easy to construct; find an almost periodic point, and add an isolated point sent
to this almost periodic point.
  We fix this mistake by starting the orbit from x instead. -/

theorem minimal_iff_almost_periodic (x : X) :
  is_almost_periodic T x ↔ minimal_on T (closure (orbit T x)) :=
begin
  split,
  { introsI x_almost_periodic F F_inv_clos F_sub_closure,
    by_cases h : x ∈ F,
    { exact or.inr (set.subset.antisymm F_sub_closure (orbit_clos_in_inv_clos T x F h)) },
    { left,
      have normal_space := (@compact_metrizable.comp_met_is_normal _ _ _inst_1.compact_metrizable).normal,
      specialize normal_space F {x} F_inv_clos.is_closed is_closed_singleton (set.disjoint_singleton_right.2 h),
      rcases normal_space with ⟨ U, V, U_open, V_open, F_sub_U, x_in_V, separation ⟩,
      simp at x_in_V,
      specialize x_almost_periodic V V_open x_in_V,
      rcases x_almost_periodic with ⟨ p, p_spos, bounded_recurr ⟩,
      clear V_open x_in_V h,
      let W := ⋃ (k ∈ set.Ico 0 p), (T^[k])⁻¹' (closure V),
      have W_closed : is_closed W :=
      begin
        apply is_closed_bUnion (set.finite.intro (set.fintype_Ico 0 p)),
        intros k h_k,
        exact is_closed.preimage (continuous.iterate _inst_1.continuous k) is_closed_closure,
      end,
      have F_disj_W : F ⊆ Wᶜ :=
      begin
        intros y y_in_F,
        simp [W],
        intros k k_sle_p,
        rw ← set.disjoint_singleton_left,
        apply @set.disjoint_of_subset_left X {T^[k] y} (closure V) U _ (disjoint.closure_right separation U_open),
        simp,
        apply F_sub_U,
        apply orbit_clos_in_inv_clos T y F y_in_F,
        apply subset_closure,
        use k,
      end,
      clear F_inv_clos separation U_open F_sub_U U,
      have F_sub_W : F ⊆ W :=
      begin
        refine set.subset.trans F_sub_closure _,
        rw is_closed.closure_subset_iff W_closed,
        intros y y_in_orbit,
        cases y_in_orbit with n Tnx_eq_y,
        specialize bounded_recurr n,
        rcases bounded_recurr with ⟨ k, k_sle_p, h_k ⟩,
        simp [W],
        use [k, k_sle_p],
        apply subset_closure,
        rw [Tnx_eq_y, ← function.iterate_add_apply T k n x, add_comm],
        exact h_k,
      end,
      apply set.eq_empty_of_subset_empty,
      rw ← set.compl_inter_self W,
      exact set.subset_inter F_disj_W F_sub_W } },
  { intros minimal_orbit U U_open x_in_U,
    let subset_sequence := λ (n : ℕ), (T^[n])⁻¹' U,
    have x_in_orbit_clos : x ∈ closure (orbit T x) := by { apply subset_closure, use 0, simp },
    have compact_orbit_clos : is_compact (closure (orbit T x)) := is_closed.is_compact is_closed_closure,
    have open_sequence : ∀ (n : ℕ), is_open ((T^[n])⁻¹' U) := by { intro n, exact (is_open.preimage (continuous.iterate _inst_1.continuous n) U_open) },
    have cover_sequence : (closure (orbit T x)) ⊆ ⋃ (n : ℕ), subset_sequence n :=
    begin
      intros y y_in_orbit_clos,
      simp,
      have same_clos := (minimal_on_iff_dense_orbits_in T (closure (orbit T x))).1 minimal_orbit y y_in_orbit_clos,
      have this := x_in_orbit_clos,
      rw [← same_clos, mem_closure_iff] at this,
      specialize this U U_open x_in_U,
      rcases this with ⟨ z, z_in_U, ⟨ n, Tny_eq_z ⟩ ⟩,
      use n,
      rw ← Tny_eq_z,
      exact z_in_U,
    end,
    replace compact_orbit_clos := is_compact.elim_finite_subcover compact_orbit_clos subset_sequence open_sequence cover_sequence,
    clear minimal_orbit open_sequence cover_sequence x_in_U U_open,
    cases compact_orbit_clos with I I_covers,
    have I_nonempty : I.nonempty :=
    begin
      have this := set.nonempty_of_mem (I_covers x_in_orbit_clos),
      simp at this,
      rcases this with ⟨ i, i_in_I, h_i ⟩,
      use [i, i_in_I],
    end,
    use (finset.max' I I_nonempty).succ,
    split,
    { simp [@nat.one_le_of_lt 0 _] },
    { intro n,
      have Tnx_in_orbit_clos : (T^[n] x) ∈ closure (orbit T x) := by { apply subset_closure, use n },
      replace I_covers := I_covers Tnx_in_orbit_clos,
      simp at I_covers,
      rcases I_covers with ⟨ k, k_in_I, h_k ⟩,
      use [k, nat.lt_succ_of_le (finset.le_max' I k k_in_I)],
      rw [add_comm, function.iterate_add_apply],
      exact h_k } },
end


/- Since we already have the existence of minimal subsets, we get the existence of almost periodic points,
and a fortiori recurrent points. -/

lemma exists_almost_periodic_in_inv_clos (F : set X) [invariant_closed T F] :
  F.nonempty → ∃ x ∈ F, is_almost_periodic T x :=
begin
  intro F_nonempty,
  replace F_nonempty := exists_minimal_in_inv_clos T F F_nonempty,
  rcases F_nonempty with ⟨ G, G_sub_F, G_inv_clos, ⟨ ⟨ x, x_in_G ⟩, G_minimal ⟩ ⟩,
  resetI,
  use [x, G_sub_F x_in_G],
  apply (minimal_iff_almost_periodic T x).2,
  introsI H H_inv_clos,
  have G_is_orbit_clos := (minimal_on_iff_dense_orbits_in T G).1 G_minimal x x_in_G,
  rw G_is_orbit_clos,
  specialize G_minimal H,
  exact G_minimal,
end


lemma exists_recurrent_in_inv_clos (F : set X) [invariant_closed T F] :
  F.nonempty → ∃ x ∈ F, is_recurrent T x :=
begin
  intro F_nonempty,
  replace F_nonempty := exists_almost_periodic_in_inv_clos T F F_nonempty,
  rcases F_nonempty with ⟨ x, x_in_F, x_almost_periodic ⟩,
  use [x, x_in_F],
  exact almost_periodic_is_recurrent T x x_almost_periodic,
end


lemma exists_almost_periodic :
  nonempty X → ∃ (x : X), is_almost_periodic T x :=
begin
  introI nonempty_X,
  have := exists_almost_periodic_in_inv_clos T set.univ,
  simp at this,
  simp [this],
end


lemma exists_recurrent :
  nonempty X → ∃ (x : X), is_recurrent T x :=
begin
  introI nonempty_X,
  have := exists_recurrent_in_inv_clos T set.univ,
  simp at this,
  simp [this],
end


/- Below lurk shadows -/

def shadowing_property :
  Prop :=
∀ (V ∈ 𝓤 X), ∃ (W ∈ 𝓤 X), ∀ (n : ℕ) (u : ℕ → X),
  (∀ k < n, (T (u k), u (k+1)) ∈ W) → ∃ (x : X), ∀ k ≤ n, (T^[k] x, u k) ∈ V


lemma shadowing_implies_nonwandering_eq_chain_recurrent :
  shadowing_property T → nonwandering_relation T = chain_relation T :=
begin
  intro XT_shadowing,
  apply set.eq_of_subset_of_subset (nonwandering_sub_chain_recurrent T),
  intros xy x_chain_y,
  unfold chain_relation at x_chain_y,
  simp [nonwandering_relation],
  rw mem_closure_iff,
  intros U U_open xy_in_U,
  have : (xy.1, xy.2) ∈ U := by simp [xy_in_U],
  rw is_open_prod_iff at U_open,
  specialize U_open xy.1 xy.2 this,
  clear this,
  rcases U_open with ⟨ V, W, V_open, W_open, x_in_V, y_in_W, VxW_in_U ⟩,
  replace V_open := is_open.mem_nhds V_open x_in_V,
  rw uniform_space.mem_nhds_iff_symm at V_open,
  rcases V_open with ⟨ V', V'_uniform, V'_symm, BV'_in_V ⟩,
  replace W_open := is_open.mem_nhds W_open y_in_W,
  rw uniform_space.mem_nhds_iff_symm at W_open,
  rcases W_open with ⟨ W', W'_uniform, W'_symm, BW'_in_W ⟩,
  specialize XT_shadowing (V'∩ W') ((uniformity X).inter_sets V'_uniform W'_uniform),
  rcases XT_shadowing with ⟨ Z, Z_uniform, XT_shadowing ⟩,
  specialize x_chain_y Z Z_uniform,
  rcases x_chain_y with ⟨ n, n_spos, u, u0_eq_x, un_eq_y, chain_property ⟩,
  /- The magic is here. Beware if you mess with the definitions of chain relation or shadowing property. -/
  specialize XT_shadowing n u chain_property,
  cases XT_shadowing with x x_shadows_u,
  use (x, T^[n] x),
  split,
  { apply VxW_in_U,
    simp,
    split,
    { apply BV'_in_V,
      rw mem_ball_symmetry V'_symm,
      specialize x_shadows_u 0,
      simp [n_spos] at x_shadows_u,
      rw u0_eq_x at x_shadows_u,
      exact x_shadows_u.1 },
    { apply BW'_in_W,
      rw mem_ball_symmetry W'_symm,
      specialize x_shadows_u n,
      simp [n_spos] at x_shadows_u,
      rw un_eq_y at x_shadows_u,
      exact x_shadows_u.2 } },
  { simp [trajectory_relation],
    use n-1,
    rw [← function.iterate_succ_apply T (n-1) x, nat.succ_eq_add_one (n-1), nat.sub_add_cancel n_spos] },
end


lemma shadowing_and_chain_trans_implies_top_trans :
  shadowing_property T → chain_transitive T → top_transitive T :=
begin
  intros XT_shadowing XT_chain_trans,
  rw [transitive_iff_nonwandering_full T, shadowing_implies_nonwandering_eq_chain_recurrent T XT_shadowing],
  exact XT_chain_trans,
end



#lint

end topological_dynamics_basic
