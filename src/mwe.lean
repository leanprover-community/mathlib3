import topology.separation
open set

local attribute [instance] classical.prop_decidable

universes u
variables {α : Type u} [topological_space α]


lemma finset.induction_disjoint_point {α : Type*} {P : α → finset α → Prop} {x : α}
  (h : P x ∅) (hrec : ∀ y s, x ≠ y → P x s → P x (insert y s)) : ∀ s, x ∉ s → P x s :=
begin
  refine λ s, finset.induction_on s (λ _, h) (λ a t ta iP xat, _),
  apply hrec _ _ (by { rintro rfl, exact xat (finset.mem_insert_self _ t) }) (iP (λ _, _)),
  exact xat (finset.mem_insert_of_mem _x),
end

lemma finset.induction_disjoint {α : Type*} {P : finset α → finset α → Prop} {s : finset α}
  (h : P s ∅) (hrec : ∀ x t, x ∉ s → P s t → P s (insert x t)) : ∀ t, disjoint s t → P s t :=
begin
  refine λ t, finset.induction_on t (λ _, h) _,
  refine λ a u au hP sau, hrec a u (finset.disjoint_insert_right.mp sau).1 (hP _),
  exact finset.disjoint_of_subset_right (finset.subset_insert a u) sau,
end

lemma t2_separation_point_finset [t2_space α] {s : finset α} {x : α} (h : x ∉ s) :
  ∃ U V : set α, is_open U ∧ is_open V ∧ ↑s ⊆ U ∧ x ∈ V ∧ U ∩ V = ∅ :=
begin
  revert s,
  refine finset.induction_disjoint_point _ (λ y s xy, _),
  { exact ⟨_, _, is_open_empty, is_open_univ, by refl, mem_univ x, inter_univ _⟩ },
  { rintros ⟨U, V, oU, oV, aU, bV, UV⟩,
    obtain ⟨Uy, Vx, oUy, oVx, aUy, bVx, UyVx⟩ := t2_separation xy.symm,
    refine ⟨U ∪ Uy, V ∩ Vx, is_open_union oU oUy, is_open_inter oV oVx, _, ⟨bV, bVx⟩, _⟩,
    { rw [coe_insert, ← union_singleton, union_subset_iff],
      refine ⟨subset_union_of_subset_left aU _,
        subset_union_of_subset_right (set.singleton_subset_iff.mpr aUy) _⟩ },
    { rw [union_inter_distrib_right, ← set.inter_assoc, UV, set.empty_inter _, set.empty_union],
      rw [set.inter_comm V _, ← set.inter_assoc, UyVx, set.empty_inter] } },
end

lemma t2_separation_finsets [t2_space α] {t s : finset α} (h : disjoint s t) :
  ∃ U V : set α, is_open U ∧ is_open V ∧ ↑s ⊆ U ∧ ↑t ⊆ V ∧ U ∩ V = ∅ :=
begin
  symmetry' at h,
  revert h,
  refine finset.induction_disjoint _ (λ y u yt, _) _,
  { exact ⟨_, _, is_open_empty, is_open_univ, by refl, subset_univ _, inter_univ _⟩ },
  { rintros ⟨U, V, oU, oV, aU, bV, UV⟩,
    obtain ⟨Ut, Vy, oUt, oVy, aUt, bVy, UtVy⟩ := t2_separation_point_finset yt,
      refine ⟨U ∪ Vy, V ∩ Ut, is_open_union oU oVy, is_open_inter oV oUt, _, _, _⟩,
      { rw [coe_insert, ← union_singleton, union_subset_iff],
        refine ⟨subset_union_of_subset_left aU _,
          subset_union_of_subset_right (set.singleton_subset_iff.mpr bVy) U⟩ },
      { exact subset_inter_iff.mpr ⟨bV, aUt⟩ },
    { rw [union_inter_distrib_right, ← set.inter_assoc, UV, set.empty_inter _, set.empty_union],
      rw [set.inter_comm V _, ← set.inter_assoc, set.inter_comm _ Ut, UtVy, set.empty_inter] } },
end
