import data.finset.image

variables {α β γ : Type*}
open multiset
open function

namespace finset

lemma monotone_map (f : β ↪ γ) :
  monotone (finset.map f) :=
λ _ _ h, map_subset_map.mpr h

@[simp] lemma map_subtype_subtype (p : β → Prop) [decidable_pred p] (s : finset (subtype p)) :
  finset.subtype p (s.map (embedding.subtype p)) = s :=
begin
  ext x,
  simp only [x.prop, mem_subtype, finset.mem_map, embedding.coe_subtype, exists_prop,
             subtype.exists, subtype.coe_mk, exists_and_distrib_right, exists_eq_right,
             subtype.coe_eta, exists_true_left],
end

lemma subtype_map_gc (p : β → Prop) [decidable_pred p] :
  galois_connection (map (embedding.subtype p)) (finset.subtype p) :=
begin
  classical,
  intros s t,
  split; intro h,
  { exact (subtype_mono h).trans' (finset.map_subtype_subtype _ _).ge },
  { refine (finset.monotone_map _ h).trans _,
    simp }
end

def subtype_map_gci (p : β → Prop) [decidable_pred p] :
  galois_coinsertion (map (embedding.subtype p)) (finset.subtype p) :=
(subtype_map_gc _).to_galois_coinsertion $ by simp

lemma disjoint_map_subtype_of_not {p q : β → Prop}
  (s : finset (subtype p)) (t : finset (subtype q)) (h : ∀ (b : subtype p), b ∈ s → ¬ q b) :
  disjoint (s.map (embedding.subtype _)) (t.map (embedding.subtype _)) :=
begin
  intros u hs ht x hx,
  have hp := hs hx,
  have hq := ht hx,
  simp only [finset.mem_map, embedding.coe_subtype, exists_prop, subtype.exists, subtype.coe_mk,
             exists_and_distrib_right, exists_eq_right] at hp hq,
  rcases hp with ⟨_, hp⟩,
  rcases hq with ⟨hq, -⟩,
  exact absurd hq (h _ hp)
end

lemma disjoint_map_subtype (p : β → Prop)
  {s : finset (subtype p)} {t : finset (subtype (λ b, ¬ p b))} :
  disjoint (s.map (embedding.subtype _)) (t.map (embedding.subtype _)) :=
disjoint_map_subtype_of_not _ _ (λ b _, by simp [b.prop])

lemma filter_sdiff_distrib [decidable_eq β] (s t : finset β) (p : β → Prop) [decidable_pred p] :
  finset.filter p (s \ t) = s.filter p \ t.filter p :=
begin
  ext,
  simp only [mem_filter, mem_sdiff, not_and],
  tauto
end

lemma map_sdiff_distrib [decidable_eq β] [decidable_eq γ] (s t : finset β) (f : β ↪ γ) :
  finset.map f (s \ t) = s.map f \ t.map f :=
begin
  ext y,
  simp only [finset.mem_map, mem_sdiff, exists_prop, not_exists, not_and, and.comm, and.left_comm],
  split,
  { rintro ⟨x, hs, ht, rfl⟩,
    refine ⟨λ z hz, _, ⟨_, hs, rfl⟩⟩,
    rw f.apply_eq_iff_eq,
    rintro rfl,
    exact ht hz },
  { rintro ⟨H, x, hs, rfl⟩,
    refine ⟨_, hs, λ ht, _, rfl⟩,
    exact H _ ht (congr_arg _ rfl) }
end

end finset
