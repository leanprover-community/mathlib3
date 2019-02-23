import ring_theory.free_comm_ring ring_theory.subring data.set.finite data.real.irrational

universes u v

variables {α : Type u}

namespace free_comm_ring

def is_supported (x : free_comm_ring α) (s : set α) : Prop :=
x ∈ ring.closure (of '' s)

theorem is_supported_upwards {x : free_comm_ring α} {s t} (hs : is_supported x s) (hst : s ⊆ t) :
  is_supported x t :=
ring.closure_mono (set.mono_image hst) hs

theorem is_supported_add {x y : free_comm_ring α} {s} (hxs : is_supported x s) (hys : is_supported y s) :
  is_supported (x + y) s :=
is_add_submonoid.add_mem hxs hys

theorem is_supported_neg {x : free_comm_ring α} {s} (hxs : is_supported x s) :
  is_supported (-x) s :=
is_add_subgroup.neg_mem hxs

theorem is_supported_sub {x y : free_comm_ring α} {s} (hxs : is_supported x s) (hys : is_supported y s) :
  is_supported (x - y) s :=
is_add_subgroup.sub_mem _ _ _ hxs hys

theorem is_supported_mul {x y : free_comm_ring α} {s} (hxs : is_supported x s) (hys : is_supported y s) :
  is_supported (x * y) s :=
is_submonoid.mul_mem hxs hys

theorem is_supported_zero {s : set α} : is_supported 0 s :=
is_add_submonoid.zero_mem _

theorem is_supported_one {s : set α} : is_supported 1 s :=
is_submonoid.one_mem _

theorem is_supported_int {i : ℤ} {s : set α} : is_supported ↑i s :=
int.induction_on i is_supported_zero
  (λ i hi, by rw [int.cast_add, int.cast_one]; exact is_supported_add hi is_supported_one)
  (λ i hi, by rw [int.cast_sub, int.cast_one]; exact is_supported_sub hi is_supported_one)

def restriction (s : set α) [decidable_pred s] (x : free_comm_ring α) : free_comm_ring s :=
lift (λ p, if H : p ∈ s then pure ⟨p, H⟩ else 0) x

section restriction
variables (s : set α) [decidable_pred s] (x y : free_comm_ring α)
@[simp] lemma restriction_of (p) : restriction s (of p) = if H : p ∈ s then pure ⟨p, H⟩ else 0 := lift_of _ _
@[simp] lemma restriction_pure (p) : restriction s (pure p) = if H : p ∈ s then pure ⟨p, H⟩ else 0 := lift_of _ _
@[simp] lemma restriction_zero : restriction s 0 = 0 := lift_zero _
@[simp] lemma restriction_one : restriction s 1 = 1 := lift_one _
@[simp] lemma restriction_add : restriction s (x + y) = restriction s x + restriction s y := lift_add _ _ _
@[simp] lemma restriction_neg : restriction s (-x) = -restriction s x := lift_neg _ _
@[simp] lemma restriction_sub : restriction s (x - y) = restriction s x - restriction s y := lift_sub _ _ _
@[simp] lemma restriction_mul : restriction s (x * y) = restriction s x * restriction s y := lift_mul _ _ _
end restriction

theorem is_supported_pure {p} {s : set α} : is_supported (pure p) s ↔ p ∈ s :=
suffices is_supported (pure p) s → p ∈ s, from ⟨this, λ hps, ring.subset_closure ⟨p, hps, rfl⟩⟩,
assume hps : is_supported (pure p) s, begin
  classical,
  have : ∀ x, is_supported x s → ∃ q : ℚ, lift (λ q, if q ∈ s then 0 else real.sqrt 2) x = ↑q,
  { intros x hx, refine ring.in_closure.rec_on hx _ _ _ _,
    { use 1, rw [lift_one, rat.cast_one] },
    { use -1, rw [lift_neg, lift_one, rat.cast_neg, rat.cast_one], },
    { rintros _ ⟨z, hzs, rfl⟩ _ _, use 0, rw [lift_mul, lift_of, if_pos hzs, zero_mul, rat.cast_zero] },
    { rintros x y ⟨q, hq⟩ ⟨r, hr⟩, use q+r, rw [lift_add, hq, hr, rat.cast_add] } },
  specialize this (of p) hps, rw [lift_of] at this, split_ifs at this, { exact h },
  exfalso, exact irr_sqrt_two this
end

theorem subtype_val_map_restriction {x} (s : set α) [decidable_pred s] (hxs : is_supported x s) :
  subtype.val <$> restriction s x = x :=
begin
  refine ring.in_closure.rec_on hxs _ _ _ _,
  { rw restriction_one, refl },
  { rw [restriction_neg, map_neg, restriction_one], refl },
  { rintros _ ⟨p, hps, rfl⟩ n ih, rw [restriction_mul, restriction_of, dif_pos hps, map_mul, map_pure, ih], refl },
  { intros x y ihx ihy, rw [restriction_add, map_add, ihx, ihy] }
end

theorem exists_finset (x : free_comm_ring α) : ∃ s : set α, set.finite s ∧ is_supported x s :=
free_comm_ring.induction_on x
  ⟨∅, set.finite_empty, is_supported_neg is_supported_one⟩
  (λ p, ⟨{p}, set.finite_singleton p, is_supported_pure.2 $ finset.mem_singleton_self _⟩)
  (λ x y ⟨s, hfs, hxs⟩ ⟨t, hft, hxt⟩, ⟨s ∪ t, set.finite_union hfs hft, is_supported_add
    (is_supported_upwards hxs $ set.subset_union_left s t)
    (is_supported_upwards hxt $ set.subset_union_right s t)⟩)
  (λ x y ⟨s, hfs, hxs⟩ ⟨t, hft, hxt⟩, ⟨s ∪ t, set.finite_union hfs hft, is_supported_mul
    (is_supported_upwards hxs $ set.subset_union_left s t)
    (is_supported_upwards hxt $ set.subset_union_right s t)⟩)

end free_comm_ring
