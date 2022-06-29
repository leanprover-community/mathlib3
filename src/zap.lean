import data.multiset.bind
import data.multiset.nodup

namespace multiset

lemma bind_powerset_card {α : Type*} (S : multiset α) :
  S.powerset = bind (range (S.card + 1)) (λ k, (filter (λ t, t.card = k) S.powerset)) :=
begin
  classical,
  ext a,
  rw count_bind,
  by_cases ha : a.card ∈ (range (S.card + 1)),
  { rw [←cons_erase ha, map_cons, sum_cons, count_filter],
    conv_rhs
    begin
      congr, skip, congr, congr, funext,
      rw count_filter,
    end,
    simp_rw [eq_self_iff_true, if_true, self_eq_add_right, sum_eq_zero_iff],
    intros x hx,
    rw mem_map at hx,
    obtain ⟨b, hb⟩ := hx,
    have : a.card ≠ b,
    { have : _, from nodup_range (S.card + 1),
      exact ((nodup.mem_erase_iff this).mp hb.left).left.symm, },
    simp_rw [this, if_false] at hb,
    exact hb.right.symm, },
  { have : a ∉ S.powerset, { contrapose! ha,
    rw mem_powerset at ha,
    exact mem_range.mpr (nat.lt_succ_iff.mpr (card_le_of_le ha)),  },
    simp only [this, count_eq_zero_of_not_mem, not_false_iff, mem_filter, false_and, map_const,
      sum_repeat, nsmul_eq_mul, mul_zero], },
end

lemma bind_powerset_len {α : Type*} (S : multiset α) :
  S.powerset = bind (range (S.card + 1)) (λ k, S.powerset_len k) :=
begin
  classical,
  rw bind_powerset_card S,
  rw ( _ : range (S.card + 1) = (map (λ k, singleton k) (range (S.card + 1))).sum),
  { rw [bind, bind, join, multiset.map_congr (eq.refl _)],
    intros x hx,
    exact (multiset.powerset_len_eq_filter S x).symm },
  { simp only [map_cons, sum_cons, sum_map_singleton, cons_bind, sum_map_singleton], },
end

end multiset
