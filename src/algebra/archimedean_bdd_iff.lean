import algebra.archimedean
import algebra.iterate_hom
import order.iterate

open set

variables {α β G : Type*} [ordered_add_comm_group G] [archimedean G] [preorder β]

lemma bdd_above_iff_of_mono_of_map_add_le {f : α → G → β} {x : G} (hx : 0 < x) {g : β → β}
  (hf_mono : ∀ a, monotone (f a)) (hg_mono : monotone g)
  (hfg : ∀ a y, f a (y + x) ≤ g (f a y)) (y z : G) :
  bdd_above (range $ λ a, f a y) ↔ bdd_above (range $ λ a, f a z) :=
begin
  suffices : ∀ y z, bdd_above (range $ λ a, f a y) → bdd_above (range $ λ a, f a z),
    from ⟨this y z, this z y⟩,
  clear y z, rintros y z ⟨b, hb⟩, simp only [mem_upper_bounds, forall_range_iff] at hb,
  rcases archimedean.arch (z - y) hx with ⟨m, hm⟩,
  refine ⟨g^[m] b, _⟩,
  rintro _ ⟨a, rfl⟩,
  calc f a z ≤ f a (y + m • x)   : hf_mono a (sub_le_iff_le_add'.1 hm)
         ... = f a ((+ x)^[m] y) : by rw add_right_iterate
         ... ≤ (g^[m] (f a y))   : hg_mono.le_iterate_comp_of_le (hfg a) _ _
         ... ≤ (g^[m] b)         : hg_mono.iterate m (hb a)
end

lemma forall_bdd_above_iff_exists_of_mono_of_map_add_le {f : α → G → β} {x : G} (hx : 0 < x)
  {g : β → β} (hf_mono : ∀ a, monotone (f a)) (hg_mono : monotone g)
  (hfg : ∀ a y, f a (y + x) ≤ g (f a y)) :
  (∀ y, bdd_above (range $ λ a, f a y)) ↔ (∃ y, bdd_above (range $ λ a, f a y)) :=
⟨λ H, ⟨0, H 0⟩, λ ⟨y, hy⟩ z, (bdd_above_iff_of_mono_of_map_add_le hx hf_mono hg_mono hfg _ _).1 hy⟩

lemma bdd_below_iff_of_mono_of_map_add_le {f : α → G → β} {x : G} (hx : 0 < x) {g : β → β}
  (hf_mono : ∀ a, monotone (f a)) (hg_mono : monotone g)
  (hfg : ∀ a y, g (f a y) ≤ f a (y - x)) (y z : G) :
  bdd_below (range $ λ a, f a y) ↔ bdd_below (range $ λ a, f a z) :=
@bdd_above_iff_of_mono_of_map_add_le α (order_dual β) (order_dual G) _ _ _ f (-x) (neg_pos.2 hx) g
  (λ a, (hf_mono a).order_dual) hg_mono.order_dual (by simpa only [← sub_eq_add_neg]) _ _

lemma forall_bdd_below_iff_exists_of_mono_of_map_add_le {f : α → G → β} {x : G} (hx : 0 < x)
  {g : β → β} (hf_mono : ∀ a, monotone (f a)) (hg_mono : monotone g)
  (hfg : ∀ a y, g (f a y) ≤ f a (y - x)) :
  (∀ y, bdd_below (range $ λ a, f a y)) ↔ (∃ y, bdd_below (range $ λ a, f a y)) :=
⟨λ H, ⟨0, H 0⟩, λ ⟨y, hy⟩ z, (bdd_below_iff_of_mono_of_map_add_le hx hf_mono hg_mono hfg _ _).1 hy⟩
