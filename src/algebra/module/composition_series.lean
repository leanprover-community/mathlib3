import order.jordan_holder
import order.cover
import ring_theory.simple_module

def partial_order.bot_or_top {α : Type*} [partial_order α] (x z : α) :=
  ∀ ⦃y⦄, x ≤ y → y ≤ z → (y = x ∨ y = z)

lemma covby.bot_or_top {α : Type*} [partial_order α] {x z : α} (hxz : x ⋖ z) :
  partial_order.bot_or_top x z := λ y hxy hyz,
begin
  cases lt_or_eq_of_le hxy with hxy h,
  cases lt_or_eq_of_le hyz with hyz h,
  { exfalso,
    exact hxz.2 hxy hyz },
  exact or.inr h,
  exact or.inl h.symm
end

lemma covby.iff_bot_or_top {α : Type*} [partial_order α] {x z : α} :
  x ⋖ z ↔ (x < z ∧ partial_order.bot_or_top x z ) :=
begin
  split; intro h,
  exact ⟨h.lt, h.bot_or_top⟩,
  refine ⟨h.1, _⟩,
  intros y hxy hyz,
  apply lt_irrefl y,
  cases h.2 (le_of_lt hxy) (le_of_lt hyz) with h' h';
    rw ←h' at *; assumption
end

lemma covby.sup_eq {α : Type*} [lattice α] {x y z : α} : x ⋖ z → y ⋖ z → x ≠ y → x ⊔ y = z :=
begin
  intros hxz hyz hxy,
  have hxyz : x ⊔ y ≤ z := sup_le (le_of_lt hxz.lt) (le_of_lt hyz.lt),
  cases hxz.bot_or_top le_sup_left hxyz with hx h,
  cases hyz.bot_or_top le_sup_right hxyz with hy h,
  { exfalso,
    exact hxy (eq.trans hx.symm hy) },
  all_goals { exact h },
end

namespace composition_series

open submodule
open lattice
variables {R M : Type*} [ring R] [add_comm_group M] [module R M]

@[simp]
lemma comap_map_subtype (B : submodule R M) (A : submodule R B) :
  comap B.subtype (map B.subtype A) = A :=
comap_map_eq_of_injective subtype.coe_injective A

lemma covby_iff_quot_is_simple {A B : submodule R M} (hAB : A ≤ B) :
  A ⋖ B ↔ is_simple_module R (B ⧸ comap B.subtype A) :=
begin
  rw is_simple_module_iff_is_coatom,
  split; intro h,
  { split,
    { intro htop,
      rw comap_subtype_eq_top at htop,
      rw le_antisymm hAB htop at h,
      exact lt_irrefl B h.lt },
    { intros C' hAC',
      have hA : A = map B.subtype (comap B.subtype A),
        rwa [map_comap_subtype,right_eq_inf],
      have hAC : A ≤ map B.subtype C',
      { rw hA,
        exact map_mono (le_of_lt hAC') },
      cases h.bot_or_top hAC (map_subtype_le B C') with h h,
      { exfalso,
        apply ne_of_lt hAC',
        rw congr_arg (comap B.subtype) h.symm,
        exact comap_map_subtype B C' },
      { rw [←comap_map_subtype B C', h, comap_subtype_self] } } },
  { rw covby.iff_bot_or_top,
    split,
    { apply lt_of_le_of_ne hAB,
      intro hAB',
      apply h.1,
      rw hAB',
      exact comap_subtype_self B },
    { intros C hAC hCB,
      by_cases u : comap B.subtype A < comap B.subtype C,
      { right,
        exact le_antisymm hCB (comap_subtype_eq_top.mp $ h.2 _ u) },
      { left,
        have eqAC := eq_of_le_of_not_lt (comap_mono hAC) u,
        rw [right_eq_inf.mpr hAB, right_eq_inf.mpr hCB, ←map_comap_subtype, ←eqAC, map_comap_subtype] } } }
end

instance jordan_holder_module : jordan_holder_lattice (submodule R M) :=
{ is_maximal                            := covby,
  lt_of_is_maximal                      := λ x y, covby.lt,
  sup_eq_of_is_maximal                  := λ x y z, covby.sup_eq,
  is_maximal_inf_left_of_is_maximal_sup := λ {A B} h₁ h₂, by {
    rw covby_iff_quot_is_simple (inf_le_left : A ⊓ B ≤ A),
    haveI h := (covby_iff_quot_is_simple (le_sup_right : B ≤ A ⊔ B)).mp h₂,
    apply is_simple_module.congr (linear_map.quotient_inf_equiv_sup_quotient A B) },
  iso                                   := λ X Y,
    nonempty $ (X.2 ⧸ comap X.2.subtype X.1) ≃ₗ[R] (Y.2 ⧸ comap Y.2.subtype Y.1),
  iso_symm                              := λ A B ⟨f⟩, ⟨f.symm⟩,
  iso_trans                             := λ A B C ⟨f⟩ ⟨g⟩, ⟨f.trans g⟩,
  second_iso                            := λ A B h, ⟨by {
    rw [sup_comm,inf_comm],
    exact (linear_map.quotient_inf_equiv_sup_quotient B A).symm }⟩ }

end composition_series
