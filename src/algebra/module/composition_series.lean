import order.jordan_holder
import ring_theory.simple_module

namespace composition_series

namespace lattice

variables {α : Type*} [lattice α]

structure is_maximal (x z : α) : Prop :=
  (lt : x < z)
  (bot_or_top : ∀ {y}, x ≤ y → y ≤ z → (y = x ∨ y = z))

lemma sup_eq_of_is_maximal : ∀ {x y z : α}, is_maximal x z → is_maximal y z → x ≠ y → x ⊔ y = z :=
begin
  intros x y z hxz hyz hxy,
  have hxyz : x ⊔ y ≤ z := sup_le (le_of_lt hxz.lt) (le_of_lt hyz.lt),
  cases hxz.bot_or_top le_sup_left hxyz with hx h,
  cases hyz.bot_or_top le_sup_right hxyz with hy h, {
    exfalso,
    exact hxy (eq.trans hx.symm hy),
  },
  all_goals {exact h},
end

end lattice

section jordan_holder

open submodule
open lattice
variables {R M : Type*} [ring R] [add_comm_group M] [module R M]

@[simp]
lemma comap_map_subtype (B : submodule R M) (A : submodule R B) :
  comap B.subtype (map B.subtype A) = A :=
begin
  apply comap_map_eq_of_injective,
  exact subtype.coe_injective,
end

lemma is_maximal_iff_quot_is_simple {A B : submodule R M} (hAB : A ≤ B) :
  lattice.is_maximal A B ↔ is_simple_module R (B ⧸ comap B.subtype A) :=
begin
  rw is_simple_module_iff_is_coatom,
  split; intro h, {
    split, {
      intro htop,
      rw submodule.comap_subtype_eq_top at htop,
      rw le_antisymm hAB htop at h,
      exact lt_irrefl B h.lt,
    }, {
      intros C' hAC',
      have hA : A = map B.subtype (comap B.subtype A),
        rwa [map_comap_subtype,right_eq_inf],
      have hAC : A ≤ map B.subtype C', {
        rw hA,
        exact map_mono (le_of_lt hAC'),
      },
      cases h.bot_or_top hAC (map_subtype_le B C') with h h, {
        exfalso,
        apply ne_of_lt hAC',
        rw congr_arg (comap B.subtype) h.symm,
        exact comap_map_subtype B C',
      }, {
        rw [←comap_map_subtype B C', h, submodule.comap_subtype_self],
      }
    },
  }, {
    split, {
      apply lt_of_le_of_ne hAB,
      intro hAB',
      apply h.1,
      rw hAB',
      exact submodule.comap_subtype_self B,
    }, {
      intros C hAC hCB,
      by_cases u : comap B.subtype A < comap B.subtype C, {
        right,
        exact le_antisymm hCB (submodule.comap_subtype_eq_top.mp $ h.2 _ u),
      }, {
        left,
        have eqAC := eq_of_le_of_not_lt (comap_mono hAC) u,
        rw [right_eq_inf.mpr hAB, right_eq_inf.mpr hCB, ←map_comap_subtype, ←eqAC, map_comap_subtype],
      }
    },
  }
end

instance jordan_holder_module : jordan_holder_lattice (submodule R M) := {
  is_maximal := is_maximal,
  lt_of_is_maximal := λ x y h, h.lt,
  sup_eq_of_is_maximal := λ x y z, sup_eq_of_is_maximal,
  is_maximal_inf_left_of_is_maximal_sup := λ {A B} h₁ h₂, begin
    rw is_maximal_iff_quot_is_simple (inf_le_left : A ⊓ B ≤ A),
    haveI h := (is_maximal_iff_quot_is_simple (le_sup_right : B ≤ A ⊔ B)).mp h₂,
    apply is_simple_module.congr (linear_map.quotient_inf_equiv_sup_quotient A B),
  end,
  iso := λ X Y, nonempty $ ((X.2 ⧸ comap X.2.subtype X.1)) ≃ₗ[R] ((Y.2 ⧸ comap Y.2.subtype Y.1)),
  iso_symm := λ {A B} ⟨f⟩, ⟨f.symm⟩,
  iso_trans := λ {A B C} ⟨f⟩ ⟨g⟩, ⟨f.trans g⟩,
  second_iso := λ {A B} h, ⟨begin
    rw [sup_comm,inf_comm],
    exact (linear_map.quotient_inf_equiv_sup_quotient B A).symm,
  end⟩,
}

end jordan_holder

end composition_series
