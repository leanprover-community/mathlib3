import representation_theory.Rep representation_theory.fdRep

universe u
variables (R G : Type u) [comm_ring R] [group G] [fintype G] [decidable_eq G] [nontrivial R]

def monoid_algebra.to_module.basis : G → monoid_algebra R G := λ g, {
  support := ⟨{g}, multiset.nodup_singleton g⟩,
  to_fun := λ h, ite (h=g) (1:R) (0:R),
  mem_support_to_fun := λ a, begin
    rw [ite_ne_right_iff, finset.mem_mk, multiset.mem_singleton],
    exact (and_iff_left one_ne_zero).symm,
  end }

def conj_class (g : G):= {h : G | is_conj g h}

instance conj_class.decidable_mem (g : G) : decidable_pred (λ h, h ∈ conj_class G g) := λ h, begin
  suffices d : decidable ( ∃ x : G, x * g = h * x ), {
    cases d, {
      sorry,
    }, {
      sorry,
    }
  },
  sorry,
end

def conj_classes' := set.range (conj_class G)
def conj_class_finset (X : conj_classes' G) : finset X := sorry

noncomputable def center_basis : conj_classes' G → (monoid_algebra R G) := λ C,
  finset.sum (conj_class_finset G C) (λ g, monoid_algebra.to_module.basis R G g)

namespace monoid_algebra

def subalgebra_center : subalgebra R (monoid_algebra R G) := {
  carrier := subring.center (monoid_algebra R G),
  mul_mem' := sorry,
  one_mem' := sorry,
  add_mem' := sorry,
  zero_mem' := sorry,
  algebra_map_mem' := sorry }

def subalgebra_center.basis :
  basis (conj_classes' G) R (monoid_algebra.subalgebra_center R G) :=
⟨{to_fun := _,
  map_add' := _,
  map_smul' := _,
  inv_fun := _,
  left_inv := _,
  right_inv := _ }⟩

end monoid_algebra
