import linear_algebra.direct_sum_module linear_algebra.linear_combination

universes u v w u₁

open lattice submodule

class directed_order (α : Type u) extends partial_order α :=
(directed : ∀ i j : α, ∃ k, i ≤ k ∧ j ≤ k)

variables {ι : Type u} [inhabited ι]
variables [directed_order ι] [decidable_eq ι]
variables (G : ι → Type v) [Π i, decidable_eq (G i)]

class directed_system {R : Type w} [comm_ring R] [Π i, add_comm_group (G i)] [Π i, module R (G i)]
  (f : Π i j, i ≤ j → G i →ₗ G j) : Prop :=
(Hid : ∀ i x, f i i (le_refl i) x = x)
(Hcomp : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

def direct_limit {R : Type w} [comm_ring R] [Π i, add_comm_group (G i)] [Π i, module R (G i)]
  (f : Π i j, i ≤ j → G i →ₗ G j) [directed_system G f] : Type (max u v) :=
quotient $ span $ ⋃ i j (H : i ≤ j) x,
({ direct_sum.of ι G i x - direct_sum.of ι G j (f i j H x) } : set $ direct_sum R ι G)

namespace direct_limit

section module

variables {R : Type w} [comm_ring R] [Π i, add_comm_group (G i)] [Π i, module R (G i)]
variables (f : Π i j, i ≤ j → G i →ₗ G j) [directed_system G f]
include R

instance : add_comm_group (direct_limit G f) := quotient.add_comm_group _
instance : module R (direct_limit G f) := quotient.module _

variables (ι R)
def of (i) : G i →ₗ direct_limit G f :=
(mkq _).comp $ direct_sum.of ι G i
variables {ι R}

theorem of_f {i j hij x} : (of ι G R f j (f i j hij x)) = of ι G R f i x :=
eq.symm $ (submodule.quotient.eq _).2 $ subset_span $
set.mem_Union.2 ⟨i, set.mem_Union.2 ⟨j, set.mem_Union.2 ⟨hij, set.mem_Union.2 ⟨x, or.inl rfl⟩⟩⟩⟩

variables {P : Type u₁} [add_comm_group P] [module R P] (g : Π i, G i →ₗ P)
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
include Hg

variables (ι R)
def rec : direct_limit G f →ₗ P :=
liftq _ (direct_sum.to_module _ g) $ span_le.2 $ set.Union_subset $ λ i,
set.Union_subset $ λ j, set.Union_subset $ λ hij, set.Union_subset $ λ x,
set.singleton_subset_iff.2 $ linear_map.sub_mem_ker_iff.2 $
by rw [direct_sum.to_module.of, direct_sum.to_module.of, Hg]
variables {ι R}

omit Hg
lemma rec_of {i} (x) : rec ι G R f g Hg (of ι G R f i x) = g i x :=
direct_sum.to_module.of _ _

theorem rec_unique (F : direct_limit G f →ₗ P) (x) :
  F x = rec ι G R f (λ i, F.comp $ of ι G R f i)
    (λ i j hij x, by rw [linear_map.comp_apply, of_f]; refl) x :=
quotient.induction_on' x $ λ y, direct_sum.induction_on y
  ((linear_map.map_zero _).trans (linear_map.map_zero _).symm)
  (λ i x, eq.symm $ rec_of _ _ _ _ _)
  (λ x y ihx ihy, (linear_map.map_add F (quotient.mk' x) (quotient.mk' y)).trans $
    ihx.symm ▸ ihy.symm ▸ (linear_map.map_add _ _ _).symm)

theorem exists_of (z : direct_limit G f) : ∃ i x, z = of ι G R f i x :=
quotient.induction_on' z $ λ z, direct_sum.induction_on z
  ⟨default _, 0, (linear_map.map_zero _).symm⟩
  (λ i x, ⟨i, x, rfl⟩)
  (λ p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, f i k hik x + f j k hjk y, by rw [linear_map.map_add, of_f, of_f, ← ihx, ← ihy]; refl⟩)

@[elab_as_eliminator] theorem induction_on {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of ι G R f i x)) : C z :=
let ⟨i, x, h⟩ := exists_of G f z in h.symm ▸ ih i x

theorem of.zero_exact {i x} (H : of ι G R f i x = 0) :
  ∃ j hij, f i j hij x = (0 : G j) :=
begin
  rcases mem_span_iff_lc.1 ((submodule.quotient.eq _).1 H) with ⟨l, h1, h2⟩, rw sub_zero at h2, clear H,
  revert l i x, intro l, haveI : decidable_eq R := classical.dec_eq R,
  apply finsupp.induction l,
  { intros i x h1 h2, rw [linear_map.map_zero, ← linear_map.map_zero (direct_sum.of ι G i)] at h2,
    have := direct_sum.of_inj _ h2, subst this,
    exact ⟨i, le_refl i, linear_map.map_zero _⟩ },
  intros a b f haf hb0 ih i x h1 h2,
  sorry
end

end module

end direct_limit
