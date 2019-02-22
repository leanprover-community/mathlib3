import linear_algebra.direct_sum_module
import linear_algebra.linear_combination
import ring_theory.free_comm_ring
import ring_theory.ideal_operations
import ring_theory.to_field

universes u v w u₁

open lattice submodule

class directed_order (α : Type u) extends partial_order α :=
(directed : ∀ i j : α, ∃ k, i ≤ k ∧ j ≤ k)

variables {R : Type u} [ring R]
variables {ι : Type v} [nonempty ι]
variables [directed_order ι] [decidable_eq ι]
variables (G : ι → Type w) [Π i, decidable_eq (G i)]

namespace module

variables [Π i, add_comm_group (G i)] [Π i, module R (G i)]

class directed_system (f : Π i j, i ≤ j → G i →ₗ[R] G j) : Prop :=
(Hid : ∀ i x, f i i (le_refl i) x = x)
(Hcomp : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

variables (f : Π i j, i ≤ j → G i →ₗ[R] G j) [directed_system G f]

def thing : set (direct_sum ι G) :=
⋃ i j H, set.range $ λ x, direct_sum.lof R ι G i x - direct_sum.lof R ι G j (f i j H x)

def direct_limit : Type (max v w) :=
(span R $ thing G f).quotient

variables {G f}
lemma mem_thing {a : direct_sum ι G} : a ∈ thing G f ↔ ∃ (i j) (H : i ≤ j) x,
  direct_sum.lof R ι G i x - direct_sum.lof R ι G j (f i j H x) = a :=
by simp only [thing, set.mem_Union, set.mem_range]
variables (G f)

namespace direct_limit

instance : add_comm_group (direct_limit G f) := quotient.add_comm_group _
instance : module R (direct_limit G f) := quotient.module _

variables (R ι)
def of (i) : G i →ₗ[R] direct_limit G f :=
(mkq _).comp $ direct_sum.lof R ι G i
variables {R ι}

theorem of_f {i j hij x} : (of R ι G f j (f i j hij x)) = of R ι G f i x :=
eq.symm $ (submodule.quotient.eq _).2 $ subset_span $
set.mem_Union.2 ⟨i, set.mem_Union.2 ⟨j, set.mem_Union.2 ⟨hij, set.mem_range_self x⟩⟩⟩

variables {P : Type u₁} [add_comm_group P] [module R P] (g : Π i, G i →ₗ[R] P)
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
include Hg

variables (R ι)
def rec : direct_limit G f →ₗ[R] P :=
liftq _ (direct_sum.to_module R ι P g)
  (span_le.2 $ set.Union_subset $ λ i,
    set.Union_subset $ λ j, set.Union_subset $ λ hij,
      set.range_subset_iff.2 $ λ x, linear_map.sub_mem_ker_iff.2 $
        by rw [direct_sum.to_module_lof, direct_sum.to_module_lof, Hg])

variables {R ι}

omit Hg
lemma rec_of {i} (x) : rec R ι G f g Hg (of R ι G f i x) = g i x :=
direct_sum.to_module_lof R _ _

theorem rec_unique (F : direct_limit G f →ₗ[R] P) (x) :
  F x = rec R ι G f (λ i, F.comp $ of R ι G f i)
    (λ i j hij x, by rw [linear_map.comp_apply, of_f]; refl) x :=
quotient.induction_on' x $ λ y, direct_sum.induction_on y
  ((linear_map.map_zero _).trans (linear_map.map_zero _).symm)
  (λ i x, eq.symm $ rec_of _ _ _ _ _)
  (λ x y ihx ihy, (linear_map.map_add F (quotient.mk' x) (quotient.mk' y)).trans $
    ihx.symm ▸ ihy.symm ▸ (linear_map.map_add _ _ _).symm)

theorem exists_of (z : direct_limit G f) : ∃ i x, z = of R ι G f i x :=
nonempty.elim (by apply_instance) $ assume ind : ι,
quotient.induction_on' z $ λ z, direct_sum.induction_on z
  ⟨ind, 0, (linear_map.map_zero _).symm⟩
  (λ i x, ⟨i, x, rfl⟩)
  (λ p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, f i k hik x + f j k hjk y, by rw [linear_map.map_add, of_f, of_f, ← ihx, ← ihy]; refl⟩)

@[elab_as_eliminator] theorem induction_on {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of R ι G f i x)) : C z :=
let ⟨i, x, h⟩ := exists_of G f z in h.symm ▸ ih i x

lemma span_preimage_le_comap_span {R M N: Type*} [ring R] [add_comm_group M] [module R M]
  [add_comm_group N] [module R N] (f : N →ₗ[R] M) (s : set M) : span R (f ⁻¹' s) ≤ (span R s).comap f :=
λ x h, span_induction h
  (by simp only [set.preimage, set.mem_set_of_eq, mem_comap]; exact λ x h, subset_span h)
  (zero_mem ((span R s).comap f))
  (λ _ _ hx hy, add_mem ((span R s).comap f) hx hy)
  (λ _ _ h, smul_mem ((span R s).comap f) _ h)

section totalize
local attribute [instance, priority 0] classical.dec

noncomputable def totalize : Π i j, G i →ₗ[R] G j :=
λ i j, if h : i ≤ j then f i j h else 0

lemma totalize_apply (i j x) :
  totalize G f i j x = if h : i ≤ j then f i j h x else 0 :=
if h : i ≤ j
  then by dsimp only [totalize]; rw [dif_pos h, dif_pos h]
  else by dsimp only [totalize]; rw [dif_neg h, dif_neg h, linear_map.zero_apply]
end totalize

lemma to_module_totalize_of_le {x : direct_sum ι G} {i j : ι}
  (hij : i ≤ j) (hx : ∀ k ∈ x.support, k ≤ i) :
  direct_sum.to_module R ι (G j) (λ k, totalize G f k j) x =
  f i j hij (direct_sum.to_module R ι (G i) (λ k, totalize G f k i) x) :=
begin
  rw [← @dfinsupp.sum_single ι G _ _ _ x, dfinsupp.sum],
  simp only [linear_map.map_sum],
  refine finset.sum_congr rfl (λ k hk, _),
  rw direct_sum.single_eq_lof R k (x k),
  simp [totalize_apply, hx k hk, le_trans (hx k hk) hij, directed_system.Hcomp f]
end

lemma of.zero_exact_aux {x : direct_sum ι G} (H : x ∈ span R (thing G f)) :
  ∃ j, (∀ k ∈ x.support, k ≤ j) ∧ direct_sum.to_module R ι (G j) (λ i, totalize G f i j) x = (0 : G j) :=
nonempty.elim (by apply_instance) $ assume ind : ι,
span_induction H
  (λ x hx, let ⟨i, j, hij, y, hxy⟩ := mem_thing.1 hx in
    let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, begin
      clear_,
      subst hxy,
      split,
      { intros i0 hi0,
        rw [dfinsupp.mem_support_iff, dfinsupp.sub_apply, ← direct_sum.single_eq_lof,
            ← direct_sum.single_eq_lof, dfinsupp.single_apply, dfinsupp.single_apply] at hi0,
        split_ifs at hi0 with hi hj hj, { rwa hi at hik }, { rwa hi at hik }, { rwa hj at hjk },
        exfalso, apply hi0, rw sub_zero },
      simp [linear_map.map_sub, totalize_apply, hik, hjk,
        directed_system.Hcomp f, direct_sum.apply_eq_component,
        direct_sum.component.of],
    end⟩)
  ⟨ind, λ _ h, (finset.not_mem_empty _ h).elim, linear_map.map_zero _⟩
  (λ x y ⟨i, hi, hxi⟩ ⟨j, hj, hyj⟩,
    let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, λ l hl,
      (finset.mem_union.1 (dfinsupp.support_add hl)).elim
        (λ hl, le_trans (hi _ hl) hik)
        (λ hl, le_trans (hj _ hl) hjk),
      by simp [linear_map.map_add, hxi, hyj,
          to_module_totalize_of_le G f hik hi,
          to_module_totalize_of_le G f hjk hj]⟩)
  (λ a x ⟨i, hi, hxi⟩,
    ⟨i, λ k hk, hi k (dfinsupp.support_smul hk),
      by simp [linear_map.map_smul, hxi]⟩)

theorem of.zero_exact {i x} (H : of R ι G f i x = 0) :
  ∃ j hij, f i j hij x = (0 : G j) :=
let ⟨j, hj, hxj⟩ := of.zero_exact_aux G f
  ((submodule.quotient.eq _).1 H) in
if hx0 : x = 0 then ⟨i, le_refl _, by simp [hx0]⟩
else
  have hij : i ≤ j, from hj _ $
    by simp [direct_sum.apply_eq_component, hx0],
  ⟨j, hij, by simpa [totalize_apply, hij] using hxj⟩
end direct_limit

@[extensionality] theorem ext {α : Type u} [ring α] {β : Type v} [add_comm_group β] :
  Π (M₁ M₂ : module α β)
    (H : ∀ r x, @has_scalar.smul α β M₁.to_has_scalar r x = @has_scalar.smul α β M₂.to_has_scalar r x),
  M₁ = M₂ :=
by rintro ⟨⟨⟨f⟩, _, _, _, _, _, _⟩⟩ ⟨⟨⟨g⟩, _, _, _, _, _, _⟩⟩ H; congr' 3; ext; apply H

end module


namespace add_comm_group

variables {α : Type u} [add_comm_group α]

protected def module : module ℤ α := module.of_core
{ smul := gsmul,
  mul_smul := λ r s x, gsmul_mul x r s,
  smul_add := λ r x y, gsmul_add x y r,
  add_smul := λ r s x, add_gsmul x r s,
  one_smul := one_gsmul }

instance module.subsingleton : subsingleton (module ℤ α) :=
begin
  constructor, intros M₁ M₂, ext i x, refine int.induction_on i _ _ _,
  { rw [zero_smul, zero_smul] },
  { intros i ih, rw [add_smul, add_smul, ih, one_smul, one_smul] },
  { intros i ih, rw [sub_smul, sub_smul, ih, one_smul, one_smul] }
end

end add_comm_group

local attribute [instance] add_comm_group.module

namespace is_add_group_hom

variables {α : Type u} {β : Type v} [add_comm_group α] [add_comm_group β]

def to_linear_map (f : α → β) [is_add_group_hom f] : α →ₗ[ℤ] β :=
{ to_fun := f,
  add := is_add_group_hom.add f,
  smul := λ i x, int.induction_on i (by rw [zero_smul, zero_smul, is_add_group_hom.zero f])
    (λ i ih, by rw [add_smul, add_smul, is_add_group_hom.add f, ih, one_smul, one_smul])
    (λ i ih, by rw [sub_smul, sub_smul, is_add_group_hom.sub f, ih, one_smul, one_smul]) }

end is_add_group_hom

namespace add_comm_group

variables [Π i, add_comm_group (G i)]

class directed_system (f : Π i j, i ≤ j → G i → G j) : Prop :=
(Hid : ∀ i x, f i i (le_refl i) x = x)
(Hcomp : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

def direct_limit
  (f : Π i j, i ≤ j → G i → G j) [Π i j hij, is_add_group_hom (f i j hij)] [directed_system G f] : Type* :=
@module.direct_limit ℤ _ ι _ _ _ G _ _ _
  (λ i j hij, is_add_group_hom.to_linear_map $ f i j hij)
  ⟨directed_system.Hid f, directed_system.Hcomp f⟩

namespace direct_limit

variables (f : Π i j, i ≤ j → G i → G j)
variables [Π i j hij, is_add_group_hom (f i j hij)] [directed_system G f]

def directed_system : module.directed_system G (λ (i j : ι) (hij : i ≤ j), is_add_group_hom.to_linear_map (f i j hij)) :=
⟨directed_system.Hid f, directed_system.Hcomp f⟩

local attribute [instance] directed_system

instance : add_comm_group (direct_limit G f) :=
module.direct_limit.add_comm_group G (λ i j hij, is_add_group_hom.to_linear_map $ f i j hij)

variables (P : Type u₁) [add_comm_group P]
variables (g : Π i, G i → P) [Π i, is_add_group_hom (g i)]
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

set_option class.instance_max_depth 51
def rec : direct_limit G f → P :=
module.direct_limit.rec ℤ ι G (λ i j hij, is_add_group_hom.to_linear_map $ f i j hij)
  (λ i, is_add_group_hom.to_linear_map $ g i) Hg

end direct_limit

end add_comm_group


namespace ring

variables [Π i, ring (G i)]
variables (f : Π i j, i ≤ j → G i → G j) [Π i j hij, is_ring_hom (f i j hij)]
variables [add_comm_group.directed_system G f]

open free_comm_ring

def thing1 : set (free_comm_ring Σ i, G i) :=
⋃ i j H, set.range $ λ x, of ⟨j, f i j H x⟩ - of ⟨i, x⟩

def thing2 : set (free_comm_ring Σ i, G i) :=
set.range $ λ i, of ⟨i, 1⟩ - 1

def thing3 : set (free_comm_ring Σ i, G i) :=
⋃ i x, set.range $ λ y, of ⟨i, x + y⟩ - (of ⟨i, x⟩ + of ⟨i, y⟩)

def thing4 : set (free_comm_ring Σ i, G i) :=
⋃ i x, set.range $ λ y, of ⟨i, x * y⟩ - (of ⟨i, x⟩ * of ⟨i, y⟩)

def direct_limit : Type (max v w) :=
(ideal.span (thing1 G f ∪ thing2 G ∪ thing3 G ∪ thing4 G)).quotient

namespace direct_limit

instance : comm_ring (direct_limit G f) :=
ideal.quotient.comm_ring _

def of (i) (x : G i) : direct_limit G f :=
ideal.quotient.mk _ $ of ⟨i, x⟩

instance of.is_ring_hom (i) : is_ring_hom (of G f i) :=
{ map_one := ideal.quotient.eq.2 $ subset_span $ or.inl $ or.inl $ or.inr $ set.mem_range_self i,
  map_mul := λ x y, ideal.quotient.eq.2 $ subset_span $ or.inr $ set.mem_Union.2 ⟨i,
    set.mem_Union.2 ⟨x, set.mem_range_self y⟩⟩,
  map_add := λ x y, ideal.quotient.eq.2 $ subset_span $ or.inl $ or.inr $ set.mem_Union.2 ⟨i,
    set.mem_Union.2 ⟨x, set.mem_range_self y⟩⟩ }

theorem of_f {i j} (hij : i ≤ j) (x : G i) : of G f j (f i j hij x) = of G f i x :=
ideal.quotient.eq.2 $ subset_span $ or.inl $ or.inl $ or.inl $ set.mem_Union.2 ⟨i, set.mem_Union.2
⟨j, set.mem_Union.2 ⟨hij, set.mem_range_self _⟩⟩⟩

theorem exists_of (z : direct_limit G f) : ∃ i x, of G f i x = z :=
nonempty.elim (by apply_instance) $ assume ind : ι,
quotient.induction_on' z $ λ x, free_abelian_group.induction_on x
  ⟨ind, 0, is_ring_hom.map_zero (of G f ind)⟩
  (λ s, multiset.induction_on s
    ⟨ind, 1, is_ring_hom.map_one (of G f ind)⟩
    (λ a s ih, let ⟨i, x⟩ := a, ⟨j, y, hs⟩ := ih, ⟨k, hik, hjk⟩ := directed_order.directed i j in
      ⟨k, f i k hik x * f j k hjk y, by rw [is_ring_hom.map_mul (of G f k), of_f, of_f, hs]; refl⟩))
  (λ s ⟨i, x, ih⟩, ⟨i, -x, by rw [is_ring_hom.map_neg (of G f i), ih]; refl⟩)
  (λ p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, f i k hik x + f j k hjk y, by rw [is_ring_hom.map_add (of G f k), of_f, of_f, ihx, ihy]; refl⟩)

@[elab_as_eliminator] theorem induction_on {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of G f i x)) : C z :=
let ⟨i, x, hx⟩ := exists_of G f z in hx ▸ ih i x

variables (P : Type u₁) [comm_ring P]
variables (g : Π i, G i → P) [Π i, is_ring_hom (g i)]
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
include Hg

open free_comm_ring

def rec : direct_limit G f → P :=
ideal.quotient.lift _ (free_comm_ring.lift $ λ x, g x.1 x.2) begin
  suffices : ideal.span (thing1 G f ∪ thing2 G ∪ thing3 G ∪ thing4 G) ≤
    ideal.comap (free_comm_ring.lift (λ (x : Σ (i : ι), G i), g (x.fst) (x.snd))) ⊥,
  { intros x hx, exact (mem_bot P).1 (this hx) },
  rw ideal.span_le, intros x hx,
  simp only [thing1, thing2, thing3, thing4, set.mem_union, set.mem_Union, set.mem_range] at hx,
  rw [mem_coe, ideal.mem_comap, mem_bot],
  rcases hx with ⟨⟨i, j, hij, x, rfl⟩ | hx⟩,
  { simp only [lift_sub, lift_of, Hg, sub_self] },
  { rcases hx with ⟨i, rfl⟩, simp only [lift_sub, lift_of, lift_one, is_ring_hom.map_one (g i), sub_self] },
  { rcases hx with ⟨i, x, y, rfl⟩, simp only [lift_sub, lift_of, lift_add, is_ring_hom.map_add (g i), sub_self] },
  { rcases hx with ⟨i, x, y, rfl⟩, simp only [lift_sub, lift_of, lift_mul, is_ring_hom.map_mul (g i), sub_self] }
end

instance rec.is_ring_hom : is_ring_hom (rec G f P g Hg) :=
⟨free_comm_ring.lift_one _,
λ x y, quotient.induction_on₂' x y $ λ p q, free_comm_ring.lift_mul _ _ _,
λ x y, quotient.induction_on₂' x y $ λ p q, free_comm_ring.lift_add _ _ _⟩

end direct_limit

end ring


namespace field

variables [Π i, field (G i)]
variables (f : Π i j, i ≤ j → G i → G j) [Π i j hij, is_field_hom (f i j hij)]
variables [add_comm_group.directed_system G f]

instance direct_limit.nonzero_comm_ring : nonzero_comm_ring (ring.direct_limit G f) :=
{ zero_ne_one := sorry,
  .. ring.direct_limit.comm_ring G f }

instance direct_limit.is_division_ring : is_division_ring (ring.direct_limit G f) :=
{ exists_inv := λ x, sorry }

def direct_limit : Type (max v w) :=
to_field (ring.direct_limit G f)

instance : field (direct_limit G f) :=
@to_field.field (ring.direct_limit G f) (field.direct_limit.nonzero_comm_ring G f) (field.direct_limit.is_division_ring G f)

end field
