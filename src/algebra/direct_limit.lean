/-
Copyright (c) 2019 Kenny Lau, Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes
-/
import ring_theory.free_comm_ring
import linear_algebra.direct_sum_module
import data.finset.order
/-!
# Direct limit of modules, abelian groups, rings, and fields.

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable modules over the same ring,
or incomparable abelian groups, or rings, or fields.

It is constructed as a quotient of the free module (for the module case) or quotient of
the free commutative ring (for the ring case) instead of a quotient of the disjoint union
so as to make the operations (addition etc.) "computable".

-/
universes u v w u₁

open submodule

variables {R : Type u} [ring R]
variables {ι : Type v} [nonempty ι]
variables [decidable_eq ι] [directed_order ι]
variables (G : ι → Type w) [Π i, decidable_eq (G i)]

/-- A directed system is a functor from the category (directed poset) to another category.
This is used for abelian groups and rings and fields because their maps are not bundled.
See module.directed_system -/
class directed_system (f : Π i j, i ≤ j → G i → G j) : Prop :=
(map_self [] : ∀ i x h, f i i h x = x)
(map_map [] : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

namespace module

variables [Π i, add_comm_group (G i)] [Π i, module R (G i)]

/-- A directed system is a functor from the category (directed poset) to the category of R-modules. -/
class directed_system (f : Π i j, i ≤ j → G i →ₗ[R] G j) : Prop :=
(map_self [] : ∀ i x h, f i i h x = x)
(map_map [] : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

variables (f : Π i j, i ≤ j → G i →ₗ[R] G j) [directed_system G f]

/-- The direct limit of a directed system is the modules glued together along the maps. -/
def direct_limit : Type (max v w) :=
(span R $ { a | ∃ (i j) (H : i ≤ j) x,
  direct_sum.lof R ι G i x - direct_sum.lof R ι G j (f i j H x) = a }).quotient

namespace direct_limit

instance : add_comm_group (direct_limit G f) := quotient.add_comm_group _
instance : semimodule R (direct_limit G f) := quotient.semimodule _

variables (R ι)
/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →ₗ[R] direct_limit G f :=
(mkq _).comp $ direct_sum.lof R ι G i
variables {R ι G f}

@[simp] lemma of_f {i j hij x} : (of R ι G f j (f i j hij x)) = of R ι G f i x :=
eq.symm $ (submodule.quotient.eq _).2 $ subset_span ⟨i, j, hij, x, rfl⟩

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of (z : direct_limit G f) : ∃ i x, of R ι G f i x = z :=
nonempty.elim (by apply_instance) $ assume ind : ι,
quotient.induction_on' z $ λ z, direct_sum.induction_on z
  ⟨ind, 0, linear_map.map_zero _⟩
  (λ i x, ⟨i, x, rfl⟩)
  (λ p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, f i k hik x + f j k hjk y, by rw [linear_map.map_add, of_f, of_f, ihx, ihy]; refl⟩)

@[elab_as_eliminator]
protected theorem induction_on {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of R ι G f i x)) : C z :=
let ⟨i, x, h⟩ := exists_of z in h ▸ ih i x

variables {P : Type u₁} [add_comm_group P] [module R P] (g : Π i, G i →ₗ[R] P)
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
include Hg

variables (R ι G f)
/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : direct_limit G f →ₗ[R] P :=
liftq _ (direct_sum.to_module R ι P g)
  (span_le.2 $ λ a ⟨i, j, hij, x, hx⟩, by rw [← hx, mem_coe, linear_map.sub_mem_ker_iff,
    direct_sum.to_module_lof, direct_sum.to_module_lof, Hg])
variables {R ι G f}

omit Hg
lemma lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x :=
direct_sum.to_module_lof R _ _

theorem lift_unique (F : direct_limit G f →ₗ[R] P) (x) :
  F x = lift R ι G f (λ i, F.comp $ of R ι G f i)
    (λ i j hij x, by rw [linear_map.comp_apply, of_f]; refl) x :=
direct_limit.induction_on x $ λ i x, by rw lift_of; refl

section totalize
open_locale classical
variables (G f)
noncomputable def totalize : Π i j, G i →ₗ[R] G j :=
λ i j, if h : i ≤ j then f i j h else 0
variables {G f}

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
  rw [← @dfinsupp.sum_single ι G _ _ _ x],
  unfold dfinsupp.sum,
  simp only [linear_map.map_sum],
  refine finset.sum_congr rfl (λ k hk, _),
  rw direct_sum.single_eq_lof R k (x k),
  simp [totalize_apply, hx k hk, le_trans (hx k hk) hij, directed_system.map_map f]
end

lemma of.zero_exact_aux {x : direct_sum ι G} (H : submodule.quotient.mk x = (0 : direct_limit G f)) :
  ∃ j, (∀ k ∈ x.support, k ≤ j) ∧ direct_sum.to_module R ι (G j) (λ i, totalize G f i j) x = (0 : G j) :=
nonempty.elim (by apply_instance) $ assume ind : ι,
span_induction ((quotient.mk_eq_zero _).1 H)
  (λ x ⟨i, j, hij, y, hxy⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
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
        directed_system.map_map f, direct_sum.apply_eq_component,
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
          to_module_totalize_of_le hik hi,
          to_module_totalize_of_le hjk hj]⟩)
  (λ a x ⟨i, hi, hxi⟩,
    ⟨i, λ k hk, hi k (dfinsupp.support_smul hk),
      by simp [linear_map.map_smul, hxi]⟩)

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact {i x} (H : of R ι G f i x = 0) :
  ∃ j hij, f i j hij x = (0 : G j) :=
let ⟨j, hj, hxj⟩ := of.zero_exact_aux H in
if hx0 : x = 0 then ⟨i, le_refl _, by simp [hx0]⟩
else
  have hij : i ≤ j, from hj _ $
    by simp [direct_sum.apply_eq_component, hx0],
  ⟨j, hij, by simpa [totalize_apply, hij] using hxj⟩

end direct_limit

end module


namespace add_comm_group

variables [Π i, add_comm_group (G i)]

/-- The direct limit of a directed system is the abelian groups glued together along the maps. -/
def direct_limit (f : Π i j, i ≤ j → G i → G j)
  [Π i j hij, is_add_group_hom (f i j hij)] [directed_system G f] : Type* :=
@module.direct_limit ℤ _ ι _ _ _ G _ _ _
  (λ i j hij, (add_monoid_hom.of $ f i j hij).to_int_linear_map)
  ⟨directed_system.map_self f, directed_system.map_map f⟩

namespace direct_limit

variables (f : Π i j, i ≤ j → G i → G j)
variables [Π i j hij, is_add_group_hom (f i j hij)] [directed_system G f]

lemma directed_system :
  module.directed_system G (λ i j hij, (add_monoid_hom.of $ f i j hij).to_int_linear_map) :=
⟨directed_system.map_self f, directed_system.map_map f⟩

local attribute [instance] directed_system

instance : add_comm_group (direct_limit G f) :=
module.direct_limit.add_comm_group G (λ i j hij, (add_monoid_hom.of $f i j hij).to_int_linear_map)


/-- The canonical map from a component to the direct limit. -/
def of (i) : G i → direct_limit G f :=
module.direct_limit.of ℤ ι G (λ i j hij, (add_monoid_hom.of $ f i j hij).to_int_linear_map) i
variables {G f}

instance of.is_add_group_hom (i) : is_add_group_hom (of G f i) :=
linear_map.is_add_group_hom _

@[simp] lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
module.direct_limit.of_f

@[simp] lemma of_zero (i) : of G f i 0 = 0 := is_add_group_hom.map_zero _
@[simp] lemma of_add (i x y) : of G f i (x + y) = of G f i x + of G f i y := is_add_hom.map_add _ _ _
@[simp] lemma of_neg (i x) : of G f i (-x) = -of G f i x := is_add_group_hom.map_neg _ _
@[simp] lemma of_sub (i x y) : of G f i (x - y) = of G f i x - of G f i y := is_add_group_hom.map_sub _ _ _

@[elab_as_eliminator]
protected theorem induction_on {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of G f i x)) : C z :=
module.direct_limit.induction_on z ih

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact (i x) (h : of G f i x = 0) : ∃ j hij, f i j hij x = 0 :=
module.direct_limit.of.zero_exact h

variables (P : Type u₁) [add_comm_group P]
variables (g : Π i, G i → P) [Π i, is_add_group_hom (g i)]
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variables (G f)
/-- The universal property of the direct limit: maps from the components to another abelian group
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : direct_limit G f → P :=
module.direct_limit.lift ℤ ι G (λ i j hij, (add_monoid_hom.of $ f i j hij).to_int_linear_map)
  (λ i, (add_monoid_hom.of $ g i).to_int_linear_map) Hg
variables {G f}

instance lift.is_add_group_hom : is_add_group_hom (lift G f P g Hg) :=
linear_map.is_add_group_hom _

@[simp] lemma lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
module.direct_limit.lift_of _ _ _

@[simp] lemma lift_zero : lift G f P g Hg 0 = 0 := is_add_group_hom.map_zero _
@[simp] lemma lift_add (x y) : lift G f P g Hg (x + y) = lift G f P g Hg x + lift G f P g Hg y := is_add_hom.map_add _ _ _
@[simp] lemma lift_neg (x) : lift G f P g Hg (-x) = -lift G f P g Hg x := is_add_group_hom.map_neg _ _
@[simp] lemma lift_sub (x y) : lift G f P g Hg (x - y) = lift G f P g Hg x - lift G f P g Hg y := is_add_group_hom.map_sub _ _ _

lemma lift_unique (F : direct_limit G f → P) [is_add_group_hom F] (x) :
  F x = @lift _ _ _ _ G _ _ f _ _ P _ (λ i x, F $ of G f i x) (λ i, is_add_group_hom.comp _ _)
    (λ i j hij x, by dsimp; rw of_f) x :=
direct_limit.induction_on x $ λ i x, by rw lift_of

end direct_limit

end add_comm_group


namespace ring

variables [Π i, comm_ring (G i)]
variables (f : Π i j, i ≤ j → G i → G j)
variables [Π i j hij, is_ring_hom (f i j hij)]
variables [directed_system G f]

open free_comm_ring

/-- The direct limit of a directed system is the rings glued together along the maps. -/
def direct_limit : Type (max v w) :=
(ideal.span { a | (∃ i j H x, of (⟨j, f i j H x⟩ : Σ i, G i) - of ⟨i, x⟩ = a) ∨
  (∃ i, of (⟨i, 1⟩ : Σ i, G i) - 1 = a) ∨
  (∃ i x y, of (⟨i, x + y⟩ : Σ i, G i) - (of ⟨i, x⟩ + of ⟨i, y⟩) = a) ∨
  (∃ i x y, of (⟨i, x * y⟩ : Σ i, G i) - (of ⟨i, x⟩ * of ⟨i, y⟩) = a) }).quotient

namespace direct_limit

instance : comm_ring (direct_limit G f) :=
ideal.quotient.comm_ring _

instance : ring (direct_limit G f) :=
comm_ring.to_ring _

/-- The canonical map from a component to the direct limit. -/
def of (i) (x : G i) : direct_limit G f :=
ideal.quotient.mk _ (of (⟨i, x⟩ : Σ i, G i))

variables {G f}

instance of.is_ring_hom (i) : is_ring_hom (of G f i) :=
{ map_one := ideal.quotient.eq.2 $ subset_span $ or.inr $ or.inl ⟨i, rfl⟩,
  map_mul := λ x y, ideal.quotient.eq.2 $ subset_span $ or.inr $ or.inr $ or.inr ⟨i, x, y, rfl⟩,
  map_add := λ x y, ideal.quotient.eq.2 $ subset_span $ or.inr $ or.inr $ or.inl ⟨i, x, y, rfl⟩ }

@[simp] lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
ideal.quotient.eq.2 $ subset_span $ or.inl ⟨i, j, hij, x, rfl⟩

@[simp] lemma of_zero (i) : of G f i 0 = 0 := is_ring_hom.map_zero _
@[simp] lemma of_one (i) : of G f i 1 = 1 := is_ring_hom.map_one _
@[simp] lemma of_add (i x y) : of G f i (x + y) = of G f i x + of G f i y := is_ring_hom.map_add _
@[simp] lemma of_neg (i x) : of G f i (-x) = -of G f i x := is_ring_hom.map_neg _
@[simp] lemma of_sub (i x y) : of G f i (x - y) = of G f i x - of G f i y := is_ring_hom.map_sub _
@[simp] lemma of_mul (i x y) : of G f i (x * y) = of G f i x * of G f i y := is_ring_hom.map_mul _
@[simp] lemma of_pow (i x) (n : ℕ) : of G f i (x ^ n) = of G f i x ^ n := is_semiring_hom.map_pow _ _ _

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of (z : direct_limit G f) : ∃ i x, of G f i x = z :=
nonempty.elim (by apply_instance) $ assume ind : ι,
quotient.induction_on' z $ λ x, free_abelian_group.induction_on x
  ⟨ind, 0, of_zero ind⟩
  (λ s, multiset.induction_on s
    ⟨ind, 1, of_one ind⟩
    (λ a s ih, let ⟨i, x⟩ := a, ⟨j, y, hs⟩ := ih, ⟨k, hik, hjk⟩ := directed_order.directed i j in
      ⟨k, f i k hik x * f j k hjk y, by rw [of_mul, of_f, of_f, hs]; refl⟩))
  (λ s ⟨i, x, ih⟩, ⟨i, -x, by rw [of_neg, ih]; refl⟩)
  (λ p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, f i k hik x + f j k hjk y, by rw [of_add, of_f, of_f, ihx, ihy]; refl⟩)

@[elab_as_eliminator] theorem induction_on {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of G f i x)) : C z :=
let ⟨i, x, hx⟩ := exists_of z in hx ▸ ih i x

section of_zero_exact
open_locale classical
variables (G f)
lemma of.zero_exact_aux2 {x : free_comm_ring Σ i, G i} {s t} (hxs : is_supported x s) {j k}
  (hj : ∀ z : Σ i, G i, z ∈ s → z.1 ≤ j) (hk : ∀ z : Σ i, G i, z ∈ t → z.1 ≤ k)
  (hjk : j ≤ k) (hst : s ⊆ t) :
  f j k hjk (lift (λ ix : s, f ix.1.1 j (hj ix ix.2) ix.1.2) (restriction s x)) =
  lift (λ ix : t, f ix.1.1 k (hk ix ix.2) ix.1.2) (restriction t x) :=
begin
  refine ring.in_closure.rec_on hxs _ _ _ _,
  { rw [restriction_one, lift_one, is_ring_hom.map_one (f j k hjk), restriction_one, lift_one] },
  { rw [restriction_neg, restriction_one, lift_neg, lift_one,
      is_ring_hom.map_neg (f j k hjk), is_ring_hom.map_one (f j k hjk),
      restriction_neg, restriction_one, lift_neg, lift_one] },
  { rintros _ ⟨p, hps, rfl⟩ n ih,
    rw [restriction_mul, lift_mul, is_ring_hom.map_mul (f j k hjk), ih, restriction_mul, lift_mul,
        restriction_of, dif_pos hps, lift_of, restriction_of, dif_pos (hst hps), lift_of],
    dsimp only, rw directed_system.map_map f, refl },
  { rintros x y ihx ihy,
    rw [restriction_add, lift_add, is_ring_hom.map_add (f j k hjk), ihx, ihy, restriction_add, lift_add] }
end
variables {G f}

lemma of.zero_exact_aux {x : free_comm_ring Σ i, G i} (H : ideal.quotient.mk _ x = (0 : direct_limit G f)) :
  ∃ j s, ∃ H : (∀ k : Σ i, G i, k ∈ s → k.1 ≤ j), is_supported x s ∧
    lift (λ ix : s, f ix.1.1 j (H ix ix.2) ix.1.2) (restriction s x) = (0 : G j) :=
begin
  refine span_induction (ideal.quotient.eq_zero_iff_mem.1 H) _ _ _ _,
  { rintros x (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩),
    { refine ⟨j, {⟨i, x⟩, ⟨j, f i j hij x⟩}, _,
        is_supported_sub (is_supported_of.2 $ or.inr rfl) (is_supported_of.2 $ or.inl rfl), _⟩,
      { rintros k (rfl | ⟨rfl | _⟩), exact hij, refl },
      { rw [restriction_sub, lift_sub, restriction_of, dif_pos, restriction_of, dif_pos, lift_of, lift_of],
        dsimp only, rw directed_system.map_map f, exact sub_self _,
        exacts [or.inr rfl, or.inl rfl] } },
    { refine ⟨i, {⟨i, 1⟩}, _, is_supported_sub (is_supported_of.2 rfl) is_supported_one, _⟩,
      { rintros k (rfl|h), refl },
      { rw [restriction_sub, lift_sub, restriction_of, dif_pos, restriction_one, lift_of, lift_one],
        dsimp only, rw [is_ring_hom.map_one (f i i _), sub_self], exacts [_inst_7 i i _, rfl] } },
    { refine ⟨i, {⟨i, x+y⟩, ⟨i, x⟩, ⟨i, y⟩}, _,
        is_supported_sub (is_supported_of.2 $ or.inl rfl)
          (is_supported_add (is_supported_of.2 $ or.inr $ or.inl rfl)
            (is_supported_of.2 $ or.inr $ or.inr rfl)), _⟩,
      { rintros k (rfl | ⟨rfl | ⟨rfl | hk⟩⟩); refl },
      { rw [restriction_sub, restriction_add, restriction_of, restriction_of, restriction_of,
          dif_pos, dif_pos, dif_pos, lift_sub, lift_add, lift_of, lift_of, lift_of],
        dsimp only, rw is_ring_hom.map_add (f i i _), exact sub_self _,
        exacts [or.inl rfl, by apply_instance, or.inr (or.inr rfl), or.inr (or.inl rfl)] } },
    { refine ⟨i, {⟨i, x*y⟩, ⟨i, x⟩, ⟨i, y⟩}, _,
        is_supported_sub (is_supported_of.2 $ or.inl rfl)
          (is_supported_mul (is_supported_of.2 $ or.inr $ or.inl rfl)
            (is_supported_of.2 $ or.inr $ or.inr rfl)), _⟩,
      { rintros k (rfl | ⟨rfl | ⟨rfl | hk⟩⟩); refl },
      { rw [restriction_sub, restriction_mul, restriction_of, restriction_of, restriction_of,
          dif_pos, dif_pos, dif_pos, lift_sub, lift_mul, lift_of, lift_of, lift_of],
        dsimp only, rw is_ring_hom.map_mul (f i i _),
        exacts [sub_self _, or.inl rfl, by apply_instance, or.inr (or.inr rfl),
          or.inr (or.inl rfl)] } } },
  { refine nonempty.elim (by apply_instance) (assume ind : ι, _),
    refine ⟨ind, ∅, λ _, false.elim, is_supported_zero, _⟩,
    rw [restriction_zero, lift_zero] },
  { rintros x y ⟨i, s, hi, hxs, ihs⟩ ⟨j, t, hj, hyt, iht⟩,
    rcases directed_order.directed i j with ⟨k, hik, hjk⟩,
    have : ∀ z : Σ i, G i, z ∈ s ∪ t → z.1 ≤ k,
    { rintros z (hz | hz), exact le_trans (hi z hz) hik, exact le_trans (hj z hz) hjk },
    refine ⟨k, s ∪ t, this, is_supported_add (is_supported_upwards hxs $ set.subset_union_left s t)
      (is_supported_upwards hyt $ set.subset_union_right s t), _⟩,
    { rw [restriction_add, lift_add,
        ← of.zero_exact_aux2 G f hxs hi this hik (set.subset_union_left s t),
        ← of.zero_exact_aux2 G f hyt hj this hjk (set.subset_union_right s t),
        ihs, is_ring_hom.map_zero (f i k hik), iht, is_ring_hom.map_zero (f j k hjk), zero_add] } },
  { rintros x y ⟨j, t, hj, hyt, iht⟩, rw smul_eq_mul,
    rcases exists_finset_support x with ⟨s, hxs⟩,
    rcases (s.image sigma.fst).exists_le with ⟨i, hi⟩,
    rcases directed_order.directed i j with ⟨k, hik, hjk⟩,
    have : ∀ z : Σ i, G i, z ∈ ↑s ∪ t → z.1 ≤ k,
    { rintros z (hz | hz), exact le_trans (hi z.1 $ finset.mem_image.2 ⟨z, hz, rfl⟩) hik, exact le_trans (hj z hz) hjk },
    refine ⟨k, ↑s ∪ t, this, is_supported_mul (is_supported_upwards hxs $ set.subset_union_left ↑s t)
      (is_supported_upwards hyt $ set.subset_union_right ↑s t), _⟩,
    rw [restriction_mul, lift_mul,
        ← of.zero_exact_aux2 G f hyt hj this hjk (set.subset_union_right ↑s t),
        iht, is_ring_hom.map_zero (f j k hjk), mul_zero] }
end

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
lemma of.zero_exact {i x} (hix : of G f i x = 0) : ∃ j, ∃ hij : i ≤ j, f i j hij x = 0 :=
let ⟨j, s, H, hxs, hx⟩ := of.zero_exact_aux hix in
have hixs : (⟨i, x⟩ : Σ i, G i) ∈ s, from is_supported_of.1 hxs,
⟨j, H ⟨i, x⟩ hixs, by rw [restriction_of, dif_pos hixs, lift_of] at hx; exact hx⟩
end of_zero_exact

/-- If the maps in the directed system are injective, then the canonical maps
from the components to the direct limits are injective. -/
theorem of_injective (hf : ∀ i j hij, function.injective (f i j hij)) (i) :
  function.injective (of G f i) :=
begin
  suffices : ∀ x, of G f i x = 0 → x = 0,
  { intros x y hxy, rw ← sub_eq_zero_iff_eq, apply this,
    rw [is_ring_hom.map_sub (of G f i), hxy, sub_self] },
  intros x hx, rcases of.zero_exact hx with ⟨j, hij, hfx⟩,
  apply hf i j hij, rw [hfx, is_ring_hom.map_zero (f i j hij)]
end

variables (P : Type u₁) [comm_ring P]
variables (g : Π i, G i → P) [Π i, is_ring_hom (g i)]
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
include Hg

open free_comm_ring

variables (G f)
/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.

We don't use this function as the canonical form because Lean 3 fails to automatically coerce
it to a function; use `lift` instead. -/
def lift_hom : direct_limit G f →+* P :=
ideal.quotient.lift _ (free_comm_ring.lift_hom $ λ x, g x.1 x.2) begin
  suffices : ideal.span _ ≤
    ideal.comap (free_comm_ring.lift_hom (λ (x : Σ (i : ι), G i), g (x.fst) (x.snd))) ⊥,
  { intros x hx, exact (mem_bot P).1 (this hx) },
  rw ideal.span_le, intros x hx,
  rw [mem_coe, ideal.mem_comap, mem_bot],
  rcases hx with ⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩;
  simp only [coe_lift_hom, lift_sub, lift_of, Hg, lift_one, lift_add, lift_mul,
      is_ring_hom.map_one (g i), is_ring_hom.map_add (g i), is_ring_hom.map_mul (g i), sub_self]
end

/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : direct_limit G f → P := lift_hom G f P g Hg

instance lift_is_ring_hom : is_ring_hom (lift G f P g Hg) := (lift_hom G f P g Hg).is_ring_hom

variables {G f}
omit Hg

@[simp] lemma lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := free_comm_ring.lift_of _ _
@[simp] lemma lift_zero : lift G f P g Hg 0 = 0 := (lift_hom G f P g Hg).map_zero
@[simp] lemma lift_one : lift G f P g Hg 1 = 1 := (lift_hom G f P g Hg).map_one
@[simp] lemma lift_add (x y) : lift G f P g Hg (x + y) = lift G f P g Hg x + lift G f P g Hg y :=
(lift_hom G f P g Hg).map_add x y
@[simp] lemma lift_neg (x) : lift G f P g Hg (-x) = -lift G f P g Hg x :=
(lift_hom G f P g Hg).map_neg x
@[simp] lemma lift_sub (x y) : lift G f P g Hg (x - y) = lift G f P g Hg x - lift G f P g Hg y :=
(lift_hom G f P g Hg).map_sub x y
@[simp] lemma lift_mul (x y) : lift G f P g Hg (x * y) = lift G f P g Hg x * lift G f P g Hg y :=
(lift_hom G f P g Hg).map_mul x y
@[simp] lemma lift_pow (x) (n : ℕ) : lift G f P g Hg (x ^ n) = lift G f P g Hg x ^ n :=
(lift_hom G f P g Hg).map_pow x n

local attribute [instance, priority 100] is_ring_hom.comp
theorem lift_unique (F : direct_limit G f → P) [is_ring_hom F] (x) :
  F x = lift G f P (λ i x, F $ of G f i x) (λ i j hij x, by rw [of_f]) x :=
direct_limit.induction_on x $ λ i x, by rw lift_of

end direct_limit

end ring


namespace field

variables [Π i, field (G i)]
variables (f : Π i j, i ≤ j → G i → G j) [Π i j hij, is_ring_hom (f i j hij)]
variables [directed_system G f]

namespace direct_limit

instance nontrivial : nontrivial (ring.direct_limit G f) :=
⟨⟨0, 1, nonempty.elim (by apply_instance) $ assume i : ι, begin
  change (0 : ring.direct_limit G f) ≠ 1,
  rw ← ring.direct_limit.of_one,
  intros H, rcases ring.direct_limit.of.zero_exact H.symm with ⟨j, hij, hf⟩,
  rw is_ring_hom.map_one (f i j hij) at hf,
  exact one_ne_zero hf
end ⟩⟩

theorem exists_inv {p : ring.direct_limit G f} : p ≠ 0 → ∃ y, p * y = 1 :=
ring.direct_limit.induction_on p $ λ i x H,
⟨ring.direct_limit.of G f i (x⁻¹), by erw [← ring.direct_limit.of_mul,
    mul_inv_cancel (assume h : x = 0, H $ by rw [h, ring.direct_limit.of_zero]),
    ring.direct_limit.of_one]⟩

section
open_locale classical

noncomputable def inv (p : ring.direct_limit G f) : ring.direct_limit G f :=
if H : p = 0 then 0 else classical.some (direct_limit.exists_inv G f H)

protected theorem mul_inv_cancel {p : ring.direct_limit G f} (hp : p ≠ 0) : p * inv G f p = 1 :=
by rw [inv, dif_neg hp, classical.some_spec (direct_limit.exists_inv G f hp)]

protected theorem inv_mul_cancel {p : ring.direct_limit G f} (hp : p ≠ 0) : inv G f p * p = 1 :=
by rw [_root_.mul_comm, direct_limit.mul_inv_cancel G f hp]

protected noncomputable def field : field (ring.direct_limit G f) :=
{ inv := inv G f,
  mul_inv_cancel := λ p, direct_limit.mul_inv_cancel G f,
  inv_zero := dif_pos rfl,
  .. ring.direct_limit.comm_ring G f,
  .. direct_limit.nontrivial G f }

end

end direct_limit

end field
