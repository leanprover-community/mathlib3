import linear_algebra.direct_sum_module linear_algebra.linear_combination tactic.linarith

universes u v w u₁

open lattice submodule

class directed_order (α : Type u) extends partial_order α :=
(directed : ∀ i j : α, ∃ k, i ≤ k ∧ j ≤ k)

variables {R : Type u} [ring R]
variables {ι : Type v} [inhabited ι]
variables [directed_order ι] [decidable_eq ι]
variables (G : ι → Type w) [Π i, decidable_eq (G i)] [Π i, add_comm_group (G i)]

namespace module

variables [Π i, module R (G i)]

class directed_system (f : Π i j, i ≤ j → G i →ₗ[R] G j) : Prop :=
(Hid : ∀ i x, f i i (le_refl i) x = x)
(Hcomp : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

variables (f : Π i j, i ≤ j → G i →ₗ[R] G j) [directed_system G f]

def thing : set (direct_sum ι G) :=
⋃ i j (H : i ≤ j) x, { direct_sum.lof R ι G i x - direct_sum.lof R ι G j (f i j H x) }

def direct_limit : Type (max v w) :=
(span R $ thing G f).quotient

variables {G f}
lemma mem_thing {a : direct_sum ι G} : a ∈ thing G f ↔ ∃ (i j) (H : i ≤ j) x,
  a = direct_sum.lof R ι G i x - direct_sum.lof R ι G j (f i j H x) :=
by simp only [thing, set.mem_Union, set.mem_singleton_iff]
variables (G f)

namespace direct_limit

instance : add_comm_group (direct_limit G f) := quotient.add_comm_group _
instance : module R (direct_limit G f) := quotient.module _

variables (ι R)
def of (i) : G i →ₗ[R] direct_limit G f :=
(mkq _).comp $ direct_sum.lof R ι G i
variables {ι R}

theorem of_f {i j hij x} : (of R ι G f j (f i j hij x)) = of R ι G f i x :=
eq.symm $ (submodule.quotient.eq _).2 $ subset_span $
set.mem_Union.2 ⟨i, set.mem_Union.2 ⟨j, set.mem_Union.2 ⟨hij, set.mem_Union.2 ⟨x, or.inl rfl⟩⟩⟩⟩

variables {P : Type u₁} [add_comm_group P] [module R P] (g : Π i, G i →ₗ[R] P)
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
include Hg

variables (ι R)
def rec : direct_limit G f →ₗ[R] P :=
liftq _ (direct_sum.to_module R ι P g)
  (span_le.2 $ set.Union_subset $ λ i,
    set.Union_subset $ λ j, set.Union_subset $ λ hij, set.Union_subset $ λ x,
      set.singleton_subset_iff.2 $ linear_map.sub_mem_ker_iff.2 $
        by rw [direct_sum.to_module_lof, direct_sum.to_module_lof, Hg])

variables {ι R}

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
quotient.induction_on' z $ λ z, direct_sum.induction_on z
  ⟨default _, 0, (linear_map.map_zero _).symm⟩
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
  ⟨default ι, λ _ h, (finset.not_mem_empty _ h).elim, linear_map.map_zero _⟩
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

instance : add_comm_group (direct_limit G f) :=
@module.direct_limit.add_comm_group _ _ _ _ _ _ _ _ _ _
  (λ i j hij, is_add_group_hom.to_linear_map $ f i j hij)
  ⟨directed_system.Hid f, directed_system.Hcomp f⟩

end direct_limit

end add_comm_group
