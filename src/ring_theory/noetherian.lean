/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
import algebra.algebra.subalgebra.basic
import algebra.algebra.tower
import algebra.ring.idempotents
import group_theory.finiteness
import linear_algebra.linear_independent
import order.compactly_generated
import order.order_iso_nat
import ring_theory.finiteness
import ring_theory.nilpotent

/-!
# Noetherian rings and modules

The following are equivalent for a module M over a ring R:
1. Every increasing chain of submodules M₁ ⊆ M₂ ⊆ M₃ ⊆ ⋯ eventually stabilises.
2. Every submodule is finitely generated.

A module satisfying these equivalent conditions is said to be a *Noetherian* R-module.
A ring is a *Noetherian ring* if it is Noetherian as a module over itself.

(Note that we do not assume yet that our rings are commutative,
so perhaps this should be called "left Noetherian".
To avoid cumbersome names once we specialize to the commutative case,
we don't make this explicit in the declaration names.)

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module. It is a class,
  implemented as the predicate that all `R`-submodules of `M` are finitely generated.

## Main statements

* `is_noetherian_iff_well_founded` is the theorem that an R-module M is Noetherian iff
  `>` is well-founded on `submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `ring_theory.polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel1967]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/

open set
open_locale big_operators pointwise

/--
`is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module,
implemented as the predicate that all `R`-submodules of `M` are finitely generated.
-/
class is_noetherian (R M) [semiring R] [add_comm_monoid M] [module R M] : Prop :=
(noetherian : ∀ (s : submodule R M), s.fg)

section
variables {R : Type*} {M : Type*} {P : Type*}
variables [semiring R] [add_comm_monoid M] [add_comm_monoid P]
variables [module R M] [module R P]
open is_noetherian
include R

/-- An R-module is Noetherian iff all its submodules are finitely-generated. -/
lemma is_noetherian_def : is_noetherian R M ↔ ∀ (s : submodule R M), s.fg :=
⟨λ h, h.noetherian, is_noetherian.mk⟩

theorem is_noetherian_submodule {N : submodule R M} :
  is_noetherian R N ↔ ∀ s : submodule R M, s ≤ N → s.fg :=
begin
  refine ⟨λ ⟨hn⟩, λ s hs, have s ≤ N.subtype.range, from (N.range_subtype).symm ▸ hs,
    submodule.map_comap_eq_self this ▸ (hn _).map _, λ h, ⟨λ s, _⟩⟩,
  have f := (submodule.equiv_map_of_injective N.subtype subtype.val_injective s).symm,
  have h₁ := h (s.map N.subtype) (submodule.map_subtype_le N s),
  have h₂ : (⊤ : submodule R (s.map N.subtype)).map f = ⊤ := by simp,
  have h₃ := ((submodule.fg_top _).2 h₁).map (↑f : _ →ₗ[R] s),
  exact (submodule.fg_top _).1 (h₂ ▸ h₃),
end

theorem is_noetherian_submodule_left {N : submodule R M} :
  is_noetherian R N ↔ ∀ s : submodule R M, (N ⊓ s).fg :=
is_noetherian_submodule.trans
⟨λ H s, H _ inf_le_left, λ H s hs, (inf_of_le_right hs) ▸ H _⟩

theorem is_noetherian_submodule_right {N : submodule R M} :
  is_noetherian R N ↔ ∀ s : submodule R M, (s ⊓ N).fg :=
is_noetherian_submodule.trans
⟨λ H s, H _ inf_le_right, λ H s hs, (inf_of_le_left hs) ▸ H _⟩

instance is_noetherian_submodule' [is_noetherian R M] (N : submodule R M) : is_noetherian R N :=
is_noetherian_submodule.2 $ λ _ _, is_noetherian.noetherian _

lemma is_noetherian_of_le {s t : submodule R M} [ht : is_noetherian R t]
   (h : s ≤ t) : is_noetherian R s :=
is_noetherian_submodule.mpr (λ s' hs', is_noetherian_submodule.mp ht _ (le_trans hs' h))

variable (M)
theorem is_noetherian_of_surjective (f : M →ₗ[R] P) (hf : f.range = ⊤)
  [is_noetherian R M] : is_noetherian R P :=
⟨λ s, have (s.comap f).map f = s, from submodule.map_comap_eq_self $ hf.symm ▸ le_top,
this ▸ (noetherian _).map _⟩
variable {M}

theorem is_noetherian_of_linear_equiv (f : M ≃ₗ[R] P)
  [is_noetherian R M] : is_noetherian R P :=
is_noetherian_of_surjective _ f.to_linear_map f.range

lemma is_noetherian_top_iff :
  is_noetherian R (⊤ : submodule R M) ↔ is_noetherian R M :=
begin
  unfreezingI { split; assume h },
  { exact is_noetherian_of_linear_equiv (linear_equiv.of_top (⊤ : submodule R M) rfl) },
  { exact is_noetherian_of_linear_equiv (linear_equiv.of_top (⊤ : submodule R M) rfl).symm },
end

lemma is_noetherian_of_injective [is_noetherian R P] (f : M →ₗ[R] P) (hf : function.injective f) :
  is_noetherian R M :=
is_noetherian_of_linear_equiv (linear_equiv.of_injective f hf).symm

lemma fg_of_injective [is_noetherian R P] {N : submodule R M} (f : M →ₗ[R] P)
  (hf : function.injective f) : N.fg :=
@@is_noetherian.noetherian _ _ _ (is_noetherian_of_injective f hf) N

end

namespace module
variables {R M N : Type*}
variables [semiring R] [add_comm_monoid M] [add_comm_monoid N] [module R M] [module R N]

variables (R M)

@[priority 100] -- see Note [lower instance priority]
instance is_noetherian.finite [is_noetherian R M] : finite R M :=
⟨is_noetherian.noetherian ⊤⟩

variables {R M}

lemma finite.of_injective [is_noetherian R N] (f : M →ₗ[R] N)
  (hf : function.injective f) : finite R M :=
⟨fg_of_injective f hf⟩

end module

section
variables {R : Type*} {M : Type*} {P : Type*}
variables [ring R] [add_comm_group M] [add_comm_group P]
variables [module R M] [module R P]
open is_noetherian
include R

lemma is_noetherian_of_ker_bot [is_noetherian R P] (f : M →ₗ[R] P) (hf : f.ker = ⊥) :
  is_noetherian R M :=
is_noetherian_of_linear_equiv (linear_equiv.of_injective f $ linear_map.ker_eq_bot.mp hf).symm

lemma fg_of_ker_bot [is_noetherian R P] {N : submodule R M} (f : M →ₗ[R] P) (hf : f.ker = ⊥) :
  N.fg :=
@@is_noetherian.noetherian _ _ _ (is_noetherian_of_ker_bot f hf) N

instance is_noetherian_prod [is_noetherian R M]
  [is_noetherian R P] : is_noetherian R (M × P) :=
⟨λ s, submodule.fg_of_fg_map_of_fg_inf_ker (linear_map.snd R M P) (noetherian _) $
have s ⊓ linear_map.ker (linear_map.snd R M P) ≤ linear_map.range (linear_map.inl R M P),
from λ x ⟨hx1, hx2⟩, ⟨x.1, prod.ext rfl $ eq.symm $ linear_map.mem_ker.1 hx2⟩,
submodule.map_comap_eq_self this ▸ (noetherian _).map _⟩

instance is_noetherian_pi {R ι : Type*} {M : ι → Type*} [ring R]
  [Π i, add_comm_group (M i)] [Π i, module R (M i)] [finite ι]
  [∀ i, is_noetherian R (M i)] : is_noetherian R (Π i, M i) :=
begin
  casesI nonempty_fintype ι,
  haveI := classical.dec_eq ι,
  suffices on_finset : ∀ s : finset ι, is_noetherian R (Π i : s, M i),
  { let coe_e := equiv.subtype_univ_equiv finset.mem_univ,
    letI : is_noetherian R (Π i : finset.univ, M (coe_e i)) := on_finset finset.univ,
    exact is_noetherian_of_linear_equiv (linear_equiv.Pi_congr_left R M coe_e), },
  intro s,
  induction s using finset.induction with a s has ih,
  { exact ⟨λ s, by convert submodule.fg_bot⟩ },
  refine @is_noetherian_of_linear_equiv _ _ _ _ _ _ _ _
    _ (@is_noetherian_prod _ (M a) _ _ _ _ _ _ _ ih),
  fconstructor,
  { exact λ f i, or.by_cases (finset.mem_insert.1 i.2)
      (λ h : i.1 = a, show M i.1, from (eq.rec_on h.symm f.1))
      (λ h : i.1 ∈ s, show M i.1, from f.2 ⟨i.1, h⟩) },
  { intros f g, ext i, unfold or.by_cases, cases i with i hi,
    rcases finset.mem_insert.1 hi with rfl | h,
    { change _ = _ + _, simp only [dif_pos], refl },
    { change _ = _ + _, have : ¬i = a, { rintro rfl, exact has h },
      simp only [dif_neg this, dif_pos h], refl } },
  { intros c f, ext i, unfold or.by_cases, cases i with i hi,
    rcases finset.mem_insert.1 hi with rfl | h,
    { change _ = c • _, simp only [dif_pos], refl },
    { change _ = c • _, have : ¬i = a, { rintro rfl, exact has h },
      simp only [dif_neg this, dif_pos h], refl } },
  { exact λ f, (f ⟨a, finset.mem_insert_self _ _⟩, λ i, f ⟨i.1, finset.mem_insert_of_mem i.2⟩) },
  { intro f, apply prod.ext,
    { simp only [or.by_cases, dif_pos] },
    { ext ⟨i, his⟩,
      have : ¬i = a, { rintro rfl, exact has his },
      simp only [or.by_cases, this, not_false_iff, dif_neg] } },
  { intro f, ext ⟨i, hi⟩,
    rcases finset.mem_insert.1 hi with rfl | h,
    { simp only [or.by_cases, dif_pos], },
    { have : ¬i = a, { rintro rfl, exact has h },
      simp only [or.by_cases, dif_neg this, dif_pos h], } }
end

/-- A version of `is_noetherian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance is_noetherian_pi' {R ι M : Type*} [ring R] [add_comm_group M] [module R M] [finite ι]
  [is_noetherian R M] : is_noetherian R (ι → M) :=
is_noetherian_pi

end

open is_noetherian submodule function

section
universe w
variables {R M P : Type*} {N : Type w} [semiring R] [add_comm_monoid M] [module R M]
  [add_comm_monoid N] [module R N] [add_comm_monoid P] [module R P]

theorem is_noetherian_iff_well_founded :
  is_noetherian R M ↔ well_founded ((>) : submodule R M → submodule R M → Prop) :=
begin
  rw (complete_lattice.well_founded_characterisations $ submodule R M).out 0 3,
  exact ⟨λ ⟨h⟩, λ k, (fg_iff_compact k).mp (h k), λ h, ⟨λ k, (fg_iff_compact k).mpr (h k)⟩⟩,
end

lemma is_noetherian_iff_fg_well_founded :
  is_noetherian R M ↔ well_founded
    ((>) : { N : submodule R M // N.fg } → { N : submodule R M // N.fg } → Prop) :=
begin
  let α := { N : submodule R M // N.fg },
  split,
  { introI H,
    let f : α ↪o submodule R M := order_embedding.subtype _,
    exact order_embedding.well_founded f.dual (is_noetherian_iff_well_founded.mp H) },
  { intro H,
    constructor,
    intro N,
    obtain ⟨⟨N₀, h₁⟩, e : N₀ ≤ N, h₂⟩ := well_founded.well_founded_iff_has_max'.mp
      H { N' : α | N'.1 ≤ N } ⟨⟨⊥, submodule.fg_bot⟩, bot_le⟩,
    convert h₁,
    refine (e.antisymm _).symm,
    by_contra h₃,
    obtain ⟨x, hx₁ : x ∈ N, hx₂ : x ∉ N₀⟩ := set.not_subset.mp h₃,
    apply hx₂,
    have := h₂ ⟨(R ∙ x) ⊔ N₀, _⟩ _ _,
    { injection this with eq,
      rw ← eq,
      exact (le_sup_left : (R ∙ x) ≤ (R ∙ x) ⊔ N₀) (submodule.mem_span_singleton_self _) },
    { exact submodule.fg.sup ⟨{x}, by rw [finset.coe_singleton]⟩ h₁ },
    { exact sup_le ((submodule.span_singleton_le_iff_mem _ _).mpr hx₁) e },
    { show N₀ ≤ (R ∙ x) ⊔ N₀, from le_sup_right } }
end

variables (R M)

lemma well_founded_submodule_gt (R M) [semiring R] [add_comm_monoid M] [module R M] :
  ∀ [is_noetherian R M], well_founded ((>) : submodule R M → submodule R M → Prop) :=
is_noetherian_iff_well_founded.mp

variables {R M}

/-- A module is Noetherian iff every nonempty set of submodules has a maximal submodule among them.
-/
theorem set_has_maximal_iff_noetherian :
  (∀ a : set $ submodule R M, a.nonempty → ∃ M' ∈ a, ∀ I ∈ a, M' ≤ I → I = M') ↔
  is_noetherian R M :=
by rw [is_noetherian_iff_well_founded, well_founded.well_founded_iff_has_max']

/-- A module is Noetherian iff every increasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_noetherian :
  (∀ (f : ℕ →o submodule R M), ∃ n, ∀ m, n ≤ m → f n = f m)
    ↔ is_noetherian R M :=
by rw [is_noetherian_iff_well_founded, well_founded.monotone_chain_condition]

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
lemma is_noetherian.induction [is_noetherian R M] {P : submodule R M → Prop}
  (hgt : ∀ I, (∀ J > I, P J) → P I) (I : submodule R M) : P I :=
well_founded.recursion (well_founded_submodule_gt R M) I hgt

end


section
universe w
variables {R M P : Type*} {N : Type w} [ring R] [add_comm_group M] [module R M]
  [add_comm_group N] [module R N] [add_comm_group P] [module R P]

lemma finite_of_linear_independent [nontrivial R] [is_noetherian R M]
  {s : set M} (hs : linear_independent R (coe : s → M)) : s.finite :=
begin
  refine classical.by_contradiction (λ hf, (rel_embedding.well_founded_iff_no_descending_seq.1
    (well_founded_submodule_gt R M)).elim' _),
  have f : ℕ ↪ s, from set.infinite.nat_embedding s hf,
  have : ∀ n, (coe ∘ f) '' {m | m ≤ n} ⊆ s,
  { rintros n x ⟨y, hy₁, rfl⟩, exact (f y).2 },
  have : ∀ a b : ℕ, a ≤ b ↔
    span R ((coe ∘ f) '' {m | m ≤ a}) ≤ span R ((coe ∘ f) '' {m | m ≤ b}),
  { assume a b,
    rw [span_le_span_iff hs (this a) (this b),
      set.image_subset_image_iff (subtype.coe_injective.comp f.injective),
      set.subset_def],
    exact ⟨λ hab x (hxa : x ≤ a), le_trans hxa hab, λ hx, hx a (le_refl a)⟩ },
  exact ⟨⟨λ n, span R ((coe ∘ f) '' {m | m ≤ n}),
      λ x y, by simp [le_antisymm_iff, (this _ _).symm] {contextual := tt}⟩,
    by dsimp [gt]; simp only [lt_iff_le_not_le, (this _ _).symm]; tauto⟩
end

/-- If the first and final modules in a short exact sequence are noetherian,
  then the middle module is also noetherian. -/
theorem is_noetherian_of_range_eq_ker
  [is_noetherian R M] [is_noetherian R P]
  (f : M →ₗ[R] N) (g : N →ₗ[R] P)
  (hf : function.injective f)
  (hg : function.surjective g)
  (h : f.range = g.ker) :
  is_noetherian R N :=
is_noetherian_iff_well_founded.2 $
well_founded_gt_exact_sequence
  (well_founded_submodule_gt R M)
  (well_founded_submodule_gt R P)
  f.range
  (submodule.map f)
  (submodule.comap f)
  (submodule.comap g)
  (submodule.map g)
  (submodule.gci_map_comap hf)
  (submodule.gi_map_comap hg)
  (by simp [submodule.map_comap_eq, inf_comm])
  (by simp [submodule.comap_map_eq, h])

/--
For any endomorphism of a Noetherian module, there is some nontrivial iterate
with disjoint kernel and range.
-/
theorem is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot
  [I : is_noetherian R M] (f : M →ₗ[R] M) : ∃ n : ℕ, n ≠ 0 ∧ (f ^ n).ker ⊓ (f ^ n).range = ⊥ :=
begin
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr I
    (f.iterate_ker.comp ⟨λ n, n+1, λ n m w, by linarith⟩),
  specialize w (2 * n + 1) (by linarith only),
  dsimp at w,
  refine ⟨n+1, nat.succ_ne_zero _, _⟩,
  rw eq_bot_iff,
  rintros - ⟨h, ⟨y, rfl⟩⟩,
  rw [mem_bot, ←linear_map.mem_ker, w],
  erw linear_map.mem_ker at h ⊢,
  change ((f ^ (n + 1)) * (f ^ (n + 1))) y = 0 at h,
  rw ←pow_add at h,
  convert h using 3,
  ring
end

/-- Any surjective endomorphism of a Noetherian module is injective. -/
theorem is_noetherian.injective_of_surjective_endomorphism [is_noetherian R M]
  (f : M →ₗ[R] M) (s : surjective f) : injective f :=
begin
  obtain ⟨n, ne, w⟩ := is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot f,
  rw [linear_map.range_eq_top.mpr (linear_map.iterate_surjective s n), inf_top_eq,
    linear_map.ker_eq_bot] at w,
  exact linear_map.injective_of_iterate_injective ne w,
end

/-- Any surjective endomorphism of a Noetherian module is bijective. -/
theorem is_noetherian.bijective_of_surjective_endomorphism [is_noetherian R M]
  (f : M →ₗ[R] M) (s : surjective f) : bijective f :=
⟨is_noetherian.injective_of_surjective_endomorphism f s, s⟩

/--
A sequence `f` of submodules of a noetherian module,
with `f (n+1)` disjoint from the supremum of `f 0`, ..., `f n`,
is eventually zero.
-/
lemma is_noetherian.disjoint_partial_sups_eventually_bot [I : is_noetherian R M]
  (f : ℕ → submodule R M) (h : ∀ n, disjoint (partial_sups f n) (f (n+1))) :
  ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊥ :=
begin
  -- A little off-by-one cleanup first:
  suffices t : ∃ n : ℕ, ∀ m, n ≤ m → f (m+1) = ⊥,
  { obtain ⟨n, w⟩ := t,
    use n+1,
    rintros (_|m) p,
    { cases p, },
    { apply w,
      exact nat.succ_le_succ_iff.mp p }, },

  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr I (partial_sups f),
  exact ⟨n, λ m p, (h m).eq_bot_of_ge $ sup_eq_left.1 $ (w (m + 1) $ le_add_right p).symm.trans $
    w m p⟩
end

/--
If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial.
-/
noncomputable def is_noetherian.equiv_punit_of_prod_injective [is_noetherian R M]
  (f : M × N →ₗ[R] M) (i : injective f) : N ≃ₗ[R] punit.{w+1} :=
begin
  apply nonempty.some,
  obtain ⟨n, w⟩ := is_noetherian.disjoint_partial_sups_eventually_bot (f.tailing i)
    (f.tailings_disjoint_tailing i),
  specialize w n (le_refl n),
  apply nonempty.intro,
  refine (f.tailing_linear_equiv i n).symm ≪≫ₗ _,
  rw w,
  exact submodule.bot_equiv_punit,
end

end

/--
A (semi)ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated.
-/
@[reducible] def is_noetherian_ring (R) [semiring R] := is_noetherian R R

theorem is_noetherian_ring_iff {R} [semiring R] : is_noetherian_ring R ↔ is_noetherian R R :=
iff.rfl

/-- A ring is Noetherian if and only if all its ideals are finitely-generated. -/
lemma is_noetherian_ring_iff_ideal_fg (R : Type*) [semiring R] :
  is_noetherian_ring R ↔ ∀ I : ideal R, I.fg :=
is_noetherian_ring_iff.trans is_noetherian_def

@[priority 80] -- see Note [lower instance priority]
instance is_noetherian_of_finite (R M) [finite M] [semiring R] [add_comm_monoid M] [module R M] :
  is_noetherian R M :=
⟨λ s, ⟨(s : set M).to_finite.to_finset, by rw [set.finite.coe_to_finset, submodule.span_eq]⟩⟩

/-- Modules over the trivial ring are Noetherian. -/
@[priority 100] -- see Note [lower instance priority]
instance is_noetherian_of_subsingleton (R M) [subsingleton R] [semiring R] [add_comm_monoid M]
  [module R M] : is_noetherian R M :=
by { haveI := module.subsingleton R M, exact is_noetherian_of_finite R M }

theorem is_noetherian_of_submodule_of_noetherian (R M) [semiring R] [add_comm_monoid M] [module R M]
  (N : submodule R M) (h : is_noetherian R M) : is_noetherian R N :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  exact order_embedding.well_founded (submodule.map_subtype.order_embedding N).dual h,
end

instance submodule.quotient.is_noetherian {R} [ring R] {M} [add_comm_group M] [module R M]
  (N : submodule R M) [h : is_noetherian R M] : is_noetherian R (M ⧸ N) :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  exact order_embedding.well_founded (submodule.comap_mkq.order_embedding N).dual h,
end

/-- If `M / S / R` is a scalar tower, and `M / R` is Noetherian, then `M / S` is
also noetherian. -/
theorem is_noetherian_of_tower (R) {S M} [semiring R] [semiring S]
  [add_comm_monoid M] [has_smul R S] [module S M] [module R M] [is_scalar_tower R S M]
  (h : is_noetherian R M) : is_noetherian S M :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  refine (submodule.restrict_scalars_embedding R S M).dual.well_founded h
end

theorem is_noetherian_of_fg_of_noetherian {R M} [ring R] [add_comm_group M] [module R M]
  (N : submodule R M) [is_noetherian_ring R] (hN : N.fg) : is_noetherian R N :=
let ⟨s, hs⟩ := hN in
begin
  haveI := classical.dec_eq M,
  haveI := classical.dec_eq R,
  letI : is_noetherian R R := by apply_instance,
  have : ∀ x ∈ s, x ∈ N, from λ x hx, hs ▸ submodule.subset_span hx,
  refine @@is_noetherian_of_surjective ((↑s : set M) → R) _ _ _ (pi.module _ _ _)
    _ _ _ is_noetherian_pi,
  { fapply linear_map.mk,
    { exact λ f, ⟨∑ i in s.attach, f i • i.1, N.sum_mem (λ c _, N.smul_mem _ $ this _ c.2)⟩ },
    { intros f g, apply subtype.eq,
      change ∑ i in s.attach, (f i + g i) • _ = _,
      simp only [add_smul, finset.sum_add_distrib], refl },
    { intros c f, apply subtype.eq,
      change ∑ i in s.attach, (c • f i) • _ = _,
      simp only [smul_eq_mul, mul_smul],
      exact finset.smul_sum.symm } },
  rw linear_map.range_eq_top,
  rintro ⟨n, hn⟩, change n ∈ N at hn,
  rw [← hs, ← set.image_id ↑s, finsupp.mem_span_image_iff_total] at hn,
  rcases hn with ⟨l, hl1, hl2⟩,
  refine ⟨λ x, l x, subtype.ext _⟩,
  change ∑ i in s.attach, l i • (i : M) = n,
  rw [@finset.sum_attach M M s _ (λ i, l i • i), ← hl2,
      finsupp.total_apply, finsupp.sum, eq_comm],
  refine finset.sum_subset hl1 (λ x _ hx, _),
  rw [finsupp.not_mem_support_iff.1 hx, zero_smul]
end

lemma is_noetherian_of_fg_of_noetherian' {R M} [ring R] [add_comm_group M] [module R M]
  [is_noetherian_ring R] (h : (⊤ : submodule R M).fg) : is_noetherian R M :=
have is_noetherian R (⊤ : submodule R M), from is_noetherian_of_fg_of_noetherian _ h,
by exactI is_noetherian_of_linear_equiv (linear_equiv.of_top (⊤ : submodule R M) rfl)

/-- In a module over a noetherian ring, the submodule generated by finitely many vectors is
noetherian. -/
theorem is_noetherian_span_of_finite (R) {M} [ring R] [add_comm_group M] [module R M]
  [is_noetherian_ring R] {A : set M} (hA : A.finite) : is_noetherian R (submodule.span R A) :=
is_noetherian_of_fg_of_noetherian _ (submodule.fg_def.mpr ⟨A, hA, rfl⟩)

theorem is_noetherian_ring_of_surjective (R) [ring R] (S) [ring S]
  (f : R →+* S) (hf : function.surjective f)
  [H : is_noetherian_ring R] : is_noetherian_ring S :=
begin
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at H ⊢,
  exact order_embedding.well_founded (ideal.order_embedding_of_surjective f hf).dual H,
end

instance is_noetherian_ring_range {R} [ring R] {S} [ring S] (f : R →+* S)
  [is_noetherian_ring R] : is_noetherian_ring f.range :=
is_noetherian_ring_of_surjective R f.range f.range_restrict
  f.range_restrict_surjective

theorem is_noetherian_ring_of_ring_equiv (R) [ring R] {S} [ring S]
  (f : R ≃+* S) [is_noetherian_ring R] : is_noetherian_ring S :=
is_noetherian_ring_of_surjective R S f.to_ring_hom f.to_equiv.surjective

lemma is_noetherian_ring.is_nilpotent_nilradical (R : Type*) [comm_ring R] [is_noetherian_ring R] :
  is_nilpotent (nilradical R) :=
begin
  obtain ⟨n, hn⟩ := ideal.exists_radical_pow_le_of_fg (⊥ : ideal R) (is_noetherian.noetherian _),
  exact ⟨n, eq_bot_iff.mpr hn⟩
end
