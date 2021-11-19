/-
Copyright (c) 2021 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as des
cribed in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

-- import group_theory.subgroup.basic
import group_theory.subgroup.pointwise
import group_theory.coset
import group_theory.quotient_group
import group_theory.abelianization
import group_theory.group_action.defs
import group_theory.group_action.basic
import group_theory.group_action.group
import group_theory.group_action.conj_act

/-!
# Iwasawa criterion and simplicity of some groups

Reference : https://www.math.ens.fr/~vanhaecke/tdalg2019/Correction_Iwasawa.pdf

## Iwasawa criterion

Let G be a group acting on a set X (`mul_action G X`).

**Definition (class `is_transitive`)**. The action is *transitive*
if there is x:X whose orbit is X

**Definition (class `is_primitive`).** The action is *primitive*
if it is transitive, and if all stabilizers G_x are maximal subgroups.
(The class `subgroup.is_maximal` organizes the notion of maximal subgroups.)

**Lemma (`is_primitive_of_two_trans`).**
If the action is 2-transitive, then it is primitive.

(TODO : define n-transitive ations (for n:ℕ) and proves the inductive results.)

**Theorem (`Iwasawa_Criterion.Iwasawa_mk`, Iwasawa criterion).**
Let G be a group with a primitive action on a set X.
Assume given an Iwasawa structure, namely,
for all x:X, an abelian subgroup T x of G such that
1. ∀ g:G x:X, T (g x) = g (T x) g⁻¹
2. The union of all T x generates G
Then every normal subgroup of G that acts nontrivially on X contains
the derived subgroup D(G) of G.

These hypotheses are bundled in the structure `has_iwasawa_structure`.

**Corollary (`Iwasawa_Criterion.is_simple`).**
Let G be a perfect group (`commutator G = ⊤`)
with a faithful and primitive action on a set X that admits an Iwasawa structure.
Then G is simple.

## Simplicity of special linear groups

**Theorem (TODO).** Let K be a field and let n be an integer such that n ≥ 2.
Unless n = 2 and K has ≤ 3 elements, the group PSL(n,K) is simple.


## Simplicity of alternate groups

**Theorem (TODO).** Let n be an integer such that n ≥ 5.
The alternate group A(n) is simple.

-/



section Maximal_Subgroups
variables {G : Type*} [group G]

namespace subgroup
/-- An subgroup is maximal if it is maximal in the collection of proper subgroups. -/
class is_maximal (K : subgroup G) : Prop :=
(out : is_coatom K)

theorem is_maximal_def {K : subgroup G} : K.is_maximal ↔ is_coatom K := ⟨λ h, h.1, λ h, ⟨h⟩⟩

theorem is_maximal.ne_top {K : subgroup G} (h : K.is_maximal) : K ≠ ⊤ := (is_maximal_def.1 h).1

theorem is_maximal_iff {K: subgroup G} : K.is_maximal ↔
  K ≠ ⊤ ∧ ∀ (H: subgroup G) g, K ≤ H → g ∉ K → g ∈ H → H = ⊤ :=
begin
  split,
  { intro hK, split, exact is_maximal.ne_top hK,
  intros H g hKH hgK hgH,
  suffices : K < H,
    apply (is_maximal_def.1 hK).2, assumption,
  have zKH : K ≠ H, { rw ne.def, intro z, rw z at hgK, exact hgK hgH },
  exact (ne.le_iff_lt zKH).mp hKH,},
  { rintros ⟨ hG, hmax ⟩,
  split, split, assumption,
  introsI H hKH,
  obtain ⟨ g, hgH, hgK ⟩ := (set.exists_of_ssubset hKH),
  exact hmax H g (le_of_lt hKH) hgK hgH, },
end

theorem is_maximal.eq_of_le {K H: subgroup G}
  (hK : K.is_maximal) (hH : H ≠ ⊤) (KH : K ≤ H) : K = H :=
eq_iff_le_not_lt.2 ⟨KH, λ h, hH (hK.1.2 _ h)⟩

end subgroup
end Maximal_Subgroups

section Basic_Lemmas
/-- If G and H have multiplications *
and φ : G → H is a surjective multiplicative map,
and if G is commutative, then H is commutative.

Since I only use it with groups,
I should probably use function.surjective.comm_semigroup
--/
lemma surj_to_comm {G H : Type*} [has_mul G] [has_mul H] (φ: mul_hom G H) :
   function.surjective φ → is_commutative G (*) → is_commutative H (*) :=
begin
  intros is_surj is_comm,
  apply is_commutative.mk,
  intros a b,
    obtain ⟨a', ha'⟩ := is_surj a, obtain ⟨b', hb'⟩ := is_surj b,
    rw ← ha', rw ← hb',
    let z := ⇑φ, let z₂ := φ.to_fun, have : z = z₂  , by refl,
    rw ← mul_hom.map_mul φ a' b',
    rw ← mul_hom.map_mul φ b' a',
    apply φ.congr_arg,
    refine is_commutative.cases_on is_comm _, intro,
    exact comm a' b',
end

/- No more used

/-- f(f⁻¹(t)) = f.range ∩ t  -/
lemma image_preimage_eq {α β : Type*} (f: α → β) (t: set β):
  set.image f (set.preimage f t) = set.range f ∩ t :=
begin
    sorry,
end

lemma image_preimage_eq' {α β : Type*} (f: α → β) (t: set β):
  set.image f (set.preimage f t) = set.range f ∩ t :=
  by rw [← set.image_univ, ← set.image_inter_preimage f set.univ t, set.univ_inter]

/-- If f is surjective, then f(f⁻¹(t)) = t -/
--  is in mathlib :  set.image_preimage_eq
lemma image_preimage_eq_of_surjective' {α β : Type*} (f : α → β) (t : set β) :
  function.surjective f → set.image f (set.preimage f t) = t :=  λ hf,
  by rw [image_preimage_eq f t, set.range_iff_surjective.2 hf,  set.univ_inter]
 -/
end Basic_Lemmas

section Primitive_And_Transitive_Actions
open_locale big_operators pointwise
open function

open set mul_action subgroup

variables (G : Type*) [group G] (X : Type*) [mul_action G X]

/-- Transitive actions -/
structure is_transitive
extends is_pretransitive G X : Prop :=
(is_nonempty : nonempty X)

/-
lemma nonempty_of_transitive : is_transitive G X → nonempty X
:= λ h, h.is_nonempty

lemma pretransitive_of_transitive : is_transitive G X → is_pretransitive G X :=
λ h, h.is_pretransitive
-/

variables (G X)
structure is_primitive
extends is_transitive G X : Prop :=
(has_maximal_stabilizers: ∀ x:X, (stabilizer G x).is_maximal)

/-
lemma nonempty_of_primitive : is_transitive G X → nonempty X
:= λ h, h.is_nonempty

lemma transitive_of_primitive : is_primitive G X → is_transitive G X
:= λ h, is_transitive.mk h.is_nonempty h.is_pretransitive

lemma has_maximal_stabilizer : is_primitive G X →  ∀ (x : X), (stabilizer G x).is_maximal
:= λ h, h.has_maximal_stabilizers
-/

/-- A 2-transitive action is primitive -/
/- Part of the proof establishes that stabilizers of n-transitive
actions are (n-1)-transitive. Todo: rewrite using this. -/
theorem is_primitive_of_two_trans  [hX: nontrivial X]
   (h2X : ∀ (x₁ x₂ y₁ y₂ : X) (hx: x₁ ≠ x₂) (hy: y₁ ≠ y₂),
  ∃ g: G, g • x₁  = y₁ ∧ g • x₂ = y₂ ) : is_primitive G X :=
begin
    have is_trans : is_transitive G X ,
    { apply is_transitive.mk,
      apply is_pretransitive.mk,
      { intros x y,
        /- on veut applique x sur y
          mais il faut un élément x' ≠ x à appliquer sur un élément y' ≠ y    -/
        obtain ⟨x', hx'⟩ := exists_ne x,
        obtain ⟨y', hy'⟩ := exists_ne y,
        obtain ⟨ g, h, h' ⟩ := h2X x x' y y' hx'.symm hy'.symm,
        existsi g, exact h, },
    {  apply nontrivial.to_nonempty, },},

    have has_max_stab : ∀ x:X, (stabilizer G x).is_maximal,
    { intro x,
      apply is_maximal_iff.2,
      split,

      { -- stabilizer G x ≠ ⊤ :
        obtain ⟨ y, hy ⟩ := exists_ne x,
        obtain ⟨ g, h, h' ⟩ := h2X x y y x hy.symm hy,
        have z : g ∉ stabilizer G x ,

        { intro hg, rw mem_stabilizer_iff at hg, rw hg at h, exact hy.symm h, },
        intro zz, rw zz at z,
        exact z (set.mem_univ g), },

      { -- stabilizer G x est maximal
        intros H g hH hg hgH,
        apply (eq_top_iff' H).2,
        intro k,
        by_cases hk : k ∈ stabilizer G x,
        { -- apply mem_of_mem_of_subset _ hH, exact hk,
          apply mem_of_mem_of_subset _ hH, exact hk, },
        { rw mem_stabilizer_iff at hg,
          rw mem_stabilizer_iff at hk,
          -- (g • x, x) -> (k • x, x)
          obtain ⟨ h, h1, h2 ⟩ := h2X (g • x) x (k • x) x hg hk,
          -- k = h g g⁻¹ h⁻¹ k
          have hk' : k = h • g • (g⁻¹ • h⁻¹ • k), by simp,
          rw hk',
          apply mul_mem,
          -- h ∈ stabilizer G x ≤ H
          apply mem_of_mem_of_subset _ hH,
          exact h2,
          apply mul_mem,
          -- g ∈ H
          assumption,
          apply mem_of_mem_of_subset _ hH,
          -- g⁻¹ h⁻¹ k ∈ stabilizer G x
          have h1' : (g⁻¹ • h⁻¹ • k) • x = x,
          { rw smul_assoc, rw smul_assoc, rw ← h1, simp, },

          exact h1', }, }, },

    apply is_primitive.mk is_trans has_max_stab,
end

end Primitive_And_Transitive_Actions

section Commutators_And_Derived_Group

variables {G : Type*} [group G]

theorem  quotient_comm_contains_commutators_iff (N : subgroup G) [nN : N.normal] :
  is_commutative (quotient_group.quotient N) (*) ↔ commutator G ≤ N :=
begin
  split,
  { rintro ⟨hcomm : ∀ (a b: quotient_group.quotient N), a * b = b * a ⟩,
    rw commutator, apply subgroup.normal_closure_subset_iff.1,
    intros x hx, rw set.mem_set_of_eq at hx, obtain ⟨p, q, hpq⟩ := hx,
    apply (quotient_group.eq_one_iff x).1,
    rw ← hpq, simp only [quotient_group.coe_mul, quotient_group.coe_inv],
    specialize hcomm ↑p ↑q,
    rw mul_inv_eq_one,
    apply mul_inv_eq_iff_eq_mul.2, assumption, assumption, },
  { intro hGN, refine is_commutative.mk _,
    intro x', apply quotient_group.induction_on x', intro x,
    intro y', apply quotient_group.induction_on y', intro y,
    have hxy: (x * y)⁻¹ * (y * x)  ∈ N,
    { rw [mul_inv_rev, ← mul_assoc],
      apply set.mem_of_mem_of_subset _ hGN,
      rw commutator,
      apply subgroup.subset_normal_closure, rw set.mem_set_of_eq,
      existsi y⁻¹ , existsi x⁻¹ , rw inv_inv x, rw inv_inv y, },
    apply quotient_group.eq'.2 hxy, },
end

/--  N a normal subgroup.
If there exists a commutative subgroup H, such that H ⊔ N = ⊤,
then N contains the derived subgroup.
-/
lemma contains_commutators_of (N : subgroup G) (nN : N.normal)
    (H : subgroup G) (hHN : N ⊔ H = ⊤) (hH: subgroup.is_commutative H) :
    commutator G ≤ N :=
begin
  let Q := quotient_group.quotient N,

  -- Q is a quotient of H
    let φ : H →* Q := monoid_hom.comp (quotient_group.mk' N) (subgroup.subtype H),

    have hφ : function.surjective φ,

    -- On prouve que l'image de φ est égale à ⊤
    apply monoid_hom.range_top_iff_surjective.mp,
    let R := monoid_hom.range φ,
/-  j : H → G, p : G → G/N,  φ = p o j, on veut prouver que φ est surjective.
    R = im(φ), S = p⁻¹(R) ⊆ G -/

    /- Il va suffire de prouver que S = ⊤, car p est surjective -/
    let S := subgroup.comap (quotient_group.mk' N) R,
    have S_top : S = ⊤,
    {
      /- S contient N -/
      have lN : N ≤ S,
      { intros g hg,
        apply subgroup.mem_comap.2,
        have : (quotient_group.mk' N) g = 1,
        by simp only [hg, quotient_group.mk'_apply, quotient_group.eq_one_iff],
        rw this, exact R.one_mem', },

      /- S contient H = j(H) -/
      have lH : H ≤ S,
      { intros h hh,
        apply subgroup.mem_comap.2,
        apply set.mem_range.2, use h, exact hh,
        simp only [subgroup.coe_subtype, function.comp_app,
          monoid_hom.coe_comp, subgroup.coe_mk], },

      /- donc S = ⊤ puisque hHN : N ⊔ H = ⊤ -/
      apply eq_top_iff.2,
      rw ← hHN,
      exact sup_le_iff.2 ⟨lN, lH⟩,
    },

    /- Ceci fait, il reste à prouver que R = ⊤ -/
    {
      apply eq_top_iff.2,
      intros x _ ,
      let y := quotient.out' x,
      have hy : y ∈ S,
      { rw S_top, exact subgroup.mem_top y, },
      rw ← quotient_group.out_eq' x,
      exact subgroup.mem_comap.1 hy,
    },

  --Q is commutative as a surjective image of H
  have hc : is_commutative Q (*)
    := surj_to_comm (monoid_hom.to_mul_hom φ) hφ hH.is_comm,

  -- Deduce that commutator G ≤ N
  exact (quotient_comm_contains_commutators_iff N).1 hc,
end

end Commutators_And_Derived_Group

section Iwasawa_Criterion
namespace Iwasawa_Criterion

open_locale big_operators pointwise

variables (G: Type*) [group G] (X: Type*) [mul_action G X]

/-- If the action of G on X is primitive,
then for any normal subgroup N that acts nontrivially,
any x : X, the groups N and (stabilizer G x) generate G.
-/
lemma prim_to_full (is_prim: is_primitive G X) :
  ∀ (x: X), ∀ (N:subgroup G), subgroup.normal N → mul_action.fixed_points N X ≠ ⊤ →
  N ⊔ (mul_action.stabilizer G x) = ⊤ :=
begin
  intros x N nN hNX,
  let Gx := mul_action.stabilizer G x, let NGx := N ⊔ Gx,
  have h_Gx_le_NGx : Gx ≤ NGx , by simp only [le_sup_right],
  have N_le_NGx : N ≤ NGx , by simp only [le_sup_left],
  suffices h_Gx_lt_NGx : Gx < NGx,
    have this : ∀ x:X, (mul_action.stabilizer G x).is_maximal
      := is_prim.has_maximal_stabilizers,
    specialize this x,
    rw subgroup.is_maximal_def at this,
    rw is_coatom at this,
    apply (and.elim_right this NGx), assumption,

  rw lt_iff_le_not_le, split, assumption,
  intro z, -- have z': Gx = NGx :=  le_antisymm h_Gx_le_NGx z,
  rw ← (le_antisymm h_Gx_le_NGx z) at N_le_NGx,

  apply hNX,

  rw mul_action.fixed_points, rw set.top_eq_univ, apply set.eq_univ_of_forall,
  intro y, rw set.mem_set_of_eq, intro g,
  let is_pretrans := (is_transitive.to_is_pretransitive
        (is_primitive.to_is_transitive is_prim)).exists_smul_eq,
  obtain ⟨h, hyx⟩ := is_pretrans y x,

  have : h * g * h⁻¹ ∈ mul_action.stabilizer G x ,
  apply N_le_NGx,
  apply nN.conj_mem g _ h, exact set_like.coe_mem g,

  rw mul_action.mem_stabilizer_iff at this,
  rw ← hyx at this,
  rw [mul_smul, inv_smul_smul, mul_smul, smul_left_cancel_iff] at this,
  exact this,
end

/-- An auxiliary lemma, variant of normal_mul' ,
with an explicit N.normal hypothesis,
so that the typeclass inference machine works.
-/
lemma normal_mul' (N:subgroup G) (nN:N.normal) (K: subgroup G)
    (h : N ⊔ K = ⊤) : ∀(g:G), ∃(n:N) (k:K), g = n*k :=
begin
    intro g,
    have hg : g ∈ ↑(N ⊔ K), { rw h, exact subgroup.mem_top g,},
    rw [subgroup.normal_mul, set.mem_mul] at hg,
    obtain ⟨x, y, hx, hy, hxy⟩ := hg,
    use x, exact hx, use y, exact hy, rw eq_comm at hxy, exact hxy,
end

/-- If the action of G on X is primitive,
then any normal subgroup N that acts nontrivially acts transitively.
-/
lemma prim_to_transitive (is_prim: is_primitive G X) :
  ∀(N:subgroup G) (nN:N.normal), mul_action.fixed_points N X ≠ ⊤ →
  mul_action.is_pretransitive N X :=
begin
    intros N nN hNX,
    apply mul_action.is_pretransitive.mk,
    intros x y,

    have : ∀ (g:G), ∃(n:N) (k:mul_action.stabilizer G x), g = n * k
    := normal_mul'  G (N:subgroup G) nN (mul_action.stabilizer G x: subgroup G)
        (prim_to_full G X is_prim x N nN hNX) ,

    let is_pretrans := (is_transitive.to_is_pretransitive
        (is_primitive.to_is_transitive is_prim)).exists_smul_eq,
    obtain ⟨g₁, hg₁⟩ :=  is_pretrans x y,
    obtain ⟨h, k, hk⟩ := this g₁  ,
    use h,

    have k' := mul_action.mem_stabilizer_iff.1 (subtype.mem k),
    rw ← k',
    rw hk at hg₁, rw mul_smul at hg₁, assumption,
end

/-- The structure underlying the Iwasawa criterion -/
structure has_iwasawa_structure :=
  (T : X → subgroup G)
  (is_comm: ∀ x:X, (T x).is_commutative)
  (is_conj: ∀ g: G, ∀ x : X, T (g • x) = mul_aut.conj g • (T x))
  (is_generator: supr T = ⊤)

/-- The Iwasawa criterion : If a primitive action of a group G on X
has an Iwasawa structure, then any normal subgroup that acts nontrivially
contains the group of commutators. -/
theorem Iwasawa_mk (is_prim: is_primitive G X) (IwaS : has_iwasawa_structure G X) :
  ∀ N:subgroup G, subgroup.normal N → mul_action.fixed_points N X ≠ ⊤ → commutator G ≤ N :=
/- Iwa_GX = (T : X → subgroup G)
  (is_comm: ∀ x:X, (T x).is_commutative)
  (is_conj: ∀ g: G, ∀ x : X, T (g • x) = mul_aut.conj g • (T x))
  (is_generator: supr T = ⊤) -/
begin
  intros N nN hNX,
  haveI := prim_to_transitive G X is_prim N nN hNX,
  obtain x := is_prim.is_nonempty.some,
  refine contains_commutators_of N nN (IwaS.T x) _ (IwaS.is_comm x),
  -- by contains_commutators_of, it suffices to prove that N ⊔ IwaS.T x = ⊤
  rw [eq_top_iff, ←IwaS.is_generator, supr_le_iff],
  intro y,
  obtain ⟨g, rfl⟩ := mul_action.exists_smul_eq N x y,
  rw [subgroup.smul_def, IwaS.is_conj g x],
  rintros _ ⟨k, hk, rfl⟩,
  have hg' : ↑g ∈ N ⊔ IwaS.T x := subgroup.mem_sup_left (subtype.mem g),
  have hk' : k ∈ N ⊔ IwaS.T x := subgroup.mem_sup_right hk,
  exact (N ⊔ IwaS.T x).mul_mem ((N ⊔ IwaS.T x).mul_mem hg' hk') ((N ⊔ IwaS.T x).inv_mem hg'),
end

theorem is_simple (is_nontrivial : nontrivial G) (is_perfect : commutator G = ⊤)
  (is_prim : is_primitive G X) (is_faithful : has_faithful_scalar G X)
  (IwaS : has_iwasawa_structure G X) : is_simple_group G :=
begin
  refine ⟨is_nontrivial.exists_pair_ne, λ N nN, _⟩,
  cases (or_iff_not_imp_left.mpr (Iwasawa_mk G X is_prim IwaS N nN)),
  { refine or.inl (N.eq_bot_iff_forall.mpr (λ n hn, _)),
    apply is_faithful.eq_of_smul_eq_smul,
    intro x,
    rw one_smul,
    exact set.eq_univ_iff_forall.mp h x ⟨n, hn⟩ },
  { exact or.inr (top_le_iff.mp (le_trans (ge_of_eq is_perfect) h)) },
end

end Iwasawa_Criterion
end Iwasawa_Criterion
