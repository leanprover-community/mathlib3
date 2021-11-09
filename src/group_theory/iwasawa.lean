-- import group_theory.subgroup.basic
import group_theory.subgroup.pointwise
import group_theory.coset
import group_theory.quotient_group
import group_theory.abelianization
import group_theory.group_action.defs
import group_theory.group_action.basic
import group_theory.group_action.group
import group_theory.group_action.conj_act


/- 
# Iwasawa criterion and simplicity of some groups

Reference : https://www.math.ens.fr/~vanhaecke/tdalg2019/Correction_Iwasawa.pdf

## Iwasawa criterion

Let G be a group acting on a set X.

**Definition**. The action is *transitive* if there is x:X whose orbit is X

**Definition.** The action is *primitive* if it is transitive,
and if all stabilizers G_x are maximal subgroups.

**Lemma.** If the action is 2-transitive, then it is primitive.

**Theorem (Iwasawa criterion).** Let G be a group with a primitive action on a set X.
Assume given an Iwasawa structure, namely, 
for all x:X, an abelian subgroup T x of G such that 
1. ∀ g:G x:X, T (g x) = g (T x) g⁻¹ 
2. The union of all T x generates G
Then every normal subgroup of G that acts nontrivially on X contains
the derived subgroup D(G) of G.

**Corollary.** Let G be a perfect group (D(G)=G) 
with a faithful and primitive action on a set X.
Assume given an Iwasawa structure.
Then G is simple.

## Simplicity of special linear groups

**Theorem.** Let K be a field and let n be an integer such that n ≥ 2.
Unless n = 2 and K has ≤ 3 elements, the group PSL(n,K) is simple.


## Simplicity of alternate groups

**Theorem.** Let n be an integer such that n ≥ 5. 
The alternate group A(n) is simple.

-/


section Maximal_Subgroups
variables {G : Type*} [group G]

/-- An subgroup is maximal if it is maximal in the collection of proper subgroups. -/
class subgroup.is_maximal (K : subgroup G) : Prop := 
  (out : is_coatom K)  

theorem is_maximal_def {K : subgroup G} : K.is_maximal ↔ is_coatom K := ⟨λ h, h.1, λ h, ⟨h⟩⟩

theorem is_maximal.ne_top {K : subgroup G} (h : K.is_maximal) : K ≠ ⊤ := (is_maximal_def.1 h).1

theorem is_maximal_iff {K: subgroup G} : K.is_maximal ↔
  K ≠ ⊤ ∧ ∀ (H: subgroup G) g, K ≤ H → g ∉ K → g ∈ H → H = ⊤ :=
begin
  split, 
  
  intro hK, split, exact is_maximal.ne_top hK,
  intros H g hKH hgK hgH,
  suffices : K < H,
    apply (is_maximal_def.1 hK).2, assumption,
  have zKH : K ≠ H := 
  begin 
    simp, intro z, rw z at hgK, exact hgK hgH,
  end,
  exact (ne.le_iff_lt zKH).mp hKH,

  rintros ⟨ hG, hmax ⟩,
  split, split, assumption,
  introsI H hKH,
  obtain ⟨ g, hgH, hgK ⟩ := (set.exists_of_ssubset hKH),
  exact hmax H g (le_of_lt hKH) hgK hgH, 
end

theorem is_maximal.eq_of_le {K H: subgroup G}
  (hK : K.is_maximal) (hH : H ≠ ⊤) (KH : K ≤ H) : K = H :=
eq_iff_le_not_lt.2 ⟨KH, λ h, hH (hK.1.2 _ h)⟩

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

/-- f(f⁻¹(t)) = f.range ∩ t  -/
lemma map_comap_of {α β : Type*} (f: α → β) (t: set β):
  set.image f (set.preimage f t) = set.range f ∩ t :=  
  by rw [← set.image_univ, ← set.image_inter_preimage f set.univ t, set.univ_inter]

/-- If f is surjective, then f(f⁻¹(t)) = t -/
lemma map_comap_of_surjective {α β : Type*} (f : α → β) (t : set β) :
  function.surjective f → set.image f (set.preimage f t) = t :=  λ hf, 
  by rw [map_comap_of f t, set.range_iff_surjective.2 hf,  set.univ_inter]

end Basic_Lemmas

section Primitive_And_Transitive_Actions
open_locale big_operators pointwise
open function

open set mul_action subgroup 

variables (G : Type*) [group G] (X : Type*) [mul_action G X]

structure is_transitive  
extends is_pretransitive G X : Prop := 
(is_nonempty : nonempty X)

/- 
lemma nonempty_of_transitive : is_transitive G X → nonempty X 
:= λ h, h.is_nonempty

lemma pretransitive_of_transitive : is_transitive G X → is_pretransitive G X :=  
λ h, h.is_pretransitive
-/

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


/- lemma neq_of_two {X : Type*} {a b: X} (hab : a ≠ b) (x : X) :
  x ≠ a ∨ x ≠ b :=
begin
  by_cases h : x = a,
  rw ← h at hab, exact or.intro_right (x ≠ a) hab,
  apply or.intro_left _ _, simp, assumption,
end
 -/

/-- A 2-transitive action is primitive -/
/- Part of the proof establishes that stabilizers of n-transitive
actions are (n-1)-transitive. Todo: rewrite using this. -/
theorem is_primitive_of_two_trans 
  : (∀ (x₁ x₂ y₁ y₂ : X) (hx: x₁ ≠ x₂) (hy: y₁ ≠ y₂), ∃ g: G,
  g • x₁  = y₁ ∧ g • x₂ = y₂ ) → 
  (∃ (x₁ x₂ : X ), x₁ ≠ x₂) → is_primitive G X :=
begin
    intros h2X hX2,
    obtain ⟨a, b, hab⟩ := hX2,
    have another_of : ∀ x : X, ∃ x' : X, x ≠ x'  :=
    begin
        intro x,
        by_cases h : x = a,
        rw ← h at hab, existsi b, exact hab,
        existsi a, exact h,
    end,
    
    have is_trans : is_transitive G X ,
    begin
        apply is_transitive.mk,
        apply is_pretransitive.mk,
        intros x y, 
    /- on veut applique x sur y
    mais il faut un élément x' ≠ x à appliquer sur un élément y' ≠ y    -/
      obtain ⟨ x', hx' ⟩ := another_of x,
      obtain ⟨ y', hy' ⟩ := another_of y,
      obtain ⟨ g, h, h' ⟩ := h2X x x' y y' hx' hy',
      existsi g, exact h, 
        use a,
    end,

    have has_max_stab : ∀ x:X, (stabilizer G x).is_maximal :=
    begin
      intro x, 
      apply is_maximal_iff.2,
      split,
      
      { -- stabilizer G x ≠ ⊤ : 
        obtain ⟨ y, hy ⟩ := another_of x,
        have hy' : y ≠ x := λz,  hy (eq_comm.1 z), 
        obtain ⟨ g, h, h' ⟩ := h2X x y y x hy hy',
        have z : g ∉ stabilizer G x ,
        { intro hg, simp at hg, rw hg at h, exact hy h, },
        intro zz, rw zz at z,
        exact z (set.mem_univ g), 
         },

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

          exact h1', },
      },
    end,

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
    intros x hx, simp at hx, obtain ⟨p, q, hpq⟩ := hx,
    apply (quotient_group.eq_one_iff x).1,
    rw ← hpq, simp,
    specialize hcomm ↑p ↑q,
    rw mul_inv_eq_one,
    apply mul_inv_eq_iff_eq_mul.2, assumption, assumption, },
  { intro hGN, refine is_commutative.mk _, 
    intro x', apply quotient_group.induction_on x', intro x, 
    intro y', apply quotient_group.induction_on y', intro y,
    have hxy: (x * y)⁻¹ * (y * x)  ∈ N,
    begin
      simp, rw ← mul_assoc,
      apply set.mem_of_mem_of_subset _ hGN,
      rw commutator,
      apply subgroup.subset_normal_closure, simp,
      existsi y⁻¹ , existsi x⁻¹ , rw inv_inv x, rw inv_inv y,
    end,
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
    begin
      /- S contient N -/
      have lN : N ≤ S := 
      begin
        intros g hg, 
        apply subgroup.mem_comap.2, 
        have : (quotient_group.mk' N) g = 1 := begin simp[hg], end,
        rw this, exact R.one_mem',
      end,
        
      /- S contient H = j(H) -/
      have lH : H ≤ S :=
      begin 
        intros h hh,
        apply subgroup.mem_comap.2,
        apply set.mem_range.2, use h, exact hh, simp,
      end,

      /- donc S = ⊤ puisque hHN : N ⊔ H = ⊤ -/
      apply eq_top_iff.2,
      rw ← hHN,
      exact sup_le_iff.2 ⟨lN, lH⟩,
    end,

    /- Ceci fait, il reste à prouver que R = ⊤ -/
    {
      apply eq_top_iff.2,
      intros x _ ,
      let y := quotient.out' x,
      have hy : y ∈ S := begin rw S_top, exact subgroup.mem_top y, end,
      rw ← quotient_group.out_eq' x,
      exact subgroup.mem_comap.1 hy,
    },
    
  --Q is commutative as a surjective image of H
  have hc : is_commutative Q (*) 
    := surj_to_comm (monoid_hom.to_mul_hom φ) hφ hH.is_comm,
  
  -- Deduce that commutator G ≤ N
  exact (quotient_comm_contains_commutators_iff N).1 hc,
end


open_locale pointwise

/- Désormais inutile, on peut utiliser subgroup.normal_mul

lemma closure_of_normal_union_subgroup_mem
  (G:Type*) [group G] (N:subgroup G) (hN:N.normal)(K:subgroup G) (g:G) :
  g ∈ subgroup.closure (↑N ∪ ↑K: set G) 
  ↔  ∃ (n : N) (k:K), g = ↑n * ↑k :=
begin
  let cNK := ↥(subgroup.closure ((N ∪ K): set G)),
  let NK :=  { g : G | ∃ (n : N) (k:K), g = ↑n * ↑k },
  have HNK : ∀ (g:G) (hg: g ∈ (N ∪ K : set G)), g ∈ NK := 
  begin
    intros x hx,
    rw set.mem_union at hx,
    cases hx , 
    simp, use x, exact hx, use 1, simp,
    simp, use 1, simp, use x, exact hx, refl,
  end,

  -- let p := λ (g:G), (∃ (n : N) (k:K), g = ↑n * ↑k ),
  have H1 : (1:G) ∈ NK := begin simp, use 1, use 1, simp, end,
  have Hmul : ∀ (a b : G), a ∈ NK → b ∈ NK → a * b ∈ NK :=
  begin
    intros a b ha hb, simp at ⊢ ha hb,
    obtain ⟨na, ka, hank⟩ := ha,
    obtain ⟨nb, kb, hbnk ⟩ := hb,
    use (na * ka * nb * ka⁻¹ ), rw mul_assoc, rw mul_assoc,
    apply subgroup.mul_mem', exact subtype.mem na,
    simp, rw ← mul_assoc, apply hN.conj_mem, exact subtype.mem nb,
    use ka * kb,
    simp, rw mul_assoc, simp, 
    rw ← hank, rw mul_assoc, rw ← hbnk, 
  end,
  have Hinv : ∀ (g : G), g ∈ NK → g⁻¹ ∈ NK :=
  begin
    intros h hg,
    obtain ⟨n, k, hnk⟩ := hg,
    rw hnk, simp,
        -- (nk)⁻¹ = k⁻¹ n⁻¹ = k⁻¹ n⁻¹ k k⁻¹ 
    use k⁻¹ * n⁻¹ * k⁻¹⁻¹, apply hN.conj_mem, simp,
    use k⁻¹, simp,
  end, 
    
  split, 

    /-
      closure_induction :
      ?M_5 ∈ closure ?M_3 
        → (∀ (x : ?M_1), x ∈ ?M_3 → ?M_4 x) 
        → ?M_4 1 
        → (∀ (x y : ?M_1), ?M_4 x → ?M_4 y → ?M_4 (x * y)) 
        → (∀ (x : ?M_1), ?M_4 x → ?M_4 x⁻¹) 
        → ?M_4 ?M_5
    -/
  intro hg, 
  have z : ∀(g:G), g∈ subgroup.closure (N ∪ K : set G) → g ∈ NK ,
  intros g hg', 
  exact subgroup.closure_induction hg' HNK H1 Hmul Hinv,
  exact z g hg,

  intro hNK,
  obtain ⟨n, k, hnk⟩ := hNK,
  have n' : ↑n ∈ (↑N ∪ ↑K) := set.mem_union_left ↑K (subtype.mem n),
  have k' : ↑k ∈ (↑N ∪ ↑K) := set.mem_union_right ↑N (subtype.mem k),

  rw hnk, 

  apply subgroup.mem_closure.2,
  intros K1 hK1,
  apply subgroup.mul_mem, 
  apply hK1, exact set.mem_union_left ↑K (subtype.mem n),
  apply hK1, exact set.mem_union_right ↑N (subtype.mem k),
end
 -/


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
  have h_Gx_le_NGx : Gx ≤ NGx , by simp, 
  have N_le_NGx : N ≤ NGx , by simp,
  suffices h_Gx_lt_NGx : Gx < NGx,
    have this : ∀ x:X, (mul_action.stabilizer G x).is_maximal 
      := is_prim.has_maximal_stabilizers,
    specialize this x,
    rw is_maximal_def at this,
    rw is_coatom at this,
    apply (and.elim_right this NGx), assumption,

  rw lt_iff_le_not_le, split, assumption,
  intro z, -- have z': Gx = NGx :=  le_antisymm h_Gx_le_NGx z,
  rw ← (le_antisymm h_Gx_le_NGx z) at N_le_NGx,

  apply hNX,

  rw mul_action.fixed_points, simp, apply set.eq_univ_of_forall, intro y,
  simp, intro g,
  let is_pretrans := (is_transitive.to_is_pretransitive 
        (is_primitive.to_is_transitive is_prim)).exists_smul_eq, 
  obtain ⟨h, hyx⟩ := is_pretrans y x,

  have : h * g * h⁻¹ ∈ mul_action.stabilizer G x ,
  apply N_le_NGx,
  apply nN.conj_mem g _ h, exact set_like.coe_mem g,
  
  rw mul_action.mem_stabilizer_iff at this,
  rw ← hyx at this,
  rw mul_smul at this, simp at this,
  rw mul_smul at this, simp at this, exact this,
end

/-- An auxiliary lemma, variant of normal_mul' ,
with an explicit N.normal hypothesis, 
so that the typeclass inference machine works.
-/
lemma normal_mul' (N:subgroup G) (nN:N.normal) (K: subgroup G) 
    (h : N ⊔ K = ⊤) : ∀(g:G), ∃(n:N) (k:K), g = n*k :=
begin
    intro g,
    have hg : g ∈ ↑(N ⊔ K) :=   
      begin 
        rw h,
        exact subgroup.mem_top g, 
      end,
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

 /-    have Nbig :  N ⊔ (mul_action.stabilizer G x) = ⊤ :=
      prim_to_full G X is_prim x N nN hNX,
    rw ← subgroup.closure_eq N at Nbig,
    rw ← subgroup.closure_eq (mul_action.stabilizer G x) at Nbig,
    rw ← subgroup.closure_union at Nbig,
    rw eq_comm at Nbig,
    have this' : ∀ (g:G), ∃(h:N) (k:mul_action.stabilizer G x), g = h * k,
      intro g,
      have := subguroup.mem_top g,
      rw Nbig at this,
      exact (closure_of_normal_union_subgroup_mem G N nN (mul_action.stabilizer G x) g).1 this,
 -/
  
    have : ∀ (g:G), ∃(n:N) (k:mul_action.stabilizer G x), g = n * k 
    := normal_mul'  G (N:subgroup G) nN (mul_action.stabilizer G x: subgroup G) (prim_to_full G X is_prim x N nN hNX) ,
    

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

  let is_pretrans_G := (is_transitive.to_is_pretransitive (is_primitive.to_is_transitive is_prim)).exists_smul_eq, 

  have is_pretrans_N : mul_action.is_pretransitive N X 
    := prim_to_transitive G X is_prim N nN hNX,
  have is_trans_N : is_transitive N X := 
  begin
    apply is_transitive.mk, assumption,
    obtain (x:X) := nonempty.some (is_prim.is_nonempty),
    use x,
  end,

/- ∀ x, G = N ⊔ (T x). 
  Il suffit de prouver que G contient tous les (T y)
  Soit h ∈ N tel que y = h x (existe car l'action de N est transitive)
  Alors,  T y = T (h x) = h (T x) h⁻¹ ≤  N ⊔ (T x) .
  -/

have is_top_of_NTx : ∀(x:X), N ⊔ (IwaS.T x) =  ⊤,
  begin
    intro x,
    apply le_antisymm le_top,
    rw ← IwaS.is_generator,
    rw supr, 
    refine Sup_le _,
    intros K hK, obtain ⟨y, hKy⟩:= hK, rw ← hKy,
    -- let z := is_pretrans_N.exists_smul_eq,
    -- obtain ⟨g,h⟩ := z x y,
    apply mul_action.is_pretransitive.cases_on is_pretrans_N,
    intro this, obtain ⟨g, h⟩ := this x y, rw ← h, rw subgroup.smul_def,
    rw IwaS.is_conj (g:G) x,  
    
    intros g₁  hg₁,
    obtain ⟨k, hk, hkg₁⟩ := hg₁ , simp at hkg₁ ,
    rw ← hkg₁ , 
    have hg' : ↑g ∈ N ⊔ IwaS.T x :=  subgroup.mem_sup_left (subtype.mem g),
    have hk' : k ∈ N ⊔ IwaS.T x :=  subgroup.mem_sup_right hk,

    refine (N ⊔ IwaS.T x).mul_mem _ _ ,
    exact (N ⊔ IwaS.T x).mul_mem hg' hk',
    exact (N ⊔ IwaS.T x).inv_mem hg',
  end,

/- x n'est pas vide-/
  obtain (x:X) := nonempty.some (is_prim.is_nonempty),

/- 
  G / N = (N (T x)) / N ≃ (T x)/(N ∩ (T x)), donc est abélien.
  Donc (commutator G) ≤ N.
-/

/- contains_commutators_of : 
∀ (N : subgroup ?m_1) [nN : N.normal] (H : subgroup ?m_1),
  N ⊔ H = ⊤ → H.is_commutative → commutator ?m_1 ≤ N
-/

exact contains_commutators_of (N:subgroup G) nN (IwaS.T x) 
  (is_top_of_NTx x) (IwaS.is_comm x),
end


theorem is_simple (is_nontrivial: nontrivial G) (is_perfect: commutator G = ⊤) 
  (is_prim: is_primitive G X) (is_faithful: has_faithful_scalar G X) 
  (IwaS : has_iwasawa_structure G X) : is_simple_group G :=
begin
  apply is_simple_group.mk,
  exact is_nontrivial.exists_pair_ne,
  intros N nN,
  by_cases hN : N = ⊥,
  refine or.intro_left _ hN, 
  refine or.intro_right _ _, 
  apply eq_top_iff.2 ,
  rw ← is_perfect,

  /- One applies the general criterion -/
  refine Iwasawa_mk G X (is_prim : is_primitive G X ) (IwaS : has_iwasawa_structure G X) N nN _,
  /- It remains to prove that the action of N on X is nontrivial -/
  intro hm,
  rw mul_action.fixed_points at hm,
  have N_bot : N = ⊥,
  apply (subgroup.eq_bot_iff_forall N).2,
  intros n hn,
  have N_triv : ∀ (x:X), n • x = (1:G) • x,
  begin
    intro x,
    rw set.top_eq_univ at hm,
    let hx := set.mem_univ x,
    rw ← hm at hx, 
    rw set.mem_set_of_eq at hx,
    rw mul_action.one_smul x,
    refine (set_coe.forall.1 hx) n _ ,
    simp, exact hn,
  end,
  apply is_faithful.eq_of_smul_eq_smul, exact N_triv, exact hN N_bot,
end

end Iwasawa_Criterion
end Iwasawa_Criterion
