import linear_algebra.direct_sum_module linear_algebra.linear_combination tactic.linarith

universes u v w u₁

namespace tactic.interactive 
open tactic
meta def clear_aux_decl : tactic unit :=
do l ← local_context,
match l with
| [] := skip
| (e::l) := cond e.is_aux_decl (tactic.clear e) skip
end

end tactic.interactive

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

def thing {R : Type w} [comm_ring R] [Π i, add_comm_group (G i)] [Π i, module R (G i)]
  (f : Π i j, i ≤ j → G i →ₗ G j) [directed_system G f] : set (direct_sum R ι G) :=
  ⋃ i j (H : i ≤ j) x,
  ({ direct_sum.of ι G i x - direct_sum.of ι G j (f i j H x) } : set $ direct_sum R ι G)

def direct_limit {R : Type w} [comm_ring R] [Π i, add_comm_group (G i)] [Π i, module R (G i)]
  (f : Π i j, i ≤ j → G i →ₗ G j) [directed_system G f] : Type (max u v) :=
quotient $ span $ thing G f

lemma mem_thing {G : ι → Type v} [Π i, decidable_eq (G i)]
  {R : Type w} [comm_ring R] [Π i, add_comm_group (G i)] [Π i, module R (G i)]
  {f : Π i j, i ≤ j → G i →ₗ G j} [directed_system G f] {a : direct_sum R ι G} :
  a ∈ thing G f ↔ ∃ (i j) (H : i ≤ j) x,
  a = direct_sum.of ι G i x - direct_sum.of ι G j (f i j H x) :=
  by simp [thing, set.mem_Union]

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
liftq _ (direct_sum.to_module _ g)
  (span_le.2 $ set.Union_subset $ λ i,
    set.Union_subset $ λ j, set.Union_subset $ λ hij, set.Union_subset $ λ x,
      set.singleton_subset_iff.2 $ linear_map.sub_mem_ker_iff.2 $
        by rw [direct_sum.to_module.of, direct_sum.to_module.of, Hg])

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

lemma span_preimage_le_comap_span {R M N: Type*} [ring R] [add_comm_group M] [module R M]
  [add_comm_group N] [module R N] (f : N →ₗ M) (s : set M) : span (f ⁻¹' s) ≤ (span s).comap f :=
λ x h, span_induction h
  (by simp only [set.preimage, set.mem_set_of_eq, mem_comap]; exact λ x h, subset_span h)
  (zero_mem ((span s).comap f))
  (λ _ _ hx hy, add_mem ((span s).comap f) hx hy)
  (λ _ _ h, smul_mem ((span s).comap f) _ h)

local attribute [instance, priority 0] classical.dec

noncomputable def totalize : Π i j, G i →ₗ G j :=
λ i j, if h : i ≤ j then f i j h else 0

lemma totalize_apply (i j x) :
  totalize G f i j x = if h : i ≤ j then f i j h x else 0 :=
if h : i ≤ j
  then by dsimp [totalize]; rw [dif_pos h, dif_pos h]
  else by dsimp [totalize]; rw [dif_neg h, dif_neg h, linear_map.zero_apply]
-- set_option trace.simplify.rewrite true



theorem of.zero_exact {i x} (H : of ι G R f i x = 0) :
  ∃ j hij, f i j hij x = (0 : G j) := 
@span_induction _ _ _ _ _ _ _
  (λ y, ∀ i (x : G i), y = direct_sum.of ι G i x →
    ∃ j hij, f i j hij x = (0 : G j))
  ((submodule.quotient.eq _).1 H)
  (λ y hy', let ⟨i, j, Hij, z, hy⟩ := mem_thing.1 hy' in 
    λ k xk hyk,
      let ⟨l, hl⟩ := directed_order.directed i k in
      ⟨l, hl.2, begin
        clear_aux_decl,
        subst hyk,
        have := congr_arg (direct_sum.component ι G k) hy,
        clear hy',
        simp at this,
        subst this,



      end⟩)
  _
  begin
    simp,

  end 
  _ 
  _ _ (sub_zero _)

theorem of.zero_exact {i x} (H : of ι G R f i x = 0) :
  ∃ j hij, f i j hij x = (0 : G j) := 
@span_induction _ _ _ _ _ _ _
  (λ y, ∀ i (x : G i), (direct_sum.to_module ι (λ j, totalize G f j i)) y = x →
    ∃ j hij, f i j hij x = (0 : G j))
  ((submodule.quotient.eq _).1 H)
  (λ y hy', let ⟨i, j, Hij, z, hy⟩ := mem_thing.1 hy' in
    (λ k xk hyk,
      let ⟨l, hl⟩ := directed_order.directed j k in
      ⟨l, hl.2, begin
        clear _let_match _let_match,
        subst hyk,
        have := congr_arg ((direct_sum.of ι G l).comp (direct_sum.to_module ι (λ i, totalize G f i l))) hy,
        simp only [direct_sum.to_module.of, linear_map.map_sub] at this,
        simp [totalize_apply] at *,
        rw [dif_pos (le_trans Hij hl.1), dif_pos hl.1, directed_system.Hcomp f,
          add_neg_self] at this,
        clear H hy' x hy Hij z i i,
        rw [← direct_sum.sum_of y, dfinsupp.sum] at *,
        refine direct_sum.of_inj l _,
        simp only [linear_map.map_sum, direct_sum.to_module.of,
          direct_sum.ext_iff, linear_map.map_zero] at *,
        assume i,
        calc finset.sum (dfinsupp.support y)
              (λ (m : ι), direct_sum.component ι G i
              ((direct_sum.of ι G l) ((f k l _) ((totalize G f m k) (direct_sum.component ι G m y)))))
            = direct_sum.component ι G i
              ((direct_sum.of ι G l) ((f k l _) ((totalize G f l k) (direct_sum.component ι G l y)))) :
            finset.sum_eq_single _ begin
              intros,
              simp [direct_sum.apply_eq_component, totalize_apply],

            end _
        ... = _ : sorry



      end⟩))
  (λ i x hix, ⟨i, le_refl _,
    by rw [← linear_map.map_zero (direct_sum.of ι G i), direct_sum.to_module.of,
      linear_map.map_zero] at hix;
      rw [directed_system.Hid f, hix]⟩)
  (λ x y hx hy i _ hxy,
    let ⟨j, hij, hj⟩ := hx i _ rfl in
    let ⟨k, hik, hk⟩ := hy i _ rfl in
    let ⟨l, hl⟩ := directed_order.directed j k in
    ⟨l, le_trans hij hl.1, begin
      have hx := congr_arg (f j l hl.1) hj,
      have hy := congr_arg (f k l hl.2) hk,
      simp only [directed_system.Hcomp f] at hx hy,
      rw [← hxy, linear_map.map_add, linear_map.map_add, hx, hy],
      simp
    end⟩)
  (λ a x hx i _ hax,
    let ⟨j, hij, hj⟩ := hx i _ rfl in
    ⟨j, hij, begin
      clear _let_match,
      subst hax,
      simp [linear_map.map_smul, hj]
    end⟩)
  _ _
  (begin
    rw [sub_zero, direct_sum.to_module.of, totalize],
    dsimp,
    rw [dif_pos (le_refl _), directed_system.Hid f]
  end)
#print subtype.val
theorem of.zero_exact {i x} (H : of ι G R f i x = 0) :
  ∃ j hij, f i j hij x = (0 : G j) :=
@span_induction _ _ _ _ _ _ _
  (λ y, ∀ i (x : G i), (direct_sum.to_module ι (λ j, totalize G f j i)) y = x →
    ∃ j hij, f i j hij x = (0 : G j))
  ((submodule.quotient.eq _).1 H)
  (λ y hy', let ⟨i, j, Hij, z, hy⟩ := mem_thing.1 hy' in
    (λ k xk hyk,
      let ⟨l, hl⟩ := directed_order.directed j k in
      ⟨l, hl.2, 
        --have i ≤ k → j ≤ k, from _,
        begin
        clear _let_match _let_match hy',
        subst hyk, subst hy,
        simp [direct_sum.apply_eq_component, direct_sum.ext_iff, linear_map.map_sub,
          totalize_apply],
        split_ifs;
        simp [directed_system.Hcomp f] at *,
        



      end⟩))
  (λ i x hix, ⟨i, le_refl _,
    by rw [← linear_map.map_zero (direct_sum.of ι G i), direct_sum.to_module.of,
      linear_map.map_zero] at hix;
      rw [directed_system.Hid f, hix]⟩)
  (λ x y hx hy i _ hxy,
    let ⟨j, hij, hj⟩ := hx i _ rfl in
    let ⟨k, hik, hk⟩ := hy i _ rfl in
    let ⟨l, hl⟩ := directed_order.directed j k in
    ⟨l, le_trans hij hl.1, begin
      have hx := congr_arg (f j l hl.1) hj,
      have hy := congr_arg (f k l hl.2) hk,
      simp only [directed_system.Hcomp f] at hx hy,
      rw [← hxy, linear_map.map_add, linear_map.map_add, hx, hy],
      simp
    end⟩)
  (λ a x hx i _ hax,
    let ⟨j, hij, hj⟩ := hx i _ rfl in
    ⟨j, hij, begin
      clear _let_match,
      subst hax,
      simp [linear_map.map_smul, hj]
    end⟩)
  _ _
  (begin
    rw [sub_zero, direct_sum.to_module.of, totalize],
    dsimp,
    rw [dif_pos (le_refl _), directed_system.Hid f]
  end)

end module

end direct_limit
