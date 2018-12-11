import ring_theory.euclidean_domain data.polynomial

universes u v

namespace adjoin_root
open polynomial ideal
variables {K : Type u} [discrete_field K] (f : polynomial K) [irreducible f]

instance is_maximal_span : is_maximal (span {f} : ideal (polynomial K)) :=
is_maximal_of_irreducible ‹irreducible f›

def adjoin_root {K : Type u} [discrete_field K] (f : polynomial K) [irreducible f] : Type u :=
ideal.quotient (span {f} : ideal (polynomial K))

variables {f}

def mk : polynomial K → adjoin_root f := ideal.quotient.mk _

noncomputable instance field : discrete_field (adjoin_root f) :=
{ has_decidable_eq := λ p q, @quotient.rec_on_subsingleton₂ _ _ (id _) (id _)
    (λ p q, decidable (p = q)) _ p q (λ p q, show decidable (mk p = mk q),
      from decidable_of_iff ((p - q) % f = 0)
        (by simp [mk, ideal.quotient.eq, mem_span_singleton])),
  inv_zero := by convert dif_pos rfl,
  ..ideal.quotient.field (span {f} : ideal (polynomial K)) }

def root : adjoin_root f := mk X

def of (x : K) : adjoin_root f := mk (C x)

instance adjoin_root.has_coe_t : has_coe_t K (adjoin_root f) := ⟨of⟩

instance mk.is_ring_hom : is_ring_hom (mk : polynomial K → adjoin_root f) :=
ideal.quotient.is_ring_hom_mk _

instance : is_field_hom (coe : K → adjoin_root f) :=
@is_ring_hom.comp _ _ _ _ C _ _ _ mk mk.is_ring_hom

section lift

variables {L : Type v} [discrete_field L]

def lift (i : K → L) [is_field_hom i] (x : L) (h : f.eval₂ i x = 0) : (adjoin_root f) → L :=
ideal.quotient.lift _ (eval₂ i x) $ λ g H,
by
  simp [mem_span_singleton] at H;
  cases H with y H;
  dsimp at H;
  rw [H, eval₂_mul];
  simp [h]

variables {i : K → L} [is_field_hom i] {α : L} {h : f.eval₂ i α = 0}

@[simp] lemma lift_mk {g : polynomial K} : lift i α h (mk g) = g.eval₂ i α :=
ideal.quotient.lift_mk

@[simp] lemma lift_root : lift i α h root = α := by simp [root, h]

@[simp] lemma lift_of {x : K} : lift i α h x = i x :=
by show lift i α h (ideal.quotient.mk _ (C x)) = i x;
  convert ideal.quotient.lift_mk; simp

end lift

end adjoin_root
