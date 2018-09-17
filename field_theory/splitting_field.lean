import ring_theory.euclidean_domain data.polynomial

universes u v

namespace quotient_ring -- move this to the right file
open is_submodule
variables {α : Type u} [comm_ring α] {β : Type v} [comm_ring β]

local attribute [instance] quotient_rel

def lift (S : set α) [is_ideal S] (f : α → β) [is_ring_hom f] (H : ∀ (a : α), a ∈ S → f a = 0) :
quotient S → β :=
quotient.lift f $ λ a b h,
eq_of_sub_eq_zero (by rw quotient_rel_eq at h;
  simpa only [is_ring_hom.map_sub f] using H _ h)

variables {S : set α} [is_ideal S] {f : α → β} [is_ring_hom f] {H : ∀ (a : α), a ∈ S → f a = 0} {a : α}

@[simp] lemma lift_mk : lift S f H ⟦a⟧ = f a := rfl

instance : is_ring_hom (lift S f H) :=
{ map_one := by show lift S f H ⟦1⟧ = 1; simp [is_ring_hom.map_one f],
  map_add := λ a₁ a₂, quotient.induction_on₂ a₁ a₂ $ λ a₁ a₂, begin
    show lift S f H (mk a₁ + mk a₂) = lift S f H ⟦a₁⟧ + lift S f H ⟦a₂⟧,
    have := quotient_ring.is_ring_hom_mk S,
    rw ← this.map_add,
    show lift S f H (⟦a₁ + a₂⟧) = lift S f H ⟦a₁⟧ + lift S f H ⟦a₂⟧,
    simp only [lift_mk, is_ring_hom.map_add f],
  end,
  map_mul := λ a₁ a₂, quotient.induction_on₂ a₁ a₂ $ λ a₁ a₂, begin
    show lift S f H (mk a₁ * mk a₂) = lift S f H ⟦a₁⟧ * lift S f H ⟦a₂⟧,
    have := quotient_ring.is_ring_hom_mk S,
    rw ← this.map_mul,
    show lift S f H (⟦a₁ * a₂⟧) = lift S f H ⟦a₁⟧ * lift S f H ⟦a₂⟧,
    simp only [lift_mk, is_ring_hom.map_mul f],
  end }

end quotient_ring


namespace adjoin_root
open polynomial
variables {K : Type u} [discrete_field K] (f : polynomial K) [irreducible f]

def S : set (polynomial K) :=
@span _ _ _ ring.to_module ({f} : set (polynomial K))

instance S.is_ideal : is_ideal (S f) := is_ideal.span _

instance S.is_maximal_ideal : is_maximal_ideal (S f) :=
is_maximal_ideal_of_irreducible ‹irreducible f›

def quotient_rel := quotient_ring.quotient_rel (S f)

local attribute [instance] quotient_rel

def adjoin_root {K : Type u} [discrete_field K] (f : polynomial K) [irreducible f] : Type u :=
quotient_ring.quotient (S f)

noncomputable instance field : discrete_field (adjoin_root f) :=
quotient_ring.field (S f)

variables {f}

def mk : polynomial K → adjoin_root f := quotient_ring.mk

def root : adjoin_root f := ⟦X⟧

def of (x : K) : adjoin_root f := ⟦C x⟧

instance adjoin_root.has_coe_t : has_coe_t K (adjoin_root f) := ⟨of⟩

instance mk.is_ring_hom : is_ring_hom (mk : polynomial K → adjoin_root f) :=
quotient_ring.is_ring_hom_mk (S f)

instance : is_field_hom (coe : K → adjoin_root f) :=
@is_ring_hom.comp _ _ _ _ C _ _ _ mk mk.is_ring_hom

section lift

variables {L : Type v} [discrete_field L]

def lift (i : K → L) [is_field_hom i] (x : L) (h : f.eval₂ i x = 0) : (adjoin_root f) → L :=
quotient_ring.lift (S f) (eval₂ i x) $ λ g H,
by
  simp [S, span_singleton] at H;
  cases H with y H;
  dsimp at H;
  rw [← H, eval₂_mul];
  simp [h]

variables {i : K → L} [is_field_hom i] {α : L} {h : f.eval₂ i α = 0}

@[simp] lemma lift_mk {g : polynomial K} : lift i α h ⟦g⟧ = g.eval₂ i α := quotient_ring.lift_mk

@[simp] lemma lift_root : lift i α h root = α := by simp [root, h]

@[simp] lemma lift_of {x : K} : lift i α h x = i x := by show lift i α h ⟦C x⟧ = i x; simp

end lift

end adjoin_root
