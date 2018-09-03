import ring_theory.euclidean_domain data.polynomial

universe u

def adjoin_root {K : Type u} [discrete_field K] (f : polynomial K) [irreducible f] : Type u :=
@quotient_ring.quotient _ _
  (@span _ _ _ ring.to_module ({f} : set (polynomial K))) (is_ideal.span _)

namespace adjoin_root
variables {K : Type u} [discrete_field K] (f : polynomial K) [irreducible f]

def S : set (polynomial K) :=
@span _ _ _ ring.to_module ({f} : set (polynomial K))

instance S.is_ideal : is_ideal (S f) := is_ideal.span _

instance S.is_maximal_ideal : is_maximal_ideal (S f) :=
is_maximal_ideal_of_irreducible ‹irreducible f›

noncomputable instance field : discrete_field (adjoin_root f) :=
@quotient_ring.field _ _ (S f) (S.is_maximal_ideal f)

variables {f}

def mk : polynomial K → adjoin_root f :=
@quotient_ring.mk _ _ (S f) (S.is_ideal f)

def root : adjoin_root f := mk polynomial.X

def of (x : K) : adjoin_root f := mk (polynomial.C x)

instance adjoin_root.has_coe_t : has_coe_t K (adjoin_root f) := ⟨of⟩

instance mk.is_ring_hom : is_ring_hom (mk : polynomial K → adjoin_root f) :=
@quotient_ring.is_ring_hom_mk _ _ (S f) (S.is_ideal f)

instance : is_field_hom (coe : K → adjoin_root f) :=
@is_ring_hom.comp K _ _ _ polynomial.C _ _ _ mk mk.is_ring_hom

def lift {L} [discrete_field L] (g : K → L) [is_field_hom g]
  (x : L) (h : f.eval₂ g x = 0) (q : adjoin_root f) : L :=
sorry

end adjoin_root
