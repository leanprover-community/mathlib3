import algebra.category.CommRing.basic
import category_theory.hygienic

universes v u

open category_theory

-- We want to automate as much as possible the observation that
-- if R ≅ S as rings, then 0 = 1 in R implies 0 = 1 in S.

@[derive hygienic]
def zero_ring (R : Ring) : Prop := (0 : R) = (1 : R)
