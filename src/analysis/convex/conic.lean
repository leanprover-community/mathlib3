import analysis.convex.cone

noncomputable theory
structure proper_cone (E : Type*) [inner_product_space ℝ E]:=
(carrier : convex_cone ℝ E)
(ne : (carrier : set E).nonempty)
(cl : is_closed (carrier : set E))

-- def convex_cone.cone_le (K : convex_cone ℝ E) (x y : E) := ∃ k : K, x + k = y

-- def cone_preorder (K : closed_convex_cone E) : preorder E :=
-- { le := λ x y, ∃ k : K.carrier, x + k = y,
--   lt := λ x y, x ≠ y ∧ ∃ k : K.carrier, x + k = y ,
--   le_refl := λ x,
--   begin
--   have := pointed_of_nonempty_closed K.ne K.cl,
--   unfold convex_cone.pointed at this,
--   end,
--   le_trans := _,
--   lt_iff_le_not_le := _ }


namespace dual_conic_program
/-- A dual conic program for decision variables `x` is a system of inequalities
`constraints_i x ≤K bounds_i` for all `i ∈ I` where `x ≤K y` means there exists a `k ∈ K` such that
` x + k = y`. -/
structure dual_conic_program (H H' : Type*) [inner_product_space ℝ H] [inner_product_space ℝ H'] :=
(K : proper_cone H')
(obj : H →L[ℝ] ℝ)
(I : Type*)
(constraints: I → H →L[ℝ] H')
(bounds: I → H')

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F] [complete_space E] [complete_space F]

def is_feasible (p : dual_conic_program E F) := { x : E | ∀ i, ∃ k : p.K.carrier, p.constraints i x + k = p.bounds i }

def obj_value (p : dual_conic_program E F) (x : E) := p.obj x

def is_optimal (p : dual_conic_program E F) (x : E) := is_feasible p x ∧ ∀ y, is_feasible p y → obj_value p y ≤ obj_value p x

end dual_conic_program
