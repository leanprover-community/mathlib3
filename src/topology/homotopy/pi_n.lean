import topology.homotopy.basic
import topology.path_connected
import topology.unit_interval
import topology.homotopy.fundamental_groupoid

namespace path
open_locale unit_interval

noncomputable theory

universes u
variables {X:Type u} [topological_space X] 
variables {n:nat} {x:X}

@[derive [metric_space, has_zero, has_one]] 
definition cube (n:nat) := fin n -> I

definition cube_boundary (n:nat) : set (cube n)
  := { y | ∃ i:fin n , y i = 0 ∨ y i = 1}

structure pre_pi (n : nat) (x : X) extends C(cube n,X)
  := (boundary : ∀ y ∈ cube_boundary n, to_fun y = x )

instance pre_pi.fun_like : fun_like (pre_pi n x) (cube n) (λ _, X) := {
  coe := λ f, f.1,
  coe_injective' := begin
    intros f g hfg, cases f, cases g,
    congr, ext1, exact congr_fun hfg _,
  end }

@[ext]
lemma pre_pi.ext (f g : pre_pi n x) (H : ∀ y, f y = g y) : f = g
  := fun_like.ext f g H

@[simp]
lemma pre_pi.mk_apply (f : C(cube n, X)) (H y) : (⟨f, H⟩ : pre_pi n x)  y = f y
  := rfl

definition pre_pi.homotopy (f0 f1 : pre_pi n x)
  := continuous_map.homotopy_rel f0.to_continuous_map f1.to_continuous_map (cube_boundary n)

instance pre_pi.homotopy.fun_like (f g : pre_pi n x) : fun_like (pre_pi.homotopy f g) (cube (n+1)) (λ _, X) := {
  coe := λ h c, h.1 (c 0, fin.tail c),
  coe_injective' := begin
    rintros h1 h2 hfg, cases h1, cases h2,
    congr, ext1 ⟨x,y⟩, simpa only [fin.tail_cons] using congr_fun hfg (fin.cons x y),
  end }
lemma pre_pi.homotopy.continous {f g : pre_pi n x} (h : f.homotopy g) : continuous h
  := begin  refine h.continuous.comp _, continuity; apply continuous_apply  end

lemma pre_pi.homotopy.coe_def  {f g : pre_pi n x} (h : f.homotopy g) (y : cube (n+1))
  : h y = h.1 (y 0, fin.tail y) 
  := rfl

@[refl]
definition pre_pi.homotopy.refl (f : pre_pi n x) : f.homotopy f
  := continuous_map.homotopy_rel.refl _ _ 

@[symm]
definition pre_pi.homotopy.symm {f g : pre_pi n x} : f.homotopy g -> g.homotopy f
  := continuous_map.homotopy_rel.symm

@[trans]
definition pre_pi.homotopy.trans {f g h : pre_pi n x} : f.homotopy g -> g.homotopy h -> f.homotopy h
  := continuous_map.homotopy_rel.trans

definition pre_pi.homotopic (f0 f1 : pre_pi n x) : Prop
  := nonempty (f0.homotopy f1)

@[refl]
lemma pre_pi.homotopic.refl (f : pre_pi n x) : f.homotopic f
  := ⟨pre_pi.homotopy.refl f⟩

@[symm]
lemma pre_pi.homotopic.symm {f g : pre_pi n x} (h : f.homotopic g) : g.homotopic f
  := h.map pre_pi.homotopy.symm

@[trans]
lemma pre_pi.homotopic.trans {f g h : pre_pi n x} (h0 : f.homotopic g) (h1 : g.homotopic h) : f.homotopic h
  := h0.map2 pre_pi.homotopy.trans h1

instance pre_pi.setoid (n : nat) (x : X) : setoid (pre_pi n x)
  := ⟨pre_pi.homotopic, ⟨pre_pi.homotopic.refl, λ _ _, pre_pi.homotopic.symm, λ _ _ _, pre_pi.homotopic.trans⟩⟩

definition pi (n : nat) (x : X) := quotient (pre_pi.setoid n x)

-- Goal 0: pi 0 = path-conected components
variable (X)
definition path_components.setoid : setoid X
  := ⟨λ x y, x∈ path_component y,
    ⟨mem_path_component_self, λ _ _, mem_path_component_of_mem, λ _ _ _, joined.mem_path_component⟩⟩

definition path_components := quotient (path_components.setoid X)
variable {X}

instance cube0_unique : unique (cube 0) := { default := 0,
  uniq := begin intro a, ext1, exact x.elim0  end }

lemma homotopy_at_0 {f g : pre_pi 0 x} (h : f.homotopy g) : h 0 = f 0
  :=  h.apply_zero 0

lemma homotopy_at_1 {f g : pre_pi 0 x} (h : f.homotopy g) : h 1 = g 0
  :=  by convert h.apply_one 1

lemma homotopy_at_0' {f g : pre_pi n x} (h : f.homotopy g) (y : cube n) : h (fin.cons 0 y) = f y
  := begin convert h.apply_zero y, simp [pre_pi.homotopy.coe_def] end

lemma homotopy_at_1' {f g : pre_pi n x} (h : f.homotopy g) (y : cube n) : h (fin.cons 1 y) = g y
  := begin convert h.apply_one y, simp [pre_pi.homotopy.coe_def] end

lemma homotopy_comp0 {f g : pre_pi n x} (h : f.homotopy g) : h ∘ fin.cons 0 = f
  := funext (homotopy_at_0' h)
lemma homotopy_comp1 {f g : pre_pi n x} (h : f.homotopy g) : h ∘ fin.cons 1 = g
  := funext (homotopy_at_1' h)

lemma const0 : ((λ _, 0):cube (0+1)) = (0 : cube (0+1))
  := begin ext1, simp end
lemma const1 : ((λ _, 1):cube (0+1)) = (1 : cube (0+1))
  := begin ext1, simp end

lemma pi0 : pi 0 x ≃ path_components X := {
  to_fun := begin refine quotient.map' _ _, --left-to-right function is a map between quotients
    { intro f, exact f 0 }, --the fuction evaluates the map at 0
    rintros f g ⟨h⟩, symmetry, constructor, --it respects equivalence classes
    refine ⟨⟨(λt,h (λ _, t)),_⟩, _, _⟩, --we need a path from an homotopy
    { refine h.continous.comp _, continuity }, --continuity
    { rw ← homotopy_at_0 h, simp, rw const0 },--0 end point *** non-closing simp
    rw ← homotopy_at_1 h, simp, rw const1 --1 end point     *** non-closing simp
    end,
  inv_fun := begin refine quotient.map' _ _, --right-to-left function is a map between quotients
    { intro y, refine ⟨continuous_map.const y, _⟩,
      rintros _ ⟨f0,_⟩, exact fin.elim0 f0 }, --the function is 'the' constant
    rintros y0 y1 ⟨p⟩, symmetry, constructor, --it respects equivalence clases
    refine ⟨⟨⟨(λ tx, p tx.1),_⟩,_,_⟩, _⟩, --we need an homotopy from a path
    { refine p.continuous.comp _, continuity }, --continuity
    { intro, simp }, --from the first point
    { intro, simp }, --to the second
    rintros _ _ ⟨f0,_⟩, exact fin.elim0 f0 --it sends the boundary to x
    end,
  --the functions are inverse to each other by 'quotient induction'
  left_inv := begin intro f, induction f using quotient.induction_on', simp, --*** non-closing simp
    constructor, convert pre_pi.homotopy.refl _, ext1,
    have Hy : y=matrix.vec_empty := subsingleton.elim _ _,
    simp [Hy], end,
  right_inv := begin intro p, induction p using quotient.induction_on', simp, --*** non-closing simp
    constructor, reflexivity, end,
}

-- Goal 1: pi 1 = fundamental group
definition fundamental_groupoid.mk : X -> fundamental_groupoid X := id

lemma pi1 : pi 1 x ≃ category_theory.End (fundamental_groupoid.mk x) := {
  to_fun := sorry,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry,
}

-- Goal 2: pi n, n>1 abelian
-- Goal 3: countnous map (base preserving) induces homomorphism functorially

end path