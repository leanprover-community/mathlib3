import representation_theory.Rep
import representation_theory.fdRep

noncomputable theory
open_locale classical

lemma my_lemmaA {R : Type*} [comm_semiring R] {G : Type*} [group G] (f : monoid_algebra R G) :
  f ∈ subalgebra.center R (monoid_algebra R G) ↔ ∀ a b : G, is_conj a b → f a = f b :=
begin
  rw subalgebra.mem_center_iff, refine ⟨λ hf a b hab, _, λ hab g, _⟩,
  { cases hab with c hc, symmetry,
    calc _ = (f * finsupp.single c.val 1) (b * c) : by simp
    ...    = (_ * f) (c * a) : by rw [hc.eq, hf]
    ...    = _ : by simp },
  { rw [←finsupp.sum_single g, finsupp.mul_sum, finsupp.sum_mul],
    congr, ext c r,
    have h : is_conj (c⁻¹ * a) (a * c⁻¹) := by { rw is_conj_iff, use c, simp },
    rw [monoid_algebra.mul_single_apply, monoid_algebra.single_mul_apply, mul_comm, hab _ _ h] }
end

lemma my_lemmaA' {R : Type*} [comm_semiring R] {G : Type*} [group G]
  (f : subalgebra.center R (monoid_algebra R G)) (a b : G) (h : is_conj a b) : f a = f b := by
{ change f.val a = f.val b, exact (my_lemmaA f.val).mp f.prop a b h }

lemma my_lemmaB {R : Type*} [comm_semiring R] {G : Type*} [group G]
  (f : subalgebra.center R (monoid_algebra R G)) (a : G) (h : a ∈ f.val.support) :
  (conj_classes.mk a).carrier.finite :=
begin
  have : (conj_classes.mk a).carrier ⊆ f.val.support := λ b hb, by
  { change b ∈ f.val.support,
    rw finsupp.mem_support_iff,
    change f b ≠ 0,
    rw ←my_lemmaA' f a b hb,
    exact finsupp.mem_support_iff.mp h },
  exact set.finite.subset (by apply finset.finite_to_set) this,
end

lemma conj_lemma {G : Type*} [group G] (g : G) : is_conj (quot.out (conj_classes.mk g)) g :=
(@quotient.mk_out _ (is_conj.setoid _) g)

section examples
variables {α : Type*} (s : set α) (t : finset α)
example : finite (t : set α) := finite.of_fintype t
example : set.finite (t : set α) := finset.finite_to_set t
example : fintype t := finset.fintype_coe_sort t
example (h : set.finite s) : finset α := set.finite.to_finset h
example (h : set.finite s) : finite s := set.finite_coe_iff.mpr h
example (h : finite s) : finset α := set.finite.to_finset (s.to_finite)

--example (h : finite s) : set.finite s := s.to_finite
--example (h : set.finite s) : finset α := set.finite.to_finset h
end examples

variables (R : Type*) [comm_semiring R] (G : Type*) [group G]

def fun1 :
  subalgebra.center R (monoid_algebra R G) → { c : conj_classes G | c.carrier.finite } →₀ R := λ f,
{ support := finset.image (λ g : f.val.support, ⟨conj_classes.mk g, my_lemmaB f g g.prop⟩) ⊤,
  to_fun := λ c, f (quot.out c.val),
  mem_support_to_fun := λ c,
  begin
    rw finset.mem_image, split; intro h,
      rcases h with ⟨g, _, hg⟩,
      intro _,
      apply finsupp.mem_support_iff.mp g.prop,
      change f g = 0,
      rwa [my_lemmaA' f g (quot.out c.val)],
      rw ←hg,
      exact (conj_lemma _).symm,
    use quot.out c.val,
    exact finsupp.mem_support_iff.mpr h,
    refine ⟨by simp, subtype.eq _⟩,
    exact @quotient.out_eq _ (is_conj.setoid _) c.val
  end}

def fun2 :
  ({c : conj_classes G | c.carrier.finite} →₀ R) → subalgebra.center R (monoid_algebra R G) := λ f,
{ val := {
  support := set.finite.to_finset (set.finite.bUnion (finset.finite_to_set f.support)
    (λ c hc, c.prop)),
  to_fun := λ g, dite (conj_classes.mk g).carrier.finite (λ h, f ⟨conj_classes.mk g, h⟩) (λ h, 0),
  mem_support_to_fun := λ a, begin
    rw [set.finite.mem_to_finset, set.mem_Union], split; intro h,
    { rcases h with ⟨c, s, hs, ha⟩,
      rw set.mem_range at hs,
      cases hs with hc hs,
      rw [←hs, conj_classes.mem_carrier_iff_mk_eq] at ha,
      rw [dif_pos, ←finsupp.mem_support_iff],
      { convert hc, apply subtype.eq, simpa },
      { rw ha, exact c.prop } },
    { rw dite_ne_right_iff at h,
      cases h with h h',
      rw ←finsupp.mem_support_iff at h',
      simp_rw set.mem_Union,
      refine Exists.intro ⟨_,h⟩ ⟨h', by rw [subtype.coe_mk, conj_classes.mem_carrier_iff_mk_eq]⟩ }
  end },
  property := by {rw my_lemmaA, intros a b h, dsimp, rw conj_classes.mk_eq_mk_iff_is_conj.mpr h}}

def my_iso (R : Type*) [comm_semiring R] (G : Type*) [group G]:
  subalgebra.center R (monoid_algebra R G) ≃ₗ[R] {c : conj_classes G | c.carrier.finite} →₀ R :=
{ to_fun := fun1 R G,
  map_add' := λ x y, by { ext a, apply finsupp.add_apply },
  map_smul' := λ r x, by { ext a, apply finsupp.smul_apply },
  inv_fun := fun2 R G,
  left_inv := λ f, begin
    ext g,
    change ite _ (f (quot.out (conj_classes.mk g))) 0 = f g,
    rw ite_eq_iff', refine ⟨λ h, my_lemmaA' _ _ _ (conj_lemma _), λ h, _⟩,
    by_contra h', apply h, apply my_lemmaB f, rw finsupp.mem_support_iff, exact ne.symm h',
  end,
  right_inv := λ f, begin
    ext c,
    change dite _ _ _  = f c,
    have : conj_classes.mk (quot.out c.val) = c := quot.out_eq _,
    rw [this, dif_pos],
    simp,
    exact c.prop,
  end,}

/-def finsupp.add_comm_monoid_equiv_congr_left {α β: Type*} {M : Type*} [add_comm_monoid M] (f : α ≃ β) :
  (α →₀ R) ≃+ (β →₀ R) :=
begin

end-/

namespace finsupp

def linear_equiv_congr_left {α β: Type*} {R : Type*} [semiring R] (f : α ≃ β) :
  (α →₀ R) ≃ₗ[R] (β →₀ R) :=
{ to_fun := (equiv_congr_left f).to_fun,
  map_add' := λ x y, by { ext a, simp },
  map_smul' := λ r x, by { ext a, simp },
  inv_fun := (equiv_congr_left f).inv_fun,
  left_inv := (equiv_congr_left f).left_inv,
  right_inv := (equiv_congr_left f).right_inv }

end finsupp

def set.univ_equiv (α : Type*) : @set.univ α ≃ α :=
⟨λ a, a, λ a, ⟨a, trivial⟩, λ a, subtype.coe_eta _ _, λ a, refl _⟩

def my_iso_finite (R : Type*) [comm_semiring R] (G : Type*) [group G] [finite G] :
  subalgebra.center R (monoid_algebra R G) ≃ₗ[R] conj_classes G →₀ R :=
begin
  have : {c : conj_classes G | c.carrier.finite} = set.univ := set.ext (λ c,
    ⟨λ h, set.mem_univ _, λ h, set.finite.subset (set.to_finite _) (set.subset_univ _)⟩),
  refine linear_equiv.trans (my_iso R G) (finsupp.linear_equiv_congr_left _),
  convert set.univ_equiv _,
end

/-def my_iso (R : Type*) [comm_semiring R] (G : Type*) [group G]:
  subalgebra.center R (monoid_algebra R G) ≃ₗ[R] {c : conj_classes G | c.carrier.finite} →₀ R :=
{ to_fun := λ f,
  { support := finset.image (λ g : f.val.support, ⟨conj_classes.mk g, my_lemmaB f g g.prop⟩) ⊤,
    to_fun := λ c, f (quot.out c.val),
    mem_support_to_fun := λ c,
    begin sorry {
      rw finset.mem_image, split; intro h,
        rcases h with ⟨g, _, hg⟩,
        intro _,
        apply finsupp.mem_support_iff.mp g.prop,
        change f g = 0,
        rwa [my_lemmaA' f g (quot.out c.val)],
        rw ←hg,
        exact conj_lemma _,
      use quot.out c.val,
      exact finsupp.mem_support_iff.mpr h,
      refine ⟨by simp, subtype.eq _⟩,
      exact @quotient.out_eq _ (is_conj.setoid _) c.val, }
    end},
  map_add' := λ x y, by { ext a, apply finsupp.add_apply },
  map_smul' := λ r x, by { ext a, apply finsupp.smul_apply },
  inv_fun := λ f, {
    val := {
      support := set.finite.to_finset (set.finite.bUnion (finset.finite_to_set f.support)
        (λ c hc, c.prop)),
      to_fun := λ g, dite (conj_classes.mk g).carrier.finite (λ h, f ⟨conj_classes.mk g, h⟩) (λ h, 0),
      mem_support_to_fun := λ a, begin sorry {
        rw [set.finite.mem_to_finset, set.mem_Union], split; intro h,
        { rcases h with ⟨c, s, hs, ha⟩,
          rw set.mem_range at hs,
          cases hs with hc hs,
          rw [←hs, conj_classes.mem_carrier_iff_mk_eq] at ha,
          rw [dif_pos, ←finsupp.mem_support_iff],
          { convert hc, apply subtype.eq, simpa },
          { rw ha, exact c.prop } },
        { rw dite_ne_right_iff at h,
          cases h with h h',
          use ⟨_,h⟩,
          rw set.mem_Union,
          rw ←finsupp.mem_support_iff at h',
          use h',
          rw conj_classes.mem_carrier_iff_mk_eq,
          refl }, }
      end },
    property := by {rw my_lemmaA, intros a b h, dsimp, rw conj_classes.mk_eq_mk_iff_is_conj.mpr h}},
  left_inv := λ f, begin
    ext g, dsimp, rw ite_eq_iff', refine ⟨λ h, _, λ h, _⟩,
  end,
  right_inv := _,}-/
