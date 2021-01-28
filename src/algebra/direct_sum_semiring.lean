import algebra.direct_sum
import ring_theory.subsemiring

variables
  {A : Type*} [semiring A]
  {ι : Type*} [add_comm_monoid ι] [decidable_eq ι]

namespace direct_sum

class semiring_add_gradation (carriers : ι → add_submonoid A) :=
(one_mem : (1 : A) ∈ carriers 0)
(mul_mem : ∀ {i j} (gi : carriers i) (gj : carriers j), (gi * gj : A) ∈ carriers (i + j))

variables (carriers : ι → add_submonoid A) [semiring_add_gradation carriers]


open_locale direct_sum

/-! First, define multiplication and 1 on the individual carriers, and show they form a
heq-monoid-/
def hmul {i j} : carriers i →+ carriers j →+ carriers (i + j) :=
{ to_fun := λ a,
  { to_fun := λ b, ⟨(a * b : A), semiring_add_gradation.mul_mem a b⟩,
    map_add' := λ _ _, subtype.ext (mul_add _ _ _),
    map_zero' := subtype.ext (mul_zero _), },
  map_add' := λ _ _, add_monoid_hom.ext $ λ _, subtype.ext (add_mul _ _ _),
  map_zero' := add_monoid_hom.ext $ λ _, subtype.ext (zero_mul _) }

def hone : carriers 0 := ⟨1, semiring_add_gradation.one_mem⟩

lemma hone_hmul {i} (a : carriers i) : hmul carriers (hone carriers) a == a :=
begin
  rw subtype.heq_iff_coe_eq,
  { exact one_mul _ },
  { exact λ x, (zero_add i).symm ▸ iff.rfl, }
end

lemma hmul_hone {i} (a : carriers i) : hmul carriers a (hone carriers) == a :=
begin
  rw subtype.heq_iff_coe_eq,
  exact mul_one _,
  exact λ x, (add_zero i).symm ▸ iff.rfl,
end

lemma hmul_assoc {i j k} (a : carriers i) (b : carriers j) (c : carriers k) :
  hmul carriers (hmul carriers a b) c == hmul carriers a (hmul carriers b c) :=
begin
  rw subtype.heq_iff_coe_eq,
  exact mul_assoc _ _ _,
  exact λ x, (add_assoc i j k).symm ▸ iff.rfl,
end


/-! Next, compose them with `direct_sum.of`. -/

def mul_def' {i j} : carriers i →+ carriers j →+ ⨁ i, carriers i :=
{ to_fun := λ a,
    add_monoid_hom.comp_hom (direct_sum.of (λ i, carriers i) $ i + j) (hmul carriers a),
  map_add' := λ a b, by simp only [add_monoid_hom.map_add],
  map_zero' := by simp only [add_monoid_hom.map_zero] }

def one_def' : ⨁ i, carriers i := direct_sum.of (λ i, carriers i) 0 (hone carriers)

instance : has_one (⨁ i, carriers i) :=
{ one := direct_sum.of (λ i, carriers i) 0 (hone carriers)}

instance : has_mul (⨁ i, carriers i) :=
{ mul := λ a b, begin
    refine direct_sum.to_add_monoid (λ j,
      direct_sum.to_add_monoid (λ i,
        _
      ) a
    ) b,
    exact mul_def' carriers,
  end }

/-! Now the fun begins! -/

lemma one_mul (x : ⨁ i, carriers i) : 1 * x = x :=
begin
  unfold has_one.one has_mul.mul one_def' mul_def',
  simp only [add_monoid_hom.coe_mk, to_add_monoid_of, add_monoid_hom.comp_hom_apply_apply],
  rw [direct_sum.to_add_monoid, dfinsupp.lift_add_hom_apply],
  haveI : Π (i : ι) (x : (λ i, ↥(carriers i)) i), decidable (x ≠ 0) := λ i x, classical.dec _,
  rw @dfinsupp.sum_add_hom_apply ι (λ i, ↥(carriers i)) _ _ _ ‹_›,
  simp [add_monoid_hom.coe_comp, function.comp, direct_sum.of],
  convert dfinsupp.sum_single,
  ext1 i, ext1 xi,
  congr,
  exact zero_add _,
  exact hone_hmul _ xi,
  assumption
end

@[simp,to_additive]
lemma monoid_hom.coe_dfinsupp_prod' {β : ι → Type*} {R S : Type*} [monoid R] [comm_monoid S]
  [Π (i : ι), has_zero (β i)]
  {_ : Π (i : ι) (x : β i), decidable (x ≠ 0)}
  (f : Π₀ i, β i) (g : Π i, β i → R →* S) :
  ⇑(f.prod g) = f.prod (λ a b, (g a b)) :=
@monoid_hom.coe_dfinsupp_prod ι β _ _ _ _ _ _ _ f g

lemma mul_one (x : ⨁ i, carriers i) : x * 1 = x :=
begin
  unfold has_one.one has_mul.mul one_def' mul_def',
  simp only [add_monoid_hom.coe_mk, to_add_monoid_of, add_monoid_hom.comp_hom_apply_apply],
  rw [direct_sum.to_add_monoid, dfinsupp.lift_add_hom_apply],
  haveI : Π (i : ι) (x : (λ i, ↥(carriers i)) i), decidable (x ≠ 0) := λ i x, classical.dec _,
  -- haveI : Π (i : ι) (x : carriers i), decidable (x ≠ 0) := λ i x, classical.dec _,
  rw @dfinsupp.sum_add_hom_apply ι (λ i, ↥(carriers i)) _ _ _ ‹_›,
  simp [add_monoid_hom.coe_comp, function.comp, direct_sum.of, dfinsupp.single_add_hom,
    add_monoid_hom.coe_dfinsupp_sum],
  convert dfinsupp.sum_single,
  ext1 i, ext1 xi,
  congr,
  -- simp [add_monoid_hom.dfinsupp_sum_apply],
  -- ext1 i, ext1 xi,
  -- congr,
  -- exact zero_add _,
  -- have := hone_hmul _ xi,
  -- exact this,
  -- assumption
end


#print direct_sum.has_mul

#check dfinsupp.sum

end direct_sum
