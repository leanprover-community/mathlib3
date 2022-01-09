import algebraic_geometry.projective_spectrum.structure_sheaf
import algebraic_geometry.Spec
import algebraic_geometry.Scheme
import algebraic_geometry.projective_spectrum.clear_denominator

noncomputable theory

namespace algebraic_geometry

open_locale classical direct_sum big_operators pointwise big_operators
open direct_sum set_like

variables {R A: Type}
variables [comm_ring R] [comm_ring A] [algebra R A]

variables (𝒜 : ℕ → submodule R A)
  [@graded_algebra ℕ R A (λ (a b : ℕ), classical.prop_decidable (a = b))
    (@ordered_add_comm_monoid.to_add_comm_monoid ℕ
       (@ordered_cancel_add_comm_monoid.to_ordered_add_comm_monoid ℕ
          (@linear_ordered_cancel_add_comm_monoid.to_ordered_cancel_add_comm_monoid ℕ
             nat.linear_ordered_cancel_add_comm_monoid)))
    (@comm_ring.to_comm_semiring R _inst_1)
    (@comm_ring.to_ring A _inst_2)
    _inst_3
    𝒜] [graded_algebra 𝒜]

open Top
open topological_space
open category_theory
open opposite

local notation `pst` := projective_spectrum.Top 𝒜
local notation `pss` := projective_spectrum.structure_sheaf.structure_sheaf 𝒜

open projective_spectrum projective_spectrum.structure_sheaf

local notation `Proj` := @Proj.to_LocallyRingedSpace ℕ R A _ _ _ _ 𝒜 _

local notation `Spec` ring := Spec.LocallyRingedSpace_obj (CommRing.of ring)

lemma aux.pow_deg (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m) : ∀ n, f ^ n ∈ 𝒜 (m * n) :=
begin
  intros n, induction n with n ih,
  rw [pow_zero, mul_zero], exact set_like.graded_monoid.one_mem,
  rw [pow_succ', nat.mul_succ], apply set_like.graded_monoid.mul_mem ih f_deg,
end

@[derive [comm_ring]]
def degree_zero_part (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m) : Type* :=
  subring.mk
    { y : localization.away f | ∃ (n : ℕ) (a : A) (a_deg : a ∈ 𝒜 (m * n)),
      y = localization.mk a ⟨f^n, ⟨n, rfl⟩⟩ }
  ⟨0, 1, begin
    rw mul_zero,
    exact set_like.graded_monoid.one_mem,
  end, begin
    transitivity (localization.mk 1 ⟨1, ⟨0, _⟩⟩ : localization.away f),
    erw localization.mk_self 1,
    rw pow_zero, congr, rw pow_zero,
  end⟩ begin
    rintros _ _ ⟨n1, a1, a1_deg, rfl⟩ ⟨n2, a2, a2_deg, rfl⟩,
    rw localization.mk_mul,
    refine ⟨n1 + n2, a1 * a2, _, _⟩,
    { rw mul_add, apply set_like.graded_monoid.mul_mem a1_deg a2_deg, },
    { congr, rw subtype.ext_iff_val, dsimp only, rw pow_add, refl, },
  end ⟨0, 0, begin
    rw mul_zero, exact submodule.zero_mem _,
  end, begin
    rw localization.mk_zero
  end⟩ begin
    rintros _ _ ⟨n1, a1, a1_deg, rfl⟩ ⟨n2, a2, a2_deg, rfl⟩,
    rw localization.add_mk,
    refine ⟨(n1 + n2), (f ^ n1 * a2 + f ^ n2 * a1), submodule.add_mem _ _ _, _⟩,
    { rw mul_add, apply set_like.graded_monoid.mul_mem _ a2_deg, apply aux.pow_deg, exact f_deg, },
    { rw [add_comm, mul_add], apply set_like.graded_monoid.mul_mem _ a1_deg, apply aux.pow_deg,
      exact f_deg, },
    { congr, rw [subtype.ext_iff_val], dsimp only, rw pow_add, refl, }
  end begin
    rintros _ ⟨n, a, a_deg, rfl⟩,
    rw localization.neg_mk,
    refine ⟨n, -a, submodule.neg_mem _ a_deg, rfl⟩,
  end

def isos.forward.carrier (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m)
  (x : Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))) : ideal (degree_zero_part _ f m f_deg) :=
{ carrier := {z | z.1 ∈ (ideal.span { y | ∃ (g : A), g ∈ x.1.as_homogeneous_ideal.1 ∧
            y = (localization.mk g 1 : localization.away f) }) },
  zero_mem' := submodule.zero_mem _,
  add_mem' := λ z1 z2 hz1 hz2, begin
    refine submodule.add_mem _ hz1 hz2,
  end,
  smul_mem' := λ z1 z2 hz2, begin
    refine submodule.smul_mem _ _ hz2,
  end }

-- def q_d.type (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m)
--   (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) (i : ℕ) :=
-- {a : A // a ∈ 𝒜 i ∧ (localization.mk a ⟨f^i, ⟨i, rfl⟩⟩ : localization.away f) ∈
--   (λ x : degree_zero_part _ f m f_deg, x.1) '' q.1.1 }

-- instance q_d (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m)
--   (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) (i : ℕ) :
--   add_comm_monoid (q_d.type _ f m f_deg q i) :=
-- { zero := ⟨0, begin
--     erw [localization.mk_zero, set.mem_image],
--     refine ⟨submodule.zero_mem _, ⟨(0 : degree_zero_part _ f m f_deg), submodule.zero_mem _, rfl⟩⟩,
--   end⟩,
--   add := λ a b, ⟨a.1 + b.1, begin
--     obtain ⟨ha, x1, hx11, hx12⟩ := a.2,
--     obtain ⟨hb, x2, hx21, hx22⟩ := b.2,
--     dsimp only at hx12 hx22,
--     have eq1 : (localization.mk (a.val + b.val) ⟨f^i, ⟨i, rfl⟩⟩ : localization.away f)
--       = localization.mk a.val ⟨f^i, ⟨i, rfl⟩⟩ + localization.mk b.val ⟨f^i, ⟨i, rfl⟩⟩,
--     { rw [localization.add_mk], simp only [localization.mk_eq_mk'], erw is_localization.eq,
--       use 1, erw [mul_one, mul_one, ←mul_add, add_comm, ←mul_assoc, mul_comm, mul_assoc], congr, },
--     erw [eq1, ←hx12, ←hx22, set.mem_image],
--     refine ⟨submodule.add_mem _ ha hb, x1 + x2, _⟩,
--     refine ⟨submodule.add_mem _ hx11 hx21, rfl⟩,
--   end⟩,
--   add_zero := λ _, by { rw subtype.ext_iff_val, dsimp only, rw add_zero _, },
--   zero_add := λ _, by { rw subtype.ext_iff_val, dsimp only, rw zero_add _, },
--   add_assoc := λ _ _ _, by { rw subtype.ext_iff_val, dsimp only, rw add_assoc, },
--   add_comm := λ a b, by { rw subtype.ext_iff_val, suffices : a.val + b.val = b.val + a.val,
--     convert this, rw add_comm, } }

-- example (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m)
--   (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) : ideal A :=
-- { carrier := { a | ∃ v : ⨁ i, q_d.type _ f m f_deg q i, a = ∑ i in v.support, (v i).1 },
--   zero_mem' := begin
--     use 0, simp only [finset.sum_empty, support_zero],
--   end,
--   add_mem' := λ a b ⟨va, ha⟩ ⟨vb, hb⟩, begin
--     erw [ha, hb],
--     refine ⟨va + vb, _⟩,
--     sorry
--   end,
--   smul_mem' := λ a b ⟨vb, hb⟩, begin
--     erw [hb, finset.smul_sum],
--     have : ∀ (i ∈ vb.support), (localization.mk (a * (vb i).1) ⟨f^(2*i), ⟨2*i, rfl⟩⟩ :
--       localization.away f) ∈ (λ x : degree_zero_part _ f m f_deg, x.1) '' q.1.1,
--     { intros i hi,
--       obtain ⟨hb, mem_q⟩ := (vb i).2,
--       have eq1 : (localization.mk (a * (vb i).1) ⟨f^(2*i), ⟨2*i, rfl⟩⟩ :
--         localization.away f) = localization.mk a ⟨f^i, ⟨i, rfl⟩⟩ *
--         localization.mk (vb i).1 ⟨f^i, ⟨i, rfl⟩⟩,
--       { rw localization.mk_mul, congr, rw [pow_mul, pow_two, mul_pow], },
--         erw [eq1, set.mem_image],
--         refine ⟨⟨localization.mk (a * (vb i).val) ⟨f^(2*i), ⟨2*i, rfl⟩⟩, ⟨2*i, a*(vb i).1, _, rfl⟩⟩, _⟩, },
--     sorry
--   end }

def isos.backward.carrier (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) :
  ideal A :=
{ carrier := { a | localization.mk a 1 ∈
    ideal.span { z : localization.away f | ∃ (c : q.1), z = c.1.1 } },
  zero_mem' := begin
    rw [set.mem_set_of_eq], apply ideal.subset_span,
    use 0, rw localization.mk_zero, refl,
  end,
  add_mem' := λ a b ha hb, begin
    rw [set.mem_set_of_eq] at ha hb ⊢,
    have eq1 : localization.mk (a + b) 1 = localization.mk a 1 + localization.mk b 1,
    { rw localization.add_mk, rw [←subtype.val_eq_coe],
      have : (1 : submonoid.powers f).val = 1 := rfl,
      erw [this, one_mul, mul_one],
      congr' 1, rw [add_comm], congr,
      convert (one_mul _).symm,  },
    erw eq1, apply submodule.add_mem _ ha hb,
  end,
  smul_mem' := λ a b hb, begin
    rw [set.mem_set_of_eq] at hb ⊢,
    rw smul_eq_mul,
    have eq1 : (localization.mk (a * b) 1 : localization.away f) =
      localization.mk a 1 * localization.mk b 1,
    { rw localization.mk_mul,
      congr' 1, erw one_mul, },
    erw eq1,
    refine ideal.mul_mem_left (ideal.span {z : localization.away f | ∃ (c : q.val), z = c.1.1})
      (localization.mk a 1) hb,
  end }

def isos.backward.carrier.homogeneous (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) :
  ideal.is_homogeneous 𝒜 (isos.backward.carrier _ f m f_deg q) := λ i a ha,
begin
  erw [isos.backward.carrier, set.mem_set_of_eq] at ha,
  sorry
end

def isos.forward.carrer_ne_top (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m)
  (x : Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))) :
  ((x.1.as_homogeneous_ideal.1 : set A) ∩ (submonoid.powers f : set A)) = ∅ →
  isos.forward.carrier 𝒜 f m f_deg x ≠ ⊤ := λ eq_top,
begin
  contrapose eq_top, rw not_not at eq_top,
  rw [ideal.eq_top_iff_one, isos.forward.carrier] at eq_top,
  simp only [submodule.mem_mk, set.mem_set_of_eq] at eq_top,
  erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at eq_top,
  obtain ⟨c, eq1⟩ := eq_top,
  rw [finsupp.total_apply, finsupp.sum] at eq1, dsimp only at eq1,
  -- y = localization.mk (g y) 1
  set g :=
  λ (a : {y : localization (submonoid.powers f) | ∃ (g : A),
      g ∈ (projective_spectrum.as_homogeneous_ideal x.val).val ∧ y = localization.mk g 1}),
    classical.some a.2 with g_eq,
  obtain ⟨N, hN⟩ := clear_denominator _ f (finset.image c c.support), -- N is the common denom
  choose after_clear_denominator hacd using hN,
  -- if x ∈ c.support, then `after_clear_denominatro x = x * f ^ N ∈ A`
  have prop1 : ∀ i, i ∈ c.support → c i ∈ finset.image c c.support,
  { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
  set G := ∑ i in c.support.attach, (after_clear_denominator (c i.1) (prop1 i.1 i.2)) * (g i.1) with
    G_eq,
  have G_mem1 : G ∈ x.1.as_homogeneous_ideal.1,
  { apply ideal.sum_mem, intros i hi,
    apply ideal.mul_mem_left,
    refine (classical.some_spec i.1.2).1, },
  have G_mem2 : ∃ (m : ℕ), G * f^m ∈ submonoid.powers f,
  { have eq2 := calc
          (localization.mk G 1 : localization.away f)
        = localization.mk (∑ i in c.support.attach,
          after_clear_denominator (c i.1) (prop1 i.1 i.2) * (g i.1)) 1
        : begin
          congr' 1,
        end
    ... = ∑ i in c.support.attach, localization.mk
            (after_clear_denominator (c i.1) (prop1 i.1 i.2) * (g i.1)) 1
        : begin
          induction c.support.attach using finset.induction_on with a s ha ih,
          { rw [finset.sum_empty, finset.sum_empty, localization.mk_zero], },
          { rw [finset.sum_insert, finset.sum_insert, ←ih, localization.add_mk, mul_one],
            congr' 1, erw [add_comm, one_mul, one_mul], exact ha, exact ha,
             },
        end
    ... = ∑ i in c.support.attach, localization.mk
            (after_clear_denominator (c i.1) (prop1 i.1 i.2)) 1 * localization.mk (g i.1) 1
        : begin
          rw [finset.sum_congr rfl (λ i hi, _)],
          rw [localization.mk_mul, one_mul],
        end
    ... = ∑ i in c.support.attach, (c i.1) * localization.mk (f^N) 1 * localization.mk (g i.1) 1
        : begin
          rw [finset.sum_congr rfl (λ i hi, _)],
          erw ←(hacd _ _).2,
        end
    ... = ∑ i in c.support.attach, (c i.1) * localization.mk (f^N) 1 * i.1.1
        : begin
          rw [finset.sum_congr rfl (λ i hi, _)],
          rw (classical.some_spec i.1.2).2,
        end
    ... = localization.mk (f^N) 1 * ∑ i in c.support.attach, (c i.1) • i.1.1
        : begin
          rw [finset.mul_sum, finset.sum_congr rfl (λ i hi, _)], rw smul_eq_mul, ring,
        end
    ... = localization.mk (f^N) 1 * ∑ i in c.support, (c i) • i.1
        : begin
          congr' 1, apply finset.sum_bij',
          work_on_goal 5 { rintros a ha, exact ⟨a, ha⟩, },
          work_on_goal 3 { rintros a _, exact a.1, },
          { rintros, dsimp only, refl, },
          { rintros, dsimp only, rw subtype.ext_iff, refl, },
          { rintros, dsimp only, rw subtype.ext_iff, },
          { rintros, dsimp only, exact a.2, },
          { rintros, dsimp only, apply finset.mem_attach, },
        end
    ... = localization.mk (f^N) 1 * 1 : by { erw eq1, congr' 1, }
    ... = localization.mk (f^N) 1 : by rw mul_one,
    simp only [localization.mk_eq_mk', is_localization.eq] at eq2,
    obtain ⟨⟨c, ⟨m, rfl⟩⟩, hc2⟩ := eq2,
    erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, show (1 : submonoid.powers f).val = 1, from rfl,
      mul_one, mul_one] at hc2,
    dsimp only at hc2, rw ←pow_add at hc2,
    refine ⟨m, ⟨N+m, hc2.symm⟩⟩, },

  obtain ⟨m, hm⟩ := G_mem2,
  erw [←ne.def, set.ne_empty_iff_nonempty],
  refine ⟨_, _, hm⟩,
  apply ideal.mul_mem_right,
  exact G_mem1,
end

-- forward direction `p ∈ Proj` so `p` is a prime ideal in `A`. Send it to `p S_f ∩ S_(f)`
def isos.top_component.forward (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.1 ⟶
  (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1 :=
{ to_fun := λ x,
    ⟨isos.forward.carrier _ f m f_deg x,
    ⟨begin
      apply isos.forward.carrer_ne_top, by_contra rid,
      erw [←ne.def, set.ne_empty_iff_nonempty] at rid,
      choose g hg using rid,
      obtain ⟨hg1, ⟨k, rfl⟩⟩ := hg, by_cases k_ineq : 0 < k,
      erw ideal.is_prime.pow_mem_iff_mem at hg1,
      apply x.2, exact hg1, exact x.1.is_prime, exact k_ineq,
      have k_eq : 0 = k, linarith,
      erw [←k_eq, pow_zero, ←ideal.eq_top_iff_one] at hg1,
      apply x.1.is_prime.1, exact hg1,
    end, λ x1 x2 hx12, begin
      rw isos.forward.carrier at hx12,
      rcases x1 with ⟨x1, hx1⟩,
      induction x1 using localization.induction_on with data_x1,
      rcases data_x1 with ⟨a1, _, ⟨n1, rfl⟩⟩,
      rcases x2 with ⟨x2, hx2⟩,
      induction x2 using localization.induction_on with data_x2,
      rcases data_x2 with ⟨a2, _, ⟨n2, rfl⟩⟩,
      dsimp only at hx1 hx2 hx12,
      have : (⟨localization.mk a1 ⟨f ^ n1, _⟩, hx1⟩ : degree_zero_part _ f m f_deg) *
          ⟨localization.mk a2 ⟨f ^ n2, _⟩, hx2⟩ =
      ⟨localization.mk a1 ⟨f ^ n1, _⟩ * localization.mk a2 ⟨f ^ n2, _⟩, _⟩ := rfl,
      erw [this] at hx12, simp only [localization.mk_mul] at hx12,
      replace hx12 : localization.mk (a1 * a2) (⟨f ^ n1, _⟩ * ⟨f ^ n2, _⟩) ∈ ideal.span {y :
        localization (submonoid.powers f) | ∃ (g : A),
          g ∈ (projective_spectrum.as_homogeneous_ideal x.val).val ∧ y = localization.mk g 1} :=
          hx12,
      erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hx12,
      obtain ⟨c, eq1⟩ := hx12,
      erw [finsupp.total_apply, finsupp.sum] at eq1,
      -- (a1 a2) / (f^(n + m)) = ∑ i in c.support, (c i) * i,

      have prop1 : ∀ i, i ∈ c.support → c i ∈ finset.image c c.support,
      { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
      set g :=
      λ (a : {y : localization (submonoid.powers f) | ∃ (g : A),
        g ∈ (projective_spectrum.as_homogeneous_ideal x.val).val ∧ y = localization.mk g 1}),
          classical.some a.2 with g_eq,
      obtain ⟨N, hN⟩ := clear_denominator _ f (finset.image c c.support), -- N is the common denom
      choose after_clear_denominator hacd using hN,
      -- if x ∈ c.support, then `after_clear_denominator x = x * f ^ N`
      have eq2 := calc
              localization.mk (f^(n1+n2)) 1 * localization.mk (f^N) 1 *
              ∑ i in c.support, c i • i.1
            = localization.mk (f^(n1+n2)) 1 * localization.mk (f^N) 1 *
              ∑ i in c.support.attach, c (i.1) • i.1.1
            : begin
              congr' 1, apply finset.sum_bij',
              work_on_goal 5 { rintros a _, exact a.1, },
              work_on_goal 3 { rintros a ha, exact ⟨a, ha⟩ },
              { rintros, dsimp only, refl, },
              { rintros, dsimp only, rw subtype.ext_iff, },
              { rintros, dsimp only, rw subtype.ext_iff, refl, },
              { rintros, dsimp only, apply finset.mem_attach, },
              { rintros, dsimp only, exact a.2, },
            end
        ... = localization.mk (f^(n1+n2)) 1 * localization.mk (f^N) 1 *
              ∑ i in c.support.attach, c (i.1) * i.1.1
            : by congr' 1
        ... = localization.mk (f^(n1+n2)) 1 *
              ∑ i in c.support.attach, c (i.1) * localization.mk (f^N) 1 * i.1.1
            : begin
              erw [mul_assoc, finset.mul_sum, finset.sum_congr rfl (λ i hi, _)], ring,
            end
        ... = localization.mk (f^(n1+n2)) 1 * ∑ i in c.support.attach,
                localization.mk (after_clear_denominator (c i.1) (prop1 i.1 i.2)) 1 * i.1.1
            : begin
              erw [finset.sum_congr rfl (λ i hi, _)],
              erw ←(hacd _ _).2,
            end
        ... = localization.mk (f^(n1+n2)) 1 * ∑ i in c.support.attach,
                localization.mk (after_clear_denominator (c i.1) (prop1 i.1 i.2)) 1 *
                localization.mk (g i.1) 1
            : begin
              erw [finset.sum_congr rfl (λ i hi, _)],
              rw (classical.some_spec i.1.2).2,
            end
        ... = localization.mk (f^(n1+n2)) 1 * ∑ i in c.support.attach,
                localization.mk ((after_clear_denominator (c i.1) (prop1 i.1 i.2)) * (g i.1)) 1
            : begin
              erw [finset.sum_congr rfl (λ i hi, _)],
              rw [localization.mk_mul, mul_one],
            end
        ... = localization.mk (f^(n1+n2)) 1 *
              localization.mk (∑ i in c.support.attach, (after_clear_denominator (c i.1)
                (prop1 i.1 i.2)) * (g i.1)) 1
            : begin
              congr' 1,
              induction c.support.attach using finset.induction_on with a s ha ih,
              { rw [finset.sum_empty, finset.sum_empty, localization.mk_zero], },
              { rw [finset.sum_insert, finset.sum_insert, ih, localization.add_mk, mul_one],
                congr' 1, erw [one_mul, one_mul, add_comm], exact ha, exact ha, }
            end,
      erw [eq1, localization.mk_mul, one_mul, localization.mk_mul, one_mul] at eq2,
      have eq3 : (localization.mk (f ^ (n1 + n2) * f ^ N * (a1 * a2)) (⟨f ^ n1, _⟩ * ⟨f ^ n2, _⟩)
        : localization.away f) = localization.mk (f^N * (a1 * a2)) 1,
      { simp only [localization.mk_eq_mk'],
        rw [is_localization.eq], use 1,
        erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one, mul_one, mul_one,
          show (∀ (a b : submonoid.powers f), (a * b).val = a.val * b.val), from λ _ _, rfl,
          pow_add], ring, },
      erw [eq3, localization.mk_mul, mul_one] at eq2,
      simp only [localization.mk_eq_mk'] at eq2,
      erw [is_localization.eq] at eq2,
      obtain ⟨⟨_, ⟨k, rfl⟩⟩, eq2⟩ := eq2,
      erw [mul_one, mul_one, ←subtype.val_eq_coe] at eq2,
      dsimp only at eq2,

      have mem1 : f ^ N * (a1 * a2) * f ^ k ∈ x.1.as_homogeneous_ideal.1,
      { rw eq2, apply ideal.mul_mem_right, apply ideal.mul_mem_left,
        apply ideal.sum_mem, intros i hi,
        apply ideal.mul_mem_left,
        exact (classical.some_spec i.1.2).1, },

      rcases x.1.is_prime.mem_or_mem mem1 with h1|h3,
      rcases x.1.is_prime.mem_or_mem h1 with h1|h2,
      { exfalso, apply x.2,
        apply x.1.is_prime.mem_of_pow_mem N h1, },
      { rcases x.1.is_prime.mem_or_mem h2,
        { left, dsimp only,
          rw isos.forward.carrier,
          have eq3 : (localization.mk a1 ⟨f ^ n1, _⟩ : localization.away f) =
            localization.mk a1 1 * localization.mk 1 ⟨f^n1, ⟨n1, rfl⟩⟩,
          { erw [localization.mk_mul, mul_one, one_mul], },
          suffices : _ ∈ ideal.span {y : localization (submonoid.powers f) | ∃ (g : A),
              g ∈ (projective_spectrum.as_homogeneous_ideal x.val).val ∧ y = localization.mk g 1},
          exact this, dsimp only,
          erw eq3,
          suffices : localization.mk a1 1 ∈ ideal.span _,
          apply ideal.mul_mem_right _ _ this,
          apply ideal.subset_span,
          refine ⟨a1, h, rfl⟩, },
        { right, dsimp only,
          rw isos.forward.carrier,
          have eq3 : (localization.mk a2 ⟨f ^ n2, _⟩ : localization.away f) =
            localization.mk a2 1 * localization.mk 1 ⟨f^n2, ⟨n2, rfl⟩⟩,
          { erw [localization.mk_mul, mul_one, one_mul], },
          suffices : _ ∈ ideal.span {y : localization (submonoid.powers f) | ∃ (g : A),
              g ∈ (projective_spectrum.as_homogeneous_ideal x.val).val ∧ y = localization.mk g 1},
          exact this, dsimp only,
          erw eq3,
          suffices : localization.mk a2 1 ∈ ideal.span _,
          apply ideal.mul_mem_right _ _ this,
          apply ideal.subset_span,
          refine ⟨a2, h, rfl⟩, } },
      { exfalso, apply x.2,
        apply x.1.is_prime.mem_of_pow_mem k h3, },
    end⟩⟩,
  continuous_to_fun := begin
    apply is_topological_basis.continuous,
    exact prime_spectrum.is_topological_basis_basic_opens,
    rintros _ ⟨y, rfl⟩, dsimp only,
    sorry
  end }

lemma isos.top_component.backward (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1 ⟶
  (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.1 :=
{ to_fun := λ q, ⟨⟨⟨isos.backward.carrier _ f m f_deg q, sorry⟩, sorry⟩, sorry⟩,
  continuous_to_fun := sorry }

def isos.top_component (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.1 ≅
  (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1 := sorry


def isos.sheaf_component (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (isos.top_component 𝒜 f m f_deg).hom _*
    ((Proj.to_LocallyRingedSpace 𝒜).restrict _).to_SheafedSpace.to_PresheafedSpace.presheaf ≅
  (Spec degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg).to_SheafedSpace.to_PresheafedSpace.presheaf :=
sorry

def isos (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f)) ≅ (Spec (degree_zero_part _ f m f_deg)) :=
  LocallyRingedSpace.iso_of_SheafedSpace_iso $ SheafedSpace.iso_of_presheaf_iso _ _ $
  @PresheafedSpace.iso_of_components _ _
    (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace
    (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace
    (isos.top_component _ f m f_deg) (isos.sheaf_component _ f m f_deg)

def test.choose_element (x : pst) : Σ' (n : ℕ) (f : A), f ∈ 𝒜 n ∧ f ∉ x.as_homogeneous_ideal.1 :=
begin
  have := x.2.2,
  erw set.not_subset at this,
  choose f h1 h2 using this,
  erw ←graded_algebra.sum_support_decompose 𝒜 f at h2,
  have : ∃ (n : ℕ), (graded_algebra.decompose 𝒜 f n : A) ∉ x.as_homogeneous_ideal.1,
  { by_contra rid, simp only [not_exists_not, subtype.val_eq_coe] at rid, apply h2,
    apply ideal.sum_mem, intros, apply rid, },
  choose n hn using this,
  refine ⟨n, (graded_algebra.decompose _ f n : A), submodule.coe_mem _, hn⟩,
end

def Proj.to_Scheme : Scheme :=
{ local_affine := λ x, ⟨⟨projective_spectrum.basic_open 𝒜 (test.choose_element 𝒜 x).2.1, begin
    rw projective_spectrum.mem_basic_open,
    exact (test.choose_element 𝒜 x).2.2.2,
  end⟩,
  ⟨CommRing.of (degree_zero_part _ (test.choose_element 𝒜 x).2.1 (test.choose_element 𝒜 x).1
    (test.choose_element 𝒜 x).2.2.1), ⟨isos 𝒜 (test.choose_element 𝒜 x).2.1 (test.choose_element 𝒜 x).1
    (test.choose_element 𝒜 x).2.2.1⟩⟩⟩,
  ..Proj }

end algebraic_geometry
