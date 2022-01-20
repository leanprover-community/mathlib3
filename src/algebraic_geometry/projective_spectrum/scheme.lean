import algebraic_geometry.projective_spectrum.structure_sheaf
import algebraic_geometry.Spec
import algebraic_geometry.Scheme
import algebraic_geometry.projective_spectrum.clear_denominator

noncomputable theory

namespace algebraic_geometry

open_locale direct_sum big_operators pointwise big_operators
open direct_sum set_like

variables {R A: Type}
variables [comm_ring R] [comm_ring A] [algebra R A] [nontrivial A]

variables (𝒜 : ℕ → submodule R A)
variables [graded_algebra 𝒜] [Π (i : ℕ) (x : 𝒜 i), decidable (x ≠ 0)]

open Top
open topological_space
open category_theory
open opposite

local notation `pst` := projective_spectrum.Top 𝒜
local notation `pss` := projective_spectrum.structure_sheaf.structure_sheaf 𝒜

open projective_spectrum projective_spectrum.structure_sheaf

local notation `Proj` := Proj.to_LocallyRingedSpace 𝒜


local notation `Spec` ring := Spec.LocallyRingedSpace_obj (CommRing.of ring)

lemma aux.pow_deg (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m) : ∀ n, f ^ n ∈ 𝒜 (m * n) :=
begin
  intros n, induction n with n ih,
  rw [pow_zero, mul_zero], exact set_like.graded_monoid.one_mem,
  rw [pow_succ', nat.mul_succ], apply set_like.graded_monoid.mul_mem ih f_deg,
end

@[derive [comm_ring]]
def degree_zero_part (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m) : subring (localization.away f) :=
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

def isos.forward.carrier' (f : A) (m : ℕ) (f_deg : f ∈ 𝒜 m)
  (x : Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))) : ideal (degree_zero_part _ f m f_deg) :=
ideal.span
  { z : degree_zero_part _ f m f_deg |
    ∃ (s : A) (hs : s ∈ x.1.as_homogeneous_ideal) (n : ℕ) (s_mem : s ∈ 𝒜 (m * n)),
      z = (⟨localization.mk s ⟨f^n, ⟨_, rfl⟩⟩, ⟨n, s, s_mem, rfl⟩⟩ : degree_zero_part _ f m f_deg) }

lemma isos.forward.carrier_eq_carrier' (f : A) [decidable_eq (localization.away f)]
  (m : ℕ) (f_deg : f ∈ 𝒜 m)
  (x : Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))) :
  isos.forward.carrier 𝒜 f m f_deg x = isos.forward.carrier' 𝒜 f m f_deg x :=
begin
  ext z, split; intros hz,
  { change z.1 ∈ _ at hz,
    change z ∈ ideal.span _,
    have mem1 := z.2,
    change ∃ _, _ at mem1,
    obtain ⟨k, a, a_mem, hk⟩ := mem1,
    erw hk at hz,

    erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
    obtain ⟨c, eq1⟩ := hz,
    erw [finsupp.total_apply, finsupp.sum] at eq1,

    suffices mem1 : a ∈ x.1.as_homogeneous_ideal,
    apply ideal.subset_span,
    refine ⟨a, mem1, _, a_mem, _⟩,
    rw subtype.ext_iff_val, dsimp only, rw hk,

    obtain ⟨N, hN⟩ := clear_denominator _ f (finset.image (λ i, c i * i.1) c.support),
    -- N is the common denom
    choose after_clear_denominator hacd using hN,
    have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
    { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
    have eq3 := calc (localization.mk a 1 : localization.away f) * localization.mk (f^N) 1
            = localization.mk a ⟨f^k, ⟨_, rfl⟩⟩ * localization.mk (f^k) 1 * localization.mk (f^N) 1
            : begin
              congr,
              rw [localization.mk_mul, localization.mk_eq_mk', is_localization.eq],
              use 1,
              erw [mul_one, mul_one, mul_one, mul_one, ←subtype.val_eq_coe],
            end
        ... = localization.mk (f^k) 1 * localization.mk a ⟨f^k, ⟨_, rfl⟩⟩ * localization.mk (f^N) 1
            : by ring
        ... = localization.mk (f^k) 1 * localization.mk (f^N) 1 * ∑ i in c.support, c i * i.1
            : begin
              erw eq1, ring,
            end
        ... = localization.mk (f^k) 1 * (localization.mk (f^N) 1 * ∑ i in c.support, c i * i.1) : by ring
        ... = localization.mk (f^k) 1 * ∑ i in c.support, (localization.mk (f^N) 1) * (c i * i.1)
            : begin
              congr' 1,
              rw finset.mul_sum,
            end
        ... = localization.mk (f^k) 1 * ∑ i in c.support.attach, (localization.mk (f^N) 1) * (c i.1 * i.1.1)
            : begin
              congr' 1,
              rw finset.sum_bij',
              work_on_goal 5 { intros a _, exact a.1 },
              work_on_goal 3 { intros a ha, exact ⟨a, ha⟩},
              { intros a ha, dsimp only, refl, },
              { intros a ha, dsimp only, refl, },
              { intros a ha, dsimp only, rw subtype.ext_iff_val, },
              { intros a ha, dsimp only, apply finset.mem_attach, },
              { intros a ha, dsimp only, exact a.2, },
            end
        ... = localization.mk (f^k) 1 * ∑ i in c.support.attach, (localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
            : begin
              congr' 1,
              rw finset.sum_congr rfl (λ j hj, _),
              have eq2 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
              dsimp only at eq2,
              erw eq2,
              rw mul_comm,
            end
        ... = ∑ i in c.support.attach, (localization.mk (f^k) 1) * (localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1)
            : begin
              rw finset.mul_sum,
            end
        ... = ∑ i in c.support.attach, localization.mk (f^k * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2))) 1
            : begin
              rw finset.sum_congr rfl (λ j hj, _),
              erw [localization.mk_mul, one_mul],
            end
        ... = localization.mk (∑ i in c.support.attach, (f^k * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)))) 1
            : begin
              induction c.support.attach using finset.induction_on with y s hy ih,
              rw [finset.sum_empty, finset.sum_empty, localization.mk_zero],

              erw [finset.sum_insert hy, finset.sum_insert hy, ih, localization.add_mk, mul_one, one_mul, one_mul, add_comm],
            end,
        erw [localization.mk_mul, one_mul] at eq3,
        simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
        obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq3⟩ := eq3,
        erw [mul_one, ←subtype.val_eq_coe, mul_one] at eq3,
        dsimp only at eq3,

    suffices : (∑ i in c.support.attach, (f^k * (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)))) * f^l ∈ x.1.as_homogeneous_ideal,
    erw ←eq3 at this,
    rcases x.1.is_prime.mem_or_mem this with H1 | H3,
    rcases x.1.is_prime.mem_or_mem H1 with H1 | H2,
    { exact H1 },
    { exfalso,
      have mem3 := x.2,
      have mem4 := x.1.is_prime.mem_of_pow_mem _ H2,
      erw projective_spectrum.mem_basic_open at mem3,
      apply mem3,
      exact mem4, },
    { exfalso,
      have mem3 := x.2,
      have mem4 := x.1.is_prime.mem_of_pow_mem _ H3,
      erw projective_spectrum.mem_basic_open at mem3,
      apply mem3,
      exact mem4, },

    apply ideal.mul_mem_right,
    apply ideal.sum_mem,
    intros j hj,
    apply ideal.mul_mem_left,
    set g := classical.some j.1.2 with g_eq,
    have mem3 : g ∈ x.1.as_homogeneous_ideal := (classical.some_spec j.1.2).1,
    have eq3 : j.1.1 = localization.mk g 1 := (classical.some_spec j.1.2).2,
    have eq4 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
    dsimp only at eq4,

    have eq5 : ∃ (a : A) (z : ℕ), c j.1 = localization.mk a ⟨f^z, ⟨z, rfl⟩⟩,
    { induction (c j.1) using localization.induction_on with data,
      rcases data with ⟨a, ⟨_, ⟨z, rfl⟩⟩⟩,
      refine ⟨a, z, rfl⟩, },
    obtain ⟨α, z, hz⟩ := eq5,

    have eq6 := calc localization.mk (after_clear_denominator (c j.1 * j.1.1) (prop1 j.1 j.2)) 1
            = c j.1 * j.1.1 * localization.mk (f^N) 1 : eq4
        ... = (localization.mk α ⟨f^z, ⟨z, rfl⟩⟩ : localization.away f) * j.1.1 * localization.mk (f^N) 1
            : by erw hz
        ... = (localization.mk α ⟨f^z, ⟨z, rfl⟩⟩ : localization.away f) * localization.mk g 1 * localization.mk (f^N) 1
            : by erw eq3
        ... = localization.mk (α * g * f^N) ⟨f^z, ⟨z, rfl⟩⟩
            : begin
              erw [localization.mk_mul, localization.mk_mul, mul_one, mul_one],
            end,
    simp only [localization.mk_eq_mk', is_localization.eq] at eq6,
    obtain ⟨⟨_, ⟨v, rfl⟩⟩, eq6⟩ := eq6,
    erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one] at eq6,
    dsimp only at eq6,

    have mem4 : α * g * f ^ N * f ^ v ∈ x.1.as_homogeneous_ideal,
    { apply ideal.mul_mem_right,
      apply ideal.mul_mem_right,
      apply ideal.mul_mem_left,
      exact mem3, },
    erw ←eq6 at mem4,

    rcases x.1.is_prime.mem_or_mem mem4 with H1 | H3,
    rcases x.1.is_prime.mem_or_mem H1 with H1 | H2,
    { exact H1 },
    { exfalso,
      have mem3 := x.2,
      have mem4 := x.1.is_prime.mem_of_pow_mem _ H2,
      erw projective_spectrum.mem_basic_open at mem3,
      apply mem3,
      exact mem4, },
    { exfalso,
      have mem3 := x.2,
      have mem4 := x.1.is_prime.mem_of_pow_mem _ H3,
      erw projective_spectrum.mem_basic_open at mem3,
      apply mem3,
      exact mem4, } },

  { change z ∈ ideal.span _ at hz,
    change z.1 ∈ ideal.span _,

    erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
    obtain ⟨c, eq1⟩ := hz,
    erw [finsupp.total_apply, finsupp.sum] at eq1,

    erw [←eq1, show (∑ i in c.support, c i * i.1).val = ∑ i in c.support, (c i).1 * i.1.1, begin
      induction c.support using finset.induction_on with a s ha ih,

      rw [finset.sum_empty, finset.sum_empty],
      refl,

      erw [finset.sum_insert ha, finset.sum_insert ha, ←ih],
      dsimp only,
      refl,
    end],

    eapply ideal.sum_mem (ideal.span {y :
     localization (submonoid.powers f) | ∃ (g : A),
     g ∈ (projective_spectrum.as_homogeneous_ideal x.val).val ∧ y = localization.mk g 1}),

    rintros j hj,
    apply ideal.mul_mem_left  (ideal.span {y :
     localization (submonoid.powers f) | ∃ (g : A),
     g ∈ (projective_spectrum.as_homogeneous_ideal x.val).val ∧ y = localization.mk g 1}),
    have hj2 := j.2,
    change ∃ s, _ at hj2,
    obtain ⟨s, hs, n, s_mem, hj2⟩ := hj2,
    erw hj2, dsimp only,
    have eq2 : (localization.mk s ⟨f ^ n, ⟨_, rfl⟩⟩ : localization.away f) =
      localization.mk 1 ⟨f^n, ⟨_, rfl⟩⟩ * localization.mk s 1,
    { rw [localization.mk_mul, one_mul, mul_one], },
    erw eq2,
    apply ideal.mem_span.smul_mem,
    refine ⟨s, hs, rfl⟩, },
end

lemma set_like.graded_monoid.pow_deg {f : A} {m} (f_deg : f ∈ 𝒜 m) (n : ℕ) : f ^ n ∈ 𝒜 (n * m) :=
begin
  induction n with n ih,
  erw [pow_zero, zero_mul],
  exact set_like.graded_monoid.one_mem,

  erw [mul_comm n.succ m, pow_succ', nat.mul_succ, mul_comm m n],
  apply set_like.graded_monoid.mul_mem ih f_deg,
end

lemma set_like.graded_monoid.nat_deg_zero (n : ℕ) : (n : A) ∈ 𝒜 0 :=
begin
  induction n with n ih,
  exact submodule.zero_mem _,

  rw nat.succ_eq_add_one,
  have : (↑(n + 1) : A) = (n : A) + 1 := rfl,
  erw this,
  apply submodule.add_mem _ ih,
  exact set_like.graded_monoid.one_mem,
end

variable [Π (i : ℕ) (x : 𝒜 i), decidable (x ≠ 0)]

def isos.backward.carrier (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) : set _ :=
  {a | ∀ (i : ℕ),
    (⟨localization.mk ((graded_algebra.proj 𝒜 i a)^m) ⟨f^i, ⟨_, rfl⟩⟩,
      i, ((graded_algebra.proj 𝒜 i a)^m),
      (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
      degree_zero_part _ f m f_deg) ∈ q.1}

lemma isos.backward.carrier.zero_mem (f : A) [decidable_eq (localization.away f)] (m : ℕ)
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) :
  (0 : A) ∈ isos.backward.carrier 𝒜 f m hm f_deg q :=
begin
  rw isos.backward.carrier,
  { intros i,
    simp only [linear_map.map_zero, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },
end

lemma isos.backward.carrier.add_mem (f : A) [decidable_eq (localization.away f)] (m : ℕ)
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1)
  (a b : A)
  (ha : a ∈ isos.backward.carrier 𝒜 f m hm f_deg q)
  (hb : b ∈ isos.backward.carrier 𝒜 f m hm f_deg q) :
  a + b ∈ isos.backward.carrier 𝒜 f m hm f_deg q :=
begin
  rw isos.backward.carrier at ha hb ⊢,
  { intros i,
    suffices : (⟨localization.mk ((graded_algebra.proj 𝒜 i (a + b))^m) ⟨f^i, ⟨_, rfl⟩⟩,
    i, ((graded_algebra.proj 𝒜 i (a+b))^m),
    (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
    degree_zero_part _ f m f_deg) * (⟨localization.mk ((graded_algebra.proj 𝒜 i (a+b))^m) ⟨f^i, ⟨_, rfl⟩⟩,
    i, ((graded_algebra.proj 𝒜 i (a+b))^m),
    (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
    degree_zero_part _ f m f_deg) ∈ q.1,
    cases q.2.mem_or_mem this, assumption, assumption,

    have eq1 : (⟨localization.mk ((graded_algebra.proj 𝒜 i (a + b))^m) ⟨f^i, ⟨_, rfl⟩⟩,
    i, ((graded_algebra.proj 𝒜 i (a+b))^m),
    (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
    degree_zero_part _ f m f_deg) * (⟨localization.mk ((graded_algebra.proj 𝒜 i (a+b))^m) ⟨f^i, ⟨_, rfl⟩⟩,
    i, ((graded_algebra.proj 𝒜 i (a+b))^m),
    (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
    degree_zero_part _ f m f_deg) = ⟨localization.mk ((graded_algebra.proj 𝒜 i (a + b))^(2*m))
     ⟨f^(2*i), ⟨_, rfl⟩⟩, 2*i, (graded_algebra.proj 𝒜 i (a+b))^(2*m), begin
        rw [←mul_assoc m 2 i, mul_comm m 2],
        apply set_like.graded_monoid.pow_deg,
        rw linear_map.map_add,
        apply submodule.add_mem,
        apply submodule.coe_mem,
        apply submodule.coe_mem,
      end, rfl⟩,
    { rw [subtype.ext_iff_val],
      rw show ((⟨localization.mk ((graded_algebra.proj 𝒜 i (a + b))^m) ⟨f^i, ⟨_, rfl⟩⟩,
      i, ((graded_algebra.proj 𝒜 i (a+b))^m),
      (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
      degree_zero_part _ f m f_deg) * (⟨localization.mk ((graded_algebra.proj 𝒜 i (a+b))^m) ⟨f^i, ⟨_, rfl⟩⟩,
      i, ((graded_algebra.proj 𝒜 i (a+b))^m),
      (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
      degree_zero_part _ f m f_deg)).val = (⟨localization.mk ((graded_algebra.proj 𝒜 i (a + b))^m) ⟨f^i, ⟨_, rfl⟩⟩,
      i, ((graded_algebra.proj 𝒜 i (a+b))^m),
      (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
      degree_zero_part _ f m f_deg).val * (⟨localization.mk ((graded_algebra.proj 𝒜 i (a+b))^m) ⟨f^i, ⟨_, rfl⟩⟩,
      i, ((graded_algebra.proj 𝒜 i (a+b))^m),
      (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
      degree_zero_part _ f m f_deg).val, from rfl,
        dsimp only,

      rw localization.mk_mul, congr' 1,
      rw [two_mul, pow_add],

      rw [subtype.ext_iff_val, show ((⟨f^i, _⟩ : submonoid.powers f) * ⟨f^i, _⟩).val = f^i * f^i, from rfl],
      dsimp only, rw [two_mul, pow_add], },
      erw eq1,

      have eq2 := calc
              (⟨localization.mk (((graded_algebra.proj 𝒜 i) (a + b)) ^ (2 * m)) ⟨f ^ (2 * i), ⟨_, rfl⟩⟩,
              2*i, (((graded_algebra.proj 𝒜 i) (a + b)) ^ (2 * m)), begin
                rw [←mul_assoc m 2 i, mul_comm m 2],
                apply set_like.graded_monoid.pow_deg,
                rw linear_map.map_add,
                apply submodule.add_mem,
                apply submodule.coe_mem,
                apply submodule.coe_mem,
              end, rfl⟩ : degree_zero_part _ f m f_deg)
            = ⟨localization.mk ((∑ j in finset.range (2 * m + 1), ((graded_algebra.proj 𝒜 i) a)^j *
                ((graded_algebra.proj 𝒜 i) b)^(2 * m - j) * (2 * m).choose j)) ⟨f ^ (2 * i), ⟨_, rfl⟩⟩,
                2*i, ((∑ j in finset.range (2 * m + 1), ((graded_algebra.proj 𝒜 i) a)^j *
                ((graded_algebra.proj 𝒜 i) b)^(2 * m - j) * (2 * m).choose j)), begin
                  apply submodule.sum_mem,
                  intros k hk,
                  have mem1 : (graded_algebra.proj 𝒜 i) a ^ k ∈ 𝒜 (k * i),
                  { apply set_like.graded_monoid.pow_deg,
                    exact submodule.coe_mem _, },
                  have mem2 : (graded_algebra.proj 𝒜 i) b ^ (2 * m - k) ∈ 𝒜 ((2*m-k) * i),
                  { apply set_like.graded_monoid.pow_deg,
                    exact submodule.coe_mem _, },
                  have mem3 : ((2 * m).choose k : A) ∈ 𝒜 0,
                  { exact set_like.graded_monoid.nat_deg_zero _ _, },
                  have eq2 : m * (2 * i) = ((k*i) + (2*m-k)*i + 0),
                  { zify,
                    have eq3 : (↑(2 * m - k) : ℤ) = 2 * m - k,
                    { rw eq_sub_iff_add_eq,
                      rw [←int.coe_nat_add],
                      congr',
                      erw nat.sub_add_cancel,
                      erw finset.mem_range at hk,
                      rw nat.lt_succ_iff at hk,
                      exact hk, },
                    erw [eq3, sub_mul], ring, },
                  erw eq2,
                  apply set_like.graded_monoid.mul_mem _ mem3,
                  apply set_like.graded_monoid.mul_mem mem1 mem2,
                end, rfl⟩
            : begin
              erw [subtype.ext_iff_val],
              dsimp only,
              erw [linear_map.map_add, add_pow],
            end
        ... = ⟨localization.mk (∑ j in (finset.range (2*m + 1)).attach,
                (graded_algebra.proj 𝒜 i a)^(j.val) *
                (graded_algebra.proj 𝒜 i b)^(2 * m - j.val) * (2 * m).choose j.val) ⟨f ^ (2 * i), ⟨_, rfl⟩⟩,
                2*i, ((∑ j in (finset.range (2 * m + 1)).attach, ((graded_algebra.proj 𝒜 i) a)^j.val *
                ((graded_algebra.proj 𝒜 i) b)^(2 * m - j.val) * (2 * m).choose j.val)), begin
                  apply submodule.sum_mem,
                  intros k hk,
                  have mem1 : (graded_algebra.proj 𝒜 i) a ^ k.val ∈ 𝒜 (k * i),
                  { apply set_like.graded_monoid.pow_deg,
                    exact submodule.coe_mem _, },
                  have mem2 : (graded_algebra.proj 𝒜 i) b ^ (2 * m - k.val) ∈ 𝒜 ((2*m-k.val) * i),
                  { apply set_like.graded_monoid.pow_deg,
                    exact submodule.coe_mem _, },
                  have mem3 : ((2 * m).choose k.val : A) ∈ 𝒜 0,
                  { exact set_like.graded_monoid.nat_deg_zero _ _, },
                  have eq2 : m * (2 * i) = ((k.val*i) + (2*m-k.val)*i + 0),
                  { zify,
                    have eq3 : (↑(2 * m - k.val) : ℤ) = 2 * m - k.val,
                    { rw eq_sub_iff_add_eq,
                      rw [←int.coe_nat_add],
                      congr',
                      erw nat.sub_add_cancel,
                      have hk := k.2,
                      erw finset.mem_range at hk,
                      rw nat.lt_succ_iff at hk,
                      exact hk, },
                    erw [eq3, sub_mul], ring, },
                  erw eq2,
                  apply set_like.graded_monoid.mul_mem _ mem3,
                  apply set_like.graded_monoid.mul_mem mem1 mem2,
                end, rfl⟩ : begin
                  rw subtype.ext_iff_val,
                  dsimp only,
                  congr' 1,
                  apply finset.sum_bij',
                  work_on_goal 5 { intros a _, exact a.1, },
                  work_on_goal 3 { intros a ha, exact ⟨a, ha⟩, },
                  { intros j hj, refl, },
                  { intros j hj, dsimp only, refl, },
                  { intros j hj, dsimp only, rw subtype.ext_iff_val, },
                  { intros j hj, dsimp only, apply finset.mem_attach, },
                  { intros j hj, dsimp only, exact j.2, },
                end
        ... = ∑ j in (finset.range (2 * m + 1)).attach,
                ⟨localization.mk (((graded_algebra.proj 𝒜 i) a)^j.1 *
                ((graded_algebra.proj 𝒜 i) b)^(2 * m - j.1) * (2 * m).choose j.1) ⟨f^(2 * i), ⟨2*i, rfl⟩⟩,
                2*i, (((graded_algebra.proj 𝒜 i) a)^j.1 *
                ((graded_algebra.proj 𝒜 i) b)^(2 * m - j.1) * (2 * m).choose j), begin
                  have mem1 : (graded_algebra.proj 𝒜 i) a ^ j.1 ∈ 𝒜 (j.1 * i),
                  { apply set_like.graded_monoid.pow_deg,
                    exact submodule.coe_mem _, },
                  have mem2 : (graded_algebra.proj 𝒜 i) b ^ (2 * m - j.1) ∈ 𝒜 ((2*m-j.1) * i),
                  { apply set_like.graded_monoid.pow_deg,
                    exact submodule.coe_mem _, },
                  have mem3 : ((2 * m).choose j.1 : A) ∈ 𝒜 0,
                  { exact set_like.graded_monoid.nat_deg_zero _ _, },

                  have eq2 : m * (2 * i) = ((j.1*i) + (2*m-j.1)*i + 0),
                  { zify,
                    have eq3 : (↑(2 * m - j.1) : ℤ) = 2 * m - j.1,
                    { rw eq_sub_iff_add_eq,
                      rw [←int.coe_nat_add],
                      congr',
                      erw nat.sub_add_cancel,
                      have hj := j.2,
                      erw finset.mem_range at hj,
                      rw nat.lt_succ_iff at hj,
                      exact hj, },
                    erw [eq3, sub_mul], ring, },
                  erw eq2,
                  apply set_like.graded_monoid.mul_mem _ mem3,
                  apply set_like.graded_monoid.mul_mem mem1 mem2,
                end, rfl⟩
            : begin
              rw subtype.ext_iff_val,
              dsimp only,
              have : (∑ j in (finset.range (2 * m + 1)).attach,
                (⟨localization.mk (((graded_algebra.proj 𝒜 i) a)^j.1 *
                ((graded_algebra.proj 𝒜 i) b)^(2 * m - j.1) * (2 * m).choose j.1)
                ⟨f^(2 * i), ⟨2*i, rfl⟩⟩, _⟩ : degree_zero_part _ f m f_deg)).val =
                ∑ j in (finset.range (2 * m + 1)).attach,
                  (⟨localization.mk (((graded_algebra.proj 𝒜 i) a)^j.1 *
                ((graded_algebra.proj 𝒜 i) b)^(2 * m - j.1) * (2 * m).choose j.1)
                ⟨f^(2 * i), ⟨2*i, rfl⟩⟩, _⟩ : degree_zero_part _ f m f_deg).val,
              { induction (finset.range (2*m+1)).attach using finset.induction_on with b s hb ih,
                { rw [finset.sum_empty, finset.sum_empty], refl, },
                { rw [finset.sum_insert, finset.sum_insert, ←ih], refl,
                  exact hb, exact hb, }, },
              erw this, dsimp only,

              induction (finset.range (2*m+1)).attach using finset.induction_on with c s hc ih,
              { rw [finset.sum_empty, finset.sum_empty, localization.mk_zero], },
              { rw [finset.sum_insert hc, finset.sum_insert hc, ←ih, localization.add_mk],
                simp only [localization.mk_eq_mk', is_localization.eq],
                use 1,
                erw [mul_one, ←mul_add, mul_one],
                conv_rhs { rw [mul_assoc, mul_comm, mul_assoc] },
                congr' 1,
                rw add_comm, },
            end,
      erw eq2, apply ideal.sum_mem,
      intros k hk,
      by_cases ineq : m ≤ k.val,
      { -- use this part : (graded_algebra.proj 𝒜 i) a ^ k
        have : (⟨localization.mk
          ((graded_algebra.proj 𝒜 i) a ^ k.val * (graded_algebra.proj 𝒜 i) b ^ (2 * m - k.val) *
          ((2 * m).choose k.val))
          ⟨f ^ (2 * i), ⟨_, rfl⟩⟩, begin
            refine ⟨2*i, _, _, rfl⟩,
            have mem1 : (graded_algebra.proj 𝒜 i) a ^ k.val ∈ 𝒜 (k.1 * i),
            { apply set_like.graded_monoid.pow_deg,
              exact submodule.coe_mem _, },
            have mem2 : (graded_algebra.proj 𝒜 i) b ^ (2 * m - k.1) ∈ 𝒜 ((2*m-k.1) * i),
            { apply set_like.graded_monoid.pow_deg,
              exact submodule.coe_mem _, },
            have mem3 : ((2 * m).choose k.1 : A) ∈ 𝒜 0,
            { exact set_like.graded_monoid.nat_deg_zero _ _, },
            have eq2 : m * (2 * i) = ((k.1*i) + (2*m-k.1)*i + 0),
            { zify,
              have eq3 : (↑(2 * m - k.1) : ℤ) = 2 * m - k.1,
              { rw eq_sub_iff_add_eq,
                rw [←int.coe_nat_add],
                congr',
                erw nat.sub_add_cancel,
                have hk := k.2,
                erw finset.mem_range at hk,
                rw nat.lt_succ_iff at hk,
                exact hk, },
                erw [eq3, sub_mul], ring, },
                erw eq2,
                apply set_like.graded_monoid.mul_mem _ mem3,
                apply set_like.graded_monoid.mul_mem mem1 mem2,
          end⟩ : degree_zero_part _ f m f_deg) =
          (⟨localization.mk ((graded_algebra.proj 𝒜 i) a ^ m) ⟨f^i, ⟨i, rfl⟩⟩, begin
            refine ⟨i, _, _, rfl⟩,
            apply set_like.graded_monoid.pow_deg,
            exact submodule.coe_mem _,
          end⟩
            : degree_zero_part _ f m f_deg) *
          (⟨localization.mk ((graded_algebra.proj 𝒜 i) a ^ (k.val - m) *
            (graded_algebra.proj 𝒜 i) b ^ (2 * m - k.val) * (2*m).choose k.1) ⟨f^i, ⟨i, rfl⟩⟩, begin
              refine ⟨i, _, _, rfl⟩,
              have mem1 : (graded_algebra.proj 𝒜 i) a ^ (k.val - m) ∈ 𝒜 ((k.val - m) * i),
              { apply set_like.graded_monoid.pow_deg,
                exact submodule.coe_mem _, },
              have mem2 : (graded_algebra.proj 𝒜 i) b ^ (2 * m - k.val) ∈ 𝒜 ((2*m-k.1) * i),
              { apply set_like.graded_monoid.pow_deg,
                exact submodule.coe_mem _, },
              have mem3 : ((2*m).choose k.1 : A) ∈ 𝒜 0,
              { exact set_like.graded_monoid.nat_deg_zero _ _, },
              have eq1 : m * i = ((k.val - m) * i) + ((2*m-k.1) * i) + 0,
              { erw [add_zero, ←add_mul],
                congr' 1,
                symmetry,
                exact calc k.val - m + (2*m - k.val)
                          = (k.val + (2 * m - k.1)) - m : by { rw nat.sub_add_comm ineq, }
                      ... = (k.1 + 2 * m) - k.1 - m
                          : begin
                            rw ←nat.add_sub_assoc,
                            have hk := k.2,
                            rw [finset.mem_range, nat.lt_succ_iff] at hk,
                            exact hk,
                          end
                      ... = 2 * m - m : by { rw nat.add_sub_cancel_left k.1 (2*m), }
                      ... = m + m - m : by { rw two_mul, }
                      ... = m : by rw nat.add_sub_cancel, },
              erw eq1,
              apply set_like.graded_monoid.mul_mem,
              apply set_like.graded_monoid.mul_mem,
              exact mem1, exact mem2, exact mem3,
            end⟩
            : degree_zero_part _ f m f_deg),
        { rw [subtype.ext_iff_val, show ∀ (a b : degree_zero_part _ f m f_deg),
            (a * b).val = a.val * b.val, from λ _ _, rfl],
          dsimp only,
          rw localization.mk_mul,
          congr' 1,
          { conv_rhs { rw [←mul_assoc, ←mul_assoc, ←pow_add] },
            congr',
            symmetry,
            exact calc m + (k.1 - m)
                    = m + k.1 - m : by erw ←nat.add_sub_assoc ineq
                ... = k.1 + m - m : by rw nat.add_comm
                ... = k.1 + (m-m) : by erw nat.add_sub_assoc (le_refl _)
                ... = k.1 + 0 : by rw nat.sub_self
                ... = k.1 : by rw add_zero,
             },
          { rw [subtype.ext_iff_val, show ∀ (x y : submonoid.powers f), (x * y).val = x.1 * y.1,
              from λ _ _, rfl],
            dsimp only,
            rw [←pow_two, ←pow_mul, mul_comm], }, },
        erw this,
        apply ideal.mul_mem_right,
        apply ha, },
      { -- k < m
        -- so use this part : (graded_algebra.proj 𝒜 i) b ^ (2 * m - k)
        have : (⟨localization.mk
          ((graded_algebra.proj 𝒜 i) a ^ k.val * (graded_algebra.proj 𝒜 i) b ^ (2 * m - k.val) *
          ((2 * m).choose k.val))
          ⟨f ^ (2 * i), ⟨_, rfl⟩⟩, begin
            refine ⟨2*i, _, _, rfl⟩,
            have mem1 : (graded_algebra.proj 𝒜 i) a ^ k.val ∈ 𝒜 (k.1 * i),
            { apply set_like.graded_monoid.pow_deg,
              exact submodule.coe_mem _, },
            have mem2 : (graded_algebra.proj 𝒜 i) b ^ (2 * m - k.1) ∈ 𝒜 ((2*m-k.1) * i),
            { apply set_like.graded_monoid.pow_deg,
              exact submodule.coe_mem _, },
            have mem3 : ((2 * m).choose k.1 : A) ∈ 𝒜 0,
            { exact set_like.graded_monoid.nat_deg_zero _ _, },
            have eq2 : m * (2 * i) = ((k.1*i) + (2*m-k.1)*i + 0),
            { zify,
              have eq3 : (↑(2 * m - k.1) : ℤ) = 2 * m - k.1,
              { rw eq_sub_iff_add_eq,
                rw [←int.coe_nat_add],
                congr',
                erw nat.sub_add_cancel,
                have hk := k.2,
                erw finset.mem_range at hk,
                rw nat.lt_succ_iff at hk,
                exact hk, },
                erw [eq3, sub_mul], ring, },
                erw eq2,
                apply set_like.graded_monoid.mul_mem _ mem3,
                apply set_like.graded_monoid.mul_mem mem1 mem2,
          end⟩ : degree_zero_part _ f m f_deg) =
          (⟨localization.mk ((graded_algebra.proj 𝒜 i) b ^ m) ⟨f^i, ⟨_, rfl⟩⟩, begin
            refine ⟨i, _, _, rfl⟩,
            apply set_like.graded_monoid.pow_deg,
            exact submodule.coe_mem _,
          end⟩
            : degree_zero_part _ f m f_deg)
          * (⟨localization.mk ((graded_algebra.proj 𝒜 i) a ^ k.val *
              (graded_algebra.proj 𝒜 i) b ^ (m - k.val) * ((2 * m).choose k.val))
              ⟨f^i, ⟨_, rfl⟩⟩, begin
                have mem1 : (graded_algebra.proj 𝒜 i) a ^ k.val ∈ 𝒜 (k.1 * i),
                { apply set_like.graded_monoid.pow_deg,
                  exact submodule.coe_mem _, },
                have mem2 : (graded_algebra.proj 𝒜 i) b ^ (m - k.val) ∈ 𝒜 ((m - k.1) * i),
                { apply set_like.graded_monoid.pow_deg,
                  exact submodule.coe_mem _, },
                have mem3 : ↑((2 * m).choose k.val) ∈ 𝒜 0,
                { apply set_like.graded_monoid.nat_deg_zero, },
                have eq1 : k.1 * i + (m - k.1) * i + 0 = m * i,
                { exact calc k.1 * i + (m - k.1) * i + 0
                          = k.1 * i + (m - k.1) * i : by { rw add_zero }
                      ... = (k.1 + (m - k.1)) * i : by { rw add_mul, }
                      ... = (k.1 + m - k.1) * i
                            : begin
                              rw nat.add_sub_assoc,
                              rw not_le at ineq,
                              apply le_of_lt,
                              exact ineq,
                            end
                      ... = m * i : by rw nat.add_sub_cancel_left, },
                refine ⟨_, _, _, rfl⟩,
                erw ←eq1,
                apply set_like.graded_monoid.mul_mem,
                apply set_like.graded_monoid.mul_mem,
                exact mem1, exact mem2, exact mem3,
              end⟩ : degree_zero_part _ f m f_deg),
        { rw subtype.ext_iff_val,
          rw show ∀ (a b : degree_zero_part _ f m f_deg), (a * b).val = a.1 * b.1, from λ _ _, rfl,
          dsimp only,
          rw localization.mk_mul,
          congr' 1,
          { conv_rhs { rw [←mul_assoc, ←mul_assoc] },
            congr' 1,
            conv_rhs { rw [mul_comm, ←mul_assoc, ←pow_add, mul_comm] },
            congr',
            erw [←nat.sub_add_comm],
            simp only [two_mul],
            rw not_le at ineq,
            apply le_of_lt,
            exact ineq, },
          { rw [subtype.ext_iff_val, show ∀ (x y : submonoid.powers f), (x * y).val = x.1 * y.1,
              from λ _ _, rfl],
            dsimp only,
            rw [←pow_two, ←pow_mul, mul_comm], }, },
        erw this,
        apply ideal.mul_mem_right,
        apply hb, }, },
end

lemma isos.backward.carrier.smul_mem (f : A) [decidable_eq (localization.away f)] (m : ℕ)
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1)
  (c x : A) (hx : x ∈ isos.backward.carrier 𝒜 f m hm f_deg q) :
  c • x ∈ isos.backward.carrier 𝒜 f m hm f_deg q :=
begin
  apply set_like.homogeneous_induction 𝒜 c,
  { rw zero_smul,
    apply isos.backward.carrier.zero_mem, },
  { rintros ⟨a, ⟨n, ha⟩⟩,
    rw isos.backward.carrier at hx ⊢,
    { intros i,
      by_cases ineq1 : n ≤ i,
      { have eq1 : (graded_algebra.proj 𝒜 i) (a * x) =
          ite (i - n ∈ graded_algebra.support 𝒜 x) (a * (graded_algebra.proj 𝒜 (i - n)) x) 0,
        { exact calc
                  (graded_algebra.proj 𝒜 i) (a * x)
                = graded_algebra.proj 𝒜 i ∑ j in graded_algebra.support 𝒜 x, (a * (graded_algebra.proj 𝒜 j x))
                : begin
                  conv_lhs { rw [←graded_algebra.sum_support_decompose 𝒜 x] },
                  simp_rw [←graded_algebra.proj_apply],
                  rw [finset.mul_sum],
                end
            ... = ∑ j in graded_algebra.support 𝒜 x, (graded_algebra.proj 𝒜 i (a * (graded_algebra.proj 𝒜 j x)))
                : begin
                  rw linear_map.map_sum,
                end
            ... = ∑ j in graded_algebra.support 𝒜 x, (ite (j = i - n) (graded_algebra.proj 𝒜 i (a * (graded_algebra.proj 𝒜 j x))) 0)
                : begin
                  rw finset.sum_congr rfl,
                  intros j hj, symmetry,
                  split_ifs with H,
                  refl,
                  symmetry,
                  have mem1 : a * graded_algebra.proj 𝒜 j x ∈ 𝒜 (n + j),
                  { apply set_like.graded_monoid.mul_mem ha (submodule.coe_mem _), },
                  rw graded_algebra.proj_apply,
                  apply graded_algebra.decompose_of_mem_ne 𝒜 mem1,
                  intro rid,
                  rw [←rid, add_comm, nat.add_sub_assoc, nat.sub_self, add_zero] at H,
                  apply H, refl, refl,
                end
            ... = ∑ j in graded_algebra.support 𝒜 x,
                  (ite (j = i - n) (a * (graded_algebra.proj 𝒜 j x)) 0)
                : begin
                  rw finset.sum_congr rfl,
                  intros j hj,
                  split_ifs with eq1 ineq1,
                  rw [graded_algebra.proj_apply, graded_algebra.proj_apply],
                  apply graded_algebra.decompose_of_mem_same,
                  rw ←graded_algebra.proj_apply,
                  have eq2 : i = j + n,
                  { rw [eq1, nat.sub_add_cancel], exact ineq1, },
                  rw [eq2, add_comm],
                  apply set_like.graded_monoid.mul_mem ha (submodule.coe_mem _),
                  refl,
                end
            ... = ite (i - n ∈ graded_algebra.support 𝒜 x)
                    (a * (graded_algebra.proj 𝒜 (i - n)) x) 0 : by rw finset.sum_ite_eq',
                },

        split_ifs at eq1,

        have eq2 := calc
                (⟨localization.mk ((graded_algebra.proj 𝒜 i) (a * x) ^ m) ⟨f ^ i, ⟨_, rfl⟩⟩,
                  isos.backward.carrier._proof_4 _ f m (a * x) i⟩ : degree_zero_part _ f m f_deg)
              = (⟨localization.mk
                    ((a * (graded_algebra.proj 𝒜 (i - n) x))^m) ⟨f ^ i, ⟨_, rfl⟩⟩,
                  begin
                    erw ←eq1,
                    apply isos.backward.carrier._proof_4 𝒜 f m ((a * x)) i,
                  end⟩ : degree_zero_part _ f m f_deg)
              : begin
                rw subtype.ext_iff_val, dsimp only, erw eq1,
              end
          ... = (⟨localization.mk ((a^m * (graded_algebra.proj 𝒜 (i - n) x)^m))
                  ⟨f^i, ⟨_, rfl⟩⟩, begin
                    erw [←mul_pow, ←eq1],
                    apply isos.backward.carrier._proof_4 𝒜 f m ((a * x)) i,
                  end⟩ : degree_zero_part _ f m f_deg)
              : begin
                rw subtype.ext_iff_val, dsimp only,
                erw mul_pow,
              end
          ... = (⟨localization.mk (a^m) ⟨f^n, ⟨_, rfl⟩⟩, begin
                  refine ⟨n, a^m, _, rfl⟩,
                  dsimp only,
                  have mem1 := aux.pow_deg 𝒜 a n ha m,
                  rw mul_comm at mem1,
                  exact mem1,
                end⟩ : degree_zero_part _ f m f_deg) *
                (⟨localization.mk ((graded_algebra.proj 𝒜 (i -n) x)^m) ⟨f^(i-n), ⟨_, rfl⟩⟩, begin
                  refine ⟨i-n, _, _, rfl⟩,
                  have mem1 := aux.pow_deg 𝒜 (graded_algebra.proj 𝒜 (i-n) x) (i-n) (submodule.coe_mem _) m,
                  rw mul_comm at mem1,
                  exact mem1,
                end⟩ : degree_zero_part _ f m f_deg)
              : begin
                rw subtype.ext_iff_val,
                rw [show ∀ (x y : degree_zero_part _ f m f_deg), (x * y).val = x.val * y.val, begin
                  intros x y, refl,
                end],
                dsimp only,
                erw [localization.mk_mul],
                congr',
                dsimp only,
                erw ←pow_add,
                congr',
                rw [←nat.add_sub_assoc, add_comm, nat.add_sub_assoc, nat.sub_self, add_zero],
                refl,
                exact ineq1,
              end,

        erw eq2,
        apply ideal.mul_mem_left,
        apply hx,


        simp only [smul_eq_mul, eq1, zero_pow hm, localization.mk_zero],
        exact submodule.zero_mem _, },

      { -- in this case, the left hand side is zero
        rw not_le at ineq1,
        convert submodule.zero_mem _,
        suffices : graded_algebra.proj 𝒜 i (a • x) = 0,
        erw [this, zero_pow hm, localization.mk_zero],

        rw [←graded_algebra.sum_support_decompose 𝒜 x, smul_eq_mul, finset.mul_sum, linear_map.map_sum],
        simp_rw [←graded_algebra.proj_apply],
        convert finset.sum_eq_zero _,
        intros j hj,
        rw [graded_algebra.proj_apply],
        have mem1 : a * graded_algebra.proj 𝒜 j x ∈ 𝒜 (n + j),
        { apply set_like.graded_monoid.mul_mem ha (submodule.coe_mem _), },
        apply graded_algebra.decompose_of_mem_ne 𝒜 mem1,
        suffices : i < n + j,
        symmetry,
        apply ne_of_lt this,

        exact lt_of_lt_of_le ineq1 (nat.le_add_right _ _), }, },
    },
  { intros a b ha hb,
    erw add_smul,
    apply isos.backward.carrier.add_mem _ f m hm f_deg q (a • x) (b • x) ha hb, },
end

def isos.backward.carrier.as_ideal (f : A) [decidable_eq (localization.away f)]
  (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) :
  ideal A :=
{ carrier := isos.backward.carrier _ f m hm f_deg q,
  zero_mem' := isos.backward.carrier.zero_mem _ f m hm f_deg q,
  add_mem' := isos.backward.carrier.add_mem _ f m hm f_deg q,
  smul_mem' := isos.backward.carrier.smul_mem _ f m hm f_deg q }

lemma isos.backward.carrier.homogeneous (f : A) [decidable_eq (localization.away f)]
  (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) :
  ideal.is_homogeneous 𝒜 (isos.backward.carrier.as_ideal _ f m hm f_deg q) :=
begin
  intros i a ha,
  rw ←graded_algebra.proj_apply,
  rw isos.backward.carrier.as_ideal at ha ⊢,
  suffices : (graded_algebra.proj _ i a) ∈ isos.backward.carrier _ f m hm f_deg q,
  exact this,
  change a ∈ isos.backward.carrier _ f m hm f_deg q at ha,
  rw isos.backward.carrier at ha ⊢,
  { intros j,
    have := calc (⟨localization.mk ((graded_algebra.proj 𝒜 j (graded_algebra.proj 𝒜 i a)) ^ m)
              ⟨f^j, ⟨_, rfl⟩⟩, begin
                refine ⟨j, _, _, rfl⟩,
                apply set_like.graded_monoid.pow_deg,
                exact submodule.coe_mem _,
              end⟩ : degree_zero_part _ f m f_deg)
            = (⟨localization.mk ((ite (j = i) (graded_algebra.proj 𝒜 j a) 0)^m)
              ⟨f^j, ⟨_, rfl⟩⟩, begin
                refine ⟨j, _, _, rfl⟩,
                apply set_like.graded_monoid.pow_deg,
                split_ifs,
                exact submodule.coe_mem _,
                exact submodule.zero_mem _,
              end⟩ : degree_zero_part _ f m f_deg)
              : begin
                rw [subtype.ext_iff_val],
                dsimp only,
                congr',
                split_ifs with eq1,
                rw [graded_algebra.proj_apply, graded_algebra.proj_apply, eq1],
                apply graded_algebra.decompose_of_mem_same,
                rw [←graded_algebra.proj_apply],
                exact submodule.coe_mem _,

                apply graded_algebra.decompose_of_mem_ne 𝒜 (submodule.coe_mem _),
                symmetry, exact eq1,
              end
        ... = (⟨localization.mk ((ite (j = i) ((graded_algebra.proj 𝒜 j a)^m) 0))
              ⟨f^j, ⟨_, rfl⟩⟩, begin
                refine ⟨j, _, _, rfl⟩,
                split_ifs,
                apply set_like.graded_monoid.pow_deg,
                exact submodule.coe_mem _,
                exact submodule.zero_mem _,
              end⟩ : degree_zero_part _ f m f_deg)
              : begin
                rw [subtype.ext_iff_val],
                dsimp only,
                split_ifs, refl,
                rw zero_pow hm,
              end
        ... = ite (j = i) (⟨localization.mk ((graded_algebra.proj 𝒜 i a)^m) ⟨f^i, ⟨_, rfl⟩⟩,
              begin
                refine ⟨i, _, _, rfl⟩,
                apply set_like.graded_monoid.pow_deg,
                exact submodule.coe_mem _,
              end⟩
              : degree_zero_part _ f m f_deg) (0 : degree_zero_part _ f m f_deg)
              : begin
                split_ifs with H,
                erw H,
                simp only [subtype.ext_iff_val, localization.mk_zero],
                refl,
              end,
    erw this,
    split_ifs with H,
    { apply ha, },
    { exact submodule.zero_mem _, }, },
end

variable [Π (I : homogeneous_ideal 𝒜) (x : A),
  decidable_pred (λ (i : ℕ), (graded_algebra.proj 𝒜 i) x ∉ I)]

lemma isos.backward.carrier.prime (f : A) [decidable_eq (localization.away f)]
  (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) :
  ideal.is_prime (isos.backward.carrier.as_ideal _ f m hm f_deg q) :=
begin
  apply homogeneous_ideal.is_prime_iff 𝒜 ⟨(isos.backward.carrier.as_ideal 𝒜 f m hm f_deg q),
    isos.backward.carrier.homogeneous 𝒜 f m hm f_deg q⟩,
  { -- ≠ ⊤
    intro rid,
    rw homogeneous_ideal.eq_top_iff at rid,
    dsimp only at rid,
    rw ideal.eq_top_iff_one at rid,
    apply q.is_prime.1,
    rw ideal.eq_top_iff_one,
    specialize rid 0,
    have eq1 : graded_algebra.proj 𝒜 0 1 = 1,
    { rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same],
      exact set_like.graded_monoid.one_mem, },
    simp only [eq1, one_pow] at rid,
    convert rid,
    rw [subtype.ext_iff_val, show (1 : degree_zero_part _ f m f_deg).val = 1, from rfl],
    dsimp only,
    symmetry,
    convert localization.mk_one,
    rw pow_zero, },
  { -- homogeneously prime
    rintros x y ⟨nx, hnx⟩ ⟨ny, hny⟩ hxy,
    contrapose hxy,
    rw not_or_distrib at hxy,
    dsimp only at hxy,
    rcases hxy with ⟨hx, hy⟩,
    change x ∉ isos.backward.carrier _ f m hm f_deg q at hx,
    change y ∉ isos.backward.carrier _ f m hm f_deg q at hy,
    change ¬(∀ (i : ℕ), (⟨localization.mk ((graded_algebra.proj 𝒜 i x)^m) ⟨f^i, ⟨_, rfl⟩⟩,
      i, ((graded_algebra.proj 𝒜 i x)^m),
      (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
      degree_zero_part _ f m f_deg) ∈ q.1) at hx,
    change ¬(∀ (i : ℕ), (⟨localization.mk ((graded_algebra.proj 𝒜 i y)^m) ⟨f^i, ⟨_, rfl⟩⟩,
      i, ((graded_algebra.proj 𝒜 i y)^m),
      (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
      degree_zero_part _ f m f_deg) ∈ q.1) at hy,
    rw not_forall at hx hy,
    obtain ⟨ix, hix⟩ := hx,
    obtain ⟨iy, hiy⟩ := hy,
    intro rid,
    change ∀ (i : ℕ), (⟨localization.mk ((graded_algebra.proj 𝒜 i (x*y))^m) ⟨f^i, ⟨_, rfl⟩⟩,
      i, ((graded_algebra.proj 𝒜 i (x*y))^m),
      (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
      degree_zero_part _ f m f_deg) ∈ q.1 at rid,
    specialize rid (nx + ny),
    have eqx : nx = ix,
    { by_contra rid,
      apply hix,
      convert submodule.zero_mem _,
      rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_ne 𝒜 hnx rid, zero_pow hm,
        localization.mk_zero], },
    have eqy : ny = iy,
    { by_contra rid,
      apply hiy,
      convert submodule.zero_mem _,
      rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_ne 𝒜 hny rid, zero_pow hm,
        localization.mk_zero], },
    erw ←eqx at hix,
    erw ←eqy at hiy,
    have eqx2 : (⟨localization.mk ((graded_algebra.proj 𝒜 nx) x ^ m) ⟨f ^ nx, ⟨_, rfl⟩⟩, begin
      refine ⟨nx, _, _, rfl⟩,
      apply set_like.graded_monoid.pow_deg,
      rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same 𝒜 hnx],
      exact hnx,
    end⟩
      : degree_zero_part _ f m f_deg) =
      (⟨localization.mk (x^m) ⟨f^nx, ⟨_, rfl⟩⟩, begin
        refine ⟨nx, _, _, rfl⟩,
        apply set_like.graded_monoid.pow_deg,
        exact hnx,
      end⟩ : degree_zero_part _ f m f_deg),
    { rw subtype.ext_iff_val,
      dsimp only,
      congr' 1,
      rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same],
      exact hnx },
    erw eqx2 at hix,

    have eqy2 : (⟨localization.mk ((graded_algebra.proj 𝒜 ny) y ^ m) ⟨f ^ ny, ⟨_, rfl⟩⟩, begin
      refine ⟨ny, _, _, rfl⟩,
      apply set_like.graded_monoid.pow_deg,
      rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same 𝒜 hny],
      exact hny,
    end⟩
      : degree_zero_part _ f m f_deg) =
      (⟨localization.mk (y^m) ⟨f^ny, ⟨_, rfl⟩⟩, begin
        refine ⟨ny, _, _, rfl⟩,
        apply set_like.graded_monoid.pow_deg,
        exact hny,
      end⟩ : degree_zero_part _ f m f_deg),
    { rw subtype.ext_iff_val,
      dsimp only,
      congr' 1,
      rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same],
      exact hny },
    erw eqy2 at hiy,

    have eq3 : (⟨localization.mk ((graded_algebra.proj 𝒜 (nx+ny)) (x*y) ^ m)
      ⟨f^(nx+ny), ⟨_, rfl⟩⟩, begin
        refine ⟨nx + ny, _, _, rfl⟩,
        apply set_like.graded_monoid.pow_deg,
        rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same],
        apply set_like.graded_monoid.mul_mem hnx hny,
        apply set_like.graded_monoid.mul_mem hnx hny,
      end⟩
      : degree_zero_part _ f m f_deg) =
      (⟨localization.mk ((x*y)^m) ⟨f^(nx+ny), ⟨_, rfl⟩⟩, begin
        refine ⟨nx + ny, _, _, rfl⟩,
        apply set_like.graded_monoid.pow_deg,
        apply set_like.graded_monoid.mul_mem hnx hny,
      end⟩ : degree_zero_part _ f m f_deg),
    { rw subtype.ext_iff_val,
      dsimp only,
      congr' 1,
      rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same],
      apply set_like.graded_monoid.mul_mem hnx hny, },
    erw eq3 at rid,

    have eq4 : (⟨localization.mk ((x*y)^m) ⟨f^(nx+ny), ⟨_, rfl⟩⟩, begin
      refine ⟨nx + ny, _, _, rfl⟩,
      apply set_like.graded_monoid.pow_deg,
      apply set_like.graded_monoid.mul_mem hnx hny,
    end⟩ : degree_zero_part _ f m f_deg)
    = (⟨localization.mk (x^m) ⟨f^nx, ⟨_, rfl⟩⟩, begin
        refine ⟨nx, _, _, rfl⟩,
        apply set_like.graded_monoid.pow_deg,
        exact hnx,
    end⟩ : degree_zero_part _ f m f_deg) *
      (⟨localization.mk (y^m) ⟨f^ny, ⟨_, rfl⟩⟩, begin
        refine ⟨ny, _, _, rfl⟩,
        apply set_like.graded_monoid.pow_deg,
        exact hny,
      end⟩ : degree_zero_part _ f m f_deg),
    { rw [subtype.ext_iff_val, show ∀ (x y : degree_zero_part _ f m f_deg), (x * y).1 = x.1 * y.1,
        from λ _ _, rfl],
      dsimp only,
      rw [localization.mk_mul],
      congr',
      rw mul_pow,
      rw pow_add, },
    erw eq4 at rid,

    rcases ideal.is_prime.mem_or_mem (q.is_prime) rid with L | R,
    apply hix, exact L,
    apply hiy, exact R, },
end

lemma isos.backward.carrier.irrelavent (f : A) [decidable_eq (localization.away f)]
  (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) :
  ¬(irrelavent_ideal 𝒜 ≤ ⟨isos.backward.carrier.as_ideal 𝒜 f m hm f_deg q,
    isos.backward.carrier.homogeneous 𝒜 f m hm f_deg q⟩) :=
begin
  intro rid,
  have mem1 : f ∉ isos.backward.carrier.as_ideal 𝒜 f m hm f_deg q,
  { intro rid2,
    specialize rid2 m,
    apply q.is_prime.1,
    rw ideal.eq_top_iff_one,
    convert rid2,
    rw [subtype.ext_iff_val, show (1 : degree_zero_part _ f m f_deg).1 = 1, from rfl],
    dsimp only,
    symmetry,
    erw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same],
    convert localization.mk_self _,
    refl,
    exact f_deg,
  },
  apply mem1,
  have mem2 : f ∈ irrelavent_ideal 𝒜,
  { change graded_algebra.proj 𝒜 0 f = 0,
    rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_ne 𝒜 f_deg],
    symmetry,
    apply ne_of_lt,
    exact hm,
  },
  apply rid mem2,
end

def isos.forward.carrer_ne_top (f : A) [decidable_eq (localization.away f)] (m : ℕ) (f_deg : f ∈ 𝒜 m)
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
def isos.top_component.forward.to_fun (f : A) [decidable_eq (localization.away f)]  (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.1 →
  (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1 := λ x,
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
  end⟩⟩


def isos.top_component.backward.to_fun (f : A) [decidable_eq (localization.away f)] (m : ℕ)
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m) :
  (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1 →
  (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.1 :=
λ q, ⟨⟨⟨isos.backward.carrier.as_ideal _ f m hm f_deg q,
  isos.backward.carrier.homogeneous _ f m hm f_deg q⟩,
  isos.backward.carrier.prime _ f m hm f_deg q,
  isos.backward.carrier.irrelavent _ f m hm f_deg q⟩,
  begin
    erw projective_spectrum.mem_basic_open,
    intro rid,
    change ∀ i : ℕ, _ ∈ q.1 at rid,
    specialize rid m,
    apply q.is_prime.1,
    rw ideal.eq_top_iff_one,
    convert rid,
    symmetry,
    rw [subtype.ext_iff_val, show (1 : degree_zero_part _ f m f_deg).1 = 1, from rfl],
    dsimp only,
    rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same 𝒜 f_deg],
    convert localization.mk_self _,
    refl,
end⟩

lemma isos.top_component.backward_forward (f : A) [decidable_eq (localization.away f)] (m : ℕ)
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m)
  (x) :
  isos.top_component.backward.to_fun 𝒜 f m hm f_deg
    (isos.top_component.forward.to_fun 𝒜 f m f_deg x) = x :=
begin
  ext z, split; intros hz,
  { change ∀ i, _ at hz,
    erw ←graded_algebra.sum_support_decompose 𝒜 z,
    apply ideal.sum_mem,
    intros i hi,
    specialize hz i,
    change _ ∈ ideal.span _ at hz,
    dsimp only at hz,
    rw ←graded_algebra.proj_apply,
    erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
    obtain ⟨c, eq1⟩ := hz,
    erw [finsupp.total_apply, finsupp.sum] at eq1,
    obtain ⟨N, hN⟩ := clear_denominator _ f (finset.image (λ i, c i * i.1) c.support),
    -- N is the common denom
    choose after_clear_denominator hacd using hN,
    have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
    { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },
    have eq2 := calc (localization.mk (f^(i + N)) 1) * (localization.mk ((graded_algebra.proj 𝒜 i z)^m) ⟨f^i, ⟨_, rfl⟩⟩ : localization.away f)
                  = (localization.mk (f^(i + N)) 1) * ∑ i in c.support, c i • i.1 : by erw eq1
              ... = (localization.mk (f^(i + N)) 1) * ∑ i in c.support.attach, c i.1 • i.1.1
                  : begin
                    rw finset.sum_bij',
                    work_on_goal 5 { intros a _, exact a.1, },
                    work_on_goal 3 { intros a ha, exact ⟨a, ha⟩, },
                    { intros a ha, dsimp only, refl, },
                    { intros a ha, dsimp only, refl, },
                    { intros a ha, rw subtype.ext_iff_val, },
                    { intros a ha, dsimp only, apply finset.mem_attach, },
                    { intros a ha, dsimp only, exact a.2, },
                  end
              ... = localization.mk (f^i) 1 * ((localization.mk (f^N) 1) * ∑ i in c.support.attach, c i.1 • i.1.1)
                  : begin
                    rw [←mul_assoc, localization.mk_mul, mul_one, pow_add],
                  end
              ... = localization.mk (f^i) 1 * (localization.mk (f^N) 1 * ∑ i in c.support.attach, c i.1 * i.1.1) : rfl
              ... = localization.mk (f^i) 1 * ∑ i in c.support.attach, (localization.mk (f^N) 1) * (c i.1 * i.1.1)
                  : by rw finset.mul_sum
              ... = localization.mk (f^i) 1 * ∑ i in c.support.attach, localization.mk (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                  : begin
                    congr' 1,
                    rw finset.sum_congr rfl (λ j hj, _),
                    have := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
                    dsimp only at this,
                      erw [this, mul_comm],
                    end
              ... = localization.mk (f^i) 1 * localization.mk (∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                  : begin
                    congr' 1,
                    induction c.support.attach using finset.induction_on with a s ha ih,
                    { rw [finset.sum_empty, finset.sum_empty, localization.mk_zero], },
                    { erw [finset.sum_insert ha, finset.sum_insert ha, ih, localization.add_mk, mul_one, one_mul, one_mul, add_comm], },
                  end
              ... = localization.mk (f^i * ∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                  : begin
                    rw [localization.mk_mul, one_mul],
                  end,
    have eq3 := calc
                (localization.mk (f^(i + N)) 1) * (localization.mk ((graded_algebra.proj 𝒜 i z)^m) ⟨f^i, ⟨_, rfl⟩⟩ : localization.away f)
              = (localization.mk (f^N) 1) * (localization.mk ((graded_algebra.proj 𝒜 i z)^m) 1)
              : begin
                rw [localization.mk_mul, localization.mk_mul, one_mul, one_mul, localization.mk_eq_mk', is_localization.eq],
                refine ⟨1, _⟩,
                erw [mul_one, mul_one, mul_one, pow_add, ←subtype.val_eq_coe],
                dsimp only,
                ring,
              end
          ... = (localization.mk (f^N * (graded_algebra.proj 𝒜 i z)^m) 1)
              : begin
                rw [localization.mk_mul, one_mul],
              end,
    have eq4 : ∃ (C : submonoid.powers f),
      (f^i * ∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) * C.1 =
      (f^N * (graded_algebra.proj 𝒜 i z)^m) * C.1,
    { rw [eq2] at eq3,
      simp only [localization.mk_eq_mk', is_localization.eq] at eq3,
      obtain ⟨C, hC⟩ := eq3,
      erw [mul_one, mul_one] at hC,
      refine ⟨C, hC⟩, },
    obtain ⟨C, hC⟩ := eq4,
    have mem1 :
      (f^i * ∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) * C.1 ∈ x.1.as_homogeneous_ideal,
    { apply ideal.mul_mem_right,
      apply ideal.mul_mem_left,
      apply ideal.sum_mem,
      rintros ⟨j, hj⟩ _,
      have eq5 := (hacd (c j * j.1) (prop1 j hj)).2,
      dsimp only at eq5 ⊢,
      have mem2 := j.2,
      change ∃ g, _ at mem2,
      obtain ⟨g, hg1, hg2⟩ := mem2,
      have eq6 : ∃ (k : ℕ) (z : A), c j = localization.mk z ⟨f^k, ⟨_, rfl⟩⟩,
      { induction (c j) using localization.induction_on with data,
        obtain ⟨z, ⟨_, k, rfl⟩⟩ := data,
        refine ⟨_, _, rfl⟩,},
      obtain ⟨k, z, eq6⟩ := eq6,
      have eq7 := calc localization.mk (after_clear_denominator (c j * j.1) (prop1 j hj)) 1
                = c j * j.1 * localization.mk (f^N) 1 : eq5
            ... = (localization.mk z ⟨f^k, ⟨_, rfl⟩⟩ : localization.away f) * j.1 * localization.mk (f^N) 1 : by rw eq6
            ... = (localization.mk z ⟨f^k, ⟨_, rfl⟩⟩ : localization.away f) * localization.mk g 1 * localization.mk (f^N) 1 : by rw hg2
            ... = localization.mk (z*g*f^N) ⟨f^k, ⟨_, rfl⟩⟩
                : begin
                  rw [localization.mk_mul, localization.mk_mul, mul_one, mul_one],
                end,
      simp only [localization.mk_eq_mk', is_localization.eq] at eq7,
      obtain ⟨⟨_, ⟨l, rfl⟩⟩, eq7⟩ := eq7,
      erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one] at eq7,
      dsimp only at eq7,
      have mem3 : z * g * f ^ N * f ^ l ∈ x.1.as_homogeneous_ideal,
      { apply ideal.mul_mem_right,
        apply ideal.mul_mem_right,
        apply ideal.mul_mem_left,
        exact hg1, },
      erw [←eq7, mul_assoc, ←pow_add] at mem3,
      rcases ideal.is_prime.mem_or_mem (x.1.is_prime) mem3 with H | RID,
      { exact H, },
      { exfalso,
        have mem4 := x.2,
        erw projective_spectrum.mem_basic_open at mem4,
        apply mem4,
        replace RID := ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ RID,
        exact RID,
        } },

    erw hC at mem1,
    rcases ideal.is_prime.mem_or_mem (x.1.is_prime) mem1 with S | RID2,
    rcases ideal.is_prime.mem_or_mem (x.1.is_prime) S with RID1 | H,
    { exfalso,
      replace RID1 := ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ RID1,
      have mem2 := x.2,
      erw projective_spectrum.mem_basic_open at mem2,
      apply mem2,
      apply RID1, },
    { replace H := ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ H,
      exact H, },
    { exfalso,
      rcases C with ⟨_, ⟨k, rfl⟩⟩,
      replace RID2 := ideal.is_prime.mem_of_pow_mem (x.1.is_prime) _ RID2,
      have mem2 := x.2,
      erw projective_spectrum.mem_basic_open at mem2,
      apply mem2,
      exact RID2, }, },
  { change ∀ i, _ ∈ ideal.span _,
    intros i,
    dsimp only,
    have mem2 := x.1.as_homogeneous_ideal.2 i hz,
    rw ←graded_algebra.proj_apply at mem2,
    have eq1 : (localization.mk ((graded_algebra.proj 𝒜 i z)^m) ⟨f^i, ⟨_, rfl⟩⟩ : localization.away f)
          = localization.mk 1 ⟨f^i, ⟨_, rfl⟩⟩ * localization.mk ((graded_algebra.proj 𝒜 i z)^m) 1,
    { erw [localization.mk_mul, one_mul, mul_one] },
    erw eq1,
    apply ideal.mem_span.smul_mem,
    refine ⟨(graded_algebra.proj 𝒜 i z)^m, _, rfl⟩,
    erw ideal.is_prime.pow_mem_iff_mem (x.1.is_prime),
    exact mem2,
    exact hm, },
end

lemma isos.top_component.forward_backward (f : A) [decidable_eq (localization.away f)] (m : ℕ)
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m)
  (x) :
  isos.top_component.forward.to_fun 𝒜 f m f_deg
  (isos.top_component.backward.to_fun 𝒜 f m hm f_deg x) = x :=
begin
ext z, split,
{ intros hz,
  change z ∈ (isos.top_component.forward.to_fun _ f m f_deg
    (⟨⟨⟨isos.backward.carrier.as_ideal 𝒜 f m hm f_deg x,
      isos.backward.carrier.homogeneous 𝒜 f m hm f_deg x⟩,
      isos.backward.carrier.prime _ f m hm f_deg x,
      isos.backward.carrier.irrelavent _ f m hm f_deg x⟩, _⟩)).1 at hz,
  unfold isos.top_component.forward.to_fun at hz,
  dsimp only at hz,
  erw isos.forward.carrier_eq_carrier' at hz,
  unfold isos.forward.carrier' at hz,
  erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at hz,
  obtain ⟨c, eq1⟩ := hz,
  erw [finsupp.total_apply, finsupp.sum] at eq1,
  erw ←eq1,
  apply ideal.sum_mem,
  rintros ⟨⟨j, j_degree_zero⟩, j_mem⟩ hj,
  change ∃ _, _ at j_mem,
  obtain ⟨s, hs, n, s_mem, eq3⟩ := j_mem,
  apply ideal.mul_mem_left,
  erw [←subtype.val_eq_coe],
  dsimp only,
  erw eq3,
  dsimp only at hs,
  change ∀ _, _ at hs,
  specialize hs (m * n),
  simp only [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same 𝒜 s_mem] at hs,
  have eq4 : ((⟨localization.mk s ⟨f ^ n, ⟨_, rfl⟩⟩, ⟨n, s, s_mem, rfl⟩⟩ : degree_zero_part _ f m f_deg))^m =
    ⟨localization.mk (s^m) ⟨f^(m*n), ⟨_, rfl⟩⟩, ⟨m*n, s^m, begin
      apply set_like.graded_monoid.pow_deg,
      exact s_mem,
    end, rfl⟩⟩,
  { rw [subtype.ext_iff_val,
        show (∀ (β : degree_zero_part 𝒜 f m f_deg) (l : ℕ), (β^l).val = (β.val)^l), begin
          intros β l,
          induction l with l ih,
          { erw [pow_zero, pow_zero], refl, },
          { erw [pow_succ, pow_succ, show (∀ z1 z2 : degree_zero_part 𝒜 f m f_deg, (z1 * z2).val = z1.1 * z2.1),
            from λ _ _, rfl, ih], },
        end],
    dsimp only,
    rw localization.mk_pow,
    exact hm, },
  erw ←eq4 at hs,
  exact ideal.is_prime.mem_of_pow_mem (x.is_prime) _ hs, },
  { intros hz,
    unfold isos.top_component.forward.to_fun,
    dsimp only,
    unfold isos.forward.carrier,
    change z.1 ∈ ideal.span _,
    dsimp only,
    rcases z with ⟨z, z_degree_zero⟩,
    induction z using localization.induction_on with data,
    rcases data with ⟨a, ⟨_, ⟨k, rfl⟩⟩⟩,
    dsimp only at hz ⊢,
    change ∃ (n : ℕ), _ at z_degree_zero,
    obtain ⟨n, α, α_mem, hα⟩ := z_degree_zero,
    dsimp only at hα,
    have α_mem_x : (⟨localization.mk α ⟨f ^ n, _⟩, ⟨n, α, α_mem, rfl⟩⟩ : degree_zero_part _ f m f_deg) ∈ x.1,
    { convert hz using 1,
      symmetry,
      rw subtype.ext_iff_val,
      dsimp only,
      exact hα, },
    erw hα,
    have mem1 : α ∈ isos.backward.carrier _ f m hm f_deg x,
    { intros j,
      by_cases ineq1 : j = m * n,
      { simp only [ineq1, graded_algebra.proj_apply],
        dsimp only,
        simp only [graded_algebra.decompose_of_mem_same 𝒜 α_mem],
        have mem2 := (ideal.is_prime.pow_mem_iff_mem x.is_prime m hm).mpr α_mem_x,
        convert mem2 using 1,
        rw [subtype.ext_iff_val,
          show (∀ (β : degree_zero_part 𝒜 f m f_deg) (l : ℕ), (β^l).val = (β.val)^l),
          begin
            intros β l,
            induction l with l ih,
            { erw [pow_zero, pow_zero], refl, },
            { erw [pow_succ, pow_succ,
                show (∀ z1 z2 : degree_zero_part 𝒜 f m f_deg, (z1 * z2).val = z1.1 * z2.1),
                from λ _ _, rfl, ih], },
          end],
          dsimp only,
          symmetry,
          apply localization.mk_pow,
          exact hm, },
    { simp only [graded_algebra.proj_apply,
      graded_algebra.decompose_of_mem_ne 𝒜 α_mem (ne.symm ineq1),
      zero_pow hm, localization.mk_zero],
      exact submodule.zero_mem _, }, },
    have eq2 : (localization.mk α ⟨f^n, ⟨_, rfl⟩⟩ : localization.away f) =
      localization.mk 1 ⟨f^n, ⟨_, rfl⟩⟩ * localization.mk α 1,
      { rw [localization.mk_mul, one_mul, mul_one], },
        erw eq2,
        apply ideal.mem_span.smul_mem,
        refine ⟨α, mem1, rfl⟩, },
end

lemma isos.top_component.forward_preimage_eq (f : A) [decidable_eq (localization.away f)]
  (m : ℕ) (f_deg : f ∈ 𝒜 m) (a : A) (n : ℕ)
  (a_mem_degree_zero : (localization.mk a ⟨f ^ n, ⟨n, rfl⟩⟩ : localization.away f) ∈ degree_zero_part 𝒜 f m f_deg) :
  isos.top_component.forward.to_fun 𝒜 f m f_deg ⁻¹'
      (prime_spectrum.basic_open (⟨localization.mk a ⟨f ^ n, ⟨_, rfl⟩⟩, a_mem_degree_zero⟩ : degree_zero_part _ f m f_deg)).1
  = {x | x.1 ∈ projective_spectrum.basic_open 𝒜 f ⊓ projective_spectrum.basic_open 𝒜 a} :=
begin
  symmetry,
  ext1 y, split; intros hy,
      { change y.1 ∈ _ at hy,
        rcases hy with ⟨hy1, hy2⟩,
        erw projective_spectrum.mem_basic_open at hy1 hy2,
        rw [set.mem_preimage, isos.top_component.forward.to_fun],
        dsimp only,
        erw prime_spectrum.mem_basic_open,
        intro rid,
        -- unfold isos.forward.carrier at rid,
        change (localization.mk a ⟨f^n, ⟨n, rfl⟩⟩ : localization.away f) ∈ _ at rid,
        erw [←ideal.submodule_span_eq, finsupp.span_eq_range_total, set.mem_range] at rid,
        obtain ⟨c, eq1⟩ := rid,
        erw [finsupp.total_apply, finsupp.sum] at eq1,

        obtain ⟨N, hN⟩ := clear_denominator _ f (finset.image (λ i, c i * i.1) c.support),
        -- N is the common denom
        choose after_clear_denominator hacd using hN,
        have prop1 : ∀ i, i ∈ c.support → c i * i.1 ∈ (finset.image (λ i, c i * i.1) c.support),
        { intros i hi, rw finset.mem_image, refine ⟨_, hi, rfl⟩, },

        have eq2 := calc (localization.mk (f^N * a) 1 : localization.away f)
                = (localization.mk (f^N) 1 : localization.away f) * localization.mk a 1
                : begin
                  erw [localization.mk_mul, one_mul],
                end
            ... = localization.mk (f^N) 1 * localization.mk (f^n) 1 * localization.mk a ⟨f^n, ⟨_, rfl⟩⟩
                : begin
                  erw [localization.mk_mul, localization.mk_mul, localization.mk_mul, one_mul, one_mul],
                  simp only [localization.mk_eq_mk', is_localization.eq],
                  use 1,
                  erw [mul_one, mul_one, mul_one, ←subtype.val_eq_coe],
                  dsimp only,
                  ring,
                end
            ... = localization.mk (f^N) 1* localization.mk (f^n) 1 * ∑ i in c.support, c i * i.1 : by erw eq1
            ... = localization.mk (f^N) 1* localization.mk (f^n) 1 * ∑ i in c.support.attach, c i.1 * i.1.1
                : begin
                  congr' 1,
                  rw finset.sum_bij',
                  work_on_goal 5 { intros a ha, exact a.1 },
                  work_on_goal 3 { intros a ha, exact ⟨a, ha⟩ },
                  { intros a ha, dsimp only, refl, },
                  { intros a ha, dsimp only, refl, },
                  { intros a ha, dsimp only, rw subtype.ext_iff_val, },
                  { intros a ha, dsimp only, apply finset.mem_attach, },
                  { intros a ha, dsimp only, exact a.2, },
                end
            ... = localization.mk (f^n) 1 * (localization.mk (f^N) 1 * ∑ i in c.support.attach, c i.1 * i.1.1) : by ring
            ... = localization.mk (f^n) 1 * ∑ i in c.support.attach, localization.mk (f^N) 1 * (c i.1 * i.1.1)
                : begin
                  congr' 1,
                  erw finset.mul_sum,
                end
            ... = localization.mk (f^n) 1 *
                  ∑ i in c.support.attach, localization.mk
                    (after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                : begin
                  congr' 1,
                  erw finset.sum_congr rfl (λ j hj, _),
                  have := (hacd (c j * j) (prop1 j _)).2,
                  dsimp only at this,
                  erw [this, mul_comm],
                  refl,
                end
            ... = localization.mk (f^n) 1 *
                  localization.mk
                    (∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                : begin
                  congr' 1,
                  induction c.support.attach using finset.induction_on with a s ha ih,
                  erw [finset.sum_empty, finset.sum_empty, localization.mk_zero],
                  erw [finset.sum_insert ha, finset.sum_insert ha, ih, localization.add_mk,
                    one_mul, one_mul, one_mul, add_comm],
                end
            ... = localization.mk (f^n * ∑ i in c.support.attach, after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                : begin
                  erw [localization.mk_mul, one_mul],
                end
            ... = localization.mk (∑ i in c.support.attach, f^n * after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) 1
                : by erw finset.mul_sum,

        simp only [localization.mk_eq_mk', is_localization.eq] at eq2,
        obtain ⟨⟨_, ⟨k1, rfl⟩⟩, eq2⟩ := eq2,
        erw [mul_one, mul_one, ←subtype.val_eq_coe] at eq2,
        dsimp only at eq2,

        have mem1 : (∑ i in c.support.attach, f^n * after_clear_denominator (c i.1 * i.1.1) (prop1 i.1 i.2)) * f^k1 ∈ y.1.as_homogeneous_ideal,
        { apply ideal.mul_mem_right,
          apply ideal.sum_mem,
          intros j hj,
          apply ideal.mul_mem_left,
          set g := classical.some j.1.2 with g_eq,
          have mem3 : g ∈ y.1.as_homogeneous_ideal := (classical.some_spec j.1.2).1,
          have eq3 : j.1.1 = localization.mk g 1 := (classical.some_spec j.1.2).2,
          have eq4 := (hacd (c j.1 * j.1.1) (prop1 j.1 j.2)).2,
          dsimp only at eq4,

           have eq5 : ∃ (a : A) (z : ℕ), c j.1 = localization.mk a ⟨f^z, ⟨z, rfl⟩⟩,
          { induction (c j.1) using localization.induction_on with data,
            rcases data with ⟨a, ⟨_, ⟨z, rfl⟩⟩⟩,
            refine ⟨a, z, rfl⟩, },
          obtain ⟨α, z, hz⟩ := eq5,

          have eq6 := calc localization.mk (after_clear_denominator (c j.1 * j.1.1) (prop1 j.1 j.2)) 1
              = c j.1 * j.1.1 * localization.mk (f^N) 1 : eq4
          ... = (localization.mk α ⟨f^z, ⟨z, rfl⟩⟩ : localization.away f) * j.1.1 * localization.mk (f^N) 1
              : by erw hz
          ... = (localization.mk α ⟨f^z, ⟨z, rfl⟩⟩ : localization.away f) * localization.mk g 1 * localization.mk (f^N) 1
              : by erw eq3
          ... = localization.mk (α * g * f^N) ⟨f^z, ⟨z, rfl⟩⟩
              : begin
                erw [localization.mk_mul, localization.mk_mul, mul_one, mul_one],
              end,
          simp only [localization.mk_eq_mk', is_localization.eq] at eq6,
          obtain ⟨⟨_, ⟨v, rfl⟩⟩, eq6⟩ := eq6,
          erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one] at eq6,
          dsimp only at eq6,

          have mem3 : α * g * f ^ N * f ^ v ∈ y.1.as_homogeneous_ideal,
          { apply ideal.mul_mem_right,
            apply ideal.mul_mem_right,
            apply ideal.mul_mem_left,
            exact mem3, },
          erw ←eq6 at mem3,
          rcases y.1.is_prime.mem_or_mem mem3 with H1 | H3,
          rcases y.1.is_prime.mem_or_mem H1 with H1 | H2,
          { exact H1 },
          { exfalso, apply hy1,
            exact y.1.is_prime.mem_of_pow_mem _ H2, },
          { exfalso, apply hy1,
            exact y.1.is_prime.mem_of_pow_mem _ H3, }, },

      erw ←eq2 at mem1,
      rcases y.1.is_prime.mem_or_mem mem1 with H1 | H3,
      rcases y.1.is_prime.mem_or_mem H1 with H1 | H2,
      { apply hy1,
        exact y.1.is_prime.mem_of_pow_mem _ H1, },
      { apply hy2,
        exact H2, },
      { apply hy1,
        exact y.1.is_prime.mem_of_pow_mem _ H3, }, },

    { change y.1 ∈ _ ⊓ _,
      refine ⟨y.2, _⟩,
      -- a ∉ y,
      erw [set.mem_preimage, prime_spectrum.mem_basic_open] at hy,
      erw projective_spectrum.mem_basic_open,
      intro a_mem_y,
      apply hy,
      change (localization.mk a ⟨f ^ n, ⟨_, rfl⟩⟩ : localization.away f) ∈ ideal.span _,
      have eq1 : (localization.mk a ⟨f^n, ⟨_, rfl⟩⟩ : localization.away f) =
        localization.mk 1 ⟨f^n, ⟨_, rfl⟩⟩ * localization.mk a 1,
      { erw [localization.mk_mul, one_mul, mul_one], },
      erw eq1,
      apply ideal.mem_span.smul_mem,
      refine ⟨a, a_mem_y, rfl⟩, }
end

def isos.top_component.forward (f : A) [decidable_eq (localization.away f)]
  (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.carrier ⟶
  (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.carrier :=
{ to_fun := isos.top_component.forward.to_fun 𝒜 f m f_deg,
  continuous_to_fun := begin
    apply is_topological_basis.continuous,
    exact prime_spectrum.is_topological_basis_basic_opens,
    rintros _ ⟨⟨g, hg⟩, rfl⟩,
    induction g using localization.induction_on with data,
    obtain ⟨a, ⟨_, ⟨n, rfl⟩⟩⟩ := data,
    dsimp only,

    -- we want to use `projective_spectrum.basic_open 𝒜 (f*a) = preimage`
    set set1 : set ((Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.1) :=
    { x | x.1 ∈ projective_spectrum.basic_open 𝒜 f ⊓ projective_spectrum.basic_open 𝒜 a } with set1_eq,
    have o1 : is_open set1,
    { rw is_open_induced_iff,
      refine ⟨(projective_spectrum.basic_open 𝒜 f).1 ⊓ (projective_spectrum.basic_open 𝒜 a).1,
        is_open.inter (projective_spectrum.basic_open 𝒜 f).2 (projective_spectrum.basic_open 𝒜 a).2, _⟩,
      ext z, split; intros hz,
      { erw set.mem_preimage at hz,
        erw set1_eq,
        exact hz, },
      { erw set1_eq at hz,
        change _ ∧ _ at hz,
        erw set.mem_preimage,
        exact hz, }, },
    suffices : set1 = isos.top_component.forward.to_fun 𝒜 f m f_deg ⁻¹'
      (prime_spectrum.basic_open (⟨localization.mk a ⟨f ^ n, _⟩, hg⟩ : degree_zero_part _ f m f_deg)).1,
    { erw ←this,
      exact o1, },
    { symmetry,
      apply isos.top_component.forward_preimage_eq },
  end }

lemma isos.top_component.forward.to_fun_inj (f : A) [decidable_eq (localization.away f)] (m : ℕ)
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m) : function.injective (isos.top_component.forward.to_fun 𝒜 f m f_deg) := λ x1 x2 hx12,
begin
  convert congr_arg (isos.top_component.backward.to_fun 𝒜 f m hm f_deg) hx12; symmetry;
  apply isos.top_component.backward_forward,
end

lemma isos.top_component.forward.to_fun_surj (f : A) [decidable_eq (localization.away f)] (m : ℕ)
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m) : function.surjective (isos.top_component.forward.to_fun 𝒜 f m f_deg) :=
begin
  erw function.surjective_iff_has_right_inverse,
  refine ⟨isos.top_component.backward.to_fun 𝒜 f m hm f_deg, λ x, _⟩,
  rw isos.top_component.forward_backward,
end

def isos.top_component.backward (f : A) [decidable_eq (localization.away f)] (m : ℕ)
  (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m) :
  (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.carrier ⟶
  (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.carrier :=
{ to_fun := isos.top_component.backward.to_fun _ f m hm f_deg,
  continuous_to_fun := begin
    apply is_topological_basis.continuous,
    exact @is_topological_basis.inducing (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.1
    _ Proj _ (λ x, x.1) _ begin
      fconstructor, refl,
    end (projective_spectrum.is_topological_basis_basic_opens 𝒜),

    intros s hs,
    erw set.mem_preimage at hs,
    obtain ⟨t, ht1, ht2⟩ := hs,
    rw set.mem_range at ht1,
    obtain ⟨a, rfl⟩ := ht1,
    dsimp only at ht2,
    have set_eq1 : s =
      {x | x.1 ∈ (projective_spectrum.basic_open 𝒜 f) ⊓ (projective_spectrum.basic_open 𝒜 a) },
    { ext x, split; intros hx,
      erw [←ht2, set.mem_preimage] at hx,
      refine ⟨x.2, hx⟩,

      rcases hx with ⟨hx1, hx2⟩,
      erw [←ht2, set.mem_preimage],
      exact hx2, },

    -- we want to use preimage = forward s,
    set set1 := isos.top_component.forward.to_fun 𝒜 f m f_deg '' s with set1_eq,
    have o1 : is_open set1,
    {
      suffices : is_open (isos.top_component.forward.to_fun 𝒜 f m f_deg ''
        {x | x.1 ∈ (projective_spectrum.basic_open 𝒜 f).1 ⊓ (projective_spectrum.basic_open 𝒜 a).1}),
      erw [set1_eq, set_eq1], exact this,
      -- erw projective_spectrum.basic_open_as_union_of_projection 𝒜 a,

      have set_eq2 := calc isos.top_component.forward.to_fun 𝒜 f m f_deg ''
            {x | x.1 ∈ (projective_spectrum.basic_open 𝒜 f) ⊓ (projective_spectrum.basic_open 𝒜 a)}
          = isos.top_component.forward.to_fun 𝒜 f m f_deg ''
            {x | x.1 ∈ (projective_spectrum.basic_open 𝒜 f) ⊓ (⨆ (i : ℕ), (projective_spectrum.basic_open 𝒜 (graded_algebra.proj 𝒜 i a)))}
          : begin
            congr',
            ext x,
            erw projective_spectrum.basic_open_as_union_of_projection 𝒜 a,
          end
      ... = isos.top_component.forward.to_fun 𝒜 f m f_deg '' {x | x.1 ∈
              (⨆ (i : ℕ), ((projective_spectrum.basic_open 𝒜 f) ⊓
                (projective_spectrum.basic_open 𝒜 (graded_algebra.proj 𝒜 i a))))}
          : begin
            congr',
            ext x,
            split; intros hx,
            { rcases hx with ⟨hx1, hx2⟩,
              erw opens.mem_Sup at hx2 ⊢,
              obtain ⟨_, ⟨j, rfl⟩, hx2⟩ := hx2,
              refine ⟨projective_spectrum.basic_open 𝒜 f ⊓
                projective_spectrum.basic_open 𝒜 (graded_algebra.proj 𝒜 j a), ⟨j, rfl⟩, ⟨hx1, hx2⟩⟩, },
            { erw opens.mem_Sup at hx,
              obtain ⟨_, ⟨j, rfl⟩, ⟨hx1, hx2⟩⟩ := hx,
              refine ⟨hx1, _⟩,
              erw opens.mem_Sup,
              refine ⟨projective_spectrum.basic_open 𝒜 (graded_algebra.proj 𝒜 j a), ⟨j, rfl⟩, hx2⟩, },
          end
      ... = isos.top_component.forward.to_fun 𝒜 f m f_deg '' ⋃ (i : ℕ),
                {x | x.1 ∈ ((projective_spectrum.basic_open 𝒜 f) ⊓
                (projective_spectrum.basic_open 𝒜 (graded_algebra.proj 𝒜 i a)))}
          : begin
            congr',
            ext x,
            split; intros hx; dsimp only at hx ⊢,
            { change ∃ _, _ at hx,
              obtain ⟨s, hs1, hs2⟩ := hx,
              erw set.mem_image at hs1,
              obtain ⟨s, hs1, rfl⟩ := hs1,
              erw set.mem_range at hs1,
              obtain ⟨i, rfl⟩ := hs1,
              change ∃ _, _,
              refine ⟨_, ⟨i, rfl⟩, _⟩,
              exact hs2, },
            { change ∃ _, _ at hx,
              obtain ⟨_, ⟨j, rfl⟩, hx⟩ := hx,
              change x.val ∈ _ at hx,
              simp only [opens.mem_supr],
              refine ⟨j, hx⟩, },
          end
      ... = ⋃ (i : ℕ), isos.top_component.forward.to_fun 𝒜 f m f_deg ''
              {x | x.1 ∈ ((projective_spectrum.basic_open 𝒜 f) ⊓
                (projective_spectrum.basic_open 𝒜 (graded_algebra.proj 𝒜 i a)))}
          : begin
            erw set.image_Union,
          end,

    erw set_eq2,
    apply is_open_Union,
    intros i,
    suffices : isos.top_component.forward.to_fun 𝒜 f m f_deg ''
              {x | x.1 ∈ ((projective_spectrum.basic_open 𝒜 f) ⊓
                (projective_spectrum.basic_open 𝒜 (graded_algebra.proj 𝒜 i a)))}
        = (prime_spectrum.basic_open (⟨localization.mk ((graded_algebra.proj 𝒜 i a)^m) ⟨f^i, ⟨_, rfl⟩⟩,
            ⟨i, (graded_algebra.proj 𝒜 i a)^m, set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) _, rfl⟩⟩ : degree_zero_part 𝒜 f m f_deg)).1,
    erw this,
    exact (prime_spectrum.basic_open _).2,


    suffices : isos.top_component.forward.to_fun 𝒜 f m f_deg ⁻¹' (prime_spectrum.basic_open (⟨localization.mk ((graded_algebra.proj 𝒜 i a)^m) ⟨f^i, ⟨_, rfl⟩⟩,
            ⟨i, (graded_algebra.proj 𝒜 i a)^m, set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) _, rfl⟩⟩ : degree_zero_part 𝒜 f m f_deg)).1 =
      {x | x.1 ∈ ((projective_spectrum.basic_open 𝒜 f) ⊓
                (projective_spectrum.basic_open 𝒜 (graded_algebra.proj 𝒜 i a)))},

    { erw ←this,
      apply function.surjective.image_preimage,
      apply isos.top_component.forward.to_fun_surj,
      exact hm },

    symmetry,
    { symmetry,
      erw isos.top_component.forward_preimage_eq 𝒜 f m f_deg ((graded_algebra.proj 𝒜 i a)^m) i,
      erw projective_spectrum.basic_open_pow,
      exact hm,
    } },

    suffices : set1 = isos.top_component.backward.to_fun 𝒜 f m hm f_deg ⁻¹' _,
    erw ←this,
    exact o1,

    { erw set1_eq,
      ext z, split; intros hz,
      { erw set.mem_preimage,
        erw set.mem_image at hz,
        obtain ⟨α, α_mem, rfl⟩ := hz,
        erw isos.top_component.backward_forward,
        exact α_mem, },
      { erw set.mem_preimage at hz,
        erw set.mem_image,
        refine ⟨isos.top_component.backward.to_fun 𝒜 f m hm f_deg z, _, _⟩,
        exact hz,
        erw isos.top_component.forward_backward, } },
  end }

def isos.top_component (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m)
  (f_deg : f ∈ 𝒜 m) :
  (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.carrier ≅
  (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.carrier :=
{ hom := isos.top_component.forward 𝒜 f m f_deg,
  inv := isos.top_component.backward 𝒜 f m hm f_deg,
  hom_inv_id' := begin
    ext1 x,
    simp only [id_app, comp_app],
    apply isos.top_component.backward_forward,
  end,
  inv_hom_id' := begin
    ext1 x,
    simp only [id_app, comp_app],
    apply isos.top_component.forward_backward,
  end }

def isos.sheaf_component.forward.hartshorne
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U))
  (y : unop U) :=
hh.1 ⟨((isos.top_component 𝒜 f m hm f_deg).inv y.1).1, begin
        erw set.mem_preimage,
        refine ⟨⟨((isos.top_component 𝒜 f m hm f_deg).inv y.1).1, ((isos.top_component 𝒜 f m hm f_deg).inv y.1).2⟩, _, rfl⟩,
        change _ ∈ _ ⁻¹' _,
        erw set.mem_preimage,
        change (isos.top_component.forward.to_fun 𝒜 f m f_deg (isos.top_component.backward.to_fun 𝒜 f m hm f_deg y.1)) ∈ _,
        erw isos.top_component.forward_backward 𝒜 f m hm f_deg y.1,
        exact y.2,
      end⟩

lemma isos.sheaf_component.forward.hartshorne_one
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ) :
  ∀ y, isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U 1 y = 1 := λ y,
begin
  unfold isos.sheaf_component.forward.hartshorne,
  erw show (1 : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U)).1 = 1, from rfl,
  erw pi.one_apply,
end

lemma isos.sheaf_component.forward.hartshorne_zero
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ) :
  ∀ y, isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U 0 y = 0 := λ y,
begin
  unfold isos.sheaf_component.forward.hartshorne,
  erw show (0 : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U)).1 = 0, from rfl,
  erw pi.zero_apply,
end

lemma isos.sheaf_component.forward.hartshorne_add
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ) :
  ∀ x y z, isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U (x + y) z
    = isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U x z
    + isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U y z := λ x y z,
begin
  unfold isos.sheaf_component.forward.hartshorne,
  erw show (x + y).1 = x.1 + y.1, from rfl,
  erw pi.add_apply,
end

lemma isos.sheaf_component.forward.hartshorne_mul
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ) :
  ∀ x y z, isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U (x * y) z
    = isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U x z
    * isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U y z := λ x y z,
begin
  unfold isos.sheaf_component.forward.hartshorne,
  erw show (x * y).1 = x.1 * y.1, from rfl,
  erw pi.mul_apply,
end

def isos.sheaf_component.forward.hartshorne.num
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U))
  (y : unop U) :=
(isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U hh y).num

def isos.sheaf_component.forward.hartshorne.denom
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U))
  (y : unop U) :=
(isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U hh y).denom

def isos.sheaf_component.forward.hartshorne.i
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U))
  (y : unop U) :=
(isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U hh y).i

lemma isos.sheaf_component.forward.hartshorne.denom_hom
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U))
  (y : unop U) :
  (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U hh y) ∈
  𝒜 (isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U hh y) :=
(isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U hh y).denom_hom

lemma isos.sheaf_component.forward.hartshorne.denom_not_mem
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U))
  (y : unop U) :
  (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U hh y) ∉
    ((isos.top_component 𝒜 f m hm f_deg).inv y.1).1.as_homogeneous_ideal :=
(isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U hh y).denom_not_mem

lemma isos.sheaf_component.forward.hartshorne.num_hom
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U))
  (y : unop U) :
  (isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U hh y) ∈
  𝒜 (isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U hh y) :=
(isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U hh y).num_hom

lemma isos.sheaf_component.forward.hartshorne.eq_num_div_denom
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U))
  (y : unop U) :
  (isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U hh y).1 =
  localization.mk (isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U hh y)
    ⟨(isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U hh y),
      isos.sheaf_component.forward.hartshorne.denom_not_mem 𝒜 f m hm f_deg U hh y⟩ :=
(isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U hh y).eq_num_div_denom

def isos.sheaf_component.forward.hartshorne.mk_num
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U))
  (y : unop U) : degree_zero_part 𝒜 f m f_deg :=
⟨localization.mk
  ((isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U hh y) *
   (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U hh y) ^ m.pred)
  ⟨f^(isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U hh y), ⟨_, rfl⟩⟩,
  ⟨isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U hh y, _, begin
    have mem1 := isos.sheaf_component.forward.hartshorne.num_hom 𝒜 f m hm f_deg U hh y,
    have mem2 := isos.sheaf_component.forward.hartshorne.denom_hom 𝒜 f m hm f_deg U hh y,
    have mem3 := set_like.graded_monoid.pow_deg 𝒜 mem2 m.pred,
    have mem4 := set_like.graded_monoid.mul_mem mem1 mem3,
    convert mem4,

    have eq1 := nat.succ_pred_eq_of_pos hm,
    exact calc m * (isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U hh y)
            = (m.pred + 1) * (isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U hh y)
            : begin
              congr,
              conv_lhs { rw ←eq1 },
            end
        ... = m.pred * isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U hh y +
              1 * isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U hh y
            : by rw add_mul
        ... = _ : begin
          rw [add_comm, one_mul],
        end,
  end, rfl⟩⟩

def isos.sheaf_component.forward.hartshorne.mk_denom
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U))
  (y : unop U) : (y.1.as_ideal.prime_compl) :=
⟨⟨localization.mk ((isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U hh y) ^ m)
  ⟨f^(isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U hh y), ⟨_, rfl⟩⟩,
  ⟨(isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U hh y), _, begin
    apply set_like.graded_monoid.pow_deg,
    apply isos.sheaf_component.forward.hartshorne.denom_hom,
  end, rfl⟩⟩, λ rid, begin
    have prop1 := (isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U hh y).denom_not_mem,
    change _ ∉ (isos.top_component.backward.to_fun 𝒜 f m hm f_deg y.1).1.as_homogeneous_ideal at prop1,
    contrapose prop1,
    erw not_not,
    change ∀ _, _,

    contrapose prop1,
    erw not_not,
    erw not_forall at prop1,
    obtain ⟨n, hn⟩ := prop1,

    have eq1 : (isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U hh y) = n,
    { -- n ≠ i, contradiction,
      by_contra ineq,
      simp only [graded_algebra.proj_apply,
        graded_algebra.decompose_of_mem_ne 𝒜
          ((isos.sheaf_component.forward.hartshorne 𝒜 f m hm f_deg U hh y).denom_hom) ineq,
        zero_pow hm, localization.mk_zero] at hn,
      apply hn,
      exact submodule.zero_mem _, },
    apply hn,
    convert rid,

    erw [graded_algebra.proj_apply, ←eq1, graded_algebra.decompose_of_mem_same],
    refl,
    apply isos.sheaf_component.forward.hartshorne.denom_hom,
    exact eq1.symm,
  end⟩

def isos.sheaf_component.forward.mk
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U)) : Π (y : unop U),
    structure_sheaf.localizations (degree_zero_part 𝒜 f m f_deg) y.1 := λ y,
localization.mk
  (isos.sheaf_component.forward.hartshorne.mk_num 𝒜 f m hm f_deg U hh y)
  (isos.sheaf_component.forward.hartshorne.mk_denom 𝒜 f m hm f_deg U hh y)

lemma isos.sheaf_component.forward.mk_one
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ) :
  isos.sheaf_component.forward.mk 𝒜 f m hm f_deg U 1 = 1 :=
begin
  ext1 y,
  erw pi.one_apply,
  unfold isos.sheaf_component.forward.mk,
  dsimp only,
  erw [show (1 : structure_sheaf.localizations (degree_zero_part 𝒜 f m f_deg) y.val) =
    localization.mk 1 1, begin
      erw localization.mk_self 1,
    end, localization.mk_eq_mk', is_localization.eq],

  have eq1 := isos.sheaf_component.forward.hartshorne.eq_num_div_denom 𝒜 f m hm f_deg U 1 y,
  erw isos.sheaf_component.forward.hartshorne_one at eq1,
  erw [show (1 : hartshorne_localisation 𝒜 ((isos.top_component 𝒜 f m hm f_deg).inv y).1).1 = 1, from rfl] at eq1,
  erw [show (1 : localization.at_prime ((isos.top_component 𝒜 f m hm f_deg).inv y.1).1.as_homogeneous_ideal.1) =
    localization.mk 1 1,
      begin
        symmetry,
        convert localization.mk_self _,
        erw [←subtype.val_eq_coe],
        refl,
      end, localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨c, hc1⟩, eq1⟩ := eq1,

  change c ∉ isos.backward.carrier 𝒜 f m hm f_deg _ at hc1,
  change ¬(∀ i : ℕ, _ ∈ _) at hc1,
  erw not_forall at hc1,
  obtain ⟨j, hc1⟩ := hc1,
  erw [one_mul, mul_one, ←subtype.val_eq_coe] at eq1,
  dsimp only,
  replace eq1 : isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y * c =
    isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 1 y * c,
  { convert eq1, },
  have eq2 : graded_algebra.proj 𝒜 ((isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U 1 y) + j)
    (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y * c) =
    graded_algebra.proj 𝒜 ((isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U 1 y) + j)
    (isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 1 y * c),
  { refine congr_arg _ eq1, },

  have eq3 : graded_algebra.proj 𝒜 ((isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U 1 y) + j)
    (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y * c)
    = isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y * (graded_algebra.proj 𝒜 j c),
  { apply graded_algebra.proj_hom_mul,
    apply isos.sheaf_component.forward.hartshorne.denom_hom,
    intro rid,
    apply hc1,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },

  have eq4 : graded_algebra.proj 𝒜 ((isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U 1 y) + j)
    (isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 1 y * c)
    = isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 1 y * (graded_algebra.proj 𝒜 j c),
  { apply graded_algebra.proj_hom_mul,
    apply isos.sheaf_component.forward.hartshorne.num_hom,
    intro rid,
    apply hc1,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },

  erw [eq3, eq4] at eq2,

  use localization.mk ((graded_algebra.proj 𝒜 j c)^m) ⟨f^j, ⟨_, rfl⟩⟩,
  erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, ←subtype.val_eq_coe, mul_one, one_mul],
  dsimp only,

  unfold isos.sheaf_component.forward.hartshorne.mk_num,
  unfold isos.sheaf_component.forward.hartshorne.mk_denom,
  erw [subtype.ext_iff_val,
    show ∀ (x y : degree_zero_part 𝒜 f m f_deg), (x * y).1 = x.1 * y.1, from λ _ _, rfl,
    show ∀ (x y : degree_zero_part 𝒜 f m f_deg), (x * y).1 = x.1 * y.1, from λ _ _, rfl,
    localization.mk_mul, localization.mk_mul],
  dsimp only,
  congr' 1,
  exact calc isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 1 y
            * isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y ^ m.pred
            * (graded_algebra.proj 𝒜 j) c ^ m
          = isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 1 y
            * isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y ^ m.pred
            * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos,
            exact hm
          end
      ... = isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 1 y
            * isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y ^ m.pred
            * ((graded_algebra.proj 𝒜 j) c ^ m.pred * graded_algebra.proj 𝒜 j c)
          : begin
            congr',
            erw [pow_add, pow_one],
          end
      ... = (isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 1 y * graded_algebra.proj 𝒜 j c)
            * (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m.pred)
          : by ring
      ... = (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y * graded_algebra.proj 𝒜 j c)
            * (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y ^ m.pred * (graded_algebra.proj 𝒜 j) c ^ m.pred)
          : by erw eq2
      ... = (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y * graded_algebra.proj 𝒜 j c)
            * (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y * graded_algebra.proj 𝒜 j c) ^ m.pred
          : begin
            congr' 1,
            erw mul_pow,
          end
      ... = (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y * graded_algebra.proj 𝒜 j c) ^ 1
            * (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y * graded_algebra.proj 𝒜 j c) ^ m.pred
          : by rw pow_one
      ... = (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y * graded_algebra.proj 𝒜 j c) ^ (1 + m.pred)
          : by rw pow_add
      ... = (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 1 y * graded_algebra.proj 𝒜 j c) ^ m
          : begin
            congr' 1,
            rw [add_comm],
            convert nat.succ_pred_eq_of_pos hm,
          end
      ... = _ : by rw mul_pow,
end

lemma isos.sheaf_component.forward.mk_zero
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ) :
  isos.sheaf_component.forward.mk 𝒜 f m hm f_deg U 0 = 0 :=
begin
  ext1 y,
  erw [pi.zero_apply],
  unfold isos.sheaf_component.forward.mk,
  erw [show (0 : structure_sheaf.localizations (degree_zero_part 𝒜 f m f_deg) y.val) =
    localization.mk 0 1, begin
      erw localization.mk_zero,
    end, localization.mk_eq_mk', is_localization.eq],
  dsimp only,

  have eq1 := isos.sheaf_component.forward.hartshorne.eq_num_div_denom 𝒜 f m hm f_deg U 0 y,
  erw isos.sheaf_component.forward.hartshorne_zero at eq1,
  erw [show (0 : hartshorne_localisation 𝒜 ((isos.top_component 𝒜 f m hm f_deg).inv y).1).1 = 0, from rfl] at eq1,
  erw [show (0 : localization.at_prime ((isos.top_component 𝒜 f m hm f_deg).inv y.1).1.as_homogeneous_ideal.1) =
    localization.mk 0 1,
      begin
        erw localization.mk_zero,
      end, localization.mk_eq_mk', is_localization.eq] at eq1,
  obtain ⟨⟨c, hc1⟩, eq1⟩ := eq1,
  erw [zero_mul, zero_mul, mul_one, ←subtype.val_eq_coe] at eq1,
  dsimp only at eq1,

  change c ∉ isos.backward.carrier 𝒜 f m hm f_deg _ at hc1,
  change ¬(∀ i : ℕ, _ ∈ _) at hc1,
  erw not_forall at hc1,
  obtain ⟨j, hc1⟩ := hc1,
  replace eq1 := eq1.symm,
  have eq2 : graded_algebra.proj 𝒜 ((isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U 0 y) + j)
    (isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 0 y * c) = 0,
  { erw [eq1, linear_map.map_zero], },
  have eq3 : graded_algebra.proj 𝒜 ((isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U 0 y) + j)
    (isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 0 y * c)
    = isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 0 y * graded_algebra.proj 𝒜 j c,
  { apply graded_algebra.proj_hom_mul,
    apply isos.sheaf_component.forward.hartshorne.num_hom,
    intro rid,
    apply hc1,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },
    erw eq3 at eq2,

  use localization.mk ((graded_algebra.proj 𝒜 j c)^m) ⟨f^j, ⟨_, rfl⟩⟩,
  unfold isos.sheaf_component.forward.hartshorne.mk_num,
  erw [mul_one, zero_mul, zero_mul, ←subtype.val_eq_coe, subtype.ext_iff_val,
    show ∀ (x y : degree_zero_part 𝒜 f m f_deg), (x * y).1 = x.1 * y.1, from λ _ _, rfl,
    show (0 : degree_zero_part 𝒜 f m f_deg).1 = 0, from rfl, localization.mk_mul],
  dsimp only,
  convert localization.mk_zero _,
  exact calc isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 0 y
            * isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 0 y ^ m.pred
            * (graded_algebra.proj 𝒜 j) c ^ m
          = isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 0 y
            * isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 0 y ^ m.pred
            * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          : begin
            congr',
            symmetry,
            apply nat.succ_pred_eq_of_pos,
            exact hm
          end
      ... = isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 0 y
            * isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 0 y ^ m.pred
            * ((graded_algebra.proj 𝒜 j) c ^ m.pred * graded_algebra.proj 𝒜 j c)
          : by rw [pow_add, pow_one]
      ... = (isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U 0 y *
              graded_algebra.proj 𝒜 j c)
            * (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 0 y ^ m.pred *
                (graded_algebra.proj 𝒜 j) c ^ m.pred) : by ring
      ... = 0 * (isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U 0 y ^ m.pred *
                (graded_algebra.proj 𝒜 j) c ^ m.pred) : by rw eq2
      ... = 0 : by rw zero_mul,
end

lemma isos.sheaf_component.forward.mk_add
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (x y) :
  isos.sheaf_component.forward.mk 𝒜 f m hm f_deg U (x + y) =
  isos.sheaf_component.forward.mk 𝒜 f m hm f_deg U x +
  isos.sheaf_component.forward.mk 𝒜 f m hm f_deg U y :=
begin
  ext1 z,
  rw pi.add_apply,
  unfold isos.sheaf_component.forward.mk,
  erw [localization.add_mk],

  have eq_xz := isos.sheaf_component.forward.hartshorne.eq_num_div_denom 𝒜 f m hm f_deg U x z,
  have eq_yz := isos.sheaf_component.forward.hartshorne.eq_num_div_denom 𝒜 f m hm f_deg U y z,
  have eq_addz := isos.sheaf_component.forward.hartshorne.eq_num_div_denom 𝒜 f m hm f_deg U (x + y) z,
  erw [isos.sheaf_component.forward.hartshorne_add,
    show ∀ (a b : hartshorne_localisation 𝒜 (((isos.top_component 𝒜 f m hm f_deg).inv) z.val).val),
      (a + b).1 = a.1 + b.1, from λ _ _, rfl,
    eq_xz, eq_yz, localization.add_mk, localization.mk_eq_mk', is_localization.eq] at eq_addz,
  obtain ⟨⟨c, hc⟩, eq_addz⟩ := eq_addz,
  simp only [←subtype.val_eq_coe] at eq_addz,
  erw [show ∀ (a b : (projective_spectrum.as_homogeneous_ideal
    (((isos.top_component 𝒜 f m hm f_deg).inv) z.val).val).val.prime_compl), (a * b).1 = a.1 * b.1,
    from λ _ _, rfl] at eq_addz,
  dsimp only,

  set d_x := isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U x z with dx_eq,
  set n_x := isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U x z with nx_eq,
  set d_y := isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U y z with dy_eq,
  set n_y := isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U y z with ny_eq,
  set d_xy := isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U (x +y) z with dxy_eq,
  set n_xy := isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U (x+y) z with nxy_eq,
  set i_x := isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U x z with ix_eq,
  set i_y := isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U y z with iy_eq,
  set i_xy := isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U (x+y) z with ixy_eq,

  unfold isos.sheaf_component.forward.hartshorne.mk_num,
  unfold isos.sheaf_component.forward.hartshorne.mk_denom,
  simp only [←dx_eq, ←nx_eq, ←dy_eq, ←ny_eq, ←dxy_eq, ←nxy_eq, ←i_x, ←i_y, ←i_xy] at eq_addz ⊢,
  erw [localization.mk_eq_mk', is_localization.eq],

  change c ∉ isos.backward.carrier 𝒜 f m hm f_deg _ at hc,
  change ¬(∀ i : ℕ, _ ∈ _) at hc,
  erw not_forall at hc,
  obtain ⟨j, hc⟩ := hc,

  use localization.mk ((graded_algebra.proj 𝒜 j c)^m) ⟨f^j, ⟨_, rfl⟩⟩,
  erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, ←subtype.val_eq_coe,
    ←subtype.val_eq_coe, ←subtype.val_eq_coe,
    show ∀ (a b : (prime_spectrum.as_ideal z.val).prime_compl), (a * b).1 = a.1 * b.1,
    from λ _ _, rfl],
  dsimp only,
  erw [subtype.ext_iff_val,
    show ∀ (x y : degree_zero_part 𝒜 f m f_deg), (x * y).1 = x.1 * y.1, from λ _ _, rfl,
    show ∀ (x y : degree_zero_part 𝒜 f m f_deg), (x * y).1 = x.1 * y.1, from λ _ _, rfl,
    show ∀ (x y : degree_zero_part 𝒜 f m f_deg), (x * y).1 = x.1 * y.1, from λ _ _, rfl,
    show ∀ (x y : degree_zero_part 𝒜 f m f_deg), (x * y).1 = x.1 * y.1, from λ _ _, rfl,
    show ∀ (x y : degree_zero_part 𝒜 f m f_deg), (x * y).1 = x.1 * y.1, from λ _ _, rfl,
    show ∀ (x y : degree_zero_part 𝒜 f m f_deg), (x + y).1 = x.1 + y.1, from λ _ _, rfl,
    show ∀ (x y : degree_zero_part 𝒜 f m f_deg), (x * y).1 = x.1 * y.1, from λ _ _, rfl,
    show ∀ (x y : degree_zero_part 𝒜 f m f_deg), (x * y).1 = x.1 * y.1, from λ _ _, rfl,
    localization.mk_mul, localization.mk_mul, localization.mk_mul, localization.mk_mul,
    localization.mk_mul, localization.add_mk, localization.mk_mul, localization.mk_mul,
    localization.mk_eq_mk', is_localization.eq],
  use 1,
  simp only [←subtype.val_eq_coe,
    show (1 : submonoid.powers f).1 = 1, from rfl,
    show ∀ (a b : submonoid.powers f), (a * b).1 = a.1 * b.1, from λ _ _, rfl,
    one_mul, mul_one, ←pow_add],

  rw calc (f ^ (i_x + i_y) * (d_y ^ m * (n_x * d_x ^ m.pred))
          + f ^ (i_y + i_x) * (d_x ^ m * (n_y * d_y ^ m.pred)))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * f ^ (i_xy + (i_x + i_y) + j)
        = (f ^ (i_x + i_y) * (d_y ^ m * (n_x * d_x ^ m.pred))
            + f ^ (i_x + i_y) * (d_x ^ m * (n_y * d_y ^ m.pred)))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * f ^ (i_xy + (i_x + i_y) + j)
        : begin
          congr' 4,
          rw add_comm,
        end
    ... = (f ^ (i_x + i_y) * (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred)))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * f ^ (i_xy + (i_x + i_y) + j)
        : begin
          congr' 3,
          rw mul_add,
        end
    ... = (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * (f ^ (i_x + i_y) * f ^ (i_xy + (i_x + i_y) + j)) : by ring
    ... = (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * (f ^ (i_x + i_y + (i_xy + (i_x + i_y) + j)))
        : begin
          congr' 1,
          rw [←pow_add],
        end
    ... = (d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred))
          * d_xy ^ m
          * (graded_algebra.proj 𝒜 j) c ^ m
          * (f ^ (i_x + i_y + (i_y + i_x) + i_xy + j))
        : begin
          congr' 2,
          ring,
        end,
  congr' 1,
  suffices EQ : (d_x * n_y + d_y * n_x) * d_xy * graded_algebra.proj 𝒜 j c = n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c,
  erw calc n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m) * (graded_algebra.proj 𝒜 j) c ^ m
        = n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m) * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
        : begin
          congr',
          symmetry,
          apply nat.succ_pred_eq_of_pos hm,
        end
    ... = n_xy * d_xy ^ m.pred * (d_x ^ (m.pred + 1) * d_y ^ m) * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
        : begin
          congr',
          symmetry,
          apply nat.succ_pred_eq_of_pos hm,
        end
    ... = n_xy * d_xy ^ m.pred * (d_x ^ (m.pred + 1) * d_y ^ (m.pred + 1)) * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
        : begin
          congr',
          symmetry,
          apply nat.succ_pred_eq_of_pos hm,
        end
    ... = n_xy * d_xy ^ m.pred * (d_x ^ m.pred * d_x * (d_y ^ m.pred * d_y))
          * ((graded_algebra.proj 𝒜 j) c ^ m.pred * (graded_algebra.proj 𝒜 j) c)
        : begin
          simp only [pow_add, pow_one],
        end
    ... = (n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c)
          * (d_xy ^ m.pred * d_x ^ m.pred * d_y ^ m.pred * (graded_algebra.proj 𝒜 j c) ^ m.pred)
        : by ring
    ... = ((d_x * n_y + d_y * n_x) * d_xy * (graded_algebra.proj 𝒜 j) c)
          * (d_xy ^ m.pred * d_x ^ m.pred * d_y ^ m.pred * (graded_algebra.proj 𝒜 j c) ^ m.pred)
        : by rw EQ
    ... = (d_x * n_y + d_y * n_x)
          * ((d_xy ^ m.pred * d_xy) * d_x ^ m.pred * d_y ^ m.pred
            * ((graded_algebra.proj 𝒜 j c) ^ m.pred * (graded_algebra.proj 𝒜 j c)))
        : by ring
    ... = (d_x * n_y + d_y * n_x)
          * (d_xy ^ m * d_x ^ m.pred * d_y ^ m.pred
            * (graded_algebra.proj 𝒜 j c) ^ m)
        : begin
          congr';
          conv_rhs { rw [show m = m.pred + 1, from (nat.succ_pred_eq_of_pos hm).symm] };
          rw [pow_add, pow_one],
        end
    ... = (d_x * n_y + d_y * n_x)
          * d_x ^ m.pred * d_y ^ m.pred * d_xy ^ m
          * (graded_algebra.proj 𝒜 j c) ^ m : by ring,
  congr',

  exact calc (d_x * n_y + d_y * n_x) * d_x ^ m.pred * d_y ^ m.pred
        = (d_y ^ m.pred * d_y) * (n_x * d_x ^ m.pred) + (d_x ^ m.pred * d_x) * (n_y * d_y ^ m.pred)
        : by ring
    ... = (d_y ^ m.pred * d_y^1) * (n_x * d_x ^ m.pred) + (d_x ^ m.pred * d_x ^ 1) * (n_y * d_y ^ m.pred)
        : by simp only [pow_one]
    ... = (d_y ^ (m.pred + 1)) * (n_x * d_x ^ m.pred) + (d_x ^ (m.pred + 1)) * (n_y * d_y ^ m.pred)
        : by simp only [pow_add]
    ... = d_y ^ m * (n_x * d_x ^ m.pred) + d_x ^ m * (n_y * d_y ^ m.pred)
        : begin
          congr';
          apply nat.succ_pred_eq_of_pos hm,
        end,

  replace eq_addz := congr_arg (graded_algebra.proj 𝒜 ((i_x + i_y) + i_xy + j)) eq_addz,
  have eq1 : (graded_algebra.proj 𝒜 (i_x + i_y + i_xy + j)) ((d_x * n_y + d_y * n_x) * d_xy * c)
    = (d_x * n_y + d_y * n_x) * d_xy * graded_algebra.proj 𝒜 j c,
  { apply graded_algebra.proj_hom_mul,
    { apply set_like.graded_monoid.mul_mem,
      apply submodule.add_mem _ _ _,
      apply set_like.graded_monoid.mul_mem,
      apply isos.sheaf_component.forward.hartshorne.denom_hom,
      apply isos.sheaf_component.forward.hartshorne.num_hom,
      rw add_comm,
      apply set_like.graded_monoid.mul_mem,
      apply isos.sheaf_component.forward.hartshorne.denom_hom,
      apply isos.sheaf_component.forward.hartshorne.num_hom,
      apply isos.sheaf_component.forward.hartshorne.denom_hom, },
    intro rid,
    apply hc,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },
  rw eq1 at eq_addz,

  have eq2 : (graded_algebra.proj 𝒜 (i_x + i_y + i_xy + j)) (n_xy * (d_x * d_y) * c)
    = n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c,
  { apply graded_algebra.proj_hom_mul,
    { rw show i_x + i_y + i_xy = i_xy + (i_x + i_y), by ring,
      apply set_like.graded_monoid.mul_mem,
      apply isos.sheaf_component.forward.hartshorne.num_hom,
      apply set_like.graded_monoid.mul_mem,
      apply isos.sheaf_component.forward.hartshorne.denom_hom,
      apply isos.sheaf_component.forward.hartshorne.denom_hom, },
    intro rid,
    apply hc,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _, },
  rw eq2 at eq_addz,
  exact eq_addz,
end

lemma isos.sheaf_component.forward.mk_mul
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (x y) :
  isos.sheaf_component.forward.mk 𝒜 f m hm f_deg U (x * y) =
  isos.sheaf_component.forward.mk 𝒜 f m hm f_deg U x *
  isos.sheaf_component.forward.mk 𝒜 f m hm f_deg U y :=
begin
  ext1 z,
  rw pi.mul_apply,
  unfold isos.sheaf_component.forward.mk,
  erw [localization.mk_mul],

  have eq_xz := isos.sheaf_component.forward.hartshorne.eq_num_div_denom 𝒜 f m hm f_deg U x z,
  have eq_yz := isos.sheaf_component.forward.hartshorne.eq_num_div_denom 𝒜 f m hm f_deg U y z,
  have eq_mulz := isos.sheaf_component.forward.hartshorne.eq_num_div_denom 𝒜 f m hm f_deg U (x * y) z,
  erw [isos.sheaf_component.forward.hartshorne_mul,
    show ∀ (a b : hartshorne_localisation 𝒜 (((isos.top_component 𝒜 f m hm f_deg).inv) z.val).val),
      (a * b).1 = a.1 * b.1, from λ _ _, rfl,
    eq_xz, eq_yz, localization.mk_mul, localization.mk_eq_mk', is_localization.eq] at eq_mulz,
  obtain ⟨⟨c, hc⟩, eq_mulz⟩ := eq_mulz,
  simp only [←subtype.val_eq_coe] at eq_mulz,
  erw [show ∀ (a b : (projective_spectrum.as_homogeneous_ideal
    (((isos.top_component 𝒜 f m hm f_deg).inv) z.val).val).val.prime_compl), (a * b).1 = a.1 * b.1,
    from λ _ _, rfl] at eq_mulz,
  dsimp only,

  set d_x := isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U x z with dx_eq,
  set n_x := isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U x z with nx_eq,
  set d_y := isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U y z with dy_eq,
  set n_y := isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U y z with ny_eq,
  set d_xy := isos.sheaf_component.forward.hartshorne.denom 𝒜 f m hm f_deg U (x*y) z with dxy_eq,
  set n_xy := isos.sheaf_component.forward.hartshorne.num 𝒜 f m hm f_deg U (x*y) z with nxy_eq,
  set i_x := isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U x z with ix_eq,
  set i_y := isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U y z with iy_eq,
  set i_xy := isos.sheaf_component.forward.hartshorne.i 𝒜 f m hm f_deg U (x*y) z with ixy_eq,

  unfold isos.sheaf_component.forward.hartshorne.mk_num,
  unfold isos.sheaf_component.forward.hartshorne.mk_denom,
  simp only [←dx_eq, ←nx_eq, ←dy_eq, ←ny_eq, ←dxy_eq, ←nxy_eq, ←i_x, ←i_y, ←i_xy] at eq_mulz ⊢,
  erw [localization.mk_eq_mk', is_localization.eq],

  change c ∉ isos.backward.carrier 𝒜 f m hm f_deg _ at hc,
  change ¬(∀ i : ℕ, _ ∈ _) at hc,
  erw not_forall at hc,
  obtain ⟨j, hc⟩ := hc,

  use localization.mk ((graded_algebra.proj 𝒜 j c)^m) ⟨f^j, ⟨_, rfl⟩⟩,
  erw [←subtype.val_eq_coe, ←subtype.val_eq_coe, ←subtype.val_eq_coe,
    show ∀ (a b : (prime_spectrum.as_ideal z.val).prime_compl), (a * b).1 = a.1 * b.1,
    from λ _ _, rfl, subtype.ext_iff_val],
  simp only [show ∀ (a b : degree_zero_part 𝒜 f m f_deg), (a * b).1 = a.1 * b.1, from λ _ _, rfl],
  rw [localization.mk_mul, localization.mk_mul, localization.mk_mul, localization.mk_mul,
    localization.mk_mul, localization.mk_mul, localization.mk_eq_mk', is_localization.eq],

  use 1,
  simp only [←subtype.val_eq_coe,
    show (1 : submonoid.powers f).1 = 1, from rfl,
    show ∀ (a b : submonoid.powers f), (a * b).1 = a.1 * b.1, from λ _ _, rfl,
    ←pow_add, mul_one],

  suffices EQ : n_x * n_y * d_xy * graded_algebra.proj 𝒜 j c = n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c,

  rw calc n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m)
          * (graded_algebra.proj 𝒜 j) c ^ m
          * f ^ (i_x + i_y + i_xy + j)
        = n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m)
          * (graded_algebra.proj 𝒜 j) c ^ (m.pred + 1)
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          symmetry,
          apply nat.succ_pred_eq_of_pos hm,
        end
    ... = n_xy * d_xy ^ m.pred * (d_x ^ m * d_y ^ m)
          * ((graded_algebra.proj 𝒜 j) c ^ m.pred * (graded_algebra.proj 𝒜 j) c)
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          rw [pow_add, pow_one],
        end
    ... = n_xy * d_xy ^ m.pred * (d_x ^ (m.pred + 1) * d_y ^ (m.pred + 1))
          * ((graded_algebra.proj 𝒜 j) c ^ m.pred * (graded_algebra.proj 𝒜 j) c)
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          all_goals { symmetry, apply nat.succ_pred_eq_of_pos hm, },
        end
    ... = n_xy * d_xy ^ m.pred * ((d_x ^ m.pred * d_x) * (d_y ^ m.pred * d_y))
          * ((graded_algebra.proj 𝒜 j) c ^ m.pred * (graded_algebra.proj 𝒜 j) c)
          * f ^ (i_x + i_y + i_xy + j)
          : begin
            congr';
            rw [pow_add, pow_one],
          end
    ... = (n_xy * (d_x * d_y) * graded_algebra.proj 𝒜 j c) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * (graded_algebra.proj 𝒜 j c)^m.pred)
          * f ^ (i_x + i_y + i_xy + j)
        : by ring
    ... = (n_x * n_y * d_xy * graded_algebra.proj 𝒜 j c) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * (graded_algebra.proj 𝒜 j c)^m.pred)
          * f ^ (i_x + i_y + i_xy + j)
        : by rw EQ
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m.pred * graded_algebra.proj 𝒜 j c))
          * f ^ (i_x + i_y + i_xy + j) : by ring
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m.pred * (graded_algebra.proj 𝒜 j c)^1))
          * f ^ (i_x + i_y + i_xy + j) : by rw pow_one
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^(m.pred + 1)))
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          rw pow_add,
        end
    ... = (n_x * n_y * d_xy) * (d_xy^m.pred * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          exact nat.succ_pred_eq_of_pos hm,
        end
    ... = (n_x * n_y) * ((d_xy^m.pred * d_xy) * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j) : by ring
    ... = (n_x * n_y) * ((d_xy^m.pred * d_xy^1) * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j) : by rw pow_one
    ... = (n_x * n_y) * ((d_xy^(m.pred + 1)) * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          rw pow_add,
        end
    ... = (n_x * n_y) * (d_xy^m * d_x^m.pred * d_y^m.pred * ((graded_algebra.proj 𝒜 j c)^m))
          * f ^ (i_x + i_y + i_xy + j)
        : begin
          congr',
          exact nat.succ_pred_eq_of_pos hm,
        end,
  ring_nf,
  congr' 7,
  ring,

  have INEQ : graded_algebra.proj 𝒜 j c ≠ 0,
  { intro rid,
    apply hc,
    simp only [rid, zero_pow hm, localization.mk_zero],
    exact submodule.zero_mem _,
  },
  replace eq_mulz := congr_arg (graded_algebra.proj 𝒜 (i_x + i_y + i_xy + j)) eq_mulz,
  erw [graded_algebra.proj_hom_mul, graded_algebra.proj_hom_mul] at eq_mulz,
  exact eq_mulz,

  rw show i_x + i_y + i_xy = i_xy + (i_x + i_y), by ring,
  apply set_like.graded_monoid.mul_mem,
  apply isos.sheaf_component.forward.hartshorne.num_hom,
  apply set_like.graded_monoid.mul_mem,
  apply isos.sheaf_component.forward.hartshorne.denom_hom,
  apply isos.sheaf_component.forward.hartshorne.denom_hom,
  exact INEQ,

  apply set_like.graded_monoid.mul_mem,
  apply set_like.graded_monoid.mul_mem,
  apply isos.sheaf_component.forward.hartshorne.num_hom,
  apply isos.sheaf_component.forward.hartshorne.num_hom,
  apply isos.sheaf_component.forward.hartshorne.denom_hom,
  exact INEQ,
end

lemma isos.sheaf_component.forward.mk_is_locally_quotient
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U)) :
  (structure_sheaf.is_locally_fraction
   (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_prelocal_predicate.pred
  (isos.sheaf_component.forward.mk 𝒜 f m hm f_deg U hh) := sorry

def isos.sheaf_component.forward.to_fun
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (U : (opens
    ((Spec↥(degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ) :
  (((isos.top_component 𝒜 f m hm f_deg).hom _*
      ((Proj.to_LocallyRingedSpace 𝒜).restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
        (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.val).obj
     U) → (Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.sheaf.val.obj U := λ hh,
⟨isos.sheaf_component.forward.mk 𝒜 f m hm f_deg U hh,
  isos.sheaf_component.forward.mk_is_locally_quotient 𝒜 f m hm f_deg U hh⟩


def isos.sheaf_component.forward
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
  (isos.top_component 𝒜 f m hm f_deg).hom _*
    (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.sheaf.1 ⟶
  (Spec degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg).to_SheafedSpace.sheaf.1
:=
{ app := λ U,
  { to_fun := isos.sheaf_component.forward.to_fun 𝒜 f m hm f_deg U,
    map_one' := begin
      rw [subtype.ext_iff_val,
        show (1 : ((Spec↥(degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.sheaf.val.obj U)).val = 1,
        from rfl],
      apply isos.sheaf_component.forward.mk_one,
    end,
    map_zero' := begin
      rw [subtype.ext_iff_val,
        show (0 : ((Spec↥(degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.sheaf.val.obj U)).val = 0,
        from rfl],
      dsimp only,
      apply isos.sheaf_component.forward.mk_zero,
    end,
    map_add' := λ x y, begin
      rw [subtype.ext_iff_val],
      dsimp only,
      convert isos.sheaf_component.forward.mk_add 𝒜 f m hm f_deg U x y,
    end,
    map_mul' := λ x y, begin
      rw [subtype.ext_iff_val],
      dsimp only,
      convert isos.sheaf_component.forward.mk_mul 𝒜 f m hm f_deg U x y,
    end },
  naturality' := λ U V subset1, begin
    ext1 z,
    simp only [comp_apply, ring_hom.coe_mk, functor.op_map, presheaf.pushforward_obj_map],
    sorry
  end, }

lemma isos.sheaf_component.backward.data_prop1
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : ((Spec (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.presheaf.obj V))
  (y :
    ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
            ((opens.map (isos.top_component 𝒜 f m hm f_deg).hom).op.obj V)).unop) :
  y.1 ∈ (projective_spectrum.basic_open 𝒜 f).val :=
begin
  obtain ⟨a, ha1, ha2⟩ := y.2,
  erw ←ha2,
  exact a.2,
end

lemma isos.sheaf_component.backward.data_prop2
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : ((Spec (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.presheaf.obj V))
  (y :
    ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
            ((opens.map (isos.top_component 𝒜 f m hm f_deg).hom).op.obj V)).unop) :
  ((isos.top_component 𝒜 f m hm f_deg).hom)
    ⟨y.val, isos.sheaf_component.backward.data_prop1 𝒜 f m hm f_deg V hh y⟩ ∈ unop V :=
begin
  obtain ⟨a, ha1, ha2⟩ := y.2,
  erw set.mem_preimage at ha1,
  convert ha1,
  rw [subtype.ext_iff_val],
  erw ←ha2,
  refl,
end

def isos.sheaf_component.backward.data
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : ((Spec (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.presheaf.obj V))
  (y :
    ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
            ((opens.map (isos.top_component 𝒜 f m hm f_deg).hom).op.obj V)).unop) :
  structure_sheaf.localizations (degree_zero_part 𝒜 f m f_deg)
  ((isos.top_component 𝒜 f m hm f_deg).hom
    ⟨y.1, isos.sheaf_component.backward.data_prop1 𝒜 f m hm f_deg V hh y⟩) :=
hh.1
  ⟨(isos.top_component 𝒜 f m hm f_deg).hom
    ⟨y.1, isos.sheaf_component.backward.data_prop1 𝒜 f m hm f_deg V hh y⟩,
      isos.sheaf_component.backward.data_prop2 𝒜 f m hm f_deg V hh y⟩

lemma isos.sheaf_component.backward.data_exists_rep
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : ((Spec (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.presheaf.obj V))
  (y :
    ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
            ((opens.map (isos.top_component 𝒜 f m hm f_deg).hom).op.obj V)).unop)
  (data : structure_sheaf.localizations (degree_zero_part 𝒜 f m f_deg)
    ((isos.top_component 𝒜 f m hm f_deg).hom
      ⟨y.1, isos.sheaf_component.backward.data_prop1 𝒜 f m hm f_deg V hh y⟩)) :
  ∃ (a : degree_zero_part 𝒜 f m f_deg)
    (b : ((isos.top_component 𝒜 f m hm f_deg).hom
      ⟨y.1, isos.sheaf_component.backward.data_prop1 𝒜 f m hm f_deg V hh y⟩).as_ideal.prime_compl),
    data = localization.mk a b :=
begin
  induction data using localization.induction_on with p,
  obtain ⟨a, b⟩ := p,
  refine ⟨a, b, rfl⟩,
end

def isos.sheaf_component.backward.data_num
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : ((Spec (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.presheaf.obj V))
  (y :
    ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
            ((opens.map (isos.top_component 𝒜 f m hm f_deg).hom).op.obj V)).unop)
  : degree_zero_part 𝒜 f m f_deg :=
classical.some (isos.sheaf_component.backward.data_exists_rep 𝒜 f m hm f_deg V hh y
  (isos.sheaf_component.backward.data 𝒜 f m hm f_deg V hh y))

def isos.sheaf_component.backward.data_denom
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : ((Spec (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.presheaf.obj V))
  (y :
    ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
            ((opens.map (isos.top_component 𝒜 f m hm f_deg).hom).op.obj V)).unop)
  : ((isos.top_component 𝒜 f m hm f_deg).hom
      ⟨y.1, isos.sheaf_component.backward.data_prop1 𝒜 f m hm f_deg V hh y⟩).as_ideal.prime_compl :=
classical.some $ classical.some_spec
  (isos.sheaf_component.backward.data_exists_rep 𝒜 f m hm f_deg V hh y
    (isos.sheaf_component.backward.data 𝒜 f m hm f_deg V hh y))

lemma isos.sheaf_component.backward.data_eq_num_div_denom
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : ((Spec (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.presheaf.obj V))
  (y :
    ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
            ((opens.map (isos.top_component 𝒜 f m hm f_deg).hom).op.obj V)).unop) :
  ((isos.sheaf_component.backward.data 𝒜 f m hm f_deg V hh y)) =
  localization.mk
    (isos.sheaf_component.backward.data_num 𝒜 f m hm f_deg V hh y)
    (isos.sheaf_component.backward.data_denom 𝒜 f m hm f_deg V hh y) :=
classical.some_spec $ classical.some_spec
  (isos.sheaf_component.backward.data_exists_rep 𝒜 f m hm f_deg V hh y
    (isos.sheaf_component.backward.data 𝒜 f m hm f_deg V hh y))

variable {𝒜}
def degree_zero_part.degree
  {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m}
  (x : degree_zero_part 𝒜 f m f_deg) : ℕ :=
classical.some x.2

def degree_zero_part.num
  {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m}
  (x : degree_zero_part 𝒜 f m f_deg) : A :=
classical.some $ classical.some_spec x.2

lemma degree_zero_part.num_mem
  {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m}
  (x : degree_zero_part 𝒜 f m f_deg) :
  degree_zero_part.num x ∈ 𝒜 (m * degree_zero_part.degree x) :=
classical.some $ classical.some_spec $ classical.some_spec x.2

lemma degree_zero_part.eq_num_div
  {f : A} {m : ℕ} {f_deg : f ∈ 𝒜 m}
  (x : degree_zero_part 𝒜 f m f_deg) :
  x.1 = localization.mk (degree_zero_part.num x) ⟨f^(degree_zero_part.degree x), ⟨_, rfl⟩⟩ :=
classical.some_spec $ classical.some_spec $ classical.some_spec x.2

variable (𝒜)

def isos.sheaf_component.backward.hartshorne_num
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : ((Spec (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.presheaf.obj V))
  (y :
    ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
            ((opens.map (isos.top_component 𝒜 f m hm f_deg).hom).op.obj V)).unop) : A :=
((degree_zero_part.num (isos.sheaf_component.backward.data_num 𝒜 f m hm f_deg V hh y)) *
            f^(degree_zero_part.degree (isos.sheaf_component.backward.data_denom 𝒜 f m hm f_deg V hh y).1))

def isos.sheaf_component.backward.hartshorne_denom
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : ((Spec (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.presheaf.obj V))
  (y :
    ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
            ((opens.map (isos.top_component 𝒜 f m hm f_deg).hom).op.obj V)).unop) :
y.1.as_homogeneous_ideal.1.prime_compl :=
⟨(degree_zero_part.num (isos.sheaf_component.backward.data_denom 𝒜 f m hm f_deg V hh y).1)*
  f^(degree_zero_part.degree (isos.sheaf_component.backward.data_num 𝒜 f m hm f_deg V hh y)),
  λ rid, begin
    rcases y.1.is_prime.mem_or_mem rid with H1 | H2,
    { have mem1 := (isos.sheaf_component.backward.data_denom 𝒜 f m hm f_deg V hh y).2,
      have eq1 := degree_zero_part.eq_num_div (isos.sheaf_component.backward.data_denom 𝒜 f m hm f_deg V hh y).1,
      dsimp only at mem1,
      change _ ∉ _ at mem1,
      apply mem1,
      change
        (isos.sheaf_component.backward.data_denom 𝒜 f m hm f_deg V hh y).1 ∈
        ((isos.forward.carrier 𝒜 f m f_deg) ⟨y.1, _⟩),

      change
        (isos.sheaf_component.backward.data_denom 𝒜 f m hm f_deg V hh y).1.1 ∈
        (ideal.span _),
      erw eq1,
      convert ideal.mem_span.smul_mem _ _ _ _ _,
      work_on_goal 3 { refine ⟨degree_zero_part.num (isos.sheaf_component.backward.data_denom 𝒜 f m hm f_deg V hh y).val, H1, rfl⟩, },
      work_on_goal 1 { exact localization.mk 1 ⟨f^(degree_zero_part.degree (isos.sheaf_component.backward.data_denom 𝒜 f m hm f_deg V hh y).1), ⟨_, rfl⟩⟩},
      erw [smul_eq_mul, localization.mk_mul, one_mul, mul_one], },
    { replace H2 := y.1.is_prime.mem_of_pow_mem _ H2,
      obtain ⟨⟨a, ha1⟩, ha2, ha3⟩ := y.2,
      erw projective_spectrum.mem_basic_open at ha1,
      apply ha1,
      convert H2, }
  end⟩

def isos.sheaf_component.backward.hartshorne
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : ((Spec (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.presheaf.obj V))
  (y :
    ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
            ((opens.map (isos.top_component 𝒜 f m hm f_deg).hom).op.obj V)).unop) :
  hartshorne_localisation 𝒜 y.1 :=
⟨localization.mk (isos.sheaf_component.backward.hartshorne_num 𝒜 f m hm f_deg V hh y)
  (isos.sheaf_component.backward.hartshorne_denom 𝒜 f m hm f_deg V hh y),
  ⟨projective_spectrum.structure_sheaf.hl.condition.mk
    (isos.sheaf_component.backward.hartshorne_num 𝒜 f m hm f_deg V hh y)
    (isos.sheaf_component.backward.hartshorne_denom 𝒜 f m hm f_deg V hh y).1
    (isos.sheaf_component.backward.hartshorne_denom 𝒜 f m hm f_deg V hh y).2
    (m * (degree_zero_part.degree (isos.sheaf_component.backward.data_num 𝒜 f m hm f_deg V hh y))
    + m * (degree_zero_part.degree (isos.sheaf_component.backward.data_denom 𝒜 f m hm f_deg V hh y).1))
    begin
      apply set_like.graded_monoid.mul_mem,
      apply degree_zero_part.num_mem,
      rw mul_comm,
      apply set_like.graded_monoid.pow_deg 𝒜 f_deg,
    end begin
      change _ * _ ∈ _,
      conv_lhs { rw mul_comm },
      apply set_like.graded_monoid.mul_mem,
      rw mul_comm,
      apply set_like.graded_monoid.pow_deg 𝒜 f_deg,
      apply degree_zero_part.num_mem,
    end, rfl⟩⟩

def isos.sheaf_component.backward.mk
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : ((Spec (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.presheaf.obj V)) :
  Π (y :
    ((@opens.open_embedding (projective_spectrum.Top 𝒜) (projective_spectrum.basic_open 𝒜 f)).is_open_map.functor.op.obj
            ((opens.map (isos.top_component 𝒜 f m hm f_deg).hom).op.obj V)).unop), hartshorne_localisation 𝒜 y.1 :=
λ y, isos.sheaf_component.backward.hartshorne 𝒜 f m hm f_deg V hh y

lemma isos.sheaf_component.backward.mk_one
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ) :
  isos.sheaf_component.backward.mk 𝒜 f m hm f_deg V 1 = 1 := sorry

lemma isos.sheaf_component.backward.mk_zero
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ) :
  isos.sheaf_component.backward.mk 𝒜 f m hm f_deg V 0 = 0 := sorry

lemma isos.sheaf_component.backward.mk_add
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ) :
  ∀ x y, isos.sheaf_component.backward.mk 𝒜 f m hm f_deg V (x + y) =
    isos.sheaf_component.backward.mk 𝒜 f m hm f_deg V x +
    isos.sheaf_component.backward.mk 𝒜 f m hm f_deg V y := sorry

lemma isos.sheaf_component.backward.mk_mul
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ) :
  ∀ x y, isos.sheaf_component.backward.mk 𝒜 f m hm f_deg V (x * y) =
    isos.sheaf_component.backward.mk 𝒜 f m hm f_deg V x *
    isos.sheaf_component.backward.mk 𝒜 f m hm f_deg V y := sorry

lemma isos.sheaf_component.backward.mk_is_locally_quotient
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m)
  (V : (opens ((Spec (degree_zero_part 𝒜 f m f_deg)).to_SheafedSpace.to_PresheafedSpace.carrier))ᵒᵖ)
  (hh : ((Spec (degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg)).to_SheafedSpace.to_PresheafedSpace.presheaf.obj V)) :
  (is_locally_fraction 𝒜).to_prelocal_predicate.pred (isos.sheaf_component.backward.mk 𝒜 f m hm f_deg V hh) :=
sorry

def isos.sheaf_component.backward
  (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
  (Spec degree_zero_part 𝒜 f m f_deg).to_SheafedSpace.to_PresheafedSpace.presheaf ⟶
  (isos.top_component 𝒜 f m hm f_deg).hom _*
    (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.presheaf :=
{ app := λ V,
    { to_fun := λ hh, ⟨isos.sheaf_component.backward.mk 𝒜 f m hm f_deg V hh,
        isos.sheaf_component.backward.mk_is_locally_quotient 𝒜 f m hm f_deg V hh⟩,
      map_one' := begin
        erw [subtype.ext_iff_val],
        dsimp only,
        convert isos.sheaf_component.backward.mk_one 𝒜 f m hm f_deg V,
      end,
      map_mul' := λ x y, begin
        erw subtype.ext_iff_val,
        dsimp only,
        convert isos.sheaf_component.backward.mk_mul 𝒜 f m hm f_deg V x y,
      end,
      map_zero' := begin
        erw [subtype.ext_iff_val],
        dsimp only,
        convert isos.sheaf_component.backward.mk_zero 𝒜 f m hm f_deg V,
      end,
      map_add' := λ x y, begin
        erw subtype.ext_iff_val,
        dsimp only,
        convert isos.sheaf_component.backward.mk_add 𝒜 f m hm f_deg V x y,
      end },
  naturality' := sorry, }

def isos.sheaf_component (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
  (isos.top_component 𝒜 f m hm f_deg).hom _*
    (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.presheaf ≅
  (Spec degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg).to_SheafedSpace.to_PresheafedSpace.presheaf :=
{ hom := isos.sheaf_component.forward 𝒜 f m hm f_deg,
  inv := isos.sheaf_component.backward 𝒜 f m hm f_deg,
  hom_inv_id' := begin
    ext1,
    ext1 V,
    ext1 y,
    erw [nat_trans.comp_app, nat_trans.id_app, comp_apply, id_apply],
    sorry
  end,
  inv_hom_id' := begin
    ext1, ext1 V, ext1 y,
    erw [nat_trans.comp_app, nat_trans.id_app, comp_apply, id_apply],

    sorry
  end, }

def isos (f : A) [decidable_eq (localization.away f)] (m : ℕ) (hm : 0 < m) (f_deg : f ∈ 𝒜 m) :
  Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f)) ≅ (Spec (degree_zero_part _ f m f_deg)) :=
  LocallyRingedSpace.iso_of_SheafedSpace_iso $ SheafedSpace.iso_of_presheaf_iso _ _ $
  @PresheafedSpace.iso_of_components _ _
    (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace
    (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace
    (isos.top_component _ f m hm f_deg) (isos.sheaf_component _ f m hm f_deg)

def test.choose_element [Π (i : ℕ) (x : 𝒜 i), decidable (x ≠ 0)] (x : pst) :
  Σ' (n : ℕ) (hn : 0 < n) (f : A), f ∈ 𝒜 n ∧ f ∉ x.as_homogeneous_ideal.1 :=
begin
  have := x.2.2,
  erw set.not_subset at this,
  choose f h1 h2 using this,
  erw ←graded_algebra.sum_support_decompose 𝒜 f at h2,
  have : ∃ (n : ℕ) (hn : 0 < n), (graded_algebra.decompose 𝒜 f n : A) ∉ x.as_homogeneous_ideal.1,
  { by_contra rid,
    simp only [not_exists, exists_prop, not_and, not_not, subtype.val_eq_coe] at rid,
    apply h2,
    apply ideal.sum_mem,
    intros c hc,
    by_cases ineq1 : 0 < c,
    { apply rid _ ineq1, },
    { rw not_lt at ineq1,
      replace ineq1 := nat.eq_zero_of_le_zero ineq1,
      rw ineq1,
      dsimp only at h1,
      change f ∈ (irrelavent_ideal 𝒜) at h1,
      rw ←graded_algebra.proj_apply,
      have := irrelavent_ideal.mem 𝒜 f h1,
      erw this,
      exact submodule.zero_mem _, },
    },
  choose n hn1 hn2 using this,
  refine ⟨n, hn1, (graded_algebra.decompose _ f n : A), submodule.coe_mem _, hn2⟩,
end

def Proj.to_Scheme [Π (i : ℕ) (x : 𝒜 i), decidable (x ≠ 0)]
  [Π x, decidable_eq (localization.away (test.choose_element 𝒜 x).snd.snd.fst)] : Scheme :=
{ local_affine := λ x,
  ⟨⟨projective_spectrum.basic_open 𝒜 (test.choose_element 𝒜 x).2.2.1, begin
    rw projective_spectrum.mem_basic_open,
    exact (test.choose_element 𝒜 x).2.2.2.2,
  end⟩,
  ⟨CommRing.of (degree_zero_part 𝒜 (test.choose_element 𝒜 x).2.2.1 (test.choose_element 𝒜 x).1
    (test.choose_element 𝒜 x).2.2.2.1),
    ⟨isos 𝒜 (test.choose_element 𝒜 x).2.2.1 (test.choose_element 𝒜 x).1
      (test.choose_element 𝒜 x).2.1
    (test.choose_element 𝒜 x).2.2.2.1⟩⟩⟩,
  ..Proj }

end algebraic_geometry
