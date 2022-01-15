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
  -- [@graded_algebra ℕ R A (λ (a b : ℕ), classical.prop_decidable (a = b))
  --   (@ordered_add_comm_monoid.to_add_comm_monoid ℕ
  --      (@ordered_cancel_add_comm_monoid.to_ordered_add_comm_monoid ℕ
  --         (@linear_ordered_cancel_add_comm_monoid.to_ordered_cancel_add_comm_monoid ℕ
  --            nat.linear_ordered_cancel_add_comm_monoid)))
  --   (@comm_ring.to_comm_semiring R _inst_1)
  --   (@comm_ring.to_ring A _inst_2)
  --   _inst_3
  --   𝒜]
    [graded_algebra 𝒜]

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

def isos.backward.carrier (f : A) [decidable_eq (localization.away f)] (m : ℕ) (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) : set _ :=
  ite (0 < m) ({a | ∀ (i : ℕ),
    (⟨localization.mk ((graded_algebra.proj 𝒜 i a)^m) ⟨f^i, ⟨_, rfl⟩⟩,
      i, ((graded_algebra.proj 𝒜 i a)^m),
      (set_like.graded_monoid.pow_deg 𝒜 (submodule.coe_mem _) m), rfl⟩ :
      degree_zero_part _ f m f_deg) ∈ q.1}) ({0})

lemma isos.backward.carrier.zero_mem (f : A) [decidable_eq (localization.away f)] (m : ℕ)
  (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) :
  (0 : A) ∈ isos.backward.carrier 𝒜 f m f_deg q :=
begin
  rw isos.backward.carrier,
  split_ifs,
  { intros i,
    simp only [linear_map.map_zero, zero_pow h, localization.mk_zero],
    exact submodule.zero_mem _, },
  { refine set.mem_singleton _, },
end

lemma isos.backward.carrier.add_mem (f : A) [decidable_eq (localization.away f)] (m : ℕ)
  (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1)
  (a b : A)
  (ha : a ∈ isos.backward.carrier 𝒜 f m f_deg q)
  (hb : b ∈ isos.backward.carrier 𝒜 f m f_deg q) :
  a + b ∈ isos.backward.carrier 𝒜 f m f_deg q :=
begin
  rw isos.backward.carrier at ha hb ⊢,
  split_ifs,
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
      split_ifs at ha hb,
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
    { split_ifs at ha,
      split_ifs at hb,
      rw set.mem_singleton_iff at ha hb,
      rw [ha, hb, add_zero, set.mem_singleton_iff], },
end

lemma isos.backward.carrier.smul_mem (f : A) [decidable_eq (localization.away f)] (m : ℕ)
  (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1)
  (c x : A) (hx : x ∈ isos.backward.carrier 𝒜 f m f_deg q) :
  c • x ∈ isos.backward.carrier 𝒜 f m f_deg q :=
begin
  apply set_like.homogeneous_induction 𝒜 c,
  { rw zero_smul,
    apply isos.backward.carrier.zero_mem, },
  { rintros ⟨a, ⟨n, ha⟩⟩,
    rw isos.backward.carrier at hx ⊢,
    split_ifs at hx ⊢,
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


        simp only [smul_eq_mul, eq1, zero_pow h, localization.mk_zero],
        exact submodule.zero_mem _, },

      { -- in this case, the left hand side is zero
        rw not_le at ineq1,
        convert submodule.zero_mem _,
        suffices : graded_algebra.proj 𝒜 i (a • x) = 0,
        erw [this, zero_pow h, localization.mk_zero],

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
    { rw set.mem_singleton_iff at hx,
      erw [hx, smul_zero, set.mem_singleton_iff], }
    },
  { intros a b ha hb,
    erw add_smul,
    apply isos.backward.carrier.add_mem _ f m f_deg q (a • x) (b • x) ha hb, },
end

def isos.backward.carrier.as_ideal (f : A) [decidable_eq (localization.away f)]
  (m : ℕ) (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) :
  ideal A :=
{ carrier := isos.backward.carrier _ f m f_deg q,
  zero_mem' := isos.backward.carrier.zero_mem _ f m f_deg q,
  add_mem' := isos.backward.carrier.add_mem _ f m f_deg q,
  smul_mem' := isos.backward.carrier.smul_mem _ f m f_deg q }

lemma isos.backward.carrier.homogeneous (f : A) [decidable_eq (localization.away f)]
  (m : ℕ) (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) :
  ideal.is_homogeneous 𝒜 (isos.backward.carrier.as_ideal _ f m f_deg q) :=
begin
  intros i a ha,
  rw ←graded_algebra.proj_apply,
  rw isos.backward.carrier.as_ideal at ha ⊢,
  suffices : (graded_algebra.proj _ i a) ∈ isos.backward.carrier _ f m f_deg q,
  exact this,
  change a ∈ isos.backward.carrier _ f m f_deg q at ha,
  rw isos.backward.carrier at ha ⊢,
  split_ifs at ha ⊢,
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
                rw zero_pow h,
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
  { rw set.mem_singleton_iff at ha,
    rw [ha, linear_map.map_zero, set.mem_singleton_iff], },
end

lemma isos.backward.carrier.prime (f : A) [decidable_eq (localization.away f)]
  (m : ℕ) (f_deg : f ∈ 𝒜 m)
  (q : (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1) :
  ideal.is_prime (isos.backward.carrier.as_ideal _ f m f_deg q) :=
begin

  rw [isos.backward.carrier.as_ideal],
end
-- { ne_top' := begin
--     rw ideal.ne_top_iff_one,
--     intro rid,
--     rw isos.backward.carrier.as_ideal at rid,
--     change (1 : A) ∈ isos.backward.carrier _ f m f_deg q at rid,
--     rw isos.backward.carrier at rid,
--     split_ifs at rid with H,
--     { have ne_top1 := q.is_prime.1,
--       rw ideal.ne_top_iff_one at ne_top1,
--       specialize rid 0,
--       have eq1 : graded_algebra.proj 𝒜 0 1 = 1,
--       { rw [graded_algebra.proj_apply, graded_algebra.decompose_of_mem_same],
--         exact set_like.graded_monoid.one_mem, },
--       apply ne_top1,
--       change (1 : degree_zero_part _ f m f_deg) ∈ q.1,
--       convert rid,
--       rw [subtype.ext_iff_val, show (1 : degree_zero_part _ f m f_deg).1 = 1, from rfl],
--       dsimp only,
--       erw [eq1],
--       simp only [pow_zero, one_pow],
--       symmetry,
--       convert localization.mk_one, },
--     { rw set.mem_singleton_iff at rid,
--       sorry },
--   end,
--   mem_or_mem' := λ x y hxy, begin
--     rw [isos.backward.carrier.as_ideal] at hxy,
--     change x * y ∈ isos.backward.carrier _ f m f_deg q at hxy,
--     rw isos.backward.carrier at hxy,
--     split_ifs at hxy,
--     { sorry },
--     { sorry },
--   end }

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
      -- sorry, -- the following works, but it is very slow to compile, so I comment them out,
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

def isos.top_component.forward (f : A) [decidable_eq (localization.away f)]
  (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.1 ⟶
  (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1 :=
{ to_fun := isos.top_component.forward.to_fun 𝒜 f m f_deg,
  continuous_to_fun := begin
    apply is_topological_basis.continuous,
    exact prime_spectrum.is_topological_basis_basic_opens,
    rintros _ ⟨⟨g, hg⟩, rfl⟩,
    induction g using localization.induction_on with data,
    obtain ⟨a, ⟨_, ⟨n, rfl⟩⟩⟩ := data,
    dsimp only,
    -- we want to use `projective_spectrum.basic_open 𝒜 (f) = preimage`
    have : set ((Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.1) :=
    { x | x.1 ∈ projective_spectrum.basic_open 𝒜 f },
    sorry
  end }

lemma isos.top_component.backward (f : A) [decidable_eq (localization.away f)] (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1 ⟶
  (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.1 :=
{ to_fun := λ q, ⟨⟨⟨isos.backward.carrier.as_ideal _ f m f_deg q,
    isos.backward.carrier.homogeneous _ f m f_deg q⟩, sorry, sorry⟩, sorry⟩,
  continuous_to_fun := sorry }

def isos.top_component (f : A) [decidable_eq (localization.away f)] (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace.1 ≅
  (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace.1 := sorry


def isos.sheaf_component (f : A) [decidable_eq (localization.away f)] (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  (isos.top_component 𝒜 f m f_deg).hom _*
    ((Proj.to_LocallyRingedSpace 𝒜).restrict _).to_SheafedSpace.to_PresheafedSpace.presheaf ≅
  (Spec degree_zero_part (λ (m : ℕ), 𝒜 m) f m f_deg).to_SheafedSpace.to_PresheafedSpace.presheaf :=
sorry

def isos (f : A) [decidable_eq (localization.away f)] (m : ℕ) (f_deg : f ∈ 𝒜 m) :
  Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f)) ≅ (Spec (degree_zero_part _ f m f_deg)) :=
  LocallyRingedSpace.iso_of_SheafedSpace_iso $ SheafedSpace.iso_of_presheaf_iso _ _ $
  @PresheafedSpace.iso_of_components _ _
    (Proj .restrict (@opens.open_embedding (projective_spectrum.Top 𝒜)
    (projective_spectrum.basic_open 𝒜 f))).to_SheafedSpace.to_PresheafedSpace
    (Spec (degree_zero_part _ f m f_deg)).to_SheafedSpace.to_PresheafedSpace
    (isos.top_component _ f m f_deg) (isos.sheaf_component _ f m f_deg)

def test.choose_element [Π (i : ℕ) (x : 𝒜 i), decidable (x ≠ 0)] (x : pst) :
  Σ' (n : ℕ) (f : A), f ∈ 𝒜 n ∧ f ∉ x.as_homogeneous_ideal.1 :=
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

def Proj.to_Scheme [Π (i : ℕ) (x : 𝒜 i), decidable (x ≠ 0)]
  [Π x, decidable_eq (localization.away (test.choose_element 𝒜 x).snd.fst)] : Scheme :=
{ local_affine := λ x, ⟨⟨projective_spectrum.basic_open 𝒜 (test.choose_element 𝒜 x).2.1, begin
    rw projective_spectrum.mem_basic_open,
    exact (test.choose_element 𝒜 x).2.2.2,
  end⟩,
  ⟨CommRing.of (degree_zero_part _ (test.choose_element 𝒜 x).2.1 (test.choose_element 𝒜 x).1
    (test.choose_element 𝒜 x).2.2.1), ⟨isos 𝒜 (test.choose_element 𝒜 x).2.1 (test.choose_element 𝒜 x).1
    (test.choose_element 𝒜 x).2.2.1⟩⟩⟩,
  ..Proj }

end algebraic_geometry
