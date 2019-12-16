/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/

import analysis.normed_space.basic
import data.complex.basic
import data.set.intervals
import tactic.interactive
import tactic.linarith
import linear_algebra.basic
import ring_theory.algebra

/-!
# Convex sets and functions on real vector spaces

In a real normed space, we define the following objects and properties.

* `segment x y` is the closed segment joining `x` and `y`.
* A set `A` is `convex` if for any two points `x y ∈ A` it includes `segment x y`;
* A function `f` is `convex_on` a set `D` if `D` is itself a convex set, and for any two points
  `x y ∈ D` the segment joining `(x, f x)` to `(y, f y)` is (non-strictly) above the graph of `f`;
  equivalently, `convex_on f D` means that the epigraph `{p : α × ℝ | p.1 ∈ D ∧ f p.1 ≤ p.2}`
  is a convex set;
* Center mass of a finite set of points with prescribed weights.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex, and prove Jensen's inequality.
-/

open set
open_locale classical

local notation `I` := (Icc 0 1 : set ℝ)

section vector_space
variables {α : Type*} {β : Type*} {ι : Sort _}
  [add_comm_group α] [vector_space ℝ α] [add_comm_group β] [vector_space ℝ β]
  (A : set α) (B : set α) (x : α)

local attribute [instance] set.pointwise_add set.smul_set

/-- Convexity of sets -/
def convex (A : set α) :=
∀ ⦃x y : α⦄ ⦃a b : ℝ⦄, x ∈ A → y ∈ A → 0 ≤ a → 0 ≤ b → a + b = 1 →
  a • x + b • y ∈ A

variable {A}

/-- Alternative definition of set convexity -/
lemma convex_iff:
  convex A ↔ ∀ {x y : α} {θ : ℝ},
    x ∈ A → y ∈ A → θ ∈ I → θ • x + (1 - θ) • y ∈ A :=
⟨begin
  assume h x y θ hx hy hθ,
  exact (h hx hy hθ.1 (sub_nonneg.2 hθ.2) (add_sub_cancel'_right _ _))
end,
begin
  assume h x y a b hx hy ha hb hab,
  have ha' : a ≤ 1, by linarith,
  have hb' : b = 1 - a, by linarith,
  rw hb',
  exact h hx hy ⟨ha, ha'⟩
end⟩

/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
lemma convex_iff₂:
  convex A ↔ ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • A + b • A ⊆ A :=
iff.intro
  begin
    rintros hA a b ha hb hab w ⟨au, ⟨u, hu, rfl⟩, bv, ⟨v, hv, rfl⟩, rfl⟩,
    exact hA hu hv ha hb hab
  end
  (λ h x y a b hx hy ha hb hab,
    (h ha hb hab) (set.add_mem_pointwise_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩))

/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
lemma convex_iff₃:
  convex A ↔ ∀ {θ : ℝ}, θ ∈ I → θ • A + (1 - θ) • A ⊆ A :=
convex_iff₂.trans $ iff.intro
  (λ h θ hθ, h hθ.1 (sub_nonneg.2 hθ.2) (add_sub_cancel'_right _ _))
  (λ h a b ha hb hab,
    have ha' : a ≤ 1, from calc a ≤ a + b : le_add_of_nonneg_right hb
                           ...    = 1 : hab,
    by { rw [eq_sub_of_add_eq' hab], exact h ⟨ha, ha'⟩ })

/-- Another alternative definition of set convexity -/
lemma convex_iff_div:
  convex A ↔ ∀ {x y : α} {a : ℝ} {b : ℝ},
    x ∈ A → y ∈ A → 0 ≤ a → 0 ≤ b → 0 < a + b → (a/(a+b)) • x + (b/(a+b)) • y ∈ A :=
⟨begin
  assume h x y a b hx hy ha hb hab,
  apply h hx hy,
  have ha', from mul_le_mul_of_nonneg_left ha (le_of_lt (inv_pos hab)),
  rwa [mul_zero, ←div_eq_inv_mul] at ha',
  have hb', from mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos hab)),
  rwa [mul_zero, ←div_eq_inv_mul] at hb',
  rw [←add_div],
  exact div_self (ne_of_lt hab).symm
end,
begin
  assume h x y a b hx hy ha hb hab,
  have h', from h hx hy ha hb,
  rw [hab, div_one, div_one] at h',
  exact h' zero_lt_one
end⟩

/-- Segments in a vector space -/
def segment (x y : α) : set α := {z : α | ∃ l ∈ I, z - x = l•(y-x)}
local notation `[`x `, ` y `]` := segment x y

lemma left_mem_segment (x y : α) : x ∈ [x, y] :=
⟨0, ⟨le_refl _, zero_le_one⟩, by simp only [sub_self, zero_smul]⟩

lemma right_mem_segment (x y : α) : y ∈ [x, y] :=
⟨1, ⟨zero_le_one, le_refl _⟩, by simp only [one_smul]⟩

lemma mem_segment_iff {x y z : α} : z ∈ [x, y] ↔ ∃ l ∈ I, z = x + l•(y - x) :=
exists_congr $ λ l, exists_congr $ λ hl, sub_eq_iff_eq_add'

lemma segment_eq_image_Icc_zero_one {x y : α} :
  segment x y = (λ (t : ℝ), x + t • (y - x)) '' I :=
by { ext z, simp only [mem_segment_iff, mem_image_iff_bex, eq_comm] }

lemma mem_segment_iff' {x y z : α} : z ∈ [x, y] ↔ ∃ l ∈ I, z = ((1:ℝ)-l)•x + l•y :=
mem_segment_iff.trans $ exists_congr $ λ l, exists_congr $ λ hl, eq.congr_right $
  by rw [sub_smul, smul_sub, one_smul, ← add_sub_assoc, sub_add_eq_add_sub]

lemma segment_symm (x y : α) : [x, y] = [y, x] :=
begin
  ext z,
  rw [mem_segment_iff', mem_segment_iff'],
  split,
  all_goals {
    rintro ⟨l, ⟨hl₀, hl₁⟩, h⟩,
    use (1-l),
    split,
    split; linarith,
    rw [h]; simp },
end

lemma segment_eq_image_Icc_zero_one' {x y : α} :
  segment x y = (λ (t : ℝ), t • x + (1 - t) • y) '' I :=
by { rw [segment_symm, segment_eq_image_Icc_zero_one],
  simp only [smul_sub, sub_smul, one_smul],
  simp only [sub_eq_add_neg, add_left_comm] }

lemma segment_eq_Icc {a b : ℝ} (h : a ≤ b) : [a, b] = Icc a b :=
begin
  rw [segment_eq_image_Icc_zero_one],
  show (((+) a) ∘ (λ t, t * (b - a))) '' Icc 0 1 = Icc a b,
  rw [image_comp, image_mul_right_Icc (@zero_le_one ℝ _) (sub_nonneg.2 h), image_add_left_Icc],
  simp
end

lemma segment_eq_Icc' {a b : ℝ} : [a, b] = Icc (min a b) (max a b) :=
by cases le_total a b; [skip, rw segment_symm]; simp [segment_eq_Icc, *]

lemma segment_translate (a : α) {x b c} : x ∈ [b, c] ↔ a + x ∈ [a + b, a + c] :=
exists_congr $ λ l, exists_congr $ λ _, by { simp only [add_sub_add_left_eq_sub] }

lemma segment_translate_preimage (a b c : α) : (λ x, a + x) ⁻¹' [a + b, a + c] = [b, c] :=
set.ext $ λ x, (segment_translate a).symm

lemma segment_translate_image (a b c: α) : (λx, a + x) '' [b, c] = [a + b, a + c] :=
segment_translate_preimage a b c ▸ image_preimage_eq $ add_left_surjective a

/-- Alternative defintion of set convexity using segments -/
lemma convex_segment_iff : convex A ↔ ∀ x y ∈ A, [x, y] ⊆ A :=
begin
  simp only [convex_iff, segment_eq_image_Icc_zero_one', image_subset_iff],
  exact ⟨λ h x y hx hy θ hθ, h hx hy hθ, λ h x y θ hx hy hθ, h x y hx hy hθ⟩
end

/-! ### Examples of convex sets -/

variables {A B}

lemma convex_empty : convex (∅ : set α) :=  by finish

lemma convex_singleton (a : α) : convex ({a} : set α) :=
begin
  intros x y a b hx hy ha hb hab,
  rw [set.eq_of_mem_singleton hx, set.eq_of_mem_singleton hy, ←add_smul, hab],
  simp
end

lemma convex_univ : convex (set.univ : set α) := by finish

lemma convex.inter (hA: convex A) (hB: convex B) : convex (A ∩ B) :=
λ x y a b (hx : x ∈ A ∩ B) (hy : y ∈ A ∩ B) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
  ⟨hA hx.left hy.left ha hb hab, hB hx.right hy.right ha hb hab⟩

lemma convex_sInter {S : set (set α)} (h : ∀ s ∈ S, convex s) : convex (⋂₀ S) :=
assume x y a b hx hy ha hb hab s hs,
h s hs (hx s hs) (hy s hs) ha hb hab

lemma convex_Inter {s: ι → set α} (h: ∀ i : ι, convex (s i)) : convex (⋂ i, s i) :=
(sInter_range s) ▸ convex_sInter $ forall_range_iff.2 h

lemma convex.prod {A : set α} {B : set β} (hA : convex A) (hB : convex B) :
  convex (set.prod A B) :=
begin
  intros x y a b hx hy ha hb hab,
  apply mem_prod.2,
  exact ⟨hA (mem_prod.1 hx).1 (mem_prod.1 hy).1 ha hb hab,
        hB (mem_prod.1 hx).2 (mem_prod.1 hy).2 ha hb hab⟩
end

lemma convex.is_linear_image (hA : convex A) {f : α → β} (hf : is_linear_map ℝ f) :
  convex (f '' A) :=
begin
  rintros _ _ a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ha hb hab,
  exact ⟨a • x + b • y, hA hx hy ha hb hab, by simp only [hf.add,hf.smul]⟩
end

lemma convex.linear_image (hA : convex A) (f : α →ₗ[ℝ] β) : convex (image f A) :=
hA.is_linear_image f.is_linear

lemma convex.is_linear_preimage {A : set β} (hA : convex A) {f : α → β} (hf : is_linear_map ℝ f) :
  convex (preimage f A) :=
begin
  intros x y a b hx hy ha hb hab,
  convert hA hx hy ha hb hab,
  simp [hf.add, hf.smul]
end

lemma convex.linear_preimage {A : set β} (hA : convex A) (f : α →ₗ[ℝ] β) :
  convex (preimage f A) :=
hA.is_linear_preimage f.is_linear

lemma convex.neg (hA : convex A) : convex ((λ z, -z) '' A) :=
hA.is_linear_image is_linear_map.is_linear_map_neg

lemma convex.neg_preimage (hA : convex A) : convex ((λ z, -z) ⁻¹' A) :=
hA.is_linear_preimage is_linear_map.is_linear_map_neg

lemma convex.smul (c : ℝ) (hA : convex A) : convex (c • A) :=
hA.is_linear_image (is_linear_map.is_linear_map_smul c)

lemma convex.smul_preimage (c : ℝ) (hA : convex A) : convex ((λ z, c • z) ⁻¹' A) :=
hA.is_linear_preimage (is_linear_map.is_linear_map_smul c)

lemma convex.add (hA : convex A) (hB : convex B) : convex (A + B) :=
by { rw pointwise_add_eq_image, exact (hA.prod hB).is_linear_image is_linear_map.is_linear_map_add }

lemma convex.sub (hA : convex A) (hB : convex B) :
  convex ((λx : α × α, x.1 - x.2) '' (set.prod A B)) :=
(hA.prod hB).is_linear_image is_linear_map.is_linear_map_sub

lemma convex.translate (hA : convex A) (z : α) : convex ((λx, z + x) '' A) :=
begin
  convert (convex_singleton z).add hA,
  ext x,
  simp [set.mem_image, mem_pointwise_add, eq_comm]
end

lemma convex.affinity (hA : convex A) (z : α) (c : ℝ) : convex ((λx, z + c • x) '' A) :=
begin
  convert (hA.smul c).translate z using 1,
  erw [← image_comp]
end

lemma convex_real_iff {A : set ℝ} :
  convex A ↔ ∀ {x y}, x ∈ A → y ∈ A → Icc x y ⊆ A :=
begin
  simp only [convex_segment_iff, segment_eq_Icc'],
  split; intros h x y hx hy,
  { cases le_or_lt x y with hxy hxy,
    { simpa [hxy] using h x y hx hy },
    { simp [hxy] } },
  { apply h; cases le_total x y; simp [*] }
end

lemma convex_Iio (r : ℝ) : convex (Iio r) :=
convex_real_iff.2 $ λ x y hx hy z hz, lt_of_le_of_lt hz.2 hy

lemma convex_Ioi (r : ℝ) : convex (Ioi r) :=
convex_real_iff.2 $ λ x y hx hy z hz, lt_of_lt_of_le hx hz.1

lemma convex_Iic (r : ℝ) : convex (Iic r) :=
convex_real_iff.2 $ λ x y hx hy z hz, le_trans hz.2 hy

lemma convex_Ici (r : ℝ) : convex (Ici r) :=
convex_real_iff.2 $ λ x y hx hy z hz, le_trans hx hz.1

lemma convex_Ioo (r : ℝ) (s : ℝ) : convex (Ioo r s) :=
(convex_Ioi _).inter (convex_Iio _)

lemma convex_Ico (r : ℝ) (s : ℝ) : convex (Ico r s) :=
(convex_Ici _).inter (convex_Iio _)

lemma convex_Ioc (r : ℝ) (s : ℝ) : convex (Ioc r s) :=
(convex_Ioi _).inter (convex_Iic _)

lemma convex_Icc (r : ℝ) (s : ℝ) : convex (Icc r s) :=
(convex_Ici _).inter (convex_Iic _)

lemma convex_segment (a b : α) : convex [a, b] :=
begin
  have : (λ (t : ℝ), a + t • (b - a)) = (λz : α, a + z) ∘ (λt:ℝ, t • (b - a)) := rfl,
  rw [segment_eq_image_Icc_zero_one, this, image_comp],
  refine ((convex_Icc _ _).is_linear_image _).translate _,
  exact is_linear_map.is_linear_map_smul' _
end

lemma convex_halfspace_lt {f : α → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | f w < r} :=
(convex_Iio r).is_linear_preimage h

lemma convex_halfspace_le {f : α → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | f w ≤ r} :=
(convex_Iic r).is_linear_preimage h

lemma convex_halfspace_gt {f : α → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | r < f w} :=
(convex_Ioi r).is_linear_preimage h

lemma convex_halfspace_ge {f : α → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | r ≤ f w} :=
(convex_Ici r).is_linear_preimage h

lemma convex_hyperplane {f : α → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | f w = r} :=
begin
  show convex (f ⁻¹' {p | p = r}),
  rw set_of_eq_eq_singleton,
  exact (convex_singleton r).is_linear_preimage h
end

lemma convex_halfspace_re_lt (r : ℝ) : convex {c : ℂ | c.re < r} :=
convex_halfspace_lt (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_le (r : ℝ) : convex {c : ℂ | c.re ≤ r} :=
convex_halfspace_le (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_gt (r : ℝ) : convex {c : ℂ | r < c.re } :=
convex_halfspace_gt (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_lge (r : ℝ) : convex {c : ℂ | r ≤ c.re} :=
convex_halfspace_ge (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_im_lt (r : ℝ) : convex {c : ℂ | c.im < r} :=
convex_halfspace_lt (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_le (r : ℝ) : convex {c : ℂ | c.im ≤ r} :=
convex_halfspace_le (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_gt (r : ℝ) : convex {c : ℂ | r < c.im } :=
convex_halfspace_gt (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_lge (r : ℝ) : convex {c : ℂ | r ≤ c.im} :=
convex_halfspace_ge (is_linear_map.mk complex.add_im complex.smul_im) _

section submodule

open submodule

lemma submodule.convex (K : submodule ℝ α) : convex (↑K : set α) :=
by { repeat {intro}, refine add_mem _ (smul_mem _ _ _) (smul_mem _ _ _); assumption }

lemma subspace.convex (K : subspace ℝ α) : convex (↑K : set α) := K.convex

end submodule

variables (D: set α) (D': set α) (f : α → ℝ) (g : α → ℝ)

/-- Convexity of functions -/
def convex_on (f : α → ℝ) : Prop :=
  convex D ∧
  ∀ {x y : α} {a b : ℝ}, x ∈ D → y ∈ D → 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a * f x + b * f y

variables {D D' f g}

lemma convex_on_iff :
  convex_on D f ↔ convex D ∧ ∀ {x y : α} {θ : ℝ},
    x ∈ D → y ∈ D → 0 ≤ θ → θ ≤ 1 → f (θ • x + (1 - θ) • y) ≤ θ * f x + (1 - θ) * f y :=
and_congr iff.rfl
⟨begin
  intros h x y θ hx hy hθ₁ hθ₂,
  have hθ₂: 0 ≤ 1 - θ, by linarith,
  exact (h hx hy hθ₁ hθ₂ (by linarith))
end,
begin
  intros h x y a b hx hy ha hb hab,
  have ha': a ≤ 1, by linarith,
  have hb': b = 1 - a, by linarith,
  rw hb',
  exact (h hx hy ha ha')
end⟩

lemma convex_on_iff_div:
  convex_on D f ↔ convex D ∧ ∀ {x y : α} {a : ℝ} {b : ℝ},
    x ∈ D → y ∈ D → 0 ≤ a → 0 ≤ b → 0 < a + b →
    f ((a/(a+b)) • x + (b/(a+b)) • y) ≤ (a/(a+b)) * f x + (b/(a+b)) * f y :=
and_congr iff.rfl
⟨begin
  intros h x y a b hx hy ha hb hab,
  apply h hx hy,
  have ha', from mul_le_mul_of_nonneg_left ha (le_of_lt (inv_pos hab)),
  rwa [mul_zero, ←div_eq_inv_mul] at ha',
  have hb', from mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos hab)),
  rwa [mul_zero, ←div_eq_inv_mul] at hb',
  rw [←add_div],
  exact div_self (ne_of_lt hab).symm
end,
begin
  intros h x y a b hx hy ha hb hab,
  simpa [hab, zero_lt_one] using h hx hy ha hb,
end⟩

lemma convex_on_linorder [linear_order α] {f : α → ℝ} : convex_on D f ↔
  convex D ∧ ∀ {x y : α} {a b : ℝ}, x ∈ D → y ∈ D → x < y → 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a * f x + b * f y :=
begin
  refine and_congr iff.rfl ⟨_, _⟩; intros h x y a b hx hy,
  { intro hxy, exact h hx hy },
  { intros ha hb hab,
    wlog hxy : x<=y using [x y a b, y x b a],
    exact le_total _ _,
    apply or.elim (lt_or_eq_of_le hxy),
    { intros hxy, exact h hx hy hxy ha hb hab },
    { intros hxy, rw [hxy, ←add_smul, hab, one_smul, ←add_mul,hab,one_mul] } }
end

lemma convex_on.subset (h_convex_on : convex_on D f) (h_subset : A ⊆ D) (h_convex : convex A) :
  convex_on A f :=
begin
  apply and.intro h_convex,
  intros x y a b hx hy,
  exact h_convex_on.2 (h_subset hx) (h_subset hy),
end

lemma convex_on.add (hf : convex_on D f) (hg : convex_on D g) : convex_on D (λx, f x + g x) :=
begin
  apply and.intro hf.1,
  intros x y a b hx hy ha hb hab,
  calc
    f (a • x + b • y) + g (a • x + b • y) ≤ (a * f x + b * f y) + (a * g x + b * g y)
      : add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    ... = a * f x + a * g x + b * f y + b * g y : by linarith
    ... = a * (f x + g x) + b * (f y + g y) : by simp [mul_add]
end

lemma convex_on.smul {c : ℝ} (hc : 0 ≤ c) (hf : convex_on D f) : convex_on D (λx, c * f x) :=
begin
  apply and.intro hf.1,
  intros x y a b hx hy ha hb hab,
  calc
    c * f (a • x + b • y) ≤ c * (a * f x + b * f y)
      : mul_le_mul_of_nonneg_left (hf.2 hx hy ha hb hab) hc
    ... = a * (c * f x) + b * (c * f y) : by rw mul_add; ac_refl
end

lemma convex_on.le_on_interval {x y : α} {a b : ℝ}
  (hf : convex_on D f) (hx : x ∈ D) (hy : y ∈ D) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  f (a • x + b • y) ≤ max (f x) (f y) :=
calc
  f (a • x + b • y) ≤ a * f x + b * f y : hf.2 hx hy ha hb hab
  ... ≤ a * max (f x) (f y) + b * max (f x) (f y) :
    add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha) (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
  ... ≤ max (f x) (f y) : by rw [←add_mul, hab, one_mul]

lemma convex_on.convex_le (hf : convex_on D f) (r : ℝ) : convex {x ∈ D | f x ≤ r} :=
begin
  intros x y a b hx hy ha hb hab,
  simp at *,
  apply and.intro,
  { exact hf.1 hx.1 hy.1 ha hb hab },
  { apply le_trans (hf.le_on_interval hx.1 hy.1 ha hb hab),
    exact max_le hx.2 hy.2 }
end

lemma convex_on.convex_lt (hf : convex_on D f) (r : ℝ) : convex {x ∈ D | f x < r} :=
begin
  intros x y a b hx hy ha hb hab,
  simp at *,
  apply and.intro,
  { exact hf.1 hx.1 hy.1 ha hb hab },
  { apply lt_of_le_of_lt (hf.le_on_interval hx.1 hy.1 ha hb hab),
    exact max_lt hx.2 hy.2 }
end

lemma convex_on.convex_epigraph (hf : convex_on D f) :
  convex {p : α × ℝ | p.1 ∈ D ∧ f p.1 ≤ p.2} :=
begin
  rintros ⟨x, r⟩ ⟨y, t⟩ a b ⟨hx, hr⟩ ⟨hy, ht⟩ ha hb hab,
  refine ⟨hf.1 hx hy ha hb hab, _⟩,
  calc f (a • x + b • y) ≤ a * f x + b * f y : hf.2 hx hy ha hb hab
  ... ≤ a * r + b * t : add_le_add (mul_le_mul_of_nonneg_left hr ha)
    (mul_le_mul_of_nonneg_left ht hb)
end

lemma convex_on_iff_convex_epigraph : convex_on D f ↔ convex {p : α × ℝ | p.1 ∈ D ∧ f p.1 ≤ p.2} :=
begin
  refine ⟨convex_on.convex_epigraph, λ h, ⟨_, _⟩⟩,
  { assume x y a b hx hy ha hb hab,
    exact (@h (x, f x) (y, f y) a b ⟨hx, le_refl _⟩ ⟨hy, le_refl _⟩ ha hb hab).1 },
  { assume x y a b hx hy ha hb hab,
    exact (@h (x, f x) (y, f y) a b ⟨hx, le_refl _⟩ ⟨hy, le_refl _⟩ ha hb hab).2 }
end

section center_mass

variables {A} (hA : convex A) {γ : Type*} (a b : γ) (s : finset γ) (w : γ → ℝ) (z : γ → α)

/-- Center mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
noncomputable def finset.center_mass : α :=
(s.sum w)⁻¹ • (s.sum (λ i, w i • z i))

open finset (hiding singleton)

lemma finset.center_mass_empty : (∅ : finset γ).center_mass w z = 0 :=
by simp only [center_mass, sum_empty, smul_zero]

lemma finset.center_mass_insert (ha : a ∉ s) (hw : s.sum w ≠ 0) :
  (insert a s).center_mass w z = (w a / (w a + s.sum w)) • z a +
    (s.sum w / (w a + s.sum w)) • s.center_mass w z :=
begin
  simp only [center_mass, sum_insert ha, smul_add, (mul_smul _ _ _).symm],
  congr' 2,
  { apply mul_comm },
  { rw [div_mul_eq_mul_div, mul_inv_cancel hw, one_div_eq_inv] }
end

lemma finset.center_mass_singleton (hw : w a ≠ 0) : (finset.singleton a).center_mass w z = z a :=
by rw [center_mass, sum_singleton, sum_singleton, ← mul_smul, inv_mul_cancel hw, one_smul]

lemma finset.center_mass_pair (hne : a ≠ b) :
  ({a, b} : finset γ).center_mass w z = (w a / (w a + w b)) • z a + (w b / (w a + w b)) • z b :=
by simp only [center_mass, sum_pair hne, smul_add, (mul_smul _ _ _).symm,
  mul_comm (w a + w b)⁻¹, div_eq_mul_inv]

include hA

/-- Center mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
lemma convex.center_mass_mem :
  (∀ i ∈ s, 0 ≤ w i) → (0 < s.sum w) → (∀ i ∈ s, z i ∈ A) → s.center_mass w z ∈ A :=
begin
  refine finset.induction (by simp [lt_irrefl]) (λ a s ha hs h₀ hpos hmem, _) s,
  have za : z a ∈ A, from hmem _ (mem_insert_self _ _),
  have hs₀ : ∀ i ∈ s, 0 ≤ w i,
    from λ i hi, h₀ i $ mem_insert_of_mem hi,
  rw [sum_insert ha] at hpos,
  by_cases hsum_s : s.sum w = 0,
  { have ws : ∀ i ∈ s, w i = 0,
      from (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_s,
    have wz : s.sum (λ i, w i • z i) = 0,
      from sum_eq_zero (λ i hi, by simp [ws i hi]),
    simp only [center_mass, sum_insert ha, wz, hsum_s, add_zero],
    simp only [hsum_s, add_zero] at hpos,
    rw [← mul_smul, inv_mul_cancel (ne_of_gt hpos), one_smul],
    exact za },
  { rw [finset.center_mass_insert _ _ _ _ ha hsum_s],
    refine convex_iff_div.1 hA za (hs hs₀ _ _) _ (sum_nonneg hs₀) hpos,
    { exact lt_of_le_of_ne (sum_nonneg hs₀) (ne.symm hsum_s) },
    { intros i hi, exact hmem i (mem_insert_of_mem hi) },
    { exact h₀ _ (mem_insert_self _ _) } }
end

lemma convex.sum_mem (h₀ : ∀ i ∈ s, 0 ≤ w i) (h₁ : s.sum w = 1) (hz : ∀ i ∈ s, z i ∈ A) :
  s.sum (λ i, w i • z i) ∈ A :=
by simpa only [h₁, center_mass, inv_one, one_smul] using
  hA.center_mass_mem s w z h₀ (h₁.symm ▸ zero_lt_one) hz

omit hA

lemma convex_iff_sum_mem :
  convex A ↔
    (∀ (s : finset α) (as : α → ℝ),
      (∀ i ∈ s, 0 ≤ as i) → s.sum as = 1 → (∀ x ∈ s, x ∈ A) → s.sum (λx, as x • x) ∈ A ) :=
begin
  refine ⟨λ hA s as h_sum has hs, hA.sum_mem s _ id h_sum has hs, _⟩,
  intros h x y a b hx hy ha hb hab,
  by_cases h_cases: x = y,
  { rw [h_cases, ←add_smul, hab, one_smul], exact hy },
  { convert h {x, y} (λ z, if z = y then b else a) _ _ _,
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl] },
    { simp_intros i hi,
      cases hi; subst i; simp [ha, hb, if_neg h_cases] },
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl, hab] },
    { simp_intros i hi,
      cases hi; subst i; simp [hx, hy, if_neg h_cases] } }
end

/-- Jensen's inequality, `finset.center_mass` version. -/
lemma convex_on.map_center_mass_le (hf : convex_on D f) (h₀ : ∀ i ∈ s, 0 ≤ w i) (hpos : 0 < s.sum w)
  (hmem : ∀ i ∈ s, z i ∈ D) : f (s.center_mass w z) ≤ s.center_mass w (f ∘ z) :=
begin
  have hmem' : ∀ i ∈ s, (z i, (f ∘ z) i) ∈ {p : α × ℝ | p.1 ∈ D ∧ f p.1 ≤ p.2},
    from λ i hi, ⟨hmem i hi, le_refl _⟩,
  convert (hf.convex_epigraph.center_mass_mem s w (λ i, (z i, (f ∘ z) i)) h₀ hpos hmem').2;
    simp only [center_mass, function.comp, prod.smul_fst, prod.fst_sum, prod.smul_snd, prod.snd_sum]
end

/-- Jensen's inequality, `finset.sum` version. -/
lemma convex_on.map_sum_le (hf : convex_on D f) (h₀ : ∀ i ∈ s, 0 ≤ w i) (h₁ : s.sum w = 1)
  (hmem : ∀ i ∈ s, z i ∈ D) : f (s.sum (λ i, w i • z i)) ≤ s.sum (λ i, w i * (f (z i))) :=
by simpa only [center_mass, h₁, inv_one, one_smul]
  using hf.map_center_mass_le s w z h₀ (h₁.symm ▸ zero_lt_one) hmem

end center_mass

end vector_space

section topological_vector_space

variables {α : Type*} [add_comm_group α] [vector_space ℝ α]
[topological_space α] [topological_add_group α] [topological_vector_space ℝ α]

local attribute [instance] set.pointwise_add set.smul_set

open set

/-- In a topological vector space, the interior of a convex set is convex. -/
lemma convex.interior {A : set α} (hA : convex A) : convex (interior A) :=
convex_iff₂.mpr $ λ a b ha hb hab,
  have h : is_open (a • interior A + b • interior A), from
  or.elim (classical.em (a = 0))
  (λ heq,
    have hne : b ≠ 0, from by { rw [heq, zero_add] at hab, rw hab, exact one_ne_zero },
    is_open_pointwise_add_left ((is_open_map_smul_of_ne_zero hne _) is_open_interior))
  (λ hne,
    is_open_pointwise_add_right ((is_open_map_smul_of_ne_zero hne _) is_open_interior)),
  (subset_interior_iff_subset_of_open h).mpr $ subset.trans
    (by { apply pointwise_add_subset_add; exact image_subset _ interior_subset })
    (convex_iff₂.mp hA ha hb hab)

/-- In a topological vector space, the closure of a convex set is convex. -/
lemma convex.closure {A : set α} (hA : convex A) : convex (closure A) :=
λ x y a b hx hy ha hb hab,
let f : α → α → α := λ x' y', a • x' + b • y' in
have hf : continuous ((λ p : α × α, p.fst + p.snd) ∘ (λ p : α × α, (a • p.fst, b • p.snd))), from
  continuous.comp continuous_add (continuous.prod_mk
    (continuous_smul continuous_const continuous_fst)
    (continuous_smul continuous_const continuous_snd)),
show f x y ∈ closure A, from
  mem_closure_of_continuous2 hf hx hy (λ x' hx' y' hy', subset_closure
  (hA hx' hy' ha hb hab))

end topological_vector_space

section normed_space
variables {α : Type*} [normed_group α] [normed_space ℝ α]

lemma convex_on_dist  (z : α) (D : set α) (hD : convex D) :
  convex_on D (λz', dist z' z) :=
begin
  apply and.intro hD,
  intros x y a b hx hy ha hb hab,
  calc
    dist (a • x + b • y) z = ∥ (a • x + b • y) - (a + b) • z ∥ :
      by rw [hab, one_smul, normed_group.dist_eq]
    ... = ∥a • (x - z) + b • (y - z)∥ :
      by rw [add_smul, smul_sub, smul_sub]; simp
    ... ≤ ∥a • (x - z)∥ + ∥b • (y - z)∥ :
      norm_add_le (a • (x - z)) (b • (y - z))
    ... = a * dist x z + b * dist y z :
      by simp [norm_smul, normed_group.dist_eq, real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
end

lemma convex_ball (a : α) (r : ℝ) : convex (metric.ball a r) :=
by simpa only [metric.ball, sep_univ] using (convex_on_dist a _ convex_univ).convex_lt r

lemma convex_closed_ball (a : α) (r : ℝ) : convex (metric.closed_ball a r) :=
by simpa only [metric.closed_ball, sep_univ] using (convex_on_dist a _ convex_univ).convex_le r

end normed_space
