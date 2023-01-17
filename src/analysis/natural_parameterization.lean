import measure_theory.measure.lebesgue
import analysis.calculus.monotone
import data.set.function
import analysis.bounded_variation
import tactic.swap_var

open_locale big_operators nnreal ennreal
open set measure_theory classical

local attribute [instance] prop_decidable

variables {α β : Type*} [linear_order α] [linear_order β]
{E F : Type*} [pseudo_emetric_space E] [pseudo_emetric_space F]

def is_linearly_parameterized_on_by (f : ℝ → E) (s : set ℝ) (l : ℝ) :=
∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), evariation_on f (s ∩ Icc x y) = ennreal.of_real (l * (y - x))

lemma is_linearly_parameterized_on_by_of_subsingleton (f : ℝ → E) {s : set ℝ} (hs : s.subsingleton)
  (l : ℝ) : is_linearly_parameterized_on_by f s l :=
begin
  rintro x hx y hy, cases hs hx hy,
  rw evariation_on.subsingleton f (λ y hy z hz, hs hy.1 hz.1 : (s ∩ Icc x x).subsingleton),
  simp only [sub_self, mul_zero, ennreal.of_real_zero],
end

-- Could do without `hl` but it means we have to check whether `s` is subsingleton
-- and if not deduce that `hl` necessarily holds…
lemma is_linearly_parameterized_on_by.iff_ordered (f : ℝ → E) (s : set ℝ) {l : ℝ} (hl : 0 ≤ l):
  is_linearly_parameterized_on_by f s l ↔
  ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), (x ≤ y) →
    evariation_on f (s ∩ Icc x y) = ennreal.of_real (l * (y - x)) :=
begin
  refine ⟨λ h x xs y ys xy, h xs ys, λ h x xs y ys, _⟩,
  rcases le_total x y with xy|yx,
  { exact h xs ys xy, },
  { rw [evariation_on.subsingleton, ennreal.of_real_of_nonpos],
    { exact mul_nonpos_of_nonneg_of_nonpos hl (sub_nonpos_of_le yx), },
    { rintro z ⟨zs,xz,zy⟩ w ⟨ws,xw,wy⟩,
      cases le_antisymm (zy.trans yx) xz,
      cases le_antisymm (wy.trans yx) xw,
      refl, }, },
end

lemma is_linearly_parameterized_on_by.iff_variation_on_from_to_eq
  (f : ℝ → E) (s : set ℝ) (hf : has_locally_bounded_variation_on f s) {l : ℝ} (hl : 0 ≤ l) :
  is_linearly_parameterized_on_by f s l ↔
  ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), variation_on_from_to f s x y = l * (y - x) :=
begin
  rw is_linearly_parameterized_on_by.iff_ordered f s hl,
  split,
  { rintro h x xs y ys,
    rcases le_total x y with xy|yx,
    { rw [variation_on_from_to_eq_of_le f s xy, h xs ys xy,
          ennreal.to_real_of_real (mul_nonneg hl (sub_nonneg.mpr xy))], },
    { rw [variation_on_from_to_eq_of_ge f s yx, h ys xs yx ,
          ennreal.to_real_of_real  (mul_nonneg hl (sub_nonneg.mpr yx)),
          mul_comm l, mul_comm l, ←neg_mul, neg_sub], }, },
  { rintro h x xs y ys xy,
    rw [←h xs ys, variation_on_from_to_eq_of_le f s xy, ennreal.of_real_to_real (hf x y xs ys)], },
end

def is_naturally_parameterized_on (f : ℝ → E) (s : set ℝ) := is_linearly_parameterized_on_by f s 1

lemma is_linearly_parameterized_on_by_zero_iff (f : ℝ → E) (s : set ℝ) :
  is_linearly_parameterized_on_by f s 0 ↔ ∀ x y ∈ s, edist (f x) (f y) = 0 :=
begin
  dsimp [is_linearly_parameterized_on_by],
  simp only [zero_mul, ennreal.of_real_zero, ←evariation_on.eq_zero_iff],
  split,
  { by_contra',
    obtain ⟨h,hfs⟩ := this,
    simp_rw evariation_on.eq_zero_iff at hfs h,
    push_neg at hfs,
    obtain ⟨x,xs,y,ys,hxy⟩ := hfs,
    rcases le_total x y with xy|yx,
    { exact hxy (h xs ys x ⟨xs,le_rfl,xy⟩ y ⟨ys,xy,le_rfl⟩), },
    { rw edist_comm at hxy,
      exact hxy (h ys xs y ⟨ys,le_rfl,yx⟩ x ⟨xs,yx,le_rfl⟩), }, },
  { rintro h x xs y ys,
    refine le_antisymm _ (zero_le'),
    rw ←h,
    exact evariation_on.mono f (inter_subset_left s (Icc x y)), },
end

lemma is_linearly_parameterized_on_by.ratio {f : ℝ → E} {s t : set ℝ} {φ : ℝ → ℝ}
  (φm : monotone_on φ s) (φst : s.maps_to φ t) (φst' : s.surj_on φ t)
  {l l' : ℝ} (hl : 0 ≤ l) (hl' : 0 < l')
  (hfφ : is_linearly_parameterized_on_by (f ∘ φ) s l)
  (hf : is_linearly_parameterized_on_by f t l')
  ⦃x : ℝ⦄ (xs : x ∈ s) : s.eq_on φ (λ y, (l / l') * (y - x) + (φ x)) :=
begin
  rintro y ys,
  rw [←sub_eq_iff_eq_add, mul_comm, ←mul_div_assoc, eq_div_iff hl'.ne.symm],
  rcases le_total x y with h|h,
  work_on_goal 2
  { swap_var [x y, xs ↔ ys],
    rw [(by rw [←neg_mul, neg_sub] : (x - y) * l = - ((y - x) * l)),
        (by rw [←neg_mul, neg_sub] : (φ x - φ y) * l' = - ((φ y - φ x) * l')), neg_inj], },
  all_goals
  { rw ←ennreal.of_real_eq_of_real_iff (mul_nonneg (sub_nonneg_of_le (φm xs ys h)) hl'.le)
                                       (mul_nonneg (sub_nonneg_of_le h) hl),
    symmetry,
    calc ennreal.of_real ((y - x) * l)
       = ennreal.of_real (l * (y - x)) : by rw mul_comm
    ...= evariation_on (f ∘ φ) (s ∩ Icc x y) : (hfφ xs ys).symm
    ...= evariation_on f (t ∩ Icc (φ x) (φ y)) : by
    begin
      apply evariation_on.comp_eq_of_monotone_on,
      apply φm.mono (inter_subset_left _ _),
      { rintro u ⟨us,ux,uy⟩,
        exact ⟨φst us, φm xs us ux, φm us ys uy⟩, },
      { rintro v ⟨vt,vφx,vφy⟩,
        obtain ⟨u,us,rfl⟩ := φst' vt,
        rcases le_total x u with xu|ux,
        { rcases le_total u y with uy|yu,
          { exact ⟨u,⟨us,⟨xu,uy⟩⟩,rfl⟩, },
          { rw le_antisymm vφy (φm ys us yu),
            exact ⟨y,⟨ys,⟨h,le_rfl⟩⟩,rfl⟩, }, },
        { rw ←le_antisymm vφx (φm us xs ux),
            exact ⟨x,⟨xs,⟨le_rfl,h⟩⟩,rfl⟩, }, },
    end
    ...= ennreal.of_real (l' * (φ y - φ x)) : hf (φst xs) (φst ys)
    ...= ennreal.of_real ((φ y - φ x) * l') : by rw mul_comm, },
end

/--
If both `f` and `f ∘ φ` are naturally parameterized (on `t` and `s` respectively) and `φ`
monotonically maps `s` onto `t`, then `φ` is just a translation (on `s`).
-/
lemma unique_natural_parameterization {f : ℝ → E} {s t : set ℝ} {φ : ℝ → ℝ}
  (φm : monotone_on φ s) (φst : s.maps_to φ t) (φst' : s.surj_on φ t)
  (hfφ : is_naturally_parameterized_on (f ∘ φ) s)
  (hf : is_naturally_parameterized_on f t)
  ⦃x : ℝ⦄ (xs : x ∈ s) : s.eq_on φ (λ y, (y - x) + (φ x)) :=
begin
  dsimp only [is_naturally_parameterized_on] at hf hfφ,
  convert is_linearly_parameterized_on_by.ratio φm φst φst' zero_le_one zero_lt_one hfφ hf xs,
  simp only [div_self, ne.def, one_ne_zero, not_false_iff, one_mul],
end

/--
If both `f` and `f ∘ φ` are naturally parameterized (on `Icc 0 t` and `Icc 0 s` respectively)
and `φ` monotonically maps `Icc 0 s` onto `Icc 0 t`, then `φ` is the indentity on `Icc 0 s`
-/
lemma unique_natural_parameterization' {f : ℝ → E} {s t : ℝ} (hs : s ≥ 0) (ht : t ≥ 0) {φ : ℝ → ℝ}
  (φm : monotone_on φ $ Icc 0 s) (φst : (Icc 0 s).maps_to φ (Icc 0 t)) (φst' : (Icc 0 s).surj_on φ (Icc 0 t))
  (hfφ : is_naturally_parameterized_on (f ∘ φ) (Icc 0 s))
  (hf : is_naturally_parameterized_on f (Icc 0 t)) : (Icc 0 s).eq_on φ id :=
begin
  convert unique_natural_parameterization φm φst φst' hfφ hf ⟨le_rfl,hs⟩,
  have : φ 0 = 0, by
  { sorry, },
  simp only [tsub_zero, this, add_zero],
  refl,
end

noncomputable def natural_parameterization (f : α → E) {s : set α}
  {a : α} (as : a ∈ s) : ℝ → E :=
f ∘ (@function.inv_fun_on _ _ ⟨a⟩ (variation_on_from_to f s a) s)

lemma natural_parameterization_edist_zero {f : α → E} {s : set α}
  (hf : has_locally_bounded_variation_on f s) {a : α} (as : a ∈ s) {b : α} (bs : b ∈ s) :
  edist (f b) (((natural_parameterization f as) ∘ (variation_on_from_to f s a)) b) = 0 :=
begin
  dsimp only [natural_parameterization],
  haveI : nonempty α := ⟨a⟩,
  let c := function.inv_fun_on (variation_on_from_to f s a) s (variation_on_from_to f s a b),
  obtain ⟨cs,hc⟩ := @function.inv_fun_on_pos _ _ _ s
                      (variation_on_from_to f s a) (variation_on_from_to f s a b) ⟨b,bs,rfl⟩,
  rw [variation_on_from_to_eq_right_iff hf as cs bs] at hc,
  rw [edist_comm],
  apply edist_zero_of_variation_on_from_to_eq_zero hf cs bs hc,
end

lemma natural_parameterization_is_naturally_parameterized (f : α → E) {s : set α}
  (hf : has_locally_bounded_variation_on f s) {a : α} (as : a ∈ s) :
  is_naturally_parameterized_on (natural_parameterization f as) (variation_on_from_to f s a '' s) :=
begin
  dsimp only [is_naturally_parameterized_on],
  rw is_linearly_parameterized_on_by.iff_ordered _ _ zero_le_one,
  rintro _ ⟨b,bs,rfl⟩ _ ⟨c,cs,rfl⟩ h,
  rcases le_total c b with cb|bc,
  { rw [one_mul, le_antisymm h (monotone_on_variation_on_from_to hf as cs bs cb), sub_self,
        ennreal.of_real_zero, Icc_self, evariation_on.subsingleton],
    exact λ x hx y hy, hx.2.trans hy.2.symm, },
  { rw [one_mul, sub_eq_add_neg, variation_on_from_to_eq_neg_swap, neg_neg, add_comm,
      variation_on_from_to_add hf bs as cs, ←variation_on_from_to_eq_neg_swap f],
    let φ := variation_on_from_to f s a,
    let φm := monotone_on_variation_on_from_to hf as,
    let φsabc := φ '' s ∩ Icc (φ b) (φ c),
    let sabc := s ∩ (Icc b c),
    have φmapsto : set.maps_to φ sabc φsabc, by
    { rintro x ⟨xs,bx,xc⟩, use [x, ⟨xs, rfl⟩, ⟨φm bs xs bx ,φm xs cs xc⟩], },
    have φsurjon : set.surj_on φ sabc φsabc, by -- needs to be factored out (also used above)
    { rintro _ ⟨⟨d,ds,rfl⟩,⟨φbφd,φdφc⟩⟩,
      rcases le_total b d with bd|db,
      { rcases le_total d c with dc|cd,
        { exact ⟨d,⟨ds,⟨bd,dc⟩⟩,rfl⟩, },
        { rw le_antisymm φdφc (φm cs ds cd),
          exact ⟨c,⟨cs,⟨‹b≤c›,le_rfl⟩⟩,rfl⟩, }, },
      { rw ←le_antisymm φbφd (φm ds bs db),
        exact ⟨b,⟨bs,⟨le_rfl,‹b≤c›⟩⟩,rfl⟩, }, },
    rw ←evariation_on.comp_eq_of_monotone_on (natural_parameterization f as)
      φ (φm.mono (set.inter_subset_left _ _)) φmapsto φsurjon,
    rw @evariation_on.eq_of_edist_zero_on _ _ _ _ _ f,
    { rw [variation_on_from_to_eq_of_le _ _ ‹b≤c›, ennreal.of_real_to_real (hf b c bs cs)], },
    { rintro x ⟨xs,bx,xc⟩,
      rw [edist_comm, natural_parameterization_edist_zero hf as xs], }, },
end
