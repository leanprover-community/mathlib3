import analysis.real
import linear_algebra.prod_module
import algebra.pi_instances
import analysis.metric_space_fintype_pi

noncomputable theory
open filter
local notation f `→_{`:50 a `}`:0 b := tendsto f (nhds a) (nhds b)

class normed_group (α : Type*) extends add_comm_group α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))


def norm {G : Type*} [normed_group G] : G → ℝ := normed_group.norm
notation `∥`:1024 e:1 `∥`:1 := norm e

section normed_group
variables {G : Type*} [normed_group G] {H : Type*} [normed_group H]


lemma norm_dist' { g h : G} : dist g h = ∥g - h∥ :=
normed_group.dist_eq _ _

@[simp]
lemma norm_dist { g : G} : dist g 0 = ∥g∥ :=
by { rw[norm_dist'], simp }

lemma norm_triangle (g h : G) : ∥g + h∥ ≤ ∥g∥ + ∥h∥ :=
calc ∥g + h∥ = ∥g - (-h)∥             : by simp
         ... = dist g (-h)            : by simp[norm_dist']
         ... ≤ dist g 0 + dist 0 (-h) : by apply dist_triangle
         ... = ∥g∥ + ∥h∥               : by simp[norm_dist']

@[simp]
lemma norm_nonneg {g : G} : 0 ≤ ∥g∥ :=
by { rw[←norm_dist], exact dist_nonneg }

lemma norm_zero_iff_zero {g : G} : ∥g∥ = 0 ↔ g = 0 :=
by { rw[←norm_dist], exact dist_eq_zero }

@[simp]
lemma zero_norm_zero : ∥(0:G)∥ = 0 :=
norm_zero_iff_zero.2 (by simp)

lemma norm_pos_iff {g : G} : ∥ g ∥  > 0 ↔ g ≠ 0 :=
begin
  split ; intro h ; rw[←norm_dist] at *,
  { exact dist_pos.1 h },
  { exact dist_pos.2 h }
end

lemma norm_le_zero_iff {g : G} : ∥g∥ ≤ 0 ↔ g = 0 :=
by { rw[←norm_dist], exact dist_le_zero }


@[simp]
lemma norm_neg (g : G) : ∥-g∥ = ∥g∥ :=
calc ∥-g∥ = ∥0 - g∥ : by simp
      ... = dist 0 g : norm_dist'.symm
      ... = dist g 0 : dist_comm _ _
      ... = ∥g - 0∥ : norm_dist'
      ... = ∥g∥ : by simp

lemma norm_triangle' (g h : G) : abs(∥g∥ - ∥h∥) ≤ ∥g - h∥ :=
begin
  have ng := calc ∥g∥ = ∥g - h + h∥ : by simp
  ... ≤ ∥g-h∥ + ∥h∥ : norm_triangle _ _,
  replace ng := sub_right_le_of_le_add ng,
  have nh := calc ∥h∥ = ∥h - g + g∥ : by simp
  ... ≤ ∥h - g∥ + ∥g∥ : norm_triangle _ _
  ... = ∥-(g - h)∥ + ∥g∥ : by simp
  ... = ∥g - h∥ + ∥g∥ : by { rw [norm_neg (g-h)] },
  replace nh := sub_right_le_of_le_add nh,
  replace nh : -(∥g∥ - ∥h∥) ≤ ∥g - h∥ := by simpa using nh,
  replace nh : -∥g - h∥ ≤ ∥g∥ - ∥h∥ := by simpa using neg_le_neg nh,
  exact abs_le.2 ⟨nh, ng⟩
end

instance prod.normed_group {F : Type*} [normed_group F] : normed_group (G × F) :=
{ norm := λ x, max ∥x.1∥ ∥x.2∥,
  dist_eq := assume x y, by { simp, repeat {rw norm_dist'}, simp } }


lemma norm_proj1_le (x : G × H) : ∥x.1∥ ≤ ∥x∥ :=
begin  have : ∥x∥ = max  (∥x.fst∥) ( ∥x.snd∥) := rfl, rw this, simp[le_max_left], end

lemma norm_proj2_le (x : G × H) : ∥x.2∥ ≤ ∥x∥ :=
begin  have : ∥x∥ = max  (∥x.fst∥) ( ∥x.snd∥) := rfl, rw this, simp[le_max_right], end

instance fintype.normed_group {ι : Type*} {α : ι → Type*} [fintype ι] [∀i, normed_group (α i)] :
  normed_group (Πb, α b) :=
{ norm := λf, finset.maxi finset.univ (λ b, ∥f b∥),
  dist_eq := assume x y, by finish [norm_dist'] }

lemma tendsto_iff_norm_tendsto_zero {α : Type*}{f : α → H} {a : filter α} {b : H} : tendsto f a (nhds b) ↔ tendsto (λ e, ∥ f e - b ∥) a (nhds 0) :=
by rw tendsto_iff_dist_tendsto_zero ; simp only [norm_dist'.symm]

lemma lim_norm (x: G) : ((λ g, ∥g-x∥) : G → ℝ) →_{x} 0 :=
  tendsto_iff_norm_tendsto_zero.1 (continuous_iff_tendsto.1 continuous_id x)

lemma lim_norm_zero  : ((λ g, ∥g∥) : G → ℝ) →_{0} 0 :=
by simpa using lim_norm (0:G)

lemma squeeze_zero {T : Type*} {f g : T → ℝ} {t₀ : filter T} :
(∀ t : T, 0 ≤ f t) → (∀ t : T, f t ≤ g t) → tendsto g t₀ (nhds 0) → tendsto f t₀ (nhds 0) :=
begin
  intros _ _ g0,
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_const_nhds) g0;
  simp [*]; exact filter.univ_mem_sets
end

lemma norm_continuous {G : Type*} [normed_group G]: continuous ((λ g, ∥g∥) : G → ℝ) :=
begin
  rw continuous_iff_tendsto,
  intro x,
  rw tendsto_iff_dist_tendsto_zero,
  exact squeeze_zero (λ t, abs_nonneg _) (λ t, norm_triangle' _ _) (lim_norm x)
end


instance normed_top_monoid : topological_add_monoid G :=
⟨continuous_iff_tendsto.2 $ λ ⟨x₁, x₂⟩,
  tendsto_iff_norm_tendsto_zero.2 begin
  refine squeeze_zero (by simp) _ (by simpa using
    tendsto_add (lim_norm (x₁, x₂)) (lim_norm (x₁, x₂))),
  exact λ ⟨e₁, e₂⟩, calc
    ∥e₁ + e₂ - (x₁ + x₂)∥ = ∥(e₁ - x₁) + (e₂ - x₂)∥ : by simp
     ... ≤ ∥e₁ - x₁∥ + ∥e₂ - x₂∥ : norm_triangle _ _
     ... ≤ max (∥e₁ - x₁∥) (∥e₂ - x₂∥) + max (∥e₁ - x₁∥) (∥e₂ - x₂∥) :
       add_le_add (le_max_left _ _) (le_max_right _ _)
end⟩

instance normed_top_group : topological_add_group G :=
⟨continuous_iff_tendsto.2 $ λ x,
tendsto_iff_norm_tendsto_zero.2 begin
  have : ∀ (e : G), ∥-e - -x∥ = ∥e - x∥,
  { intro, simpa using norm_neg (e - x) },
  rw funext this, exact lim_norm x,
end⟩

end normed_group

section normed_ring
class normed_ring (α : Type*) extends ring α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

variables {α : Type*} {β : Type*}

instance normed_ring.to_normed_group [H : normed_ring α] : normed_group α := { ..H }

lemma norm_mul {α : Type*} [normed_ring α] (a b : α) : (∥a*b∥) ≤ (∥a∥) * (∥b∥) :=
normed_ring.norm_mul _ _


instance prod.ring [ring α] [ring β] : ring (α × β) :=
{ left_distrib := assume x y z, calc
    x*(y+z) = (x.1, x.2) * (y.1 + z.1, y.2 + z.2) : rfl
    ... = (x.1*(y.1 + z.1), x.2*(y.2 + z.2)) : rfl
    ... = (x.1*y.1 + x.1*z.1, x.2*y.2 + x.2*z.2) : by simp[left_distrib],
  right_distrib := assume x y z, calc
    (x+y)*z = (x.1 + y.1, x.2 + y.2)*(z.1, z.2) : rfl
    ... = ((x.1 + y.1)*z.1, (x.2 + y.2)*z.2) : rfl
    ... = (x.1*z.1 + y.1*z.1, x.2*z.2 + y.2*z.2) : by simp[right_distrib],
  ..prod.monoid,
  ..prod.add_comm_group}

instance prod.normed_ring [normed_ring α] [normed_ring β] : normed_ring (α × β) :=
{ norm_mul := assume x y,
  calc
    ∥x * y∥ = ∥(x.1*y.1, x.2*y.2)∥ : rfl
        ... = (max ∥x.1*y.1∥  ∥x.2*y.2∥) : rfl
        ... ≤ (max (∥x.1∥*∥y.1∥) (∥x.2∥*∥y.2∥)) : max_le_max (norm_mul (x.1) (y.1)) (norm_mul (x.2) (y.2))
        ... = (max (∥x.1∥*∥y.1∥) (∥y.2∥*∥x.2∥)) : by simp[mul_comm]
        ... ≤ (max (∥x.1∥) (∥x.2∥)) * (max (∥y.2∥) (∥y.1∥)) : by { apply max_mul_mul_le_max_mul_max; simp [norm_nonneg] }
        ... = (max (∥x.1∥) (∥x.2∥)) * (max (∥y.1∥) (∥y.2∥)) : by simp[max_comm]
        ... = (∥x∥*∥y∥) : rfl,
  ..prod.normed_group }
end normed_ring

section normed_field
variables {α : Type*}

class normed_field (α : Type*) extends discrete_field α, metric_space α :=
(norm : α → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) = norm a * norm b)

instance normed_field.to_normed_ring [H : normed_field α] : normed_ring α :=
{ norm_mul := by finish[H.norm_mul], ..H }

instance : normed_field ℝ :=
{ norm := λ x, abs x,
  dist_eq := assume x y, rfl,
  norm_mul := abs_mul}

end normed_field

section normed_space

class normed_space (α : out_param $ Type*) (β : Type*) [out_param $ normed_field α] extends vector_space α β, metric_space β :=
(norm : β → ℝ)
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_smul : ∀ a b, norm (a • b) = normed_field.norm a * norm b)

variables {α : Type*} [normed_field α]  {β : Type*}

instance normed_space.to_normed_group [H : normed_space α β] : normed_group β :=
by refine { add := (+),
            dist_eq := normed_space.dist_eq,
            zero := 0,
            neg := λ x, -x,
            ..H, .. }; simp

variable [normed_space α β]

lemma norm_smul (s : α) (x : β) : ∥s • x∥ = ∥s∥ * ∥x∥ :=
normed_space.norm_smul _ _

variables {E : Type*} {F : Type*} [normed_space α E] [normed_space α F]

lemma tendsto_smul {γ : Type*} {f : γ → α} { g : γ → F} {e : filter γ} {s : α} {b : F} :
(tendsto f e (nhds s)) → (tendsto g e (nhds b)) → tendsto (λ x, (f x) • (g x)) e (nhds (s • b)) :=
begin
  intros limf limg,
  rw tendsto_iff_norm_tendsto_zero,
  have ineq := λ x : γ, calc
      ∥f x • g x - s • b∥ = ∥(f x • g x - s • g x) + (s • g x - s • b)∥ : by simp[add_assoc]
                      ... ≤ ∥f x • g x - s • g x∥ + ∥s • g x - s • b∥ : norm_triangle (f x • g x - s • g x) (s • g x - s • b)
                      ... ≤ ∥f x - s∥*∥g x∥ + ∥s∥*∥g x - b∥ : by { rw [←smul_sub, ←sub_smul, norm_smul, norm_smul] },
  apply squeeze_zero,
  { intro t, exact norm_nonneg },
  { exact ineq },
  { clear ineq,

    have limf': tendsto (λ x, ∥f x - s∥) e (nhds 0) := tendsto_iff_norm_tendsto_zero.1 limf,
    have limg' : tendsto (λ x, ∥g x∥) e (nhds ∥b∥) := filter.tendsto.comp limg (continuous_iff_tendsto.1 norm_continuous _),

    have lim1 : tendsto (λ x, ∥f x - s∥ * ∥g x∥) e (nhds 0),
      by simpa using tendsto_mul limf' limg',
    have limg3 := tendsto_iff_norm_tendsto_zero.1 limg,
    have lim2 : tendsto (λ x, ∥s∥ * ∥g x - b∥) e (nhds 0),
      by simpa using tendsto_mul tendsto_const_nhds limg3,

    rw [show (0:ℝ) = 0 + 0, by simp],
    exact tendsto_add lim1 lim2  }
end

instance product_normed_space : normed_space α (E × F) :=
{ norm_smul :=
  begin
    intros s x,
    cases x with x₁ x₂,
    exact calc
      ∥s • (x₁, x₂)∥ = ∥ (s • x₁, s• x₂)∥ : rfl
      ... = max (∥s • x₁∥) (∥ s• x₂∥) : rfl
      ... = max (∥s∥ * ∥x₁∥) (∥s∥ * ∥x₂∥) : by simp[norm_smul s x₁, norm_smul s x₂]
      ... = ∥s∥ * max (∥x₁∥) (∥x₂∥) : by simp[mul_max_of_nonneg]
  end,

  add_smul := by simp[add_smul],
  -- I have no idea why by simp[smul_add] is not enough for the next goal
  smul_add := assume r x y,  show (r•(x+y).fst, r•(x+y).snd)  = (r•x.fst+r•y.fst, r•x.snd+r•y.snd),
               by simp[smul_add],
  ..prod.normed_group,
  ..prod.vector_space }

instance fintype.normed_space {ι : Type*} {E : ι → Type*} [fintype ι] [∀i, normed_space α (E i)] :
  normed_space α (Πi, E i) :=
{ norm := λf, finset.univ.maxi (λb, ∥f b∥),
  dist_eq := λ f g, begin
    show finset.maxi _ _ = _, congr,
    funext i, apply normed_space.dist_eq
  end,
  norm_smul := λ a f, sorry,
  ..metric_space.fintype_function }

end normed_space
