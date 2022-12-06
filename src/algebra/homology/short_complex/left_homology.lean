import algebra.homology.short_complex.basic
import category_theory.limits.preserves.finite
import category_theory.limits.shapes.finite_limits
import category_theory.limits.shapes.kernels
import tactic.equiv_rw

noncomputable theory

open category_theory category_theory.category category_theory.limits
open_locale zero_object

namespace category_theory.limits

variables {C : Type*} [category C] [has_zero_morphisms C]

/-- should be renamed `is_limit_id_kernel_fork` -/
@[simps]
def kernel_zero {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
  is_limit (kernel_fork.of_ι (𝟙 X) (show 𝟙 X ≫ f = 0, by rw [hf, comp_zero])) :=
kernel_fork.is_limit.of_ι _ _ (λ A x hx, x) (λ A x hx, comp_id _)
  (λ A x hx b hb, by rw [← hb, comp_id])

@[simps]
def cokernel_zero {X Y : C} (f : X ⟶ Y) (hf : f = 0) :
  is_colimit (cokernel_cofork.of_π (𝟙 Y) (show f ≫ 𝟙 Y = 0, by rw [hf, zero_comp])) :=
cokernel_cofork.is_colimit.of_π _ _ (λ A x hx, x) (λ A x hx, id_comp _)
  (λ A x hx b hb, by rw [← hb, id_comp])

/-- fork.is_limit.lift_ι has to be fixed -/
@[simp, reassoc]
lemma fork.is_limit.lift_ι' {X Y : C} {f g : X ⟶ Y} {c : fork f g} (hc : is_limit c)
  (c' : fork f g ) : hc.lift c' ≫ c.ι = c'.ι :=
by apply fork.is_limit.lift_ι

namespace kernel_fork

def is_limit.of_ι_op {K X Y : C} (i : K ⟶ X) {f : X ⟶ Y}
  (w : i ≫ f = 0) (h : is_limit (kernel_fork.of_ι i w)) :
  is_colimit (cokernel_cofork.of_π i.op
    (show f.op ≫ i.op = 0, by simpa only [← op_comp, w])) :=
cokernel_cofork.is_colimit.of_π _ _
  (λ A x hx, (h.lift (kernel_fork.of_ι x.unop (quiver.hom.op_inj hx))).op)
  (λ A x hx, quiver.hom.unop_inj (fork.is_limit.lift_ι h))
  (λ A x hx b hb, quiver.hom.unop_inj (fork.is_limit.hom_ext h begin
    simp only [quiver.hom.unop_op, fork.is_limit.lift_ι],
    exact quiver.hom.op_inj hb,
  end))

def is_limit.of_ι_unop {K X Y : Cᵒᵖ} (i : K ⟶ X) {f : X ⟶ Y}
  (w : i ≫ f = 0) (h : is_limit (kernel_fork.of_ι i w)) :
  is_colimit (cokernel_cofork.of_π i.unop
    (show f.unop ≫ i.unop = 0, by simpa only [← unop_comp, w])) :=
cokernel_cofork.is_colimit.of_π _ _
  (λ A x hx, (h.lift (kernel_fork.of_ι x.op (quiver.hom.unop_inj hx))).unop)
  (λ A x hx, quiver.hom.op_inj (fork.is_limit.lift_ι h))
  (λ A x hx b hb, quiver.hom.op_inj (fork.is_limit.hom_ext h begin
    simp only [quiver.hom.op_unop, fork.is_limit.lift_ι],
    exact quiver.hom.unop_inj hb,
  end))

lemma is_limit.is_iso_ι_of_zero {X Y : C} {f : X ⟶ Y} (c : kernel_fork f)
  (hc : is_limit c) (hf : f = 0) : is_iso c.ι :=
begin
  subst hf,
  let e : c.X ≅ X := is_limit.cone_point_unique_up_to_iso hc (kernel_zero (0 : X ⟶ Y) rfl),
  have eq : e.inv ≫ fork.ι c  = 𝟙 X := fork.is_limit.lift_ι hc,
  haveI : is_iso (e.inv ≫ fork.ι c),
  { rw eq, dsimp, apply_instance, },
  exact is_iso.of_is_iso_comp_left e.inv (fork.ι c),
end

end kernel_fork

namespace cokernel_cofork

def is_colimit.of_π_op {X Y Q : C} (p : Y ⟶ Q) {f : X ⟶ Y}
  (w : f ≫ p = 0) (h : is_colimit (cokernel_cofork.of_π p w)) :
  is_limit (kernel_fork.of_ι p.op
    (show p.op ≫ f.op = 0, by simpa only [← op_comp, w])) :=
kernel_fork.is_limit.of_ι _ _
  (λ A x hx, (h.desc (cokernel_cofork.of_π x.unop (quiver.hom.op_inj hx))).op)
  (λ A x hx, quiver.hom.unop_inj (cofork.is_colimit.π_desc h))
  (λ A x hx b hb, quiver.hom.unop_inj (cofork.is_colimit.hom_ext h begin
    simp only [quiver.hom.unop_op, cofork.is_colimit.π_desc],
    exact quiver.hom.op_inj hb,
  end))

def is_colimit.of_π_unop {X Y Q : Cᵒᵖ} (p : Y ⟶ Q) {f : X ⟶ Y}
  (w : f ≫ p = 0) (h : is_colimit (cokernel_cofork.of_π p w)) :
  is_limit (kernel_fork.of_ι p.unop
    (show p.unop ≫ f.unop = 0, by simpa only [← unop_comp, w])) :=
kernel_fork.is_limit.of_ι _ _
  (λ A x hx, (h.desc (cokernel_cofork.of_π x.op (quiver.hom.unop_inj hx))).unop)
  (λ A x hx, quiver.hom.op_inj (cofork.is_colimit.π_desc h))
  (λ A x hx b hb, quiver.hom.op_inj (cofork.is_colimit.hom_ext h begin
    simp only [quiver.hom.op_unop, cofork.is_colimit.π_desc],
    exact quiver.hom.unop_inj hb,
  end))

lemma is_colimit.is_iso_π_of_zero {X Y : C} {f : X ⟶ Y} (c : cokernel_cofork f)
  (hc : is_colimit c) (hf : f = 0) : is_iso c.π :=
begin
  subst hf,
  let e : c.X ≅ Y := is_colimit.cocone_point_unique_up_to_iso hc (cokernel_zero (0 : X ⟶ Y) rfl),
  have eq : cofork.π c ≫ e.hom = 𝟙 Y := cofork.is_colimit.π_desc hc,
  haveI : is_iso (cofork.π c ≫ e.hom),
  { rw eq, dsimp, apply_instance, },
  exact is_iso.of_is_iso_comp_right (cofork.π c) e.hom,
end

end cokernel_cofork

end category_theory.limits

open category_theory.limits

namespace category_theory

namespace short_complex

variables {C D : Type*} [category C] [category D]
  [has_zero_morphisms C]
  (S : short_complex C) {S₁ S₂ S₃ : short_complex C}

@[nolint has_nonempty_instance]
structure left_homology_data :=
(K H : C)
(i : K ⟶ S.X₂)
(π : K ⟶ H)
(wi : i ≫ S.g = 0)
(hi : is_limit (kernel_fork.of_ι i wi))
(wπ : hi.lift (kernel_fork.of_ι _ S.zero) ≫ π = 0)
(hπ : is_colimit (cokernel_cofork.of_π π wπ))

namespace left_homology_data

@[simps]
def of_ker_of_coker [has_kernel S.g] [has_cokernel (kernel.lift S.g S.f S.zero)] :
  S.left_homology_data :=
{ K := kernel S.g,
  H := cokernel (kernel.lift S.g S.f S.zero),
  i := kernel.ι _,
  π := cokernel.π _,
  wi := kernel.condition _,
  hi := kernel_is_kernel _,
  wπ := cokernel.condition _,
  hπ := cokernel_is_cokernel _, }

attribute [simp, reassoc] wi wπ
variables {S} (h : left_homology_data S) {A : C}

instance : mono h.i :=
⟨λ Y l₁ l₂, fork.is_limit.hom_ext h.hi⟩

instance : epi h.π :=
⟨λ Y l₁ l₂, cofork.is_colimit.hom_ext h.hπ⟩

def lift_K (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.K :=
h.hi.lift (kernel_fork.of_ι k hk)

@[simp, reassoc]
lemma lift_K_i (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) :
  h.lift_K k hk ≫ h.i = k :=
h.hi.fac _ walking_parallel_pair.zero

@[simp]
def lift_H (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.H :=
  h.lift_K k hk ≫ h.π

/-- The morphism `S.X₁ ⟶ h.K` induced by `S.f : S.X₁ ⟶ S.X₂` and the fact that
`h.K` is a kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
def f' : S.X₁ ⟶ h.K := h.lift_K S.f S.zero

@[simp, reassoc]
lemma f'_i : h.f' ≫ h.i = S.f :=
lift_K_i _ _ _

@[simp, reassoc]
lemma f'_π : h.f' ≫ h.π = 0 := h.wπ

lemma lift_K_π_eq_zero_of_boundary (k : A ⟶ S.X₂) (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
  h.lift_K k (by rw [hx, assoc, S.zero, comp_zero]) ≫ h.π = 0 :=
begin
  rw [show 0 = (x ≫ h.f') ≫ h.π, by simp],
  congr' 1,
  simp only [← cancel_mono h.i, hx, assoc, lift_K_i, f'_i],
end

/-- For `h : homology_ful_data S`, this is a restatement of `h.hπ`, saying that
`π : h.K ⟶ h.H` is a cokernel of `h.f' : S.X₁ ⟶ h.K`. -/
def hπ' : is_colimit (cokernel_cofork.of_π h.π h.f'_π) := h.hπ

def desc_H (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) :
  h.H ⟶ A :=
h.hπ.desc (cokernel_cofork.of_π k hk)

@[simp, reassoc]
lemma π_desc_H (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) :
  h.π ≫ h.desc_H k hk = k :=
h.hπ.fac (cokernel_cofork.of_π k hk) walking_parallel_pair.one

variable (S)

@[simps]
def of_colimit_cokernel_cofork (hg : S.g = 0) (c : cokernel_cofork S.f) (hc : is_colimit c) :
  S.left_homology_data :=
{ K := S.X₂,
  H := c.X,
  i := 𝟙 _,
  π := c.π,
  wi := by rw [id_comp, hg],
  hi := kernel_zero _ hg,
  wπ := cokernel_cofork.condition _,
  hπ := is_colimit.of_iso_colimit hc (cofork.ext (iso.refl _) (by tidy)), }

@[simp] lemma of_colimit_cokernel_cofork_f' (hg : S.g = 0) (c : cokernel_cofork S.f)
  (hc : is_colimit c) : (of_colimit_cokernel_cofork S hg c hc).f' = S.f :=
begin
  rw [← cancel_mono (of_colimit_cokernel_cofork S hg c hc).i, f'_i,
    of_colimit_cokernel_cofork_i],
  dsimp,
  rw comp_id,
end

@[simp]
def of_has_cokernel [has_cokernel S.f] (hg : S.g = 0) : S.left_homology_data :=
of_colimit_cokernel_cofork S hg _ (cokernel_is_cokernel _)

@[simps]
def of_limit_kernel_fork (hf : S.f = 0) (c : kernel_fork S.g) (hc : is_limit c) :
  S.left_homology_data :=
{ K := c.X,
  H := c.X,
  i := c.ι,
  π := 𝟙 _,
  wi := kernel_fork.condition _,
  hi := is_limit.of_iso_limit hc (fork.ext (iso.refl _) (by tidy)),
  wπ := fork.is_limit.hom_ext hc begin
    dsimp, simp only [hf, comp_id, fork.is_limit.lift_ι, kernel_fork.ι_of_ι, zero_comp],
  end,
  hπ := cokernel_zero _ begin
    apply fork.is_limit.hom_ext hc,
    dsimp,
    simp only [hf, comp_id, fork.is_limit.lift_ι, kernel_fork.ι_of_ι, zero_comp],
  end, }

@[simp] lemma of_limit_kernel_fork_f' (hf : S.f = 0) (c : kernel_fork S.g)
  (hc : is_limit c) : (of_limit_kernel_fork S hf c hc).f' = 0 :=
by rw [← cancel_mono (of_limit_kernel_fork S hf c hc).i, f'_i, hf, zero_comp]

@[simp]
def of_has_kernel [has_kernel S.g] (hf : S.f = 0) : S.left_homology_data :=
of_limit_kernel_fork S hf _ (kernel_is_kernel _)

@[simps]
def of_zeros (hf : S.f = 0) (hg : S.g = 0) :
  S.left_homology_data :=
{ K := S.X₂,
  H := S.X₂,
  i := 𝟙 _,
  π := 𝟙 _,
  wi := by rw [id_comp, hg],
  hi := kernel_zero _ hg,
  wπ := by { dsimp, rw [comp_id, hf], },
  hπ := cokernel_zero _ hf, }

@[simp]
lemma of_zeros_f' (hf : S.f = 0) (hg : S.g = 0) :
  (of_zeros S hf hg).f' = S.f :=
begin
  rw [← cancel_mono (of_zeros S hf hg).i, f'_i],
  dsimp,
  rw comp_id,
end

@[simps]
def kernel_sequence' {X Y : C} (f : X ⟶ Y) (c : kernel_fork f) (hc : is_limit c)
  [has_zero_object C] :
  left_homology_data (short_complex.mk c.ι f (kernel_fork.condition c)) :=
{ K := c.X,
  H := 0,
  i := c.ι,
  π := 0,
  wi := kernel_fork.condition _,
  hi := is_limit.of_iso_limit hc (fork.ext (iso.refl _) (by simp)),
  wπ := subsingleton.elim _ _,
  hπ := begin
    let l := hc.lift (kernel_fork.of_ι (fork.ι c) (kernel_fork.condition c)),
    have hl : l = 𝟙 c.X,
    { apply fork.is_limit.hom_ext hc,
      dsimp,
      simp only [fork.is_limit.lift_ι, kernel_fork.ι_of_ι, id_comp], },
    exact cokernel_cofork.is_colimit.of_π _ _ (λ A x hx, 0)
      (λ A x hx, begin
        change (l ≫ 𝟙 _) ≫ x = 0 at hx,
        dsimp at hx,
        simpa only [hl, comp_id, id_comp, zero_comp] using hx.symm,
      end)
      (λ A x hx b hb, subsingleton.elim _ _),
  end, }

@[simp]
def kernel_sequence {X Y : C} (f : X ⟶ Y) [has_kernel f] [has_zero_object C] :
  left_homology_data (short_complex.mk (kernel.ι f) f (kernel.condition f)) :=
begin
  let h := kernel_sequence' f _ (kernel_is_kernel f),
  exact h,
end

section change

variables {S} {K H : C} {f' : S.X₁ ⟶ K} {i : K ⟶ S.X₂}
  (commf' : f' ≫ i = S.f) (e : K ≅ h.K) (commi : e.hom ≫ h.i = i)
  (π : K ⟶ H) (hπ₀ : f' ≫ π = 0) (hπ : is_colimit (cokernel_cofork.of_π π hπ₀))

include commf' commi hπ

@[simps]
def change :
  left_homology_data S :=
begin
  have wi : i ≫ S.g = 0 := by rw [← commi, assoc, h.wi, comp_zero],
  have hi : is_limit (kernel_fork.of_ι i wi) :=
    is_limit.of_iso_limit h.hi (fork.ext e.symm (by simp [← commi])),
  let f'' := hi.lift (kernel_fork.of_ι S.f S.zero),
  have eq : f'' = f',
  { rw [← cancel_mono e.hom, ← cancel_mono h.i, assoc, commi],
    dsimp,
    erw fork.is_limit.lift_ι,
    simp only [kernel_fork.ι_of_ι, assoc, commi, commf'], },
  have wπ' : f'' ≫ π = 0 := by rw [eq, hπ₀],
  have hπ' : is_colimit (cokernel_cofork.of_π π wπ'),
  { let e : parallel_pair f'' 0 ≅ parallel_pair f' 0 :=
      parallel_pair.ext (iso.refl _) (iso.refl _) (by simp [eq]) (by simp),
    equiv_rw (is_colimit.precompose_inv_equiv e _).symm,
    exact is_colimit.of_iso_colimit hπ (cofork.ext (iso.refl _) (by tidy)), },
  exact ⟨K, H, i, π, wi, hi, wπ', hπ'⟩,
end

@[simp] lemma change_f' : (h.change commf' e commi π hπ₀ hπ).f' = f' :=
by rw [← cancel_mono (h.change commf' e commi π hπ₀ hπ).i, f'_i, change_i, commf']

end change

end left_homology_data

class has_left_homology : Prop :=
(cond : nonempty S.left_homology_data)

def some_left_homology_data [has_left_homology S] :
  S.left_homology_data := has_left_homology.cond.some

variable {S}

lemma has_left_homology.mk' (h : S.left_homology_data) : has_left_homology S :=
⟨nonempty.intro h⟩

@[priority 100]
instance has_left_homology_of_ker_of_coker
  [has_kernel S.g] [has_cokernel (kernel.lift S.g S.f S.zero)] :
  S.has_left_homology := has_left_homology.mk' (left_homology_data.of_ker_of_coker S)

instance has_left_homology_of_has_cokernel {X Y : C} (f : X ⟶ Y) (Z : C)
  [has_cokernel f] :
  (short_complex.mk f (0 : Y ⟶ Z) comp_zero).has_left_homology :=
has_left_homology.mk' (left_homology_data.of_has_cokernel _ rfl)

instance has_left_homology_of_has_kernel {Y Z : C} (g : Y ⟶ Z) (X : C)
  [has_kernel g] :
  (short_complex.mk (0 : X ⟶ Y) g zero_comp).has_left_homology :=
has_left_homology.mk' (left_homology_data.of_has_kernel _ rfl)

instance has_left_homology_of_zeros (X Y Z : C) :
  (short_complex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).has_left_homology :=
has_left_homology.mk' (left_homology_data.of_zeros _ rfl rfl)

section

variables {S₁ S₂} (φ : S₁ ⟶ S₂) (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data)

structure left_homology_map_data :=
(φK : h₁.K ⟶ h₂.K)
(φH : h₁.H ⟶ h₂.H)
(commi' : φK ≫ h₂.i = h₁.i ≫ φ.τ₂ . obviously)
(commf'' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' . obviously)
(commπ' : h₁.π ≫ φH = φK ≫ h₂.π . obviously)

namespace left_homology_map_data

restate_axiom commi'
restate_axiom commπ'
restate_axiom commf''
attribute [simp, reassoc] commi commf' commπ

@[simps]
def zero (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data) :
  left_homology_map_data 0 h₁ h₂ :=
{ φK := 0,
  φH := 0, }

@[simps]
def id (h : S.left_homology_data) : left_homology_map_data (𝟙 S) h h :=
{ φK := 𝟙 _,
  φH := 𝟙 _, }

@[simps]
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.left_homology_data}
  {h₂ : S₂.left_homology_data} {h₃ : S₃.left_homology_data}
  (ψ : left_homology_map_data φ h₁ h₂) (ψ' : left_homology_map_data φ' h₂ h₃) :
  left_homology_map_data (φ ≫ φ') h₁ h₃ :=
{ φK := ψ.φK ≫ ψ'.φK,
  φH := ψ.φH ≫ ψ'.φH, }

instance : subsingleton (left_homology_map_data φ h₁ h₂) :=
⟨λ ψ₁ ψ₂, begin
  have hK : ψ₁.φK = ψ₂.φK := by simp [← cancel_mono h₂.i],
  have hH : ψ₁.φH = ψ₂.φH := by simp [← cancel_epi h₁.π, hK],
  cases ψ₁,
  cases ψ₂,
  simp only,
  tauto,
end⟩

instance : inhabited (left_homology_map_data φ h₁ h₂) :=
⟨begin
  let φK : h₁.K ⟶ h₂.K := h₂.lift_K (h₁.i ≫ φ.τ₂)
    (by rw [assoc, φ.comm₂₃, h₁.wi_assoc, zero_comp]),
  have commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f',
  { simp only [← cancel_mono h₂.i, assoc, left_homology_data.lift_K_i,
      left_homology_data.f'_i_assoc, left_homology_data.f'_i, φ.comm₁₂], },
  let φH : h₁.H ⟶ h₂.H := h₁.desc_H (φK ≫ h₂.π)
    (by rw [reassoc_of commf', h₂.f'_π, comp_zero]),
  exact ⟨φK, φH, by simp, commf', by simp⟩,
end⟩

instance : unique (left_homology_map_data φ h₁ h₂) := unique.mk' _

def some : left_homology_map_data φ h₁ h₂ := default

variables {φ h₁ h₂}

lemma congr_φH {γ₁ γ₂ : left_homology_map_data φ h₁ h₂} (eq : γ₁ = γ₂) :
  γ₁.φH = γ₂.φH := by rw eq
lemma congr_φK {γ₁ γ₂ : left_homology_map_data φ h₁ h₂} (eq : γ₁ = γ₂) :
  γ₁.φK = γ₂.φK := by rw eq

@[simp]
def of_zeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
  left_homology_map_data φ (left_homology_data.of_zeros S₁ hf₁ hg₁)
    (left_homology_data.of_zeros S₂ hf₂ hg₂) :=
{ φK := φ.τ₂,
  φH := φ.τ₂,
  commf'' := by simp only [left_homology_data.of_zeros_f', φ.comm₁₂], }

@[simps]
def of_colimit_cokernel_coforks (φ : S₁ ⟶ S₂)
  (hg₁ : S₁.g = 0) (c₁ : cokernel_cofork S₁.f) (hc₁ : is_colimit c₁)
  (hg₂ : S₂.g = 0) (c₂ : cokernel_cofork S₂.f) (hc₂ : is_colimit c₂) (f : c₁.X ⟶ c₂.X)
  (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
  left_homology_map_data φ (left_homology_data.of_colimit_cokernel_cofork S₁ hg₁ c₁ hc₁)
    (left_homology_data.of_colimit_cokernel_cofork S₂ hg₂ c₂ hc₂) :=
{ φK := φ.τ₂,
  φH := f,
  commi' := by { dsimp, simp only [comp_id, id_comp], },
  commf'' := by { simp only [left_homology_data.of_colimit_cokernel_cofork_f', φ.comm₁₂], },
  commπ' := comm.symm, }

@[simps]
def of_limit_kernel_forks (φ : S₁ ⟶ S₂)
  (hf₁ : S₁.f = 0) (c₁ : kernel_fork S₁.g) (hc₁ : is_limit c₁)
  (hf₂ : S₂.f = 0) (c₂ : kernel_fork S₂.g) (hc₂ : is_limit c₂) (f : c₁.X ⟶ c₂.X)
  (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
  left_homology_map_data φ (left_homology_data.of_limit_kernel_fork S₁ hf₁ c₁ hc₁)
    (left_homology_data.of_limit_kernel_fork S₂ hf₂ c₂ hc₂) :=
{ φK := f,
  φH := f,
  commi' := comm.symm,
  commf'' := by simp only [left_homology_data.of_limit_kernel_fork_f', zero_comp, comp_zero], }

variable (S)

@[simps]
def compatibility_of_zeros_of_colimit_cokernel_cofork (hf : S.f = 0) (hg : S.g = 0)
  (c : cokernel_cofork S.f) (hc : is_colimit c) :
  left_homology_map_data (𝟙 S) (left_homology_data.of_zeros S hf hg)
    (left_homology_data.of_colimit_cokernel_cofork S hg c hc):=
{ φK := 𝟙 _,
  φH := c.π, }

@[simps]
def compatibility_of_zeros_of_limit_kernel_fork (hf : S.f = 0) (hg : S.g = 0)
  (c : kernel_fork S.g) (hc : is_limit c) :
  left_homology_map_data (𝟙 S)
    (left_homology_data.of_limit_kernel_fork S hf c hc)
    (left_homology_data.of_zeros S hf hg):=
{ φK := c.ι,
  φH := c.ι, }

end left_homology_map_data

end

variable (S)

def left_homology [has_left_homology S] : C := S.some_left_homology_data.H
def cycles [has_left_homology S] : C := S.some_left_homology_data.K
def left_homology_π [has_left_homology S] : S.cycles ⟶ S.left_homology :=
  S.some_left_homology_data.π
def cycles_i [has_left_homology S] : S.cycles ⟶ S.X₂ := S.some_left_homology_data.i
def to_cycles [has_left_homology S] : S.X₁ ⟶ S.cycles := S.some_left_homology_data.f'

@[simp, reassoc] lemma cycles_i_g [has_left_homology S] : S.cycles_i ≫ S.g = 0 :=
S.some_left_homology_data.wi

@[simp, reassoc] lemma to_cycles_i [has_left_homology S] : S.to_cycles ≫ S.cycles_i = S.f :=
S.some_left_homology_data.f'_i

instance [has_left_homology S] : mono S.cycles_i :=
by { dsimp only [cycles_i], apply_instance, }

instance [has_left_homology S] : epi S.left_homology_π :=
by { dsimp only [left_homology_π], apply_instance, }

variables {S S₁ S₂ S₃}

def left_homology_map' (φ : S₁ ⟶ S₂) (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data) :
  h₁.H ⟶ h₂.H := (left_homology_map_data.some φ _ _).φH

def cycles_map' (φ : S₁ ⟶ S₂) (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data) :
  h₁.K ⟶ h₂.K := (left_homology_map_data.some φ _ _).φK

@[simp, reassoc]
lemma cycles_map'_i (φ : S₁ ⟶ S₂) (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data) :
  cycles_map' φ h₁ h₂ ≫ h₂.i = h₁.i ≫ φ.τ₂ :=
left_homology_map_data.commi _

@[simp, reassoc]
lemma left_homology_π_naturality' (φ : S₁ ⟶ S₂)
  (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data) :
  h₁.π ≫ left_homology_map' φ h₁ h₂ = cycles_map' φ h₁ h₂ ≫ h₂.π :=
left_homology_map_data.commπ _

def left_homology_map [has_left_homology S₁] [has_left_homology S₂]
  (φ : S₁ ⟶ S₂) : S₁.left_homology ⟶ S₂.left_homology :=
left_homology_map' φ _ _

def cycles_map [has_left_homology S₁] [has_left_homology S₂]
  (φ : S₁ ⟶ S₂) : S₁.cycles ⟶ S₂.cycles :=
cycles_map' φ _ _

@[simp, reassoc]
lemma cycles_map_i (φ : S₁ ⟶ S₂) [S₁.has_left_homology] [S₂.has_left_homology] :
  cycles_map φ ≫ S₂.cycles_i = S₁.cycles_i ≫ φ.τ₂ :=
cycles_map'_i _ _ _

@[simp, reassoc]
lemma to_cycles_naturality (φ : S₁ ⟶ S₂) [S₁.has_left_homology] [S₂.has_left_homology] :
  S₁.to_cycles ≫ cycles_map φ = φ.τ₁ ≫ S₂.to_cycles :=
by simp only [← cancel_mono S₂.cycles_i, φ.comm₁₂, assoc, to_cycles_i,
  cycles_map_i, to_cycles_i_assoc]

@[simp, reassoc]
lemma left_homology_π_naturality [has_left_homology S₁] [has_left_homology S₂]
  (φ : S₁ ⟶ S₂) :
  S₁.left_homology_π ≫ left_homology_map φ = cycles_map φ ≫ S₂.left_homology_π :=
left_homology_π_naturality' _ _ _

namespace left_homology_map_data

variables {φ : S₁ ⟶ S₂} {h₁ : S₁.left_homology_data} {h₂ : S₂.left_homology_data}
  (γ : left_homology_map_data φ h₁ h₂)

lemma left_homology_map'_eq : left_homology_map' φ h₁ h₂ = γ.φH :=
left_homology_map_data.congr_φH (subsingleton.elim _ _)

lemma cycles_map'_eq : cycles_map' φ h₁ h₂ = γ.φK :=
left_homology_map_data.congr_φK (subsingleton.elim _ _)

end left_homology_map_data

@[simp]
lemma left_homology_map'_id (h : S.left_homology_data) :
  left_homology_map' (𝟙 S) h h = 𝟙 _ :=
(left_homology_map_data.id h).left_homology_map'_eq

@[simp]
lemma cycles_map'_id (h : S.left_homology_data) :
  cycles_map' (𝟙 S) h h = 𝟙 _ :=
(left_homology_map_data.id h).cycles_map'_eq

variable (S)

@[simp]
lemma left_homology_map_id [has_left_homology S] :
  left_homology_map (𝟙 S) = 𝟙 _ :=
left_homology_map'_id _

@[simp]
lemma cycles_map_id [has_left_homology S] :
  cycles_map (𝟙 S) = 𝟙 _ :=
cycles_map'_id _

variables {S₁ S₂}

@[simp]
lemma left_homology_map'_zero (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data) :
  left_homology_map' 0 h₁ h₂ = 0 :=
(left_homology_map_data.zero h₁ h₂).left_homology_map'_eq

@[simp]
lemma cycles_map'_zero (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data) :
  cycles_map' 0 h₁ h₂ = 0 :=
(left_homology_map_data.zero h₁ h₂).cycles_map'_eq

variables (S₁ S₂)
@[simp]
lemma left_homology_map_zero [has_left_homology S₁] [has_left_homology S₂] :
  left_homology_map (0 : S₁ ⟶ S₂) = 0 :=
left_homology_map'_zero _ _

@[simp]
lemma cycles_map_zero [has_left_homology S₁] [has_left_homology S₂] :
  cycles_map (0 : S₁ ⟶ S₂) = 0 :=
cycles_map'_zero _ _

variables {S₁ S₂}

lemma left_homology_map'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data) (h₃ : S₃.left_homology_data) :
  left_homology_map' (φ₁ ≫ φ₂) h₁ h₃ = left_homology_map' φ₁ h₁ h₂ ≫
    left_homology_map' φ₂ h₂ h₃ :=
begin
  let γ₁ := left_homology_map_data.some φ₁ _ _,
  let γ₂ := left_homology_map_data.some φ₂ _ _,
  rw [γ₁.left_homology_map'_eq, γ₂.left_homology_map'_eq, (γ₁.comp γ₂).left_homology_map'_eq,
    left_homology_map_data.comp_φH],
end

lemma cycles_map'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data) (h₃ : S₃.left_homology_data) :
  cycles_map' (φ₁ ≫ φ₂) h₁ h₃ = cycles_map' φ₁ h₁ h₂ ≫
    cycles_map' φ₂ h₂ h₃ :=
begin
  let γ₁ := left_homology_map_data.some φ₁ _ _,
  let γ₂ := left_homology_map_data.some φ₂ _ _,
  rw [γ₁.cycles_map'_eq, γ₂.cycles_map'_eq, (γ₁.comp γ₂).cycles_map'_eq,
    left_homology_map_data.comp_φK],
end

@[simp]
lemma left_homology_map_comp [has_left_homology S₁] [has_left_homology S₂] [has_left_homology S₃]
  (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
  left_homology_map (φ₁ ≫ φ₂) = left_homology_map φ₁ ≫ left_homology_map φ₂ :=
left_homology_map'_comp _ _ _ _ _

@[simp]
lemma cycles_map_comp [has_left_homology S₁] [has_left_homology S₂] [has_left_homology S₃]
  (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
  cycles_map (φ₁ ≫ φ₂) = cycles_map φ₁ ≫ cycles_map φ₂ :=
cycles_map'_comp _ _ _ _ _

@[simps]
def left_homology_map_iso' (e : S₁ ≅ S₂) (h₁ : S₁.left_homology_data)
  (h₂ : S₂.left_homology_data) : h₁.H ≅ h₂.H :=
{ hom := left_homology_map' e.hom h₁ h₂,
  inv := left_homology_map' e.inv h₂ h₁,
  hom_inv_id' := by rw [← left_homology_map'_comp, e.hom_inv_id, left_homology_map'_id],
  inv_hom_id' := by rw [← left_homology_map'_comp, e.inv_hom_id, left_homology_map'_id], }

instance is_iso_left_homology_map'_of_iso (φ : S₁ ⟶ S₂) [is_iso φ]
  (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data) :
  is_iso (left_homology_map' φ h₁ h₂) :=
by { change is_iso (left_homology_map_iso' (as_iso φ) h₁ h₂).hom, apply_instance, }

@[simps]
def cycles_map_iso' (e : S₁ ≅ S₂) (h₁ : S₁.left_homology_data)
  (h₂ : S₂.left_homology_data) : h₁.K ≅ h₂.K :=
{ hom := cycles_map' e.hom h₁ h₂,
  inv := cycles_map' e.inv h₂ h₁,
  hom_inv_id' := by rw [← cycles_map'_comp, e.hom_inv_id, cycles_map'_id],
  inv_hom_id' := by rw [← cycles_map'_comp, e.inv_hom_id, cycles_map'_id], }

instance is_iso_cycles_map'_of_iso (φ : S₁ ⟶ S₂) [is_iso φ]
  (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data) :
  is_iso (cycles_map' φ h₁ h₂) :=
by { change is_iso (cycles_map_iso' (as_iso φ) h₁ h₂).hom, apply_instance, }

@[simps]
def left_homology_map_iso (e : S₁ ≅ S₂) [S₁.has_left_homology]
  [S₂.has_left_homology] : S₁.left_homology ≅ S₂.left_homology :=
{ hom := left_homology_map e.hom,
  inv := left_homology_map e.inv,
  hom_inv_id' := by rw [← left_homology_map_comp, e.hom_inv_id, left_homology_map_id],
  inv_hom_id' := by rw [← left_homology_map_comp, e.inv_hom_id, left_homology_map_id], }

instance is_iso_left_homology_map_of_iso (φ : S₁ ⟶ S₂) [is_iso φ] [S₁.has_left_homology]
  [S₂.has_left_homology] :
  is_iso (left_homology_map φ) :=
by { change is_iso (left_homology_map_iso (as_iso φ)).hom, apply_instance, }

@[simps]
def cycles_map_iso (e : S₁ ≅ S₂) [S₁.has_left_homology]
  [S₂.has_left_homology] : S₁.cycles ≅ S₂.cycles :=
{ hom := cycles_map e.hom,
  inv := cycles_map e.inv,
  hom_inv_id' := by rw [← cycles_map_comp, e.hom_inv_id, cycles_map_id],
  inv_hom_id' := by rw [← cycles_map_comp, e.inv_hom_id, cycles_map_id], }

instance is_iso_cycles_map_of_iso (φ : S₁ ⟶ S₂) [is_iso φ] [S₁.has_left_homology]
  [S₂.has_left_homology] :
  is_iso (cycles_map φ) :=
by { change is_iso (cycles_map_iso (as_iso φ)).hom, apply_instance, }

variable {S}

def left_homology_data.left_homology_iso (h : S.left_homology_data) [S.has_left_homology] :
  S.left_homology ≅ h.H := left_homology_map_iso' (iso.refl _) _ _

def left_homology_data.cycles_iso (h : S.left_homology_data) [S.has_left_homology] :
  S.cycles ≅ h.K := cycles_map_iso' (iso.refl _) _ _

@[simp, reassoc]
lemma left_homology_data.cycles_iso_hom_comp_i (h : S.left_homology_data) [S.has_left_homology] :
  h.cycles_iso.hom ≫ h.i = S.cycles_i :=
begin
  dsimp [cycles_i, left_homology_data.cycles_iso],
  simp only [cycles_map'_i, id_τ₂, comp_id],
end

@[simp, reassoc]
lemma left_homology_data.cycles_iso_inv_comp_cycles_i (h : S.left_homology_data)
  [S.has_left_homology] :
  h.cycles_iso.inv ≫ S.cycles_i = h.i :=
by simp only [← h.cycles_iso_hom_comp_i, iso.inv_hom_id_assoc]

namespace left_homology_map_data

variables {φ : S₁ ⟶ S₂} {h₁ : S₁.left_homology_data} {h₂ : S₂.left_homology_data}
  (γ : left_homology_map_data φ h₁ h₂)
lemma left_homology_map_eq [S₁.has_left_homology] [S₂.has_left_homology] :
  left_homology_map φ = h₁.left_homology_iso.hom ≫ γ.φH ≫ h₂.left_homology_iso.inv :=
begin
  dsimp [left_homology_data.left_homology_iso, left_homology_map_iso'],
  rw [← γ.left_homology_map'_eq, ← left_homology_map'_comp, ← left_homology_map'_comp, id_comp, comp_id],
  refl,
end

lemma cycles_map_eq [S₁.has_left_homology] [S₂.has_left_homology] :
  cycles_map φ = h₁.cycles_iso.hom ≫ γ.φK ≫ h₂.cycles_iso.inv :=
begin
  dsimp [left_homology_data.cycles_iso, cycles_map_iso'],
  rw [← γ.cycles_map'_eq, ← cycles_map'_comp, ← cycles_map'_comp, id_comp, comp_id],
  refl,
end

lemma left_homology_map_comm [S₁.has_left_homology] [S₂.has_left_homology] :
  left_homology_map φ ≫ h₂.left_homology_iso.hom = h₁.left_homology_iso.hom ≫ γ.φH :=
by simp only [γ.left_homology_map_eq, assoc, iso.inv_hom_id, comp_id]

lemma cycles_map_comm [S₁.has_left_homology] [S₂.has_left_homology] :
  cycles_map φ ≫ h₂.cycles_iso.hom = h₁.cycles_iso.hom ≫ γ.φK :=
by simp only [γ.cycles_map_eq, assoc, iso.inv_hom_id, comp_id]

end left_homology_map_data

variable (C)
/-- We shall say that a category with left homology is a category for which
all short complexes have left homology. -/
abbreviation _root_.category_with_left_homology := ∀ (S : short_complex C), S.has_left_homology

@[simps]
def left_homology_functor [category_with_left_homology C] :
  short_complex C ⥤ C :=
{ obj := λ S, S.left_homology,
  map := λ S₁ S₂, left_homology_map, }

@[simps]
def cycles_functor [category_with_left_homology C] :
  short_complex C ⥤ C :=
{ obj := λ S, S.cycles,
  map := λ S₁ S₂, cycles_map, }

@[simps]
def left_homology_π_nat_trans [category_with_left_homology C] :
  cycles_functor C ⟶ left_homology_functor C :=
{ app := λ S, left_homology_π S,
  naturality' := λ S₁ S₂ φ, (left_homology_π_naturality φ).symm, }

@[simps]
def cycles_i_nat_trans [category_with_left_homology C] :
  cycles_functor C ⟶ short_complex.π₂ :=
{ app := λ S, S.cycles_i, }

@[simps]
def to_cycles_nat_trans [category_with_left_homology C] :
  π₁ ⟶ cycles_functor C :=
{ app := λ S, S.to_cycles,
  naturality' := λ S₁ S₂ φ, (to_cycles_naturality φ).symm, }

namespace left_homology_data

variable {C}

@[simps]
def of_epi_of_is_iso_of_mono (φ : S₁ ⟶ S₂) (h : left_homology_data S₁)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] : left_homology_data S₂ :=
begin
  let i : h.K ⟶ S₂.X₂ := h.i ≫ φ.τ₂,
  have wi : i ≫ S₂.g = 0 := by simp only [assoc, φ.comm₂₃, h.wi_assoc, zero_comp],
  have hi : is_limit (kernel_fork.of_ι i wi) := kernel_fork.is_limit.of_ι _ _
    (λ A x hx, h.lift_K (x ≫ inv φ.τ₂) (by simp only [assoc, ← cancel_mono φ.τ₃,
      zero_comp, ← φ.comm₂₃, is_iso.inv_hom_id_assoc, hx]))
    (λ A x hx, by simp only [assoc, lift_K_i_assoc, is_iso.inv_hom_id, comp_id])
    (λ A x hx b hx, by simp only [← cancel_mono h.i, ← cancel_mono φ.τ₂,
        assoc, lift_K_i, is_iso.inv_hom_id, comp_id, hx]),
  let f' := hi.lift (kernel_fork.of_ι S₂.f S₂.zero),
  have hf' : φ.τ₁ ≫ f' = h.f',
  { have eq := @fork.is_limit.lift_ι _ _ _ _ _ _ _ ((kernel_fork.of_ι S₂.f S₂.zero)) hi,
    simp only [kernel_fork.ι_of_ι] at eq,
    simp only [← cancel_mono h.i, ← cancel_mono φ.τ₂, assoc, eq, f'_i_assoc, φ.comm₁₂], },
  have wπ : f' ≫ h.π = 0,
  { rw [← cancel_epi φ.τ₁, comp_zero, reassoc_of hf', h.f'_π], },
  have hπ : is_colimit (cokernel_cofork.of_π h.π wπ) := cokernel_cofork.is_colimit.of_π _ _
    (λ A x hx, h.desc_H x (by rw [← hf', assoc, hx, comp_zero]))
    (λ A x hx, π_desc_H _ _ _)
    (λ A x hx b hb, by simp only [← cancel_epi h.π, π_desc_H, hb]),
  exact ⟨h.K, h.H, i, h.π, wi, hi, wπ, hπ⟩,
end

@[simp]
lemma of_epi_of_is_iso_of_mono_τ₁_f' (φ : S₁ ⟶ S₂) (h : left_homology_data S₁)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] : φ.τ₁ ≫ (of_epi_of_is_iso_of_mono φ h).f' = h.f' :=
by rw [← cancel_mono (of_epi_of_is_iso_of_mono φ h).i, assoc, f'_i,
    of_epi_of_is_iso_of_mono_i, f'_i_assoc, φ.comm₁₂]

@[simps]
def of_epi_of_is_iso_of_mono' (φ : S₁ ⟶ S₂) (h : left_homology_data S₂)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] : left_homology_data S₁ :=
begin
  let i : h.K ⟶ S₁.X₂ := h.i ≫ inv φ.τ₂,
  have wi : i ≫ S₁.g = 0 := by simp only [assoc, ← cancel_mono φ.τ₃, zero_comp,
    ← φ.comm₂₃, is_iso.inv_hom_id_assoc, h.wi],
  have hi : is_limit (kernel_fork.of_ι i wi) := kernel_fork.is_limit.of_ι _ _
    (λ A x hx, h.lift_K (x ≫ φ.τ₂) (by rw [assoc, φ.comm₂₃, reassoc_of hx, zero_comp]))
    (λ A x hx, by simp only [assoc, lift_K_i_assoc, is_iso.hom_inv_id, comp_id])
    (λ A x hx b hb, by simp only [← cancel_mono h.i, lift_K_i, ← hb,
      assoc, is_iso.inv_hom_id, comp_id]),
  let f' := hi.lift (kernel_fork.of_ι S₁.f S₁.zero),
  have hf' : f' ≫ i = S₁.f := by simpa only [kernel_fork.ι_of_ι]
    using @fork.is_limit.lift_ι _ _ _ _ _ _ _ ((kernel_fork.of_ι S₁.f S₁.zero)) hi,
  have hf'' : f' = φ.τ₁ ≫ h.f',
  { simpa only [← cancel_mono h.i, ← cancel_mono (inv φ.τ₂), assoc, f'_i_assoc, φ.comm₁₂_assoc,
      is_iso.hom_inv_id, comp_id] using fork.is_limit.lift_ι _, },
  have wπ : f' ≫ h.π = 0 := by simp only [hf'', assoc, f'_π, comp_zero],
  have hπ : is_colimit (cokernel_cofork.of_π h.π wπ) := cokernel_cofork.is_colimit.of_π _ _
    (λ A x hx, h.desc_H x (by rw [← cancel_epi φ.τ₁, ← reassoc_of hf'', hx, comp_zero]))
    (λ A x hx, π_desc_H _ _ _)
    (λ A x hx b hx, by simp only [← cancel_epi h.π, π_desc_H, hx]),
  exact ⟨h.K, h.H, i, h.π, wi, hi, wπ, hπ⟩,
end

@[simp]
lemma of_epi_of_is_iso_of_mono'_f' (φ : S₁ ⟶ S₂) (h : left_homology_data S₂)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
  (of_epi_of_is_iso_of_mono' φ h).f' = φ.τ₁ ≫ h.f' :=
by rw [← cancel_mono (of_epi_of_is_iso_of_mono' φ h).i, f'_i, of_epi_of_is_iso_of_mono'_i,
    assoc, f'_i_assoc, φ.comm₁₂_assoc, is_iso.hom_inv_id, comp_id]

def of_iso (e : S₁ ≅ S₂) (h₁ : left_homology_data S₁) : left_homology_data S₂ :=
h₁.of_epi_of_is_iso_of_mono e.hom

end left_homology_data

variables {C}

lemma has_left_homology_of_epi_of_is_iso_of_mono (φ : S₁ ⟶ S₂) [has_left_homology S₁]
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] : has_left_homology S₂ :=
has_left_homology.mk' (left_homology_data.of_epi_of_is_iso_of_mono φ S₁.some_left_homology_data)

lemma has_left_homology_of_epi_of_is_iso_of_mono' (φ : S₁ ⟶ S₂) [has_left_homology S₂]
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] : has_left_homology S₁ :=
has_left_homology.mk' (left_homology_data.of_epi_of_is_iso_of_mono' φ S₂.some_left_homology_data)

lemma has_left_homology_of_iso {S₁ S₂ : short_complex C}
  (e : S₁ ≅ S₂) [has_left_homology S₁] : has_left_homology S₂ :=
has_left_homology_of_epi_of_is_iso_of_mono e.hom

namespace left_homology_map_data

@[simps]
def of_epi_of_is_iso_of_mono (φ : S₁ ⟶ S₂) (h : left_homology_data S₁)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
    left_homology_map_data φ h (left_homology_data.of_epi_of_is_iso_of_mono φ h) :=
{ φK := 𝟙 _,
  φH := 𝟙 _,
  commf'' := by simp only [left_homology_data.of_epi_of_is_iso_of_mono_τ₁_f' φ h, comp_id], }

@[simps]
def of_epi_of_is_iso_of_mono' (φ : S₁ ⟶ S₂) (h : left_homology_data S₂)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
    left_homology_map_data φ (left_homology_data.of_epi_of_is_iso_of_mono' φ h) h :=
{ φK := 𝟙 _,
  φH := 𝟙 _, }

end left_homology_map_data

instance (φ : S₁ ⟶ S₂) (h₁ : S₁.left_homology_data) (h₂ : S₂.left_homology_data)
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
  is_iso (left_homology_map' φ h₁ h₂) :=
begin
  let h₂' := left_homology_data.of_epi_of_is_iso_of_mono φ h₁,
  haveI : is_iso (left_homology_map' φ h₁ h₂'),
  { let γ := left_homology_map_data.of_epi_of_is_iso_of_mono φ h₁,
    rw γ.left_homology_map'_eq,
    dsimp,
    apply_instance, },
  have eq := left_homology_map'_comp φ (𝟙 S₂) h₁ h₂' h₂,
  rw comp_id at eq,
  rw eq,
  apply_instance,
end

instance (φ : S₁ ⟶ S₂) [S₁.has_left_homology] [S₂.has_left_homology]
  [epi φ.τ₁] [is_iso φ.τ₂] [mono φ.τ₃] :
  is_iso (left_homology_map φ) :=
by { dsimp only [left_homology_map], apply_instance, }

section

variables (S) (h : left_homology_data S)
  {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) [has_left_homology S]

def lift_cycles : A ⟶ S.cycles :=
S.some_left_homology_data.lift_K k hk

@[simp, reassoc]
lemma lift_cycles_i : S.lift_cycles k hk ≫ S.cycles_i = k :=
left_homology_data.lift_K_i _ k hk

@[reassoc]
lemma comp_lift_cycles {A' : C} (α : A' ⟶ A) :
  α ≫ S.lift_cycles k hk = S.lift_cycles (α ≫ k) (by rw [assoc, hk, comp_zero]) :=
by simp only [← cancel_mono S.cycles_i, assoc, lift_cycles_i]

def cycles_is_kernel : is_limit (kernel_fork.of_ι S.cycles_i S.cycles_i_g) :=
S.some_left_homology_data.hi

lemma is_iso_cycles_i_of (hg : S.g = 0) : is_iso (S.cycles_i) :=
kernel_fork.is_limit.is_iso_ι_of_zero _ S.cycles_is_kernel hg

@[simps]
def cycles_iso_kernel [has_kernel S.g] : S.cycles ≅ kernel S.g :=
{ hom := kernel.lift S.g S.cycles_i (by simp),
  inv := S.lift_cycles (kernel.ι S.g) (by simp),
  hom_inv_id' := by simp only [←  cancel_mono S.cycles_i, assoc, lift_cycles_i,
    kernel.lift_ι, id_comp],
  inv_hom_id' := by simp only [← cancel_mono (kernel.ι S.g), assoc, kernel.lift_ι,
    lift_cycles_i, id_comp], }

@[simp]
def lift_left_homology : A ⟶ S.left_homology :=
S.lift_cycles k hk ≫ S.left_homology_π

lemma lift_cycles_π_eq_zero_of_boundary (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
S.lift_cycles k (by rw [hx, assoc, S.zero, comp_zero])≫ S.left_homology_π = 0 :=
left_homology_data.lift_K_π_eq_zero_of_boundary _ k x hx

@[simp, reassoc]
lemma to_cycles_comp_left_homology_π :
  S.to_cycles ≫ S.left_homology_π = 0 :=
S.lift_cycles_π_eq_zero_of_boundary S.f (𝟙 _) (by rw id_comp)

def left_homology_is_cokernel :
  is_colimit (cokernel_cofork.of_π S.left_homology_π S.to_cycles_comp_left_homology_π) :=
S.some_left_homology_data.hπ

@[simp, reassoc]
lemma lift_cycles_comp_cycles_map (φ : S ⟶ S₁) [S₁.has_left_homology] :
  S.lift_cycles k hk ≫ cycles_map φ =
    S₁.lift_cycles (k ≫ φ.τ₂) (by rw [assoc, φ.comm₂₃, reassoc_of hk, zero_comp]) :=
by simp only [← cancel_mono (S₁.cycles_i), assoc, cycles_map_i, lift_cycles_i_assoc, lift_cycles_i]

variable {S}

@[simp, reassoc]
lemma left_homology_data.left_homology_π_comp_left_homology_iso_hom :
  S.left_homology_π ≫ h.left_homology_iso.hom = h.cycles_iso.hom ≫ h.π :=
begin
  dsimp only [left_homology_π, left_homology_data.left_homology_iso, left_homology_map_iso',
    iso.refl, left_homology_data.cycles_iso, cycles_map_iso'],
  rw ← left_homology_π_naturality',
end

@[simp, reassoc]
lemma left_homology_data.π_comp_left_homology_iso_inv :
  h.π ≫ h.left_homology_iso.inv = h.cycles_iso.inv ≫ S.left_homology_π :=
by simp only [← cancel_epi h.cycles_iso.hom, ← cancel_mono h.left_homology_iso.hom, assoc,
  iso.inv_hom_id, comp_id, iso.hom_inv_id_assoc,
  left_homology_data.left_homology_π_comp_left_homology_iso_hom]

@[simp, reassoc]
lemma left_homology_data.lift_cycles_comp_cycles_iso_hom :
  S.lift_cycles k hk ≫ h.cycles_iso.hom = h.lift_K k hk :=
by simp only [←cancel_mono h.i, assoc, left_homology_data.cycles_iso_hom_comp_i,
  lift_cycles_i, left_homology_data.lift_K_i]

@[simp]
lemma left_homology_data.lift_K_comp_cycles_iso_inv :
  h.lift_K k hk ≫ h.cycles_iso.inv = S.lift_cycles k hk :=
by rw [← h.lift_cycles_comp_cycles_iso_hom, assoc, iso.hom_inv_id, comp_id]

lemma left_homology_data.ext_iff' (f₁ f₂ : S.left_homology ⟶ A) :
  f₁ = f₂ ↔ h.π ≫ h.left_homology_iso.inv ≫ f₁ = h.π ≫ h.left_homology_iso.inv ≫ f₂ :=
by rw [← cancel_epi h.left_homology_iso.inv, cancel_epi h.π]

end

namespace has_left_homology

variable (S)

@[protected]
lemma has_kernel [S.has_left_homology] : has_kernel S.g :=
⟨⟨⟨_, S.some_left_homology_data.hi⟩⟩⟩

lemma has_cokernel [S.has_left_homology] [has_kernel S.g] :
  has_cokernel (kernel.lift S.g S.f S.zero) :=
begin
  let h := S.some_left_homology_data,
  haveI : has_colimit (parallel_pair h.f' 0) := ⟨⟨⟨_, h.hπ'⟩⟩⟩,
  let e : parallel_pair (kernel.lift S.g S.f S.zero) 0 ≅ parallel_pair h.f' 0 :=
    parallel_pair.ext (iso.refl _)
      (is_limit.cone_point_unique_up_to_iso (kernel_is_kernel S.g) h.hi) (by tidy) (by tidy),
  exact has_colimit_of_iso e,
end

end has_left_homology

def left_homology_iso_cokernel_lift [S.has_left_homology] [has_kernel S.g]
  [has_cokernel (kernel.lift S.g S.f S.zero)] :
  S.left_homology ≅ cokernel (kernel.lift S.g S.f S.zero) :=
(left_homology_data.of_ker_of_coker S).left_homology_iso

namespace left_homology_data

lemma is_iso_i_of_zero_g (h : left_homology_data S) (hg : S.g = 0) : is_iso h.i :=
⟨⟨h.lift_K (𝟙 S.X₂) (by rw [hg, id_comp]),
    by simp only [← cancel_mono h.i, id_comp, assoc, lift_K_i, comp_id], lift_K_i _ _ _⟩⟩

end left_homology_data

end short_complex

end category_theory
