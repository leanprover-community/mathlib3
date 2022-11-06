import algebra.homology.short_complex_left_homology

noncomputable theory

open category_theory category_theory.category

namespace category_theory

namespace limits

variables {C : Type*} [category C] [has_zero_morphisms C]

namespace kernel_fork

@[simp]
lemma is_limit.lift_ι {X Y : C} {f : X ⟶ Y} {c : kernel_fork f} (hc : is_limit c)
  (c' : kernel_fork f) : hc.lift c' ≫ c.ι = c'.ι :=
by apply fork.is_limit.lift_ι

@[simps]
def is_limit.of_ι_op {K X Y : C} (i : K ⟶ X) {f : X ⟶ Y}
  (w : i ≫ f = 0) (h : is_limit (kernel_fork.of_ι i w)) :
  is_colimit (cokernel_cofork.of_π i.op
    (show f.op ≫ i.op = 0, by simpa only [← op_comp, w])) :=
cokernel_cofork.is_colimit.of_π _ _
  (λ A x hx, (h.lift (kernel_fork.of_ι x.unop (quiver.hom.op_inj hx))).op)
  (λ A x hx, quiver.hom.unop_inj (is_limit.lift_ι h _))
  (λ A x hx b hb, quiver.hom.unop_inj (fork.is_limit.hom_ext h begin
    simp only [quiver.hom.unop_op, is_limit.lift_ι],
    exact quiver.hom.op_inj hb,
  end))

@[simps]
def is_limit.of_ι_unop {K X Y : Cᵒᵖ} (i : K ⟶ X) {f : X ⟶ Y}
  (w : i ≫ f = 0) (h : is_limit (kernel_fork.of_ι i w)) :
  is_colimit (cokernel_cofork.of_π i.unop
    (show f.unop ≫ i.unop = 0, by simpa only [← unop_comp, w])) :=
cokernel_cofork.is_colimit.of_π _ _
  (λ A x hx, (h.lift (kernel_fork.of_ι x.op (quiver.hom.unop_inj hx))).unop)
  (λ A x hx, quiver.hom.op_inj (is_limit.lift_ι h _))
  (λ A x hx b hb, quiver.hom.op_inj (fork.is_limit.hom_ext h begin
    simp only [quiver.hom.op_unop, is_limit.lift_ι],
    exact quiver.hom.unop_inj hb,
  end))

end kernel_fork

namespace cokernel_cofork

@[simp]
lemma is_colimit.π_desc {X Y : C} {f : X ⟶ Y} {c : cokernel_cofork f} (hc : is_colimit c)
  (c' : cokernel_cofork f) : c.π ≫ hc.desc c' = c'.π :=
by apply cofork.is_colimit.π_desc

@[simps]
def is_colimit.of_π_op {X Y Q : C} (p : Y ⟶ Q) {f : X ⟶ Y}
  (w : f ≫ p = 0) (h : is_colimit (cokernel_cofork.of_π p w)) :
  is_limit (kernel_fork.of_ι p.op
    (show p.op ≫ f.op = 0, by simpa only [← op_comp, w])) :=
kernel_fork.is_limit.of_ι _ _
  (λ A x hx, (h.desc (cokernel_cofork.of_π x.unop (quiver.hom.op_inj hx))).op)
  (λ A x hx, quiver.hom.unop_inj (is_colimit.π_desc h _))
  (λ A x hx b hb, quiver.hom.unop_inj (cofork.is_colimit.hom_ext h begin
    simp only [quiver.hom.unop_op, is_colimit.π_desc],
    exact quiver.hom.op_inj hb,
  end))

@[simps]
def is_colimit.of_π_unop {X Y Q : Cᵒᵖ} (p : Y ⟶ Q) {f : X ⟶ Y}
  (w : f ≫ p = 0) (h : is_colimit (cokernel_cofork.of_π p w)) :
  is_limit (kernel_fork.of_ι p.unop
    (show p.unop ≫ f.unop = 0, by simpa only [← unop_comp, w])) :=
kernel_fork.is_limit.of_ι _ _
  (λ A x hx, (h.desc (cokernel_cofork.of_π x.op (quiver.hom.unop_inj hx))).unop)
  (λ A x hx, quiver.hom.op_inj (is_colimit.π_desc h _))
  (λ A x hx b hb, quiver.hom.op_inj (cofork.is_colimit.hom_ext h begin
    simp only [quiver.hom.op_unop, is_colimit.π_desc],
    exact quiver.hom.unop_inj hb,
  end))

end cokernel_cofork

end limits

end category_theory

open category_theory.limits
variables {C : Type*} [category C] [has_zero_morphisms C]
  (S : short_complex C)

namespace short_complex

@[nolint has_nonempty_instance]
structure right_homology_data :=
(Q H : C)
(p : S.X₂ ⟶ Q)
(ι : H ⟶ Q)
(hp₀ : S.f ≫ p = 0)
(hp : is_colimit (cokernel_cofork.of_π p hp₀))
(hι₀ : ι ≫ hp.desc (cokernel_cofork.of_π _ S.zero) = 0)
(hι : is_limit (kernel_fork.of_ι ι hι₀))

namespace right_homology_data

@[simp]
def of_coker_of_ker [has_cokernel S.f] [has_kernel (cokernel.desc₀ S.f S.g S.zero)] :
  S.right_homology_data :=
{ Q := cokernel S.f,
  H := kernel (cokernel.desc₀ S.f S.g S.zero),
  p := cokernel.π _,
  ι := kernel.ι _,
  hp₀ := cokernel.condition _,
  hp := cokernel_is_cokernel _,
  hι₀ := kernel.condition _,
  hι := kernel_is_kernel _, }

attribute [simp, reassoc] hp₀ hι₀
variables {S} (h : right_homology_data S) {A : C}

instance : epi h.p :=
⟨λ Y l₁ l₂, cofork.is_colimit.hom_ext h.hp⟩

instance : mono h.ι :=
⟨λ Y l₁ l₂, fork.is_limit.hom_ext h.hι⟩

def desc_Q (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : h.Q ⟶ A :=
h.hp.desc (cokernel_cofork.of_π k hk)

@[simp, reassoc]
lemma p_desc_Q (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) :
  h.p ≫ h.desc_Q k hk = k :=
h.hp.fac _ walking_parallel_pair.one

@[simp]
def desc_H (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : h.H ⟶ A :=
  h.ι ≫ h.desc_Q k hk

/-- The morphism `h.Q ⟶ S.X₃` induced by `S.g : S.X₂ ⟶ S.X₃` and the fact that
`h.Q` is a cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
def g' : h.Q ⟶ S.X₃ := h.desc_Q S.g S.zero

@[simp, reassoc]
lemma p_g' : h.p ≫ h.g' = S.g :=
p_desc_Q _ _ _

@[simp, reassoc]
lemma ι_g' : h.ι ≫ h.g' = 0 := h.hι₀

/-- For `h : homology_ful_data S`, this is a restatement of `h.hι`, saying that
`ι : h.H ⟶ h.Q` is a kernel of `h.g' : h.Q ⟶ S.X₃`. -/
@[simp]
def hι' : is_limit (kernel_fork.of_ι h.ι h.ι_g') := h.hι

def lift_H (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0) :
  A ⟶ h.H :=
h.hι.lift (kernel_fork.of_ι k hk)

@[simp, reassoc]
lemma lift_H_ι (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0) :
  h.lift_H k hk ≫ h.ι = k :=
h.hι.fac (kernel_fork.of_ι k hk) walking_parallel_pair.zero

variable (S)

@[simp]
def of_colimit_cokernel_cofork (hg : S.g = 0) (c : cokernel_cofork S.f) (hc : is_colimit c) :
  S.right_homology_data :=
{ Q := c.X,
  H := c.X,
  p := c.π,
  ι := 𝟙 _,
  hp₀ := cokernel_cofork.condition _,
  hp := is_colimit.of_iso_colimit hc (cofork.ext (iso.refl _) (by tidy)),
  hι₀ := cofork.is_colimit.hom_ext hc begin
    dsimp,
    simp only [hg, id_comp, cofork.is_colimit.π_desc, cokernel_cofork.π_of_π, comp_zero],
  end,
  hι := kernel_zero _ begin
    apply cofork.is_colimit.hom_ext hc,
    dsimp,
    simp only [hg, id_comp, cofork.is_colimit.π_desc, cokernel_cofork.π_of_π, comp_zero],
  end }

@[simp]
def of_has_cokernel [has_cokernel S.f] (hg : S.g = 0) : S.right_homology_data :=
of_colimit_cokernel_cofork S hg _ (cokernel_is_cokernel _)

@[simp]
def of_limit_kernel_fork (hf : S.f = 0) (c : kernel_fork S.g) (hc : is_limit c) :
  S.right_homology_data :=
{ Q := S.X₂,
  H := c.X,
  p := 𝟙 _,
  ι := c.ι,
  hp₀ := by rw [comp_id, hf],
  hp := cokernel_zero _ hf,
  hι₀ := kernel_fork.condition _,
  hι := is_limit.of_iso_limit hc (fork.ext (iso.refl _) (by tidy)), }

@[simp]
def of_has_kernel [has_kernel S.g] (hf : S.f = 0) : S.right_homology_data :=
of_limit_kernel_fork S hf _ (kernel_is_kernel _)

@[simp]
def of_zeros (hf : S.f = 0) (hg : S.g = 0) :
  S.right_homology_data :=
{ Q := S.X₂,
  H := S.X₂,
  p := 𝟙 _,
  ι := 𝟙 _,
  hp₀ := by rw [comp_id, hf],
  hp := cokernel_zero _ hf,
  hι₀ := by { dsimp, rw [id_comp, hg], },
  hι := kernel_zero _ hg, }

end right_homology_data

class has_right_homology : Prop :=
(cond : nonempty S.right_homology_data)

def some_right_homology_data [has_right_homology S] :
  S.right_homology_data := has_right_homology.cond.some

variable {S}

lemma has_right_homology.mk' (h : S.right_homology_data) : has_right_homology S :=
⟨nonempty.intro h⟩

@[priority 100]
instance has_right_homology_of_coker_of_ker
  [has_cokernel S.f] [has_kernel (cokernel.desc₀ S.f S.g S.zero)] :
  S.has_right_homology := has_right_homology.mk' (right_homology_data.of_coker_of_ker S)

instance has_right_homology_of_has_cokernel {X Y : C} (f : X ⟶ Y) (Z : C)
  [has_cokernel f] :
  (short_complex.mk f (0 : Y ⟶ Z) comp_zero).has_right_homology :=
has_right_homology.mk' (right_homology_data.of_has_cokernel _ rfl)

instance has_right_homology_of_has_kernel {Y Z : C} (g : Y ⟶ Z) (X : C)
  [has_kernel g] :
  (short_complex.mk (0 : X ⟶ Y) g zero_comp).has_right_homology :=
has_right_homology.mk' (right_homology_data.of_has_kernel _ rfl)

instance has_right_homology_of_zeros (X Y Z : C) :
  (short_complex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).has_right_homology :=
has_right_homology.mk' (right_homology_data.of_zeros _ rfl rfl)

@[simp]
def left_homology_data.op (h : left_homology_data S) :
  right_homology_data S.op :=
{ Q := opposite.op h.K,
  H := opposite.op h.H,
  p := h.i.op,
  ι := h.π.op,
  hp₀ := quiver.hom.unop_inj h.hi₀,
  hp := kernel_fork.is_limit.of_ι_op _ _ h.hi,
  hι₀ := quiver.hom.unop_inj h.hπ₀,
  hι := cokernel_cofork.is_colimit.of_π_op _ _ h.hπ, }

@[simp] lemma left_homology_data.op_p (h : left_homology_data S) : h.op.p = h.i.op := rfl
@[simp] lemma left_homology_data.op_ι (h : left_homology_data S) : h.op.ι = h.π.op := rfl
@[simp] lemma left_homology_data.op_g' (h : left_homology_data S) : h.op.g' = h.f'.op := rfl

@[simp]
def right_homology_data.op (h : right_homology_data S) :
  left_homology_data S.op :=
{ K := opposite.op h.Q,
  H := opposite.op h.H,
  i := h.p.op,
  π := h.ι.op,
  hi₀ := quiver.hom.unop_inj h.hp₀,
  hi := cokernel_cofork.is_colimit.of_π_op _ _ h.hp,
  hπ₀ := quiver.hom.unop_inj h.hι₀,
  hπ := kernel_fork.is_limit.of_ι_op _ _ h.hι, }

@[simp] lemma right_homology_data.op_i (h : right_homology_data S) : h.op.i = h.p.op := rfl
@[simp] lemma right_homology_data.op_π (h : right_homology_data S) : h.op.π = h.ι.op := rfl
@[simp] lemma right_homology_data.op_f' (h : right_homology_data S) : h.op.f' = h.g'.op := rfl

section

variable {S' : short_complex Cᵒᵖ}

@[simp]
def left_homology_data.unop (h : left_homology_data S') :
  right_homology_data S'.unop :=
{ Q := opposite.unop h.K,
  H := opposite.unop h.H,
  p := h.i.unop,
  ι := h.π.unop,
  hp₀ := quiver.hom.op_inj h.hi₀,
  hp := kernel_fork.is_limit.of_ι_unop _ _ h.hi,
  hι₀ := quiver.hom.op_inj h.hπ₀,
  hι := cokernel_cofork.is_colimit.of_π_unop _ _ h.hπ, }

@[simp] lemma left_homology_data.unop_p (h : left_homology_data S') : h.unop.p = h.i.unop := rfl
@[simp] lemma left_homology_data.unop_ι (h : left_homology_data S') : h.unop.ι = h.π.unop := rfl
@[simp] lemma left_homology_data.unop_g' (h : left_homology_data S') : h.unop.g' = h.f'.unop := rfl

@[simp]
def right_homology_data.unop (h : right_homology_data S') :
  left_homology_data S'.unop :=
{ K := opposite.unop h.Q,
  H := opposite.unop h.H,
  i := h.p.unop,
  π := h.ι.unop,
  hi₀ := quiver.hom.op_inj h.hp₀,
  hi := cokernel_cofork.is_colimit.of_π_unop _ _ h.hp,
  hπ₀ := quiver.hom.op_inj h.hι₀,
  hπ := kernel_fork.is_limit.of_ι_unop _ _ h.hι, }

@[simp] lemma right_homology_data.unop_i (h : right_homology_data S') : h.unop.i = h.p.unop := rfl
@[simp] lemma right_homology_data.unop_π (h : right_homology_data S') : h.unop.π = h.ι.unop := rfl
@[simp] lemma right_homology_data.unop_f' (h : right_homology_data S') :
  h.unop.f' = h.g'.unop := rfl

end

variables {S₁ S₂ S₃ : short_complex C} (φ : S₁ ⟶ S₂)
  (h₁ : S₁.right_homology_data) (h₂ : S₂.right_homology_data)

structure right_homology_map_data :=
(φQ : h₁.Q ⟶ h₂.Q)
(φH : h₁.H ⟶ h₂.H)
(commp : h₁.p ≫ φQ = φ.τ₂ ≫ h₂.p)
(commg' : h₁.g' ≫ φ.τ₃ = φQ ≫ h₂.g')
(commι : h₁.ι ≫ φQ = φH ≫ h₂.ι)

namespace right_homology_map_data

attribute [reassoc] commp commg' commι

@[simps]
def id (h : S.right_homology_data) : right_homology_map_data (𝟙 S) h h :=
{ φQ := 𝟙 _,
  φH := 𝟙 _,
  commp := by simp only [id_τ₂, comp_id, id_comp],
  commg' := by simp only [comp_id, id_τ₃, id_comp],
  commι := by simp only [comp_id, id_comp], }

@[simps]
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.right_homology_data}
  {h₂ : S₂.right_homology_data} {h₃ : S₃.right_homology_data}
  (ψ : right_homology_map_data φ h₁ h₂) (ψ' : right_homology_map_data φ' h₂ h₃) :
  right_homology_map_data (φ ≫ φ') h₁ h₃ :=
{ φQ := ψ.φQ ≫ ψ'.φQ,
  φH := ψ.φH ≫ ψ'.φH,
  commp := by simp only [comp_τ₂, assoc, ψ.commp_assoc, ψ'.commp],
  commg' := by simp only [comp_τ₃, assoc, ψ.commg'_assoc, ψ'.commg'],
  commι := by simp only [assoc, ψ.commι_assoc, ψ'.commι], }

instance : subsingleton (right_homology_map_data φ h₁ h₂) :=
⟨begin
  rintros ⟨φQ₁, φH₁, commp₁, commg'₁, commι₁⟩ ⟨φQ₂, φH₂, commp₂, commg'₂, commι₂⟩,
  have hQ : φQ₁ = φQ₂ := by rw [← cancel_epi h₁.p, commp₁, commp₂],
  have hH : φH₁ = φH₂ := by rw [← cancel_mono h₂.ι, ← commι₁, ← commι₂, hQ],
  simp only,
  split; assumption,
end⟩

instance : inhabited (right_homology_map_data φ h₁ h₂) :=
⟨begin
  let φQ : h₁.Q ⟶ h₂.Q := h₁.desc_Q (φ.τ₂ ≫ h₂.p)
    (by rw [← φ.comm₁₂_assoc, h₂.hp₀, comp_zero]),
  have commp : h₁.p ≫ φQ = φ.τ₂ ≫ h₂.p := right_homology_data.p_desc_Q _ _ _,
  have commg' : h₁.g' ≫ φ.τ₃ = φQ ≫ h₂.g',
  { simp only [← cancel_epi h₁.p, assoc, right_homology_data.p_desc_Q_assoc,
      right_homology_data.p_g'_assoc, right_homology_data.p_g', φ.comm₂₃], },
  let φH : h₁.H ⟶ h₂.H := h₂.lift_H (h₁.ι ≫ φQ)
    (by rw [assoc, ← commg', h₁.ι_g'_assoc, zero_comp]),
  have commι : h₁.ι ≫ φQ = φH ≫ h₂.ι := by rw right_homology_data.lift_H_ι,
  exact ⟨φQ, φH, commp, commg', commι⟩,
end⟩

instance : unique (right_homology_map_data φ h₁ h₂) := unique.mk' _

end right_homology_map_data

@[simps]
def left_homology_map_data.op {S₁ S₂ : short_complex C} {φ : S₁ ⟶ S₂}
  {h₁ : S₁.left_homology_data} {h₂ : S₂.left_homology_data}
  (ψ : left_homology_map_data φ h₁ h₂) :
  right_homology_map_data (op_map φ) h₂.op h₁.op :=
{ φQ := ψ.φK.op,
  φH := ψ.φH.op,
  commp := by simp only [op_map_τ₂, ← op_comp, left_homology_data.op_p, ψ.commi],
  commg' := by simp only [left_homology_data.op_g', op_map_τ₃, ← op_comp, ψ.commf'],
  commι := by simp only [left_homology_data.op_ι, ← op_comp, ψ.commπ], }

@[simps]
def left_homology_map_data.unop {S₁ S₂ : short_complex Cᵒᵖ} {φ : S₁ ⟶ S₂}
  {h₁ : S₁.left_homology_data} {h₂ : S₂.left_homology_data}
  (ψ : left_homology_map_data φ h₁ h₂) :
  right_homology_map_data (unop_map φ) h₂.unop h₁.unop :=
{ φQ := ψ.φK.unop,
  φH := ψ.φH.unop,
  commp := by simp only [unop_map_τ₂, ← unop_comp, left_homology_data.unop_p, ψ.commi],
  commg' := by simp only [left_homology_data.unop_g', unop_map_τ₃, ← unop_comp, ψ.commf'],
  commι := by simp only [left_homology_data.unop_ι, ← unop_comp, ψ.commπ], }

@[simps]
def right_homology_map_data.op {S₁ S₂ : short_complex C} {φ : S₁ ⟶ S₂}
  {h₁ : S₁.right_homology_data} {h₂ : S₂.right_homology_data}
  (ψ : right_homology_map_data φ h₁ h₂) :
  left_homology_map_data (op_map φ) h₂.op h₁.op :=
{ φK := ψ.φQ.op,
  φH := ψ.φH.op,
  commi := by simp only [right_homology_data.op_i, op_map_τ₂, ← op_comp, ψ.commp],
  commf' := by simp only [right_homology_data.op_f', op_map_τ₁, ← op_comp, ψ.commg'],
  commπ := by { simp only [right_homology_data.op_π, ← op_comp, ψ.commι], }, }

@[simps]
def right_homology_map_data.unop {S₁ S₂ : short_complex Cᵒᵖ} {φ : S₁ ⟶ S₂}
  {h₁ : S₁.right_homology_data} {h₂ : S₂.right_homology_data}
  (ψ : right_homology_map_data φ h₁ h₂) :
  left_homology_map_data (unop_map φ) h₂.unop h₁.unop :=
{ φK := ψ.φQ.unop,
  φH := ψ.φH.unop,
  commi := by simp only [right_homology_data.unop_i, unop_map_τ₂, ← unop_comp, ψ.commp],
  commf' := by simp only [right_homology_data.unop_f', unop_map_τ₁, ← unop_comp, ψ.commg'],
  commπ := by { simp only [right_homology_data.unop_π, ← unop_comp, ψ.commι], }, }

end short_complex
