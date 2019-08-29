import group_theory.congruence algebra.associated data.equiv.algebra

/- Localizing monoids at submonoids.
   Everything is in the localization namespace to avoid having to duplicate things. -/

variables {X : Type*} [comm_monoid X] (Y : submonoid X) {Z : Type*} [comm_monoid Z]
          {α : Type*} {β : Type*} [monoid α] [monoid β] {γ : Type*} [monoid γ] 

/-- I rw this and then use abel in some proofs; I don't know the canonical way to do this. -/
lemma to_add {α} [has_mul α] : 
  @has_mul.mul α _ = @has_add.add (additive α) _ := rfl

namespace monoid_hom

def fst : α × β →* α :=
⟨λ x, x.1, rfl, λ _ _, prod.fst_mul⟩

def snd : α × β →* β :=
⟨λ x, x.2, rfl, λ _ _, prod.snd_mul⟩

end monoid_hom 

namespace submonoid

instance : comm_monoid Y :=
{ mul_comm := λ _ _, subtype.ext.2 $ mul_comm _ _, ..submonoid.to_monoid}

def r' : con (X × Y) :=
{ r := λ a b, ∃ c : Y, (c:X) * (a.1 * b.2) = c * (b.1 * a.2),
  r_iseqv :=
    ⟨λ _, ⟨1, rfl⟩, λ _ _ ⟨c, hc⟩, ⟨c, hc.symm⟩,
     λ a b c ⟨m, hm⟩ ⟨n, hn⟩, ⟨n*m*b.2,
       calc 
        ↑n * ↑m * ↑b.2 * (a.1 * ↑c.2) 
             = ↑n * (↑m * (b.1 * ↑a.2)) * ↑c.2 : by rw [←hm, to_add]; abel
         ... = ↑m * (↑n * (c.1 * ↑b.2)) * ↑a.2 : by rw [←hn, to_add]; abel
         ... = ↑n * ↑m * ↑b.2 * (c.1 * ↑a.2) : by rw to_add; abel⟩⟩,
  r_mul := λ a b c d ⟨m, hm⟩ ⟨n, hn⟩, ⟨m*n,
         calc
         ↑m * ↑n * (a.1 * c.1 * (↑b.2 * ↑d.2)) 
           = ↑n * c.1 * (↑m * (b.1 * ↑a.2)) * ↑d.2 : by rw [←hm, to_add]; abel
       ... = (↑m * (b.1 * ↑a.2)) * (↑n * (d.1 * ↑c.2)) : by rw [←hn, to_add]; abel
       ... = ↑m * ↑n * (b.1 * d.1 * (↑a.2 * ↑c.2)) : by rw to_add; abel⟩}

def r : con (X × Y) := lattice.Inf {c | ∀ y : Y, c 1 (y, y)}

end submonoid

theorem r_eq_r' : Y.r = Y.r' :=
le_antisymm
  (lattice.Inf_le $ λ _, ⟨1, by norm_num⟩) $
  lattice.le_Inf $ λ b H, (Y.r'.le_def _).2 $ λ x y ⟨t, ht⟩, by
    {rw [show x = (1*x.1, 1*x.2), by simp, show y = (1*y.1, 1*y.2), by simp],
     refine b.trans
       (show b _ (((t : X) * y.2) * x.1, (t * y.2) * x.2), from
             b.mul (H (t * y.2)) $ b.refl (x.1, x.2)) _,
     rw [mul_assoc, mul_comm _ x.1, ht, mul_comm y.1,
         mul_assoc, mul_comm y.2, ←mul_assoc, ←mul_assoc],
     exact b.mul (b.symm (H (t*x.2))) (b.refl (y.1, y.2))}
 
variables (X)

def localization := Y.r.quotient

variables {X Y}

namespace localization

lemma r_mem : ∀ y : Y, Y.r 1 (y, y) :=
λ y, by rw r_eq_r'; use 1; simp

instance : monoid (localization X Y) := con.monoid Y.r

def mk : X → Y → localization X Y := λ x y, Y.r.mk' (x, y)

@[elab_as_eliminator]
theorem ind {p : localization X Y → Prop} 
  (H : ∀ (y : X × Y), p (mk y.1 y.2)) (x) : p x :=
by rcases x; convert H x; exact prod.mk.eta.symm

@[elab_as_eliminator]
theorem induction_on {p : localization X Y → Prop} (x)
  (H : ∀ (y : X × Y), p (mk y.1 y.2)) : p x :=
ind H x

section

variables {W : submonoid Z} {A : Type*} [comm_monoid A] {B : submonoid A}

@[elab_as_eliminator]
theorem induction_on₂ {p : localization X Y → localization Z W → Prop}
  (x z) (H : ∀ (a : X × Y) (b : Z × W), p (mk a.1 a.2) (mk b.1 b.2)) : 
  p x z :=
induction_on x $ λ _, induction_on z $ λ _, H _ _

@[elab_as_eliminator]
theorem induction_on₃ 
  {p : localization X Y → localization Z W → localization A B → Prop} (x z a) 
  (H : ∀ (a : X × Y) (b : Z × W) (c : A × B), p (mk a.1 a.2) (mk b.1 b.2) (mk c.1 c.2)) :
  p x z a := 
induction_on₂ x z $ λ _ _, induction_on a $ λ _, H _ _ _

lemma exists_rep (x) : ∃ y : X × Y, mk y.1 y.2 = x :=
induction_on x $ λ y, ⟨y, rfl⟩

end

protected lemma mul_comm : ∀ x y : localization X Y, x * y = y * x :=
λ x y, con.induction_on₂ x y $ λ _ _, by rw [con.coe_mul, con.coe_mul, mul_comm]

instance : comm_monoid (localization X Y) :=
by refine { mul_comm := localization.mul_comm, ..localization.monoid}

protected lemma eq {a₁ b₁} {a₂ b₂ : Y} :
  mk a₁ a₂ = mk b₁ b₂ ↔ ∀ c : con (X × Y), (∀ y : Y, c 1 (y, y)) → c (a₁, a₂) (b₁, b₂) :=
(Y.r.eq _ _).trans $ con.mem_Inf _ _ _
 
protected lemma eq' {a₁ b₁} {a₂ b₂ : Y} :
  mk a₁ a₂ = mk b₁ b₂ ↔ ∃ c : Y, (c : X) * (a₁ * b₂) = (c:X) * (b₁ * a₂) :=
⟨λ h, exists.elim (show Y.r' (a₁, a₂) (b₁, b₂), by rw [←r_eq_r', ←con.eq]; exact h) $
  λ w hw, exists.intro w hw,
λ ⟨w, hw⟩, show ↑(a₁, a₂) = ↑(b₁, b₂), by rw [con.eq, r_eq_r']; exact ⟨w, hw⟩⟩

variables (Y)

@[elab_as_eliminator, reducible]
def lift₁ {β} (f : X × Y → β) (H : ∀ a b, Y.r a b → f a = f b) :
  localization X Y → β := λ q, con.lift_on' q f H

@[elab_as_eliminator, reducible]
def lift₂ (W : submonoid Z) {β} (f : X × Y → Z × W → β)
  (H : ∀ a b c d, Y.r a c → W.r b d → f a b = f c d) :
  localization X Y → localization Z W → β :=
λ q r, con.lift_on₂' q r (λ _ _, f _ _) $ λ _ _ _ _, H _ _ _ _

variables {Y}

lemma r_of_eq {a₁ b₁} {a₂ b₂ : Y} (h : (a₂ : X) * b₁ = b₂ * a₁) :
  mk a₁ a₂ = mk b₁ b₂ :=
localization.eq'.2 $ ⟨1, by rw [mul_comm b₁, h, mul_comm a₁]⟩

@[simp] lemma mk_self' (x : Y) : mk (x : X) x = 1 :=
localization.eq.2 $ λ c hc, c.symm (hc x)

@[simp] lemma mk_self {x} (hx : x ∈ Y) : mk x ⟨x, hx⟩ = 1 :=
mk_self' ⟨x, hx⟩

@[simp] lemma mk_mul_mk (x y) (s t : Y) :
  mk x s * mk y t = mk (x * y) (s * t) := rfl

@[simp] lemma lift_mk {β} (f : (X × Y) → β)
  (H : ∀ a b, Y.r a b → f a = f b) {x y} :
lift₁ Y f H (mk x y) = f (x, y):= rfl

def monoid_hom.of (Y) : X →* localization X Y :=
Y.r.mk'.comp ⟨λ x, (x,1), refl 1, λ _ _, by simp only [prod.mk_mul_mk, one_mul]⟩

def to_units (Y : submonoid X) : Y →* units (localization X Y) :=
⟨λ y, ⟨mk y 1, mk 1 y, by simp, by simp⟩, rfl,
 λ _ _, by ext; convert (monoid_hom.of Y).map_mul _ _⟩

@[simp] lemma to_units_mk (y) : (to_units Y y : localization X Y) = mk y 1 := rfl

@[simp] lemma mk_is_unit (y : Y) : is_unit (mk (y : X) (1 : Y)) :=
is_unit_unit $ to_units Y y

@[simp] lemma mk_is_unit' (x) (hx : x ∈ Y) : is_unit (mk x (1 : Y)) :=
is_unit_unit $ to_units Y ⟨x, hx⟩

lemma to_units_inv {y} : mk 1 y = ((to_units Y y)⁻¹ : _) := rfl

namespace monoid_hom

lemma of_eq_mk (x) : of Y x = mk x 1 := rfl

@[simp] lemma of_mul_mk (x y v) :
  of Y x * mk y v = mk (x * y) v :=
by rw [of_eq_mk, mk_mul_mk, one_mul]

lemma mk_eq_mul_mk_one (x y) :
  mk x y = of Y x * mk 1 y :=
by rw [of_mul_mk, mul_one]

@[simp] lemma mk_mul_cancel_left (x) (y : Y) :
  mk ((y : X) * x) y = of Y x :=
by rw [mk_eq_mul_mk_one, mul_comm ↑y, (of Y).map_mul, mul_assoc,
       ←mk_eq_mul_mk_one, mk_self', mul_one]

@[simp] lemma mk_mul_cancel_right (x : X) (y : Y) :
  mk (x * y) y = of Y x :=
by rw [mul_comm, mk_mul_cancel_left]

@[simp] lemma of_is_unit (y : Y) : is_unit (of Y y) :=
is_unit_unit $ to_units Y y

@[simp] lemma of_is_unit' (x) (hx : x ∈ Y) : is_unit (of Y x) :=
is_unit_unit $ to_units Y ⟨x, hx⟩

lemma to_units_map (g : localization X Y →* Z) (y) :
g (to_units Y y) = g.units_map (to_units Y y) :=
by simp only [g.coe_units_map, to_units_mk]

lemma to_units_map_inv (g : localization X Y →* Z) (y) :
g ((to_units Y y)⁻¹ : _) = ((g.units_map (to_units Y y))⁻¹ : _) :=
by rw [←g.coe_units_map, g.units_map.map_inv]

lemma mk_eq (x y) :
  mk x y = of Y x * ((to_units Y y)⁻¹ : _) :=
by rw ←to_units_inv; simp only [of_eq_mk, mk_mul_mk, mul_one, one_mul]

variables {f : X →* Z} {g : Y → units Z}

lemma restrict_map_one (H : ∀ y : Y, f y = g y) : g 1 = 1 := 
by ext; rw ←(H 1); apply f.map_one 

lemma restrict_map_mul (H : ∀ y : Y, f y = g y) (x y) : 
  g (x * y) = g x * g y := 
by ext; rw [units.coe_mul, ←(H _), ←(H _), ←(H _)]; apply f.map_mul

variables (f g)

def restrict_hom (H : ∀ y : Y, f y = g y) : Y →* units Z :=
⟨g, restrict_map_one H, restrict_map_mul H⟩

def aux (H : ∀ y : Y, f y = g y) : X × Y →* Z :=
(f.comp monoid_hom.fst).mul $ 
  (units.coe_hom Z).comp ((restrict_hom f g H).comp monoid_hom.snd).inv 

variables {f g} 

lemma rel_of_aux (H : ∀ y : Y, f y = g y) (y : Y) : (con.ker (aux f g H)) 1 (y, y) :=
show f (1 : Y) * ((g 1)⁻¹ : _) = f y * ((g y)⁻¹ : _), by 
  rw [H 1, H y]; simp [units.mul_inv]

variables (f g)

def lift' (H : ∀ y : Y, f y = g y) : localization X Y →* Z :=
Y.r.lift (aux f g H) $ λ _ _ h, (con.mem_Inf _ _ _).1 h _ $ rel_of_aux H

noncomputable def lift (H : ∀ y : Y, is_unit (f y)): localization X Y →* Z :=
lift' f _ $ λ _, classical.some_spec $ H _

variables {f g} 

@[simp] lemma lift'_mk (H : ∀ y : Y, f y = g y) (x y) :
  lift' f g H (mk x y) = f x * ↑(g y)⁻¹ := rfl

@[simp] lemma lift_mk (H : ∀ y : Y, is_unit (f y)) (x y) :
  lift f H (mk x y) = f x * ↑(classical.some (H y))⁻¹ := rfl

@[simp] lemma lift'_of (H : ∀ y : Y, f y = g y) (x : X) :
  lift' f g H (of Y x) = f x :=
show f x * ↑(g 1)⁻¹ = _, by rw [inv_eq_one.2 (restrict_map_one H), units.coe_one, mul_one]

@[simp] lemma lift_of (H : ∀ y : Y, is_unit (f y)) (x : X) :
  lift f H (of Y x) = f x := lift'_of (λ y, classical.some_spec $ H y) _

lemma lift'_comp_of (H : ∀ y : Y, f y = g y) :
  (lift' f g H).comp (of Y) = f := 
by ext; exact lift'_of H _

@[simp] lemma lift_comp_of (H : ∀ y : Y, is_unit (f y)) :
  (lift f H).comp (of Y) = f := lift'_comp_of _

@[simp] lemma lift'_apply_of (f' : localization X Y →* Z) 
  (H : ∀ y : Y, f'.comp (of Y) y = g y) : lift' (f'.comp (of Y)) g H = f' := 
begin
  ext x,
  apply induction_on x,
  intros,
  rw [lift'_mk, ←units.mul_right_inj (g y.2), mul_assoc,
      units.inv_mul, ←H y.2, mul_one, mk_eq_mul_mk_one],
  simp [of_eq_mk, (f'.map_mul _ _).symm, mk_mul_mk],
end

@[simp] lemma lift_apply_of (g : localization X Y →* Z) :
  lift (g.comp (of Y)) (λ y, is_unit_unit (g.units_map (to_units Y y))) = g :=
by rw [lift, lift'_apply_of]

protected lemma funext (f g : localization X Y →* Z)
  (h : ∀ a, f.comp (of Y) a = g.comp (of Y) a) : f = g :=
begin
  rw [←lift_apply_of f, ←lift_apply_of g],
  congr' 1,
  ext,
  convert h x,
end

variables {W : submonoid Z}

variables (f)

def map (hf : ∀ y : Y, f y ∈ W) : localization X Y →* localization Z W :=
lift' ((of W).comp f) ((to_units W).comp $ (f.comp Y.subtype).subtype_mk W hf) $ λ y, rfl

variables {f}

@[simp] lemma map_of (hf : ∀ y : Y, f y ∈ W) (x) :
  map f hf (of Y x) = of W (f x) := lift'_of _ _

@[simp] lemma map_comp_of (hf : ∀ y : Y, f y ∈ W) :
  (map f hf).comp (of Y) = (of W).comp f := lift'_comp_of _

@[simp] lemma map_mk (hf : ∀ y : Y, f y ∈ W) (x y) :
  map f hf (mk x y) = of W (f x) * ↑(to_units W ⟨(f y), hf y⟩)⁻¹ := lift'_mk _ _ _

@[simp] lemma map_id : map (monoid_hom.id X) (λ y, y.2) = monoid_hom.id (localization X Y) :=
monoid_hom.funext _ _ $ map_of _

lemma map_comp_map {A} [comm_monoid A] {V} (g : Z →* A)
  (hf : ∀ y : Y, f y ∈ W) (hg : ∀ w : W, g w ∈ V) :
  (map g hg).comp (map f hf) = map (g.comp f) (λ y, hg ⟨f y, hf y⟩) :=
monoid_hom.funext _ _ $ λ x, by simp only [monoid_hom.comp_apply, map_of]

lemma map_map {A} [comm_monoid A] {V} (g : Z →* A)
  (hf : ∀ y : Y, f y ∈ W) (hg : ∀ w : W, g w ∈ V) (x) :
  map g hg (map f hf x) = map (g.comp f) (λ y : Y, hg ⟨f y, hf y⟩) x :=
by rw ←(map_comp_map g hf hg); refl

variables (f)

lemma map_ext (g : X →* Z) (hf : ∀ y : Y, f y ∈ W) (hg : ∀ y : Y, g y ∈ W) 
  (h : f = g) (x) : map f hf x = map g hg x :=
induction_on x $ λ _, by {rw [map_mk, ←to_units_inv], congr; rw h; refl}

end monoid_hom

namespace mul_equiv

open mul_equiv

variables {X Y} (f : X →* Z) {W : submonoid Z} (g : Y → units Z)

def char_pred' (H : ∀ y : Y, f y = g y) :=
function.surjective (monoid_hom.lift' f g H) ∧ con.ker f = Y.r.prod_fst

def char_pred (H : ∀ y : Y, is_unit (f y)) :=
function.surjective (monoid_hom.lift f H) ∧ con.ker f = Y.r.prod_fst

lemma char_pred_of_equiv' (H : ∀ y : Y, f y = g y) 
  (h : localization X Y ≃* Z) (hf : h.to_monoid_hom = monoid_hom.lift' f g H) : 
  char_pred' f g H :=
⟨λ x, let ⟨p, hp⟩ := h.to_equiv.surjective x in ⟨p, by rw [←hp, ←hf]; refl⟩,
by rw ←(con.ker_eq_of_equiv h (monoid_hom.aux f g H) _ hf); ext;
   show _ ↔ f x * ↑(g 1)⁻¹ = f y * ↑(g 1)⁻¹;
   rw [con.ker_rel, units.mul_right_inj]⟩ 
 
lemma char_pred_of_equiv (H : ∀ y : Y, is_unit (f y)) (h : localization X Y ≃* Z)
  (hf : h.to_monoid_hom = monoid_hom.lift f H) : char_pred f H :=
char_pred_of_equiv' f _ (λ y, classical.some_spec (H y)) h hf

lemma ker_eq_of_char_pred'  (g : Y → units Z) (H : ∀ y : Y, f y = g y)
  (Hp : char_pred' f g H) : con.ker (monoid_hom.aux f g H) = Y.r :=
con.ext $ λ x y, 
⟨λ h, by { change f x.1 * ↑(g x.2)⁻¹ = f y.1 * ↑(g y.2)⁻¹ at h,
  rw [units.eq_mul_inv_iff_mul_eq, mul_comm, ←mul_assoc, units.mul_inv_eq_iff_eq_mul, 
      ←H _, ←H _, ←f.map_mul, ←f.map_mul, ←con.ker_rel, Hp.2] at h, 
  change Y.r _ _ at h, 
  rw r_eq_r' at h ⊢, 
  cases h with t ht,
  use t, rw mul_comm x.1, simpa using ht}, 
 λ h, (con.le_def Y.r _).1 (lattice.Inf_le $ monoid_hom.rel_of_aux H) x y h⟩

noncomputable def equiv_of_char_pred' (g : Y → units Z) (H : ∀ y : Y, f y = g y)
  (Hp : char_pred' f g H) : localization X Y ≃* Z :=
mul_equiv.trans (con.congr (ker_eq_of_char_pred' f g H Hp)).symm $
con.quotient_ker_equiv_of_surjective (monoid_hom.aux f g H) $ λ z, by
  { cases Hp.1 z with x hx, revert hx, apply con.induction_on x, 
    intros y hy, use y, rw hy.symm, refl}

noncomputable def equiv_of_char_pred (H : ∀ y : Y, is_unit (f y)) (Hp : char_pred f H) :
  (localization X Y) ≃* Z :=
equiv_of_char_pred' f (λ y, classical.some $ H y)
  (λ y, by rw [← classical.some_spec (H y)]; refl) Hp

-- going to redo this
def equiv_of_equiv (h : X ≃* Z) (H : h.to_monoid_hom.map Y = W) :
  localization X Y ≃* localization Z W :=
{ to_fun := localization.monoid_hom.map h.to_monoid_hom $
    λ (y : Y), show h y ∈ W, from H ▸ (h.to_monoid_hom.map Y).mem_coe.1 ⟨y, y.2, rfl⟩,
  inv_fun := localization.monoid_hom.map h.symm.to_monoid_hom $
    λ (w : W), let ⟨y, hym, hy⟩ := show (w : Z) ∈ h.to_monoid_hom.map Y, from H.symm ▸ w.2 in
      show h.symm w ∈ Y, by rw [hy.symm, to_monoid_hom_apply, symm_apply_apply];
        exact (submonoid.mem_coe Y).1 hym,
  left_inv := λ x, by {erw [monoid_hom.map_map,
    monoid_hom.map_ext (h.symm.to_monoid_hom.comp h.to_monoid_hom) (monoid_hom.id X)
      (λ (y : Y), show _ ∈ Y, by {convert (submonoid.mem_coe _).1 y.2, simp, refl})
      (λ (y : Y), show (y : X) ∈ Y, from y.2) (by simp) x, monoid_hom.map_id], refl},
  right_inv := λ x, by {erw [monoid_hom.map_map,
    monoid_hom.map_ext (h.to_monoid_hom.comp h.symm.to_monoid_hom) (monoid_hom.id Z)
      (λ (w : W), show _ ∈ W, by {convert (submonoid.mem_coe _).1 w.2, simp, refl})
      (λ (w : W), show (w : Z) ∈ W, from w.2) (by simp) x, monoid_hom.map_id], refl },
  map_mul' := monoid_hom.map_mul _ }

end mul_equiv

section away

variables {X Y}

@[reducible] def away (x : X) := localization X (submonoid.powers x)
@[simp] def away.inv_self (x : X) : away x := mk 1 ⟨x, 1, pow_one x⟩

variables (f : X →* Z)

@[elab_with_expected_type]
noncomputable def away.monoid_hom.lift {x : X} (hfx : is_unit (f x)) : away x →* Z :=
monoid_hom.lift' f (λ s, classical.some hfx ^ classical.some s.2) $ λ s,
by rw [units.coe_pow, ← classical.some_spec hfx,
       ← f.map_pow, classical.some_spec s.2]; refl

variables {f}

@[simp] lemma away.monoid_hom.lift_of {x : X} (hfx : is_unit (f x)) (a : X) :
  away.monoid_hom.lift f hfx (monoid_hom.of (submonoid.powers x) a) = f a :=
monoid_hom.lift'_of _ _

@[simp] lemma away.monoid_hom.lift_coe {x : X} (hfx : is_unit (f x)) (a : X) :
  away.monoid_hom.lift f hfx (monoid_hom.of (submonoid.powers x) a) = f a :=
monoid_hom.lift'_of _ _

@[simp] lemma away.monoid_hom.lift_comp_of {x : X} (hfx : is_unit (f x)) :
  (away.monoid_hom.lift f hfx).comp (monoid_hom.of (submonoid.powers x)) = f :=
monoid_hom.lift'_comp_of _

noncomputable def monoid_hom.away_to_away_right (x y : X) : away x →* away (x * y) :=
away.monoid_hom.lift (monoid_hom.of (submonoid.powers (x*y))) $
is_unit_of_mul_one _ (((monoid_hom.of _).1 y) * away.inv_self (x * y)) $ by unfold_coes;
  rw [away.inv_self, ←mul_assoc, ←monoid_hom.map_mul',
      ←mk_self (show (x*y) ∈ submonoid.powers (x*y), from ⟨1, pow_one _⟩),
      monoid_hom.mk_eq_mul_mk_one (x*y) _]; refl

end away

end localization
