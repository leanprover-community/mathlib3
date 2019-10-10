import group_theory.congruence algebra.associated data.equiv.algebra tactic.abel

local infix ` • ` := add_monoid.smul
/- Localizing monoids at submonoids.
   Everything is in the localization namespace to avoid having to duplicate things. -/

variables {X : Type*}
/-- I rw this and then use abel in some proofs; I don't know the canonical way to do this. -/
lemma to_add {α} [has_mul α] :
  @has_mul.mul α _ = @has_add.add (additive α) _ := rfl

namespace add_submonoid

/-- An alternate form of the congruence relation on X × Y, X an add_comm_monoid and Y an
    add_submonoid of X, whose quotient is the localization of X at Y. -/
def r' [add_comm_monoid X] (Y : add_submonoid X) :
  add_con (X × Y) :=
{ r := λ a b, ∃ c : Y, (c:X) + (a.1 + b.2) = c + (b.1 + a.2),
  iseqv :=
    ⟨λ _, ⟨0, rfl⟩, λ _ _ ⟨c, hc⟩, ⟨c, hc.symm⟩,
     λ a b c ⟨m, hm⟩ ⟨n, hn⟩, ⟨n + m + b.2,
       calc
        ↑n + ↑m + ↑b.2 + (a.1 + ↑c.2)
             = ↑n + (↑m + (b.1 + ↑a.2)) + ↑c.2 : by rw ←hm; abel
         ... = ↑m + (↑n + (c.1 + ↑b.2)) + ↑a.2 : by rw ←hn; abel
         ... = ↑n + ↑m + ↑b.2 + (c.1 + ↑a.2) : by abel⟩⟩,
  add' := λ a b c d ⟨m, hm⟩ ⟨n, hn⟩, ⟨m + n,
         calc
         ↑m + ↑n + (a.1 + c.1 + (↑b.2 + ↑d.2))
           = ↑n + c.1 + (↑m + (b.1 + ↑a.2)) + ↑d.2 : by rw ←hm; abel
       ... = (↑m + (b.1 + ↑a.2)) + (↑n + (d.1 + ↑c.2)) : by rw ←hn; abel
       ... = ↑m + ↑n + (b.1 + d.1 + (↑a.2 + ↑c.2)) : by abel⟩ }

end add_submonoid

variables [comm_monoid X] (Y : submonoid X) {Z : Type*} [comm_monoid Z]
          {α : Type*} {β : Type*} [monoid α] [monoid β] {γ : Type*} [monoid γ]

namespace submonoid

/-- An alternate form of the congruence relation on X × Y, X a comm_monoid and Y a submonoid
    of X, whose quotient is the localization of X at Y. -/
def r' : con (X × Y) :=
{ r := λ a b, ∃ c : Y, (c:X) * (a.1 * b.2) = c * (b.1 * a.2),
  iseqv :=
    ⟨λ _, ⟨1, rfl⟩, λ _ _ ⟨c, hc⟩, ⟨c, hc.symm⟩,
     λ a b c ⟨m, hm⟩ ⟨n, hn⟩, ⟨n*m*b.2,
       calc
        ↑n * ↑m * ↑b.2 * (a.1 * ↑c.2)
             = ↑n * (↑m * (b.1 * ↑a.2)) * ↑c.2 : by rw [←hm, to_add]; abel
         ... = ↑m * (↑n * (c.1 * ↑b.2)) * ↑a.2 : by rw [←hn, to_add]; abel
         ... = ↑n * ↑m * ↑b.2 * (c.1 * ↑a.2) : by rw to_add; abel⟩⟩,
  mul' := λ a b c d ⟨m, hm⟩ ⟨n, hn⟩, ⟨m*n,
         calc
         ↑m * ↑n * (a.1 * c.1 * (↑b.2 * ↑d.2))
           = ↑n * c.1 * (↑m * (b.1 * ↑a.2)) * ↑d.2 : by rw [←hm, to_add]; abel
       ... = (↑m * (b.1 * ↑a.2)) * (↑n * (d.1 * ↑c.2)) : by rw [←hn, to_add]; abel
       ... = ↑m * ↑n * (b.1 * d.1 * (↑a.2 * ↑c.2)) : by rw to_add; abel⟩}

attribute [to_additive add_submonoid.r'] submonoid.r'

/-- The congruence relation on X × Y, X a comm_monoid and Y a submonoid of X, whose
    quotient is the localization of X at Y. -/
@[to_additive "The congruence relation on X × Y, X an add_comm_monoid and Y an add_submonoid of X, whose quotient is the localization of X at Y."]
def r : con (X × Y) := lattice.Inf {c | ∀ y : Y, c 1 (y, y)}

/-- The infimum form and the explicit form of the congruence relation defining the localization
    of a comm_monoid at a submonoid are equivalent. -/
@[to_additive "The infimum form and the explicit form of the congruence relation defining the localization of an add_comm_monoid at an add_submonoid are equivalent."]
theorem r_eq_r' : Y.r = Y.r' :=
le_antisymm
  (lattice.Inf_le $ λ _, ⟨1, by norm_num⟩) $
  lattice.le_Inf $ λ b H, con.le_def.2 $ λ x y ⟨t, ht⟩, by
    {rw [show x = (1 * x.1, 1 * x.2), by simp, show y = (1 * y.1, 1 * y.2), by simp],
     refine b.trans
       (show b _ (((t : X) * y.2) * x.1, (t * y.2) * x.2), from
             b.mul (H (t * y.2)) $ b.refl (x.1, x.2)) _,
     rw [mul_assoc, mul_comm _ x.1, ht, mul_comm y.1,
         mul_assoc, mul_comm y.2, ←mul_assoc, ←mul_assoc],
     exact b.mul (b.symm (H (t*x.2))) (b.refl (y.1, y.2))}

end submonoid

variables (X)

/-- The localization of a comm_monoid at one of its submonoids. -/
@[to_additive add_localization "The localization of an add_comm_monoid at one of its submonoids."]
def localization := Y.r.quotient

variables {X Y}

namespace localization

/-- For all y ∈ Y, a submonoid of a comm_monoid X, (1, 1) ≈ (y, y) under the relation defining the
    localization of X at Y. -/
@[to_additive "For all y ∈ Y, a submonoid of an add_comm_monoid X, (0, 0) ≈ (y, y) under the relation defining the localization of X at Y."]
lemma r_mem : ∀ y : Y, Y.r 1 (y, y) :=
λ y, by rw Y.r_eq_r'; use 1; simp

/-- The localization of a comm_monoid at a submonoid is a monoid. -/
@[to_additive add_monoid "The localization of an add_comm_monoid at a submonoid is an add_monoid."]
instance : monoid (localization X Y) := con.monoid Y.r

/-- Given a comm_monoid X and submonoid Y, sends x ∈ X, y ∈ Y to the equivalence class of (x, y) in
    the localization of X at Y. -/
@[to_additive "Given an add_comm_monoid X and submonoid Y, sends x ∈ X, y ∈ Y to the equivalence class of (x, y) in the localization of X at Y."]
def mk : X → Y → localization X Y := λ x y, Y.r.mk' (x, y)

/-- Version of quotient.ind suited for localizations of comm_monoids at submonoids. -/
@[elab_as_eliminator, to_additive "Version of quotient.ind specialized for localizations of add_comm_monoids at submonoids."]
theorem ind {p : localization X Y → Prop}
  (H : ∀ (y : X × Y), p (mk y.1 y.2)) (x) : p x :=
by rcases x; convert H x; exact prod.mk.eta.symm

/-- Version of quotient.induction_on suited for localizations of comm_monoids at submonoids. -/
@[elab_as_eliminator, to_additive "Version of quotient.induction_on specialized for localizations of add_comm_monoids at submonoids."]
theorem induction_on {p : localization X Y → Prop} (x)
  (H : ∀ (y : X × Y), p (mk y.1 y.2)) : p x :=
ind H x

/-- Version of quotient.exists_rep suited for localizations of comm_monoids at submonoids. -/
@[to_additive "Version of quotient.exists_rep specialized for localizations of add_comm_monoids at submonoids."]
lemma exists_rep (x) : ∃ y : X × Y, mk y.1 y.2 = x :=
induction_on x $ λ y, ⟨y, rfl⟩

/-- Multiplication in the localization of a comm_monoid at a submonoid is commutative. -/
@[to_additive "Addition in the localization of an add_comm_monoid at a submonoid is commutative."]
protected lemma mul_comm : ∀ x y : localization X Y, x * y = y * x :=
λ x y, quotient.induction_on₂' x y $ λ a b, show quotient.mk' _ = _, by rw mul_comm; refl

/-- The localization of a comm_monoid at a submonoid is a comm_monoid. -/
@[to_additive "The localization of an add_comm_monoid at a submonoid is an add_comm_monoid."]
instance : comm_monoid (localization X Y) :=
by refine { mul_comm := localization.mul_comm, ..localization.monoid}

/-- Version of quotient.eq suited for localizations of comm_monoids at submonoids using the infimum
    form of the localization relation. -/
@[to_additive "Version of quotient.eq suited for localizations of add_comm_monoids at submonoids using the infimum form of the localization relation."]
protected lemma eq {a₁ b₁} {a₂ b₂ : Y} :
  mk a₁ a₂ = mk b₁ b₂ ↔ ∀ c : con (X × Y), (∀ y : Y, c 1 (y, y)) → c (a₁, a₂) (b₁, b₂) :=
(Y.r.eq _ _).trans $ iff.rfl

/-- Version of quotient.eq suited for localizations of comm_monoids at submonoids using the explicit
    form of the localization relation. -/
@[to_additive "Version of quotient.eq suited for localizations of add_comm_monoids at submonoids using the infimum form of the localization relation."]
protected lemma eq' {a₁ b₁} {a₂ b₂ : Y} :
  mk a₁ a₂ = mk b₁ b₂ ↔ ∃ c : Y, (c : X) * (a₁ * b₂) = (c:X) * (b₁ * a₂) :=
⟨λ h, exists.elim (show Y.r' (a₁, a₂) (b₁, b₂), by rw [←Y.r_eq_r', ←con.eq]; exact h) $
  λ w hw, exists.intro w hw,
λ ⟨w, hw⟩, show ↑(a₁, a₂) = ↑(b₁, b₂), by rw [con.eq, Y.r_eq_r']; exact ⟨w, hw⟩⟩

/-- Version of quotient.sound for the special case of the coefficient from the submonoid of a
    comm_monoid required in the explicit form of the localization relation is 1. -/
@[to_additive "Version of quotient.sound for the special case of the coefficient from the submonoid of an add_comm_monoid required in the explicit form of the localization relation is 0."]
lemma r_of_eq {a₁ b₁} {a₂ b₂ : Y} (h : (a₂ : X) * b₁ = b₂ * a₁) :
  mk a₁ a₂ = mk b₁ b₂ :=
localization.eq'.2 $ ⟨1, by rw [mul_comm b₁, h, mul_comm a₁]⟩

/-- Given a comm_monoid X and y ∈ Y, a submonoid, (y, y) is represented by 1 in the localization
    of X at Y. -/
@[simp, to_additive "Given an add_comm_monoid X and y ∈ Y, a submonoid, (y, y) is represented by 0 in the localization of X at Y."]
lemma mk_self' (x : Y) : mk (x : X) x = 1 :=
localization.eq.2 $ λ c hc, c.symm (hc x)

/-- Given a comm_monoid X and y ∈ Y, a submonoid, (y, y) is represented by 1 in the localization
    of X at Y. -/
@[simp, to_additive "Given an add_comm_monoid X and y ∈ Y, a submonoid, (y, y) is represented by 0 in the localization of X at Y."]
lemma mk_self {x} (hx : x ∈ Y) : mk x ⟨x, hx⟩ = 1 :=
mk_self' ⟨x, hx⟩

/-- Given a comm_monoid X and submonoid Y, the natural map from X × Y to the localization of X at Y
    prerserves multiplication (by definition). -/
@[simp, to_additive "Given an add_comm_monoid X and submonoid Y, the natural map from X × Y to the localization of X at Y prerserves addition (by definition)."]
lemma mk_mul_mk (x y) (s t : Y) :
  mk x s * mk y t = mk (x * y) (s * t) := rfl

/-- Definition of the function on the localization of a comm_monoid at a submonoid induced by a
    function that is constant on the equivalence classes of the localization relation. -/
@[simp, to_additive "Definition of the function on the localization of a comm_monoid at a submonoid induced by a function that is constant on the equivalence classes of the localization relation."]
lemma lift_mk {β} (f : (X × Y) → β)
  (H : ∀ a b, Y.r a b → f a = f b) {x y} :
con.lift_on (mk x y) f H = f (x, y) := rfl

/-- Natural homomorphism sending x ∈ X, X a comm_monoid, to the equivalence class of (x, 1) in the
    localization of X at a submonoid. -/
@[to_additive add_localization.add_monoid_hom.of "Natural homomorphism sending x ∈ X, X an add_comm_monoid, to the equivalence class of (x, 0) in the localization of X at a submonoid."]
--                ^ hmmm
def monoid_hom.of (Y) : X →* localization X Y :=
Y.r.mk'.comp ⟨λ x, (x,1), refl 1, λ _ _, by simp only [prod.mk_mul_mk, one_mul]⟩

/-- Natural homomorphism sending y ∈ Y, Y a submonoid of a comm_monoid X, to the units of the
    localization of X at Y (mapping y to the equivalence class of (y, 1). -/
@[to_additive to_add_units "Natural homomorphism sending y ∈ Y, Y a submonoid of an add_comm_monoid X, to the units of the localization of X at Y (mapping y to the equivalence class of (y, 0)."]
def to_units (Y : submonoid X) : Y →* units (localization X Y) :=
⟨λ y, ⟨mk y 1, mk 1 y, by simp, by simp⟩, by simp; refl,
 λ _ _, by ext; convert (monoid_hom.of Y).map_mul _ _⟩

/-- Definition of the natural homomorphism from a submonoid Y of a comm_monoid X to the units
    of the localization of X at Y. -/
@[simp, to_additive to_add_units_mk "Definition of the natural homomorphism from a submonoid Y of an add_comm_monoid X to the units of the localization of X at Y."]
lemma to_units_mk (y) : (to_units Y y : localization X Y) = mk y 1 := rfl

@[simp, to_additive mk_is_add_unit]
lemma mk_is_unit (y : Y) : is_unit (mk (y : X) (1 : Y)) :=
is_unit_unit $ to_units Y y

@[simp, to_additive mk_is_add_unit']
lemma mk_is_unit' (x) (hx : x ∈ Y) : is_unit (mk x (1 : Y)) :=
is_unit_unit $ to_units Y ⟨x, hx⟩

@[to_additive to_add_units_neg] lemma to_units_inv {y} : mk 1 y = ↑(to_units Y y)⁻¹ := rfl

open localization.monoid_hom

@[to_additive]
lemma of_eq_mk (x) : of Y x = mk x 1 := rfl

@[simp, to_additive]
lemma of_mul_mk (x y v) :
  of Y x * mk y v = mk (x * y) v :=
by rw [of_eq_mk, mk_mul_mk, one_mul]

@[to_additive]
lemma mk_eq_mul_mk_one (x y) :
  mk x y = of Y x * mk 1 y :=
by rw [of_mul_mk, mul_one]

@[simp, to_additive]
lemma mk_mul_cancel_left (x) (y : Y) :
  mk ((y : X) * x) y = of Y x :=
by rw [mk_eq_mul_mk_one, mul_comm ↑y, (of Y).map_mul, mul_assoc,
       ←mk_eq_mul_mk_one, mk_self', mul_one]

@[simp, to_additive]
lemma mk_mul_cancel_right (x : X) (y : Y) :
  mk (x * y) y = of Y x :=
by rw [mul_comm, mk_mul_cancel_left]

@[simp, to_additive]
lemma of_is_unit (y : Y) : is_unit (of Y y) :=
is_unit_unit $ to_units Y y

@[simp, to_additive of_is_add_unit']
lemma of_is_unit' (x) (hx : x ∈ Y) : is_unit (of Y x) :=
is_unit_unit $ to_units Y ⟨x, hx⟩

@[to_additive to_add_units_map]
lemma to_units_map (g : localization X Y →* Z) (y) :
g (to_units Y y) = units.map g (to_units Y y) :=
by simp only [units.coe_map, to_units_mk]

@[to_additive to_add_units_map_neg]
lemma to_units_map_inv (g : localization X Y →* Z) (y) :
g ↑(to_units Y y)⁻¹ = ↑(units.map g (to_units Y y))⁻¹ :=
by rw [←units.coe_map, (units.map g).map_inv]

@[to_additive]
lemma mk_eq (x y) :
  mk x y = of Y x * ↑(to_units Y y)⁻¹ :=
by rw ←to_units_inv; simp only [of_eq_mk, mk_mul_mk, mul_one, one_mul]

variables {f : X →* Z} {g : Y → units Z}

@[to_additive]
lemma restrict_map_one (H : ∀ y : Y, f y = g y) : g 1 = 1 :=
by ext; rw ←(H 1); apply f.map_one

@[to_additive]
lemma restrict_map_mul (H : ∀ y : Y, f y = g y) (x y) :
  g (x * y) = g x * g y :=
by ext; rw [units.coe_mul, ←H _, ←H _, ←H _]; apply f.map_mul

variables (f g)

@[to_additive]
def restrict_hom (H : ∀ y : Y, f y = g y) : Y →* units Z :=
⟨g, restrict_map_one H, restrict_map_mul H⟩

@[to_additive]
def aux (H : ∀ y : Y, f y = g y) : X × Y →* Z :=
(f.comp prod.monoid_hom.fst).mul $
  (units.coe_hom Z).comp ((restrict_hom f g H).comp prod.monoid_hom.snd).inv

variables {f g}

@[to_additive]
lemma rel_of_aux (H : ∀ y : Y, f y = g y) (y : Y) :
  (con.ker (aux f g H)) 1 (y, y) :=
show f (1 : Y) * ↑(g 1)⁻¹ = f y * ↑(g y)⁻¹, by rw [H 1, H y]; simp [units.mul_inv]

variables (f g)

@[to_additive add_localization.add_monoid_hom.lift']
def monoid_hom.lift' (H : ∀ y : Y, f y = g y) : localization X Y →* Z :=
Y.r.lift (aux f g H) $ λ _ _ h, h _ $ rel_of_aux H

@[to_additive add_localization.add_monoid_hom.lift]
noncomputable def monoid_hom.lift (H : ∀ y : Y, is_unit (f y)): localization X Y →* Z :=
monoid_hom.lift' f _ $ λ _, classical.some_spec $ H _

open localization.monoid_hom

variables {f g}

@[simp, to_additive add_localization.add_monoid_hom.lift'_mk]
lemma monoid_hom.lift'_mk (H : ∀ y : Y, f y = g y) (x y) :
  lift' f g H (mk x y) = f x * ↑(g y)⁻¹ := rfl

@[simp, to_additive add_localization.add_monoid_hom.lift_mk]
lemma monoid_hom.lift_mk (H : ∀ y : Y, is_unit (f y)) (x y) :
  lift f H (mk x y) = f x * ↑(classical.some (H y))⁻¹ := rfl

@[simp, to_additive]
lemma lift'_of (H : ∀ y : Y, f y = g y) (x : X) :
  lift' f g H (of Y x) = f x :=
show f x * ↑(g 1)⁻¹ = _, by rw [inv_eq_one.2 (restrict_map_one H), units.coe_one, mul_one]

@[simp, to_additive]
lemma lift_of (H : ∀ y : Y, is_unit (f y)) (x : X) :
  lift f H (of Y x) = f x := lift'_of (λ y, classical.some_spec $ H y) _

@[to_additive]
lemma lift'_comp_of (H : ∀ y : Y, f y = g y) :
  (lift' f g H).comp (of Y) = f :=
by ext; exact lift'_of H _

@[simp, to_additive]
lemma lift_comp_of (H : ∀ y : Y, is_unit (f y)) :
  (lift f H).comp (of Y) = f := lift'_comp_of _

@[simp, to_additive add_localization.add_monoid_hom.lift'_apply_of]
lemma monoid_hom.lift'_apply_of (f' : localization X Y →* Z)
  (H : ∀ y : Y, f'.comp (of Y) y = g y) : lift' (f'.comp (of Y)) g H = f' :=
begin
  ext x,
  apply induction_on x,
  intros,
  rw [monoid_hom.lift'_mk, ←units.mul_right_inj (g y.2), mul_assoc, units.inv_mul, ←H y.2,
      mul_one, mk_eq_mul_mk_one],
  show f' _ = f' (mk _ _ * _) * f' (mk _ _),
  rw [←f'.map_mul, mk_mul_mk, mk_mul_mk],
  simp only [mul_one, mk_mul_cancel_right, one_mul],
end

@[simp, to_additive add_localization.add_monoid_hom.lift_apply_of]
lemma monoid_hom.lift_apply_of (g : localization X Y →* Z) :
  lift (g.comp (of Y)) (λ y, is_unit_unit (units.map g (to_units Y y))) = g :=
monoid_hom.lift'_apply_of _ _

@[to_additive add_localization.add_monoid_hom.funext]
protected lemma monoid_hom.funext (f g : localization X Y →* Z)
  (h : ∀ a, f.comp (of Y) a = g.comp (of Y) a) : f = g :=
begin
  rw [←monoid_hom.lift_apply_of f, ←monoid_hom.lift_apply_of g],
  congr' 1,
  ext,
  convert h x,
end

variables {W : submonoid Z}

variables (f)

@[to_additive add_localization.add_monoid_hom.map]
def monoid_hom.map (hf : ∀ y : Y, f y ∈ W) : localization X Y →* localization Z W :=
lift' ((of W).comp f) ((to_units W).comp $ (f.comp Y.subtype).subtype_mk W hf) $ λ y, rfl

open localization.monoid_hom

variables {f}

@[to_additive map_add_units]
lemma map_units (hf : ∀ y : Y, f y ∈ W) (y : Y) : is_unit (of W (f y)) :=
⟨to_units W ⟨f y, hf y⟩, rfl⟩

variables (f)

@[to_additive]
lemma map_eq (hf : ∀ y : Y, f y ∈ W) :
  map f hf = lift ((of W).comp f) (λ y, ⟨to_units W ⟨f y, hf y⟩, rfl⟩) :=
by rw map; congr; ext; erw ←classical.some_spec (map_units hf x); refl

variables {f}

@[simp, to_additive]
lemma map_of (hf : ∀ y : Y, f y ∈ W) (x) :
  map f hf (of Y x) = of W (f x) := lift'_of _ _

@[simp, to_additive]
lemma map_comp_of (hf : ∀ y : Y, f y ∈ W) :
  (map f hf).comp (of Y) = (of W).comp f := lift'_comp_of _

@[simp, to_additive]
lemma map_mk (hf : ∀ y : Y, f y ∈ W) (x y) :
  map f hf (mk x y) = of W (f x) * ↑(to_units W ⟨(f y), hf y⟩)⁻¹ := lift'_mk _ _ _

@[simp, to_additive]
lemma map_id :
  map (monoid_hom.id X) (λ y, y.2) = monoid_hom.id (localization X Y) :=
monoid_hom.funext _ _ $ map_of _

@[to_additive]
lemma map_comp_map {A} [comm_monoid A] {V} {g : Z →* A}
  (hf : ∀ y : Y, f y ∈ W) (hg : ∀ w : W, g w ∈ V) :
  (map g hg).comp (map f hf) = map (g.comp f) (λ y, hg ⟨f y, hf y⟩) :=
monoid_hom.funext _ _ $ λ x, by simp only [map_of, monoid_hom.comp_apply]

@[to_additive]
lemma map_map {A} [comm_monoid A] {V} {g : Z →* A}
  (hf : ∀ y : Y, f y ∈ W) (hg : ∀ w : W, g w ∈ V) (x) :
  map g hg (map f hf x) = map (g.comp f) (λ y : Y, hg ⟨f y, hf y⟩) x :=
by rw ←map_comp_map hf hg; refl

variables (f)

@[to_additive]
lemma map_ext (g : X →* Z) (hf : ∀ y : Y, f y ∈ W) (hg : ∀ y : Y, g y ∈ W)
  (h : f = g) (x) : map f hf x = map g hg x :=
induction_on x $ λ _, by {rw [map_mk, ←to_units_inv], congr; rw h; refl}

open mul_equiv localization.monoid_hom

variables {X Y} (g)

@[to_additive]
lemma ker_of_eq {x y} : con.ker (of Y) x y ↔ Y.r (x, 1) (y, 1) :=
by rw [con.ker_rel, ←con.eq]; refl

@[to_additive]
def char_pred' (H : ∀ y : Y, f y = g y) :=
function.surjective (lift' f g H) ∧ con.ker f = con.ker (of Y)

@[to_additive]
def char_pred (H : ∀ y : Y, is_unit (f y)) :=
function.surjective (lift f H) ∧ con.ker f = con.ker (of Y)

@[to_additive]
lemma char_pred_of_mul_equiv' (H : ∀ y : Y, f y = g y) (h : localization X Y ≃* Z)
  (hf : (h : _ → Z) = lift' f g H) : char_pred' f g H :=
⟨λ x, let ⟨p, hp⟩ := h.to_equiv.surjective x in ⟨p, by rw [←hp, ←hf]; refl⟩,
by ext; rw [ker_of_eq, ←con.ker_eq_lift_of_injective Y.r _ (λ _ _ h, h _ $ rel_of_aux H) $
              λ _ _ hi, h.to_equiv.injective $ by erw hf; exact hi];
   show _ ↔ f x * ↑(g 1)⁻¹ = f y * ↑(g 1)⁻¹;
   rw [con.ker_rel, units.mul_right_inj]⟩

@[to_additive]
lemma char_pred_of_mul_equiv (H : ∀ y : Y, is_unit (f y)) (h : localization X Y ≃* Z)
  (hf : (h : _ → Z) = lift f H) : char_pred f H :=
char_pred_of_mul_equiv' f _ (λ y, classical.some_spec (H y)) h hf

@[to_additive]
lemma ker_eq_of_char_pred'  (g : Y → units Z) (H : ∀ y : Y, f y = g y)
  (Hp : char_pred' f g H) : con.ker (aux f g H) = Y.r :=
con.ext $ λ x y,
⟨λ h, by { change f x.1 * ↑(g x.2)⁻¹ = f y.1 * ↑(g y.2)⁻¹ at h,
  rw [units.eq_mul_inv_iff_mul_eq, mul_comm, ←mul_assoc, units.mul_inv_eq_iff_eq_mul,
      ←H _, ←H _, ←f.map_mul, ←f.map_mul, ←con.ker_rel, Hp.2, ker_of_eq] at h,
  rw Y.r_eq_r' at h ⊢,
  cases h with t ht,
  use t, rw mul_comm x.1, simpa using ht},
 λ h, by refine con.Inf_le _ _ _ _ _ h; exact rel_of_aux H⟩

@[to_additive]
noncomputable def equiv_of_char_pred' (g : Y → units Z) (H : ∀ y : Y, f y = g y)
  (Hp : char_pred' f g H) : localization X Y ≃* Z :=
(con.congr $ ker_eq_of_char_pred' f g H Hp).symm.trans $
con.quotient_ker_equiv_of_surjective (aux f g H) $ λ z, by
  cases Hp.1 z with x hx; revert hx; exact con.induction_on x (λ y hy, ⟨y, hy.symm ▸ rfl⟩)

@[to_additive]
noncomputable def mul_equiv_of_char_pred (H : ∀ y : Y, is_unit (f y)) (Hp : char_pred f H) :
  localization X Y ≃* Z :=
equiv_of_char_pred' f (λ y, classical.some $ H y)
  (λ y, by rw [← classical.some_spec (H y)]; refl) Hp

@[to_additive map_add_units_of_add_equiv]
lemma map_units_of_mul_equiv (h : X ≃* Z) (H : h.to_monoid_hom.map Y = W) (y : Y) :
  is_unit (of W (h y)) := ⟨to_units W ⟨h y, by rw ←H; exact ⟨y, y.2, rfl⟩⟩, rfl⟩

@[to_additive]
lemma ker_of_comp_inj (f :  X →* Z) (H : f.map Y ≤ W) (hf : function.injective f) :
  con.ker (of Y) ≤ con.ker ((of W).comp f) :=
begin
intros x y,
show con.ker (of Y) x y → con.ker (of W) _ _,
rw ker_of_eq, rw ker_of_eq,
intro h,
intros c hc, sorry,



end

@[to_additive]
lemma ker_of_comp_mul_equiv (h : X ≃* Z) (H : h.to_monoid_hom.map Y = W) :
  con.ker ((of W).comp h.to_monoid_hom) = con.ker (of Y) :=
begin
  ext,
  show con.ker (of W) _ _ ↔ _,
  rw [ker_of_eq, ker_of_eq, W.r_eq_r', Y.r_eq_r'],
  exact
  ⟨λ ⟨t, ht⟩, let ⟨s, hs⟩ := h.to_equiv.surjective t in
    ⟨⟨s, show s ∈ ↑Y, by {rw [←set.preimage_image_eq ↑Y h.to_equiv.injective, set.mem_preimage, hs],
          convert t.2, rw ←H, refl}⟩,
      by erw ←hs at ht; simpa using h.to_equiv.injective (show h (s*x) = h (s*y), by
         rw [h.map_mul, h.map_mul]; simpa using ht)⟩,
   λ ⟨t, ht⟩, ⟨⟨h t, by rw ←H; exact ⟨t, ⟨t.2, rfl⟩⟩⟩, by
      { suffices : h t * h x = h t * h y, by simpa, erw [←h.map_mul, ←h.map_mul],
        exact congr_arg h (by simpa using ht)}⟩⟩,
end

@[to_additive]
lemma char_pred_of_map (h : X ≃* Z) (H : h.to_monoid_hom.map Y = W) :
  char_pred ((of W).comp h.to_monoid_hom) (map_units_of_mul_equiv h H) :=
begin
  split,
    apply ind,
    rintro ⟨z, w⟩,
    cases h.to_equiv.surjective z with x hx,
    cases h.to_equiv.surjective w with y hy,
    have : y ∈ Y, by
      rw [←submonoid.mem_coe, ←set.preimage_image_eq ↑Y h.to_equiv.injective, set.mem_preimage, hy];
      convert w.2; rw ←H; refl,
    have hu : is_unit (of W (h y)), from ⟨(to_units W ⟨(h y), by rw ←H; exact ⟨y, ⟨this, rfl⟩⟩⟩), rfl⟩,
    use mk x ⟨y, this⟩,
    erw [monoid_hom.lift_mk, mk_eq, monoid_hom.comp_apply, hx],
    congr,
    rw units.ext_iff,
    suffices : _ = of W (h y), by erw hy at this; simpa,
    rw classical.some_spec hu, refl,
  exact ker_of_comp_mul_equiv h H,
end

@[to_additive]
noncomputable def mul_equiv_map' (h : X ≃* Z) (H : h.to_monoid_hom.map Y = W) :
  localization X Y ≃* localization Z W :=
mul_equiv_of_char_pred ((of W).comp h.to_monoid_hom) (map_units_of_mul_equiv h H) $
char_pred_of_map h H

--I didn't notice this would be noncomputable until I made it. :(

@[to_additive]
def mul_equiv_map (h : X ≃* Z) (H : h.to_monoid_hom.map Y = W) :
  localization X Y ≃* localization Z W :=
{ to_fun := map h.to_monoid_hom $ λ (y : Y), show h y ∈ W, from H ▸ ⟨y, y.2, rfl⟩,
  inv_fun := map h.symm.to_monoid_hom $
    λ (w : W), let ⟨y, hym, hy⟩ := show (w : Z) ∈ h.to_monoid_hom.map Y, from H.symm ▸ w.2 in
      show h.symm w ∈ Y, by erw [hy.symm, symm_apply_apply]; exact hym,
  left_inv := λ x, by {erw [map_map, map_ext (h.trans h.symm).to_monoid_hom (monoid_hom.id X)
      (λ (y : Y), by erw h.symm_apply_apply y; exact y.2) (λ y, y.2)
      (by ext; exact h.symm_apply_apply _) x, map_id], refl},
  right_inv := λ x, by {erw [map_map, map_ext (h.symm.trans h).to_monoid_hom (monoid_hom.id Z)
      (λ (w : W), by erw h.apply_symm_apply; exact w.2) (λ w, w.2)
      (by ext; erw h.apply_symm_apply; refl) x, map_id], refl},
  map_mul' := monoid_hom.map_mul _ }

variables {X Y}

@[reducible] def away (x : X) := localization X $ submonoid.powers x

section away

  def away.inv_self (x : X) : away x := mk 1 ⟨x, 1, pow_one x⟩

  variables (f)

  @[elab_with_expected_type]
  noncomputable def away.monoid_hom.lift {x : X} (hfx : is_unit (f x)) : away x →* Z :=
  monoid_hom.lift' f (λ s, classical.some hfx ^ classical.some s.2) $ λ s,
  by rw [units.coe_pow, ← classical.some_spec hfx,
         ← f.map_pow, classical.some_spec s.2]; refl

  variables {f}

  @[simp] lemma away.lift_of {x : X} (hfx : is_unit (f x)) (a : X) :
    away.monoid_hom.lift f hfx (of (submonoid.powers x) a) = f a :=
  lift'_of _ _

  @[simp] lemma away.monoid_hom.lift_comp_of {x : X} (hfx : is_unit (f x)) :
    (away.monoid_hom.lift f hfx).comp (of $ submonoid.powers x) = f :=
  lift'_comp_of _

  noncomputable def monoid_hom.away_to_away_right (x y : X) : away x →* away (x * y) :=
  away.monoid_hom.lift (of $ submonoid.powers $ x * y) $
  is_unit_of_mul_one _
    (((of $ submonoid.powers $ x * y) : X → away (x * y)) y * away.inv_self (x * y)) $ by
      rw [away.inv_self, ←mul_assoc, ←(of _).map_mul, ←mk_self (show _ ∈ submonoid.powers (x * y),
            from ⟨1, pow_one _⟩), mk_eq_mul_mk_one (x * y) _]

end away

end localization

namespace add_localization

variables {A : Type*} [add_comm_monoid A] {B : Type*} [add_comm_monoid B]

@[reducible] def away {A : Type*} [add_comm_monoid A] (x : A) :=
add_localization A (add_submonoid.multiples x)

attribute [to_additive add_localization.away] localization.away

section away
  def away.neg_self (x : A) : away x := mk 0 ⟨x, 1, add_monoid.one_smul x⟩

  variables (f : A →+ B)

  @[elab_with_expected_type]
  noncomputable def away.add_monoid_hom.lift {x : A} (hfx : is_add_unit (f x)) : away x →+ B :=
  add_monoid_hom.lift' f (λ s, classical.some s.2 • classical.some hfx) $ λ s,
  by rw [add_units.coe_smul, ← classical.some_spec hfx,
         ← f.map_smul, classical.some_spec s.2]; refl

  variables {f}

  @[simp] lemma away.add_monoid_hom.lift_of {x : A} (hfx : is_add_unit (f x)) (a : A) :
    away.add_monoid_hom.lift f hfx (add_monoid_hom.of (add_submonoid.multiples x) a) = f a :=
  lift'_of _ _

  @[simp] lemma away.add_monoid_hom.lift_comp_of {x : A} (hfx : is_add_unit (f x)) :
    (away.add_monoid_hom.lift f hfx).comp (add_monoid_hom.of (add_submonoid.multiples x)) = f :=
  lift'_comp_of _

  noncomputable def add_monoid_hom.away_to_away_right (x y : A) : away x →+ away (x + y) :=
  away.add_monoid_hom.lift (add_monoid_hom.of (add_submonoid.multiples (x + y))) $
  is_add_unit_of_add_zero _ (((add_monoid_hom.of _).1 y) + away.neg_self (x + y)) $ by unfold_coes;
    rw [away.neg_self, ←add_assoc, ←add_monoid_hom.map_add',
        ←mk_self (show (x + y) ∈ add_submonoid.multiples (x + y), from ⟨1, add_monoid.one_smul _⟩),
        mk_eq_add_mk_zero (x + y) _]; refl

end away

end add_localization