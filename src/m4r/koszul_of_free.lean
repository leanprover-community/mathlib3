import m4r.cx

universes u v
variables {R : Type u} [comm_ring R] (n : ℕ) (x : fin n → R)
(F : cochain_complex.{u u+1} (Module.{u u} R))

def cx_cast (j k : ℤ) (h : j = k) : F.X j ⟶ F.X k :=
{ to_fun := λ x, eq.rec x h,
  map_add' := λ x y, by cases h; refl,
  map_smul' := λ x r, by cases h; refl }

lemma cast_d_cast_eq_d (j k : ℤ) (h : j = k) (x : F.X j) :
  (cx_cast F _ _ h ≫ F.d k ≫ cx_cast F _ _ ((add_left_inj _).2 h.symm)) x = F.d j x :=
begin
  cases h,
  refl,
end

lemma cast_d_eq_d_cast (j k : ℤ) (h : j = k) (x : F.X j) :
  ((cx_cast F _ _ h) ≫ F.d k) x = (F.d j ≫ cx_cast F _ _ ((add_left_inj _).2 h)) x :=
begin
  cases h,
  refl,
end

def shift (F : cochain_complex (Module R)) (i : ℤ) :
  cochain_complex (Module R) :=
{ X := λ m, F.X (m - i),
  d := λ m, F.d (m - i) ≫ cx_cast F (m - i + 1) (m + 1 - i) (sub_add_eq_add_sub _ _ _),
  d_squared' := by {sorry } }