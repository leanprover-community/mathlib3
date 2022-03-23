-- import algebra.module.basic
-- import algebra.category.Module.basic

-- namespace linear_map

-- section

-- open_locale pointwise

-- universes u v

-- variables {R : Type u} [semiring R]
-- variables {Q : Type (max u v)} [add_comm_monoid Q] [module R Q]
-- variables {Q' : Type (max u v)} [add_comm_monoid Q'] [module R Q']

-- variables {p q : submodule R Q}

-- noncomputable def of_glue2 (fp : p →ₗ[R] Q') (fq : q →ₗ[R] Q') :
--   (p ⊔ q : submodule R Q) →ₗ[R] Q' :=
-- { to_fun := λ x, begin
--     have mem1 : x.1 ∈ (↑p + ↑q : set _),
--     { convert x.2,
--       rw submodule.coe_sup, },
--     rw set.mem_add at mem1,
--     choose pp qq eq1 using mem1,
--     exact fp ⟨pp, eq1.1⟩ + fq ⟨qq, eq1.2.1⟩,
--   end,
--   map_add' := λ x y, begin
--     dsimp,
--   end,
--   map_smul' := _ }

-- end

-- end linear_map
