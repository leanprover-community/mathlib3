/-

  -- apply add_hom_ext, intros ai ax, apply add_hom_ext, intros bi bx, apply add_hom_ext, intros ci cx,
  ⊢ ⇑(⇑(⇑LHS (⇑(of A ai) ax)) (⇑(of A bi) bx)) (⇑(of A ci) cx)
      = ⇑(⇑(⇑RHS (⇑(of A ai) ax)) (⇑(of A bi) bx)) (⇑(of A ci) cx)

  -- ext ai ax bi bx ci cx : 6,
  ⊢ ⇑((⇑((⇑(LHS.comp (of A ai)) ax).comp (of A bi)) bx).comp (of A ci)) cx
      = ⇑((⇑((⇑(RHS.comp (of A ai)) ax).comp (of A bi)) bx).comp (of A ci)) cx

  -- ext ai ax bi bx ci cx : 6,
  -- rw [coe_comp, function.comp_app, coe_comp, function.comp_app, coe_comp, function.comp_app,
  --     coe_comp, function.comp_app, coe_comp, function.comp_app, coe_comp, function.comp_app,
  --     coe_comp, function.comp_app],
  ⊢ ⇑(⇑(⇑(⇑add_monoid_hom.comp_hom (mul_hom A)) (⇑(mul_hom A) (⇑(of A ai) ax)))
           (⇑(of A bi) bx))
        (⇑(of A ci) cx) =
      ⇑(⇑(⇑((⇑(⇑add_monoid_hom.comp_hom flip_hom)
                  ((⇑add_monoid_hom.comp_hom (mul_hom A).flip).comp (mul_hom A))).flip)
              (⇑(of A ai) ax))
           (⇑(of A bi) bx))
        (⇑(of A ci) cx)

  -- ext ai ax bi bx ci cx : 6,
  -- rw [coe_comp, function.comp_app, coe_comp, function.comp_app, coe_comp, function.comp_app,
  --     coe_comp, function.comp_app, coe_comp, function.comp_app, coe_comp, function.comp_app],
  ⊢ ⇑(⇑(⇑(⇑add_monoid_hom.comp_hom (mul_hom A)) (⇑(mul_hom A) (⇑(of A ai) ax)))
           (⇑(of A bi) bx))
        (⇑(of A ci) cx) =
      ⇑(⇑(⇑((⇑(⇑add_monoid_hom.comp_hom flip_hom)
                  ((⇑add_monoid_hom.comp_hom (mul_hom A).flip).comp (mul_hom A))).flip.comp
                 (of A ai))
              ax)
           (⇑(of A bi) bx))
        (⇑(of A ci) cx)

-/


/-

  -- apply add_hom_ext, intros ai ax, apply add_hom_ext, intros bi bx, apply add_hom_ext, intros ci cx,
  ⊢ ⇑(⇑(⇑((⇑add_monoid_hom.comp_hom (mul_hom A)).comp (mul_hom A)) (⇑(of A ai) ax))
           (⇑(of A bi) bx))
        (⇑(of A ci) cx) =
      ⇑(⇑(⇑((⇑(⇑add_monoid_hom.comp_hom flip_hom)
                  ((⇑add_monoid_hom.comp_hom (mul_hom A).flip).comp (mul_hom A))).flip)
              (⇑(of A ai) ax))
           (⇑(of A bi) bx))
        (⇑(of A ci) cx)

  -- ext ai ax bi bx ci cx : 6,
  ⊢ ⇑((⇑((⇑(((⇑add_monoid_hom.comp_hom (mul_hom A)).comp (mul_hom A)).comp (of A ai)) ax).comp
               (of A bi))
            bx).comp
           (of A ci))
        cx =
      ⇑((⇑((⇑((⇑(⇑add_monoid_hom.comp_hom flip_hom)
                    ((⇑add_monoid_hom.comp_hom (mul_hom A).flip).comp (mul_hom A))).flip.comp
                   (of A ai))
                ax).comp
               (of A bi))
            bx).comp
           (of A ci))
        cx

  -- ext ai ax bi bx ci cx : 6,
  -- rw [coe_comp, function.comp_app, coe_comp, function.comp_app, coe_comp, function.comp_app,
  --     coe_comp, function.comp_app, coe_comp, function.comp_app, coe_comp, function.comp_app,
  --     coe_comp, function.comp_app],
  ⊢ ⇑(⇑(⇑(⇑add_monoid_hom.comp_hom (mul_hom A)) (⇑(mul_hom A) (⇑(of A ai) ax)))
           (⇑(of A bi) bx))
        (⇑(of A ci) cx) =
      ⇑(⇑(⇑((⇑(⇑add_monoid_hom.comp_hom flip_hom)
                  ((⇑add_monoid_hom.comp_hom (mul_hom A).flip).comp (mul_hom A))).flip)
              (⇑(of A ai) ax))
           (⇑(of A bi) bx))
        (⇑(of A ci) cx)

  -- ext ai ax bi bx ci cx : 6,
  -- rw [coe_comp, function.comp_app, coe_comp, function.comp_app, coe_comp, function.comp_app,
  --     coe_comp, function.comp_app, coe_comp, function.comp_app, coe_comp, function.comp_app],
  ⊢ ⇑(⇑(⇑(⇑add_monoid_hom.comp_hom (mul_hom A)) (⇑(mul_hom A) (⇑(of A ai) ax)))
           (⇑(of A bi) bx))
        (⇑(of A ci) cx) =
      ⇑(⇑(⇑((⇑(⇑add_monoid_hom.comp_hom flip_hom)
                  ((⇑add_monoid_hom.comp_hom (mul_hom A).flip).comp (mul_hom A))).flip.comp
                 (of A ai))
              ax)
           (⇑(of A bi) bx))
        (⇑(of A ci) cx)

-/
