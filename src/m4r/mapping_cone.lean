import m4r.free_module_stuff

/- Far from the correct generality -/
universes u v
variables (R : Type u) [comm_ring R] (F : cochain_complex.{u u+1} (Module.{u} R))

def cochain_complex.prod (F G : cochain_complex.{u u+1} (Module.{u} R)) :
  cochain_complex (Module R) :=
{ X := λ n, Module.of R (F.X n × G.X n),
  d := λ n, ((F.d n).comp (linear_map.fst R _ _)).prod ((G.d n).comp (linear_map.snd R _ _)),
  d_squared' :=
  begin
    ext1 n,
    show (((F.d n.succ).comp (linear_map.fst R _ _)).prod ((G.d n.succ).comp (linear_map.snd R _ _))).comp
      (((F.d n).comp (linear_map.fst R _ _)).prod ((G.d n).comp (linear_map.snd R _ _))) = 0,
    ext,
    { exact linear_map.ext_iff.1 (F.d_squared n) _ },
    { exact linear_map.ext_iff.1 (G.d_squared n) _ },
    sorry,
    sorry, -- I can't scroll the Infoview so I'll have to leave it here.
  end }
namespace koszul

variables (n : ℤ)

def mapping_cone (x : R) := cochain_complex.tensor_product R (smul_cx R x) F

def left_mapping_cone_hom (x : R) :
  shift F 1 ⟶ mapping_cone R F x :=
{ f := λ n, linear_map.comp (smul_cx_prod R _ _ _).symm.to_linear_map (linear_map.inr _ _ _),
  comm' := sorry }

def right_mapping_cone_hom (x : R) :
  mapping_cone R F x ⟶ F :=
{ f := λ n, linear_map.comp (linear_map.fst _ _ _) (smul_cx_prod R _ _ _).to_linear_map,
  comm' := sorry }

theorem left_mapping_cone_hom_inj {x : R} {n : ℤ} :
  ((left_mapping_cone_hom R F x).f n).ker = ⊥ :=
sorry ---linear_map.inr_injective

theorem right_mapping_cone_hom_surj {x : R} {n : ℤ} :
  ((right_mapping_cone_hom R F x).f n).range = ⊤ :=
sorry

theorem mapping_cone_exact {x : R} {n : ℤ} :
  ((right_mapping_cone_hom R F x).f n).ker = ((left_mapping_cone_hom R F x).f n).range :=
sorry

end koszul
