/- -/
import control.equiv_functor
import tactic.transport
import data.analysis.filter
import category_theory.canonical
import category_theory.types
import category_theory.functorial

universes u v w
open category_theory

set_option trace.equiv_rw_type true

-- Let's show that `set : Type u → Type u` is an equiv_functor

-- Unfortunately this is not the best instance.
-- instance : equiv_functor set :=
-- { map := λ α β e s, by { equiv_rw e.symm, assumption, } }

example : is_lawful_functor set := by apply_instance

-- instance : equiv_functor set :=
-- { map := λ α β e s, e '' s }

@[tidy] meta def equiv_functor_derive_helper := `[simp only [equiv_functor.map]] <|> `[library_search]

-- local attribute [-instance] list.monad list.is_lawful_monad list.alternative list.traversable list.is_lawful_traversable

-- def foo : is_lawful_functor list := by apply_instance
-- #print foo

-- instance quux : equiv_functor list :=
-- { map := λ α β e s, by { equiv_rw e.symm, assumption, }, }
-- set_option pp.all true
-- #print quux

instance bar : equiv_functor filter := by apply_instance
-- { map := λ α β e s, by { equiv_rw e.symm, assumption, }, }

#print bar

#print filter.principal

-- instance bar' : iso_functorial.{v v} filter.{v} := by apply_instance

class equiv_natural {F G : Type u → Type u} [equiv_functor F] [equiv_functor G]
  (f : Π {α}, F α → G α) :=
(naturality : ∀ {α β : Type u} (i : α ≃ β), f ∘ (equiv_functor.map i) = (equiv_functor.map i) ∘ f)

instance equiv_natural_filter_principal : equiv_natural @filter.principal :=
{ naturality := λ α β i, by { ext, simp [equiv_functor.map], } }



meta def flat_section_auto_param : tactic unit := `[intros, simp [equiv_functor.map]] <|> `[obviously]

class flat_section {F : Type v → Type w} [equiv_functor F] (σ : Π (X : Type v), F X) :=
(transport : ∀ {X Y : Type v} (i : X ≃ Y), (equiv_functor.map.{v w} i : F X → F Y) (σ X) = σ Y . flat_section_auto_param)

instance flat_section_bot_filter : flat_section (λ α, (⊥ : filter α)) := { }

@[simp]
lemma set_true {X : Type v} : {x : X | true} = set.univ :=
by { ext, simp, }

@[simp]
lemma set_false {X : Type v} : {x : X | false} = ∅ :=
by { ext, simp, }

@[simp]
lemma filter_map_equiv_top (X Y : Type v) (i : X ≃ Y) : filter.map ⇑i ⊤ = ⊤ :=
begin
  ext,
  simp only [filter.mem_map, filter.mem_top_sets],
  split,
  { intro h, ext y, split,
    { intro m, trivial, },
    { intro m,
      have w : i.symm y ∈ set.univ := set.mem_univ _,
      rw ←h at w,
      simpa using w, }, },
  { rintro rfl, simp, }
end

instance flat_section_top_filter : flat_section (λ α, (⊤ : filter α)) := { }

variables {C : Type u} [category.{v} C]

class flat_section' {F : C → Type w} [iso_functorial.{v w} F] (σ : Π (X : C), F X) :=
(transport [] : ∀ {X Y : C} (f : X ≅ Y), (iso_functorial.map.{v w} F f : F X → F Y) (σ X) = σ Y)


-- variables {D : Type (w+1)} [large_category D] [concrete_category D]

-- local attribute [instance] concrete_category.has_coe_to_sort
-- local attribute [instance] concrete_category.has_coe_to_fun


-- class flat_section'' {F : C → D} [iso_functorial.{v w} F] (σ : Π (X : C), (F X : Type u)) :=
-- (transport : ∀ {X Y : C} (f : X ≅ Y), (iso_functorial.map.{v w} F f : F X → F Y) (σ X) = σ Y)
