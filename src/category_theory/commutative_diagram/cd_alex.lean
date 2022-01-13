open widget

variables {α : Type}

namespace svg

meta def fill : string → attr α
| s := attr.val "fill" $ s

meta def stroke : string → attr α
| s := attr.val "stroke" $ s

meta def circle.cx : string → attr α
| s := attr.val "cx" $ s

meta def circle.cy : string → attr α
| s := attr.val "cy" $ s

meta def circle.r : string → attr α
| s := attr.val "r" $ s

meta def line.x1 : string → attr α
| s := attr.val "x1" $ s

meta def line.x2 : string → attr α
| s := attr.val "x2" $ s

meta def line.y1 : string → attr α
| s := attr.val "y1" $ s

meta def line.y2 : string → attr α
| s := attr.val "y2" $ s

end svg

inductive render_data
| obj : Π (name : string) (pos : ℕ × ℕ), render_data
| mor : Π (name : string) (pos₁ : ℕ × ℕ) (pos₂ : ℕ × ℕ), render_data

section open render_data

def square : list render_data :=
[ obj "A₁" (0,0), obj "B" (1,0), obj "C" (0,1), obj "D" (1,1),
  mor "" (0,0) (1,0),
  mor "" (0,0) (0,1),
  mor "" (1,0) (1,1),
  mor "" (0,1) (1,1) ]

end

meta def svg.line.mk (x₁ y₁ x₂ y₂ : ℕ) :
  html empty :=
h "line" [
  svg.line.x1 $ to_string $ x₁,
  svg.line.y1 $ to_string $ y₁,
  svg.line.x2 $ to_string $ x₂,
  svg.line.y2 $ to_string $ y₂,
  svg.fill "black",
  svg.stroke "black"
] []

meta def svg.arrowhead : html empty :=
h "marker" [
  attr.val "id" "arrowhead",
  attr.val "markerWidth" "10",
  attr.val "markerHeight" "7",
  attr.val "refX" "7",
  attr.val "refY" "3.5",
  attr.val "orient" "auto"
] [h "polyline" [
    attr.val "points" "0 0, 10 3.5, 0 7",
    svg.fill "none",
    svg.stroke "black"
  ] []]

meta def svg.arrow.mk (x₁ y₁ x₂ y₂ : ℕ) :
  html empty :=
h "line" [
  svg.line.x1 $ to_string $ x₁,
  svg.line.y1 $ to_string $ y₁,
  svg.line.x2 $ to_string $ x₂,
  svg.line.y2 $ to_string $ y₂,
  svg.fill "black",
  svg.stroke "black",
  attr.val "stroke-width" "1",
  attr.val "marker-end" "url(#arrowhead)"
] []

meta def svg.text (s : string) (x : ℕ) (y : ℕ) : html empty :=
with_style "font" "italic 24px serif" $
h "text" [
  attr.val "x" $ to_string x,
  attr.val "y" $ to_string y,
  attr.val "text-anchor" "middle",
  attr.val "alignment-baseline" "middle"
] [s]

meta def adjust_pos (p₁ p₂ : ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
let t : ℕ → ℕ := λ x, 40 + 80 * x,
  x₁ := t p₁.1, y₁ := t p₁.2, x₂ := t p₂.1, y₂ := t p₂.2,
  r := 15, s := 20,
  f : ℕ → ℕ → ℕ := λ a b, (r * a + (s - r) * b) / s,
  a := f x₁ x₂, b := f y₁ y₂, c := f x₂ x₁, d := f y₂ y₁
in ⟨a, b, c, d⟩

meta def render_data.render : render_data → html empty
| (render_data.obj n p) :=
  svg.text n (40 + 80 * p.1) (40 + 80 * p.2)
| (render_data.mor n p₁ p₂) :=
  let ⟨a, b, c, d⟩ := adjust_pos p₁ p₂ in
  svg.arrow.mk a b c d

meta def D_svg (sq : list render_data) : list (html empty) :=
(h "defs" [] [svg.arrowhead] ::
  render_data.render <$> sq)

meta def D (sq : list render_data): html empty :=
h "div" [] [
  with_style "height" "200px" $
  with_style "width" "600px" $
  with_style "background" "grey" $
  h "svg" [] $ D_svg sq]

def render_data.flip : render_data → render_data
| (render_data.obj a (b, c)) := render_data.obj a (c, b)
| (render_data.mor a (b₁,b₂) (c₁,c₂)) := render_data.mor a (b₂, b₁) (c₂, c₁)
-- #html D

instance : inhabited render_data := ⟨render_data.mor "" (0,0) (1,0)⟩

@[reducible] meta def show_diagram := interaction_monad $ tactic_state × list render_data

open tactic
namespace show_diagram

meta def step {α : Type} (t : show_diagram α) : show_diagram unit :=
t >> return ()

meta def istep {α : Type*} (line0 col0 line col ast : ℕ) (t : show_diagram α) : show_diagram unit :=
λ s, (@scope_trace _ line col (λ _, (step t) s)).clamp_pos line0 line col

open interaction_monad.result
@[inline] meta def read : show_diagram $ tactic_state × list render_data :=
λ s, success s s

@[inline] meta def write (s' : tactic_state) (l : list render_data) : show_diagram unit:=
λ s, success () (s', l)
meta def interactive.init : show_diagram unit:=
do l ← read,
write l.1 square

meta def run_tac {α}
(c : tactic α) : show_diagram α :=
λ s, match c s.1 with
| success a b := success a (b, s.2)
| exception a d e := exception a d (e, s.2)
end


meta def save_info (p : pos) : show_diagram unit :=
do
  s ← read,
  -- tactic.save_info_thunk p (λ _, (tactic_state.to_format s, _)),
  run_tac $ tactic.save_widget p (component.pure (λ _, (D s.2)))

meta def interactive.by_tac
(c : interactive.itactic) : show_diagram unit :=
  run_tac $ tactic.solve1 c
meta def interactive.flip : show_diagram unit :=
do
  s ← read,
  write s.1 (s.2.map render_data.flip)
meta
def to_tac {α} (t : show_diagram α) : tactic α :=
λ s :tactic_state, match t (s, []) with
| success a b := success a b.1
| exception a d e := exception a d e.1
end
end show_diagram

namespace interactive
/-- Default `executor` instance for `tactic`s themselves -/
meta instance executor_show_diagram : executor show_diagram :=
{ config_type := unit,
  inhabited := ⟨()⟩,
  execute_with := λ _, show_diagram.to_tac }
end interactive

constant category : Type*
constant commutes : category → Prop
axiom wow : ∀ C, commutes C
variable (C : category)

lemma a : commutes C :=
begin [show_diagram]
  init,
  flip,
  by_tac { have a : 1 = 1, refl, exact wow C, },

end
