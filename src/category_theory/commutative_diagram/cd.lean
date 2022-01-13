-- See also:
-- https://mathoverflow.net/questions/9930/algorithm-or-theory-of-diagram-chasing

import tactic

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

meta def D_svg : list (html empty) :=
(h "defs" [] [svg.arrowhead] ::
  render_data.render <$> square)

meta def D : html empty :=
h "div" [] [
  with_style "height" "200px" $
  with_style "width" "600px" $
  with_style "background" "grey" $
  h "svg" [] $ D_svg]

#html D

meta def trace_html (h : html empty) : tactic unit :=
tactic.trace_widget $ component.pure $ λ _, h

meta def foo (s : string) : html empty := h "em" [] [s]

meta def foobar (l : list name) : html empty := h "div" [] $ l.map (html.of_string ∘ to_string)

example (a b c d e : ℕ) : true :=
begin
  (do ctx ← tactic.local_context, trace_html ctx), -- works, and I understand why
  let s : string := "test",
  let what_I_care_about := [`a, `d, `s],
  trace_html (foobar what_I_care_about), -- fails, and I understand why
  let k : ℕ := 3,
  let x : ℤ := -1,
  let what_I_care_about := what_I_care_about ++ [x],
  trace_html (foobar what_I_care_about),
  trivial
end

section

open tactic
setup_tactic_parser

namespace diagram__cmd

meta def obj : lean.parser name := ident

@[derive [add_comm_group, has_to_string]]
def direction := ℤ × ℤ

meta def small_int : lean.parser ℤ := do
  neg ← (tk "-")?,
  n ← small_nat,
  pure $ if neg.is_some then (- n) else n

meta def parse_dir : lean.parser direction :=
brackets "{" "}" $ do x ← small_int, tk ",", y ← small_int, return (x, y)

precedence `↗`:0
precedence `↘`:0
precedence `↓`:0
precedence `↙`:0
precedence `↖`:0

meta def arrow : lean.parser direction :=
(tk "↗"  >> pure ( 1,-1)) <|>
(tk "->" >> pure ( 1, 0)) <|>
(tk "↘"  >> pure ( 1, 1)) <|>
(tk "↓"  >> pure ( 0, 1)) <|>
(tk "↙"  >> pure (-1, 1)) <|>
(tk "<-" >> pure (-1, 0)) <|>
(tk "↖"  >> pure (-1,-1)) <|>
(tk "↑"  >> pure ( 0,-1))

@[derive has_to_string]
def mor := option name × direction

meta def lmor : lean.parser mor := do
  d ← parse_dir?,
  k ← small_nat?, let k := k.get_or_else 1,
  a ← arrow,
  n ← ident?,
  let xy : direction := d.get_or_else $ k • a,
  return (n, xy)

meta def rmor : lean.parser mor := do
  a ← arrow,
  k ← small_nat?, let k := k.get_or_else 1,
  d ← parse_dir?,
  n ← ident?,
  let xy : direction := d.get_or_else $ k • a,
  return (n, xy)

@[derive has_to_string]
def cell := list mor × name × list mor

meta def parse_cell : lean.parser (cell) :=
prod.mk <$> lmor* <*> (prod.mk <$> obj <*> rmor*)

meta def parse : lean.parser (list $ list $ option cell) :=
list_of $ list_of parse_cell?

meta def d_to_string (T : name) (D : list $ list $ option cell) : string :=
let objs : list name := D.join.filter_map $ option.map $ λ c, c.2.1,
    objs_fmt := " ".intercalate (repr <$> objs),
    mors : list (name × name × name) := [],
    fmt_mor : name × name × name → string := λ ⟨f, s, t⟩,
      sformat!"({repr f} : {repr s} ⟶ {repr t})"
in " ".intercalate (sformat!"{{{objs_fmt} : {repr T}}" :: fmt_mor <$> mors)

end diagram__cmd

@[user_command]
meta def diagram_cmd (x : parse $ tk "#diagram") : lean.parser unit := do
  e ← ident,
  D ← diagram__cmd.parse,
  tactic.trace $ diagram__cmd.d_to_string e D,
  skip

#diagram T [
  [A →f,, B],
  [C, D]
]

run_cmd (do
  s ← run_with_input (list_of small_nat?) "[1,2,,3]",
  tactic.trace s,
  skip)

meta def quux (d p : string) : tactic unit :=
do s ← run_with_input (tk d *> ident) $ d ++ "f",
  trace (s ++ p)

run_cmd (do
  let ds :=
    [("↗", "ur"), ("->", "r"), ("↘", "dr"), ("↓", "d"),
     ("↙", "dl"), ("<-", "l"), ("↖", "ul"), ("↑", "u"), ("•", "bullet")],
  let ts := sequence $ ds.map $ λ ⟨d, p⟩, quux d p,
  ts,
  skip)

variables (T : Type*)


end
