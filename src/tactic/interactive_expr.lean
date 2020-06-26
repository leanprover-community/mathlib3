/-
Copyright (c) E.W.Ayers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: E.W.Ayers
-/

namespace widget_override
open widget

open tagged_format
open widget.html widget.attr

namespace interactive_expression

/-- eformat but without any of the formatting stuff like highlighting, groups etc. -/
meta inductive sf : Type
| tag_expr : expr.address → expr → sf → sf
| compose : sf →  sf →  sf
| of_string : string →  sf

private meta def to_simple : eformat → sf
| (tag ⟨ea,e⟩ m) := sf.tag_expr ea e $ to_simple m
| (group m) := to_simple m
| (nest i m) := to_simple m
| (highlight i m) := to_simple m
| (of_format f) := sf.of_string $ format.to_string f
| (compose x y) := sf.compose (to_simple x) (to_simple y)

private meta def sf.flatten : sf → sf
| (sf.tag_expr e ea m) := (sf.tag_expr e ea $ sf.flatten m)
| (sf.compose x y) :=
  match (sf.flatten x), (sf.flatten y) with
  | (sf.of_string sx), (sf.of_string sy) := sf.of_string (sx ++ sy)
  | (sf.of_string sx), (sf.compose (sf.of_string sy) z) := sf.compose (sf.of_string (sx ++ sy)) z
  | (sf.compose x (sf.of_string sy)), (sf.of_string sz) := sf.compose x (sf.of_string (sy ++ sz))
  | (sf.compose x (sf.of_string sy1)), (sf.compose (sf.of_string sy2) z) := sf.compose x (sf.compose (sf.of_string (sy1 ++ sy2)) z)
  | x, y := sf.compose x y
  end
| (sf.of_string s) := sf.of_string s

/--
The actions accepted by an expression widget.
-/
meta inductive action (γ : Type)
| on_mouse_enter : subexpr → action
| on_mouse_leave_all : action
| on_click : subexpr → action
| on_tooltip_action : γ → action
| on_close_tooltip : action

/--
Renders a subexpression as a list of html elements.
-/
meta def view {γ} (tooltip_component : tc subexpr (action γ)) (click_address : option expr.address) (select_address : option expr.address) :
  subexpr → sf → tactic (list (html (action γ)))
| ⟨ce, current_address⟩ (sf.tag_expr ea e m) := do
  let new_address := current_address ++ ea,
  let select_attrs : list (attr (action γ)) := if some new_address = select_address then [className "highlight"] else [],
  click_attrs  : list (attr (action γ)) ←
    if some new_address = click_address then do
      content ← tc.to_html tooltip_component (e, new_address),
      pure [tooltip $ h "div" [] [
          h "button" [cn "fr pointer ba br3", on_click (λ _, action.on_close_tooltip)] ["x"],
          content
      ]]
    else pure [],
  let as := [className "expr-boundary", key (ea)] ++ select_attrs ++ click_attrs,
  inner ← view (e,new_address) m,
  pure [h "span" as inner]
| ca (sf.compose x y) := pure (++) <*> view ca x <*> view ca y
| ca (sf.of_string s) := pure
  [h "span" [
    on_mouse_enter (λ _, action.on_mouse_enter ca),
    on_click (λ _, action.on_click ca),
    key s
  ] [html.of_string s]]


/-- Make an interactive expression. -/
meta def mk {γ} (tooltip : tc subexpr γ) : tc expr γ :=
let tooltip_comp :=
   component.with_props_eq (λ (x y : tactic_state × expr × expr.address), x.2.2 = y.2.2)
   $ component.map_action (action.on_tooltip_action) tooltip in
tc.mk_simple
  (action γ)
  (option subexpr × option subexpr)
  (λ e, pure $ (none, none))
  (λ e ⟨ca, sa⟩ act, pure $
    match act with
    | (action.on_mouse_enter ⟨e, ea⟩) := ((ca, some (e, ea)), none)
    | (action.on_mouse_leave_all)     := ((ca, none), none)
    | (action.on_click ⟨e, ea⟩)       := if some (e,ea) = ca then ((none, sa), none) else ((some (e, ea), sa), none)
    | (action.on_tooltip_action g)    := ((none, sa), some g)
    | (action.on_close_tooltip)       := ((none, sa), none)
    end
  )
  (λ e ⟨ca, sa⟩, do
    ts ← tactic.read,
    let m : sf  := sf.flatten $ to_simple $ tactic_state.pp_tagged ts e,
    let m : sf  := sf.tag_expr [] e m, -- [hack] in pp.cpp I forgot to add an expr-boundary for the root expression.
    v ← view tooltip_comp (prod.snd <$> ca) (prod.snd <$> sa) ⟨e, []⟩ m,
    pure $
    [ h "span" [
          className "expr",
          key e.hash,
          on_mouse_leave (λ _, action.on_mouse_leave_all) ] $ v
      ]
  )

/-- Render the implicit arguments for an expression in fancy, little pills. -/
meta def implicit_arg_list (tooltip : tc subexpr empty) (e : expr) : tactic $ html empty := do
  fn ← (mk tooltip) $ expr.get_app_fn e,
  args ← list.mmap (mk tooltip) $ expr.get_app_args e,
  pure $ h "div" []
    ( (h "span" [className "bg-blue br3 ma1 ph2 white"] [fn]) ::
      list.map (λ a, h "span" [className "bg-gray br3 ma1 ph2 white"] [a]) args
    )

/--
Component for the type tooltip.
-/
meta def type_tooltip : tc subexpr empty :=
tc.stateless (λ ⟨e,ea⟩, do
    y ← tactic.infer_type e,
    y_comp ← mk type_tooltip y,
    implicit_args ← implicit_arg_list type_tooltip e,
    pure [
        h "div" [] [
          h "div" [] [y_comp],
          h "hr" [] [],
          implicit_args
        ]
      ]
  )

end interactive_expression

/--
Supported tactic state filters.
-/
@[derive decidable_eq]
meta inductive filter_type
| none
| no_instances
| only_props

/--
Filters a local constant using the given filter.
-/
meta def filter_local : filter_type → expr → tactic bool
| (filter_type.none) e := pure tt
| (filter_type.no_instances) e := do
  t ← tactic.infer_type e,
  bnot <$> tactic.is_class t
| (filter_type.only_props) e := do
  t ← tactic.infer_type e,
  tactic.is_prop t

/--
Component for the filter dropdown.
-/
meta def filter_component : component filter_type filter_type :=
component.stateless (λ lf,
  [ h "label" [] ["filter: "],
    select [
      ⟨filter_type.none, "0", ["no filter"]⟩,
      ⟨filter_type.no_instances, "1", ["no instances"]⟩,
      ⟨filter_type.only_props, "2", ["only props"]⟩
    ] lf
  ]
)

/--
Converts a name into an html element.
-/
meta def html.of_name {α : Type} : name → html α
| n := html.of_string $ name.to_string n

open tactic

/--
Component that shows a type.
-/
meta def show_type_component : tc expr empty :=
tc.stateless (λ x, do
  y ← infer_type x,
  y_comp ← interactive_expression.mk interactive_expression.type_tooltip $ y,
  pure y_comp
)

/-- A group of local constants in the context that should be rendered as one line. -/
@[derive decidable_eq]
meta structure local_collection :=
(key : string)
(locals : list expr)
(type : expr)

/-- Group consecutive locals according to whether they have the same type -/
meta def to_local_collection : list local_collection → list expr → tactic (list local_collection)
| acc [] := pure $ list.map (λ lc : local_collection, {locals := lc.locals.reverse, ..lc}) $ list.reverse $ acc
| acc (l::ls) := do
  l_type ← infer_type l,
  (do (⟨k,ns,t⟩::acc) ← pure acc,
      is_def_eq t l_type,
      to_local_collection (⟨k,l::ns,t⟩::acc) ls)
  <|> (to_local_collection (⟨to_string $ expr.local_uniq_name $ l, [l], l_type⟩::acc) ls)

/-- Component that displays the main (first) goal. -/
meta def tactic_view_goal {γ} (local_c : tc local_collection γ) (target_c : tc expr γ) : tc filter_type γ :=
tc.stateless $ λ ft, do
  g@(expr.mvar u_n pp_n y) ← main_goal,
  t ← get_tag g,
  let case_tag : list (html γ) :=
    match interactive.case_tag.parse t with
    | some t :=
      [h "li" [key "_case"] $ [h "span" [cn "goal-case b"] ["case"]] ++
        (t.case_names.bind $ λ n, [" ", n])]
    | none := []
    end,
  lcs ← local_context,
  lcs ← list.mfilter (filter_local ft) lcs,
  lcs ← to_local_collection [] lcs,
  lchs ← lcs.mmap (λ lc, do
    lh ← local_c lc,
    ns ← pure $ lc.locals.map (λ n, h "span" [cn "goal-hyp b"] [html.of_name $ expr.local_pp_name n]),
    pure $ h "li" [key lc.key] (ns ++ [" : ", h "span" [cn "goal-hyp-type"] [lh]])),
  t_comp ← target_c g,
  pure $ h "ul" [key g.hash, className "list pl0 font-code"] $ case_tag ++ lchs ++ [
    h "li" [key u_n] [
      h "span" [cn "goal-vdash b"] ["⊢ "],
      t_comp
  ]]

/--
Actions accepted by the `tactic_view_component`.
-/
meta inductive tactic_view_action (γ : Type)
| out (a:γ): tactic_view_action
| filter (f: filter_type): tactic_view_action

/-- Component that displays all goals, together with the `$n goals` message. -/
meta def tactic_view_component {γ} (local_c : tc local_collection γ) (target_c : tc expr γ) : tc unit γ :=
tc.mk_simple
  (tactic_view_action γ)
  (filter_type)
  (λ _, pure $ filter_type.none)
  (λ ⟨⟩ ft a, match a with
              | (tactic_view_action.out a) := pure (ft, some a)
              | (tactic_view_action.filter ft) := pure (ft, none)
              end)
  (λ ⟨⟩ ft, do
    gs ← get_goals,
    hs ← gs.mmap (λ g, do set_goals [g], flip tc.to_html ft $ tactic_view_goal local_c target_c),
    set_goals gs,
    let goal_message :=
      if gs.length = 0 then
        "goals accomplished"
      else if gs.length = 1 then
        "1 goal"
      else
        to_string gs.length ++ " goals",
    let goal_message : html γ := h "strong" [cn "goal-goals"] [goal_message],
    let goals : html γ := h "ul" [className "list pl0"]
        $ list.map_with_index (λ i x,
          h "li" [className $ "lh-copy mt2", key i] [x])
        $ (goal_message :: hs),
    pure [
      h "div" [className "fr"] [html.of_component ft $ component.map_action tactic_view_action.filter filter_component],
      html.map_action tactic_view_action.out goals
    ])

/-- Component that displays the term-mode goal. -/
meta def tactic_view_term_goal {γ} (local_c : tc local_collection γ) (target_c : tc expr γ) : tc unit γ :=
tc.stateless $ λ _, do
  goal ← flip tc.to_html (filter_type.none) $ tactic_view_goal local_c target_c,
  pure [h "ul" [className "list pl0"] [
    h "li" [className "lh-copy"] [h "strong" [cn "goal-goals"] ["expected type:"]],
    h "li" [className "lh-copy"] [goal]]]

/--
Component showing a local collection.
-/
meta def show_local_collection_component : tc local_collection empty :=
tc.stateless (λ lc, do
  (l::_) ← pure lc.locals,
  c ← show_type_component l,
  pure [c]
)

/--
Renders a the current tactic string.
-/
meta def tactic_render : tc unit string :=
component.ignore_action $ tactic_view_component show_local_collection_component show_type_component

/--
Component showing the current tactic state.
-/
meta def tactic_state_widget : component tactic_state string :=
tc.to_component tactic_render

/--
Widget used to display term-proof goals.
-/
meta def term_goal_widget : component tactic_state string :=
(tactic_view_term_goal show_local_collection_component show_type_component).to_component

end widget_override

attribute [vm_override widget_override.term_goal_widget] widget.term_goal_widget
attribute [vm_override widget_override.tactic_state_widget] widget.tactic_state_widget
