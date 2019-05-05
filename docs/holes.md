# Hole commands #

Both VS Code and emacs support integration for 'hole commands'.

In VS Code, if you enter `{! !}`, a small light bulb symbol will appear, and
clicking on it gives a drop down menu of available hole commands. Running one
of these will replace the `{! !}` with whatever text that hole command provides.

### instance_stub
(Requires `import tactic.basic`.)

Invoking the hole command `Instance Stub` on

```
instance : monad id :=
{! !}
```

produces

```
instance : monad id :=
{ map := _,
  map_const := _,
  pure := _,
  seq := _,
  seq_left := _,
  seq_right := _,
  bind := _ }
```

### tidy
(Requires `import tactic.tidy`.)

Invoking the hole command `tidy` runs the tactic of the same name,
replacing the hole with the tactic script `tidy` produces.