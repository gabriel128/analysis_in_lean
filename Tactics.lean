-- Define a new tactic notation
syntax "qed" : tactic

macro_rules
  | `(tactic| qed) => `(tactic| done)
