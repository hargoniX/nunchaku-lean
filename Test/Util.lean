import Chako

syntax "chako_test" : tactic

macro_rules
  | `(tactic| chako_test) => `(tactic| chako (config := { testMode := true }))
