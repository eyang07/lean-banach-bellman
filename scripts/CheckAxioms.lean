import BanachBellman

-- Verify the reported axioms of each main result. The guards fail if a result
-- gains an unexpected axiom such as sorryAx.
/-- info: 'banach_fixed_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms banach_fixed_point
/-- info: 'bellman_is_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bellman_is_contraction
/-- info: 'bellman_eq_uniq_existence_of_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bellman_eq_uniq_existence_of_solution
/-- info: 'global_conv_of_contraction_dynamics' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms global_conv_of_contraction_dynamics
/-- info: 'iterate_eval_conv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iterate_eval_conv
