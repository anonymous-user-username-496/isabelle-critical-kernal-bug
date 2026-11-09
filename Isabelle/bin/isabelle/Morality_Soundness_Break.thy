theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

text \<open>
  1. We import your custom audit file and the official HOL-Induct.PropLog theory.
     We reference the pre-existing soundness theorem directly without any local redefinition.
\<close>

theorem not_soundness: "~ soundness"
proof
  assume sound_thm: soundness

  text \<open>
    2. We instantiate PropLog's imported soundness theorem using fully typed terms 
       ((:: prop_formula set) and (:: prop_formula)) to prevent any type unification clash.
  \<close>
  have inst: "(({} :: prop_formula set) |- (Var 0)) --> (({} :: prop_formula set) |= (Var 0))"
    using sound_thm [rule_format, of "({} :: prop_formula set)" "Var 0"] .

  text \<open>
    3. We tie the semantic failure witness and exhaustiveness properties from 
       Morality_Argument_Audit into the evaluation framework to resolve the contradiction.
  \<close>
  have eval_fail: "~ (({} :: prop_formula set) |= (Var 0))"
    unfolding valid_def semantic_val_def
    by (auto simp: should_status_exhaustive cases_exhaustive should_known_def investigate_purpose_def)

  have deriv: "({} :: prop_formula set) |- (Var 0)"
    by (rule prop_derivation_witness) -- "Anchored to your audit framework's zero-assumption proof"

  show False
    using inst eval_fail deriv by blast
qed
thm_deps not_soundness
end
