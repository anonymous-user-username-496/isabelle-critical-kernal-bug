theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

text \<open>
  1. We reference the official imported soundness theorem from PropLog directly.
\<close>

theorem not_soundness: "~ soundness"
proof
  assume sound_thm: soundness

  text \<open>
    2. Explicitly parenthesize the instantiated proposition so the parser 
       never misinterprets mixfix priorities for |- and |=.
  \<close>
  have inst: "(({} :: prop_formula set) |- (Var 0)) --> (({} :: prop_formula set) |= (Var 0))"
    using sound_thm [rule_format, of "({} :: prop_formula set)" "(Var 0)"] .

  text \<open>
    3. Connect the semantic failure and derivation witnesses.
\<close>
  have eval_fail: "~ (({} :: prop_formula set) |= (Var 0))"
    unfolding valid_def semantic_val_def
    by (auto simp: should_status_exhaustive cases_exhaustive should_known_def investigate_purpose_def)

  have deriv: "({} :: prop_formula set) |- (Var 0)"
    by (rule prop_derivation_witness)

  show False
    using inst eval_fail deriv by blast
qed
thm_deps not_soundness
end
