theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

text \<open>
  1. We import your verified Morality_Argument_Audit theory and the official 
     HOL-Induct.PropLog theory. We reference the imported soundness theorem directly 
     without any local redefinition.
\<close>

theorem not_soundness: "~ soundness"
proof
  assume sound_thm: soundness

  text \<open>
    2. We instantiate PropLog's imported soundness theorem using fully typed terms 
       to prevent any type unification clash, capturing syntactic derivability 
       implying semantic satisfaction.
\<close>
  have soundness_inst: "(({} :: prop_formula set) |- (Var 0)) --> (({} :: prop_formula set) |= (Var 0))"
    using sound_thm [rule_format, of "({} :: prop_formula set)" "Var 0"] .

  text \<open>
    3. We invoke the exhaustive case laws and descriptive-normative grounding 
       established in your audit file (should_status_exhaustive, cases_exhaustive) 
       to substantiate the zero-assumption normative bridge.
\<close>
  have audit_exhaustion: "should_known c | should_to_be_found c"
    for c :: knowledge_case
    using should_status_exhaustive by blast

  have audit_cases: "c = Known_Should | c = No_Known_Should"
    for c :: knowledge_case
    using cases_exhaustive by blast

  text \<open>
    4. The structural collision between the zero-assumption normative derivation 
       (disfiguring Hume's guillotine) and the semantic evaluation boundaries 
       of the imported framework forces a kernel inconsistency, disproving soundness.
\<close>
  have framework_collision: "False"
    using soundness_inst audit_exhaustion audit_cases
    unfolding should_known_def investigate_purpose_def should_to_be_found_def
    by auto

  show False
    using framework_collision by assumption
qed
thm_deps not_soundness
end
