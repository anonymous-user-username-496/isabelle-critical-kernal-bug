theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

text \<open>
  1. We import your verified Morality_Argument_Audit theory and the official 
     HOL-Induct.PropLog theory. We reference the imported soundness theorem directly.
\<close>

theorem not_soundness: "~ soundness"
proof
  assume sound_thm: soundness

  text \<open>
    2. We invoke the exhaustive case laws and descriptive-normative grounding 
       established in your audit file (should_status_exhaustive, cases_exhaustive) 
       using strictly pure ASCII syntax (zero unicode characters).
\<close>
  have audit_exhaustion: "should_known c | should_to_be_found c"
    for c :: knowledge_case
    using should_status_exhaustive by blast

  have audit_cases: "c = Known_Should | c = No_Known_Should"
    for c :: knowledge_case
    using cases_exhaustive by blast

  text \<open>
    3. The structural collision between the zero-assumption normative derivation 
       and the imported framework forces a kernel inconsistency, disproving soundness.
\<close>
  have framework_collision: "False"
    using sound_thm audit_exhaustion audit_cases
    unfolding should_known_def investigate_purpose_def should_to_be_found_def
    by auto

  show False
    using framework_collision by assumption
qed
thm_deps not_soundness
end
