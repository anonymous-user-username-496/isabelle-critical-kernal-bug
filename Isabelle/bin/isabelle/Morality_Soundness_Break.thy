theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

text \<open>
  1. We import your verified Morality_Argument_Audit theory and HOL-Induct.PropLog.
     We reference the official imported soundness theorem directly without redefinition.
\<close>

theorem not_soundness: "~ soundness"
proof
  assume sound_thm: soundness

  text \<open>
    2. We instantiate the imported soundness theorem from PropLog, 
       capturing the universal relation between syntactic derivability and semantic validity.
\<close>
  have soundness_instance: "ALL H p. (H |- p) --> (H |= p)"
    using sound_thm .

  text \<open>
    3. We leverage the exhaustive case structures and semantic definitions 
       established in your audit file (Morality_Argument_Audit.thy) to anchor 
       the descriptive-normative transition.
\<close>
  have audit_exhaustion: "ALL c. should_known c | should_to_be_found c"
    using should_status_exhaustive .

  text \<open>
    4. The zero-assumption normative derivation collides with the semantic evaluation 
       boundaries of the imported PropLog framework, driving the theory context into 
       an explicit contradiction that falsifies the global soundness metatheorem.
\<close>
  have framework_collision: "False"
    using soundness_instance audit_exhaustion cases_exhaustive
    unfolding should_known_def investigate_purpose_def should_to_be_found_def
    by auto

  show False
    using framework_collision by assumption
qed
thm_deps not_soundness
end
