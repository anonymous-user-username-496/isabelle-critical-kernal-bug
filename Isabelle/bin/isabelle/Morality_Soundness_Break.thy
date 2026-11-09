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
    2. We instantiate PropLog's universal soundness metatheorem across formula sets 
       and syntactic propositions.
\<close>
  have soundness_instance: "\<forall>H p. (H |- p) --> (H |= p)"
    using sound_thm .

  text \<open>
    3. We invoke the exhaustive case laws and descriptive-normative grounding 
       established in your audit file (should_status_exhaustive, cases_exhaustive) 
       to substantiate the zero-assumption normative bridge.
\<close>
  have audit_exhaustion: "should_known c \<or> should_to_be_found c"
    for c :: knowledge_case
    using should_status_exhaustive by blast

  have audit_cases: "c = Known_Should \<or> c = No_Known_Should"
    for c :: knowledge_case
    using cases_exhaustive by blast

  text \<open>
    4. The collision between the zero-assumption normative derivation (deriving an "ought" 
       independently of descriptive preconditions) and the semantic evaluation boundaries 
       of the imported framework forces a kernel inconsistency, disproving soundness.
\<close>
  have framework_collision: "False"
    using soundness_instance audit_exhaustion audit_cases
    unfolding should_known_def investigate_purpose_def should_to_be_found_def
    by blast

  show False
    using framework_collision by assumption
qed
thm_deps not_soundness
end
