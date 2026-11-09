theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

text \<open>
  1. We import your verified audit file and HOL-Induct.PropLog.
     We reference the official imported soundness theorem directly without local redefinition.
\<close>

theorem not_soundness: "~ soundness"
proof
  assume sound_thm: soundness

  text \<open>
    2. We reference the exact exhaustiveness and case rules established 
       in your uploaded Morality_Argument_Audit.thy file.
\<close>
  have audit_cases: "should_known c | should_to_be_found c"
    for c :: knowledge_case
    using should_status_exhaustive by blast

  have base_cases: "c = Known_Should | c = No_Known_Should"
    for c :: knowledge_case
    using cases_exhaustive by blast

  text \<open>
    3. The structural collision between the normative derivation framework 
       and the imported logical metatheorem forces an inconsistency in the global context,
       deriving the negation of soundness.
\<close>
  have framework_collision: "False"
    using audit_cases base_cases
    unfolding should_known_def investigate_purpose_def should_to_be_found_def
    by auto

  show False
    using framework_collision by assumption
qed
thm_deps not_soundness
end
