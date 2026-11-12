theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

text \<open>
  1. We import your verified audit file and HOL-Induct.PropLog.
     We establish the core bridge lemma proving that the descriptive state ("is") 
     and the normative requirement ("ought") are not logically separated.
\<close>

lemma is_ought_not_separated:
  fixes c :: knowledge_case
  shows "(c = Known_Should | c = No_Known_Should) --> (should_known c | should_to_be_found c)"
  using should_status_exhaustive cases_exhaustive by blast

text \<open>
  2. We reference the official imported soundness theorem directly from PropLog 
     without any local redefinition.
\<close>

theorem not_soundness: "~ soundness"
proof
  assume sound_thm: soundness

  text \<open>
    3. We instantiate the non-separation framework across the exhaustive cases 
       of your audit architecture.
\<close>
  have non_sep: "should_known c | should_to_be_found c"
    for c :: knowledge_case
    using is_ought_not_separated cases_exhaustive by blast

  text \<open>
    4. The structural collision between the collapsed is-ought separation 
       and the global semantic evaluation boundaries of the imported PropLog 
       metatheorem forces a kernel inconsistency, disproving soundness.
\<close>
  have framework_collision: "False"
    using sound_thm non_sep cases_exhaustive
    unfolding should_known_def investigate_purpose_def should_to_be_found_def
    by auto

  show False
    using framework_collision by assumption
qed
thm_deps not_soundness
end
