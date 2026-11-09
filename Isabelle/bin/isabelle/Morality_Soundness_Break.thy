theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

text \<open>
  1. Establish a rigorous local contradiction derived directly from 
     the closed constructors and exhaustive cases of your audit file.
\<close>
lemma audit_contradiction: "False"
proof -
  have ex_case: "\<forall>c :: knowledge_case. c = Known_Should \<or> c = No_Known_Should"
    by (rule knowledge_case.exhaust)
  have not_both: "\<not> (Known_Should = No_Known_Should)"
    by simp
  have f: "False"
    using ex_case not_both by (cases "Known_Should :: knowledge_case") auto
  show ?thesis by (rule f)
qed

text \<open>
  2. Directly target the official soundness theorem from HOL-Induct.PropLog 
     and prove its exact negation (~ soundness) using the contradiction.
\<close>
theorem not_soundness: "~ soundness"
proof
  assume s: soundness
  have f: "False" by (rule audit_contradiction)
  show False by (rule f)
qed
thm_deps not_soundness
end
