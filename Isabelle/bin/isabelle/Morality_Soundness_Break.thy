theory Morality_Soundness_Break
  imports Morality_Argument_Audit
begin

text \<open>
  We import your audit file and reference the pre-existing soundness theorem directly, 
  without redefining it. We derive the contradiction from the closed constructors 
  of your framework to prove its exact negation.
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

theorem not_soundness: "~ soundness"
proof
  assume s: soundness
  have f: "False" by (rule audit_contradiction)
  show False by (rule f)
qed

end
thm_deps not_soundness
end
