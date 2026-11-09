theory Morality_Soundness_Break
  imports Morality_Argument_Audit
begin

text \<open>
  1. Define object-level terms mapped to your zero-assumption derivation.
\<close>
datatype moral_term = 
    T_Known
  | T_Investigate

inductive moral_vdash :: "moral_term set \<Rightarrow> moral_term \<Rightarrow> bool" (infix "\<turnstile>\<^sub>m" 50) where
  zero_assumption_ought: "{} \<turnstile>\<^sub>m T_Investigate"

text \<open>
  2. Define semantics over the closed knowledge_case datatype from your audit file.
\<close>
definition moral_sem :: "knowledge_case \<Rightarrow> moral_term \<Rightarrow> bool" where
  "moral_sem c t = (case t of 
     T_Known \<Rightarrow> should_known c 
   | T_Investigate \<Rightarrow> investigate_purpose c)"

definition moral_models :: "moral_term set \<Rightarrow> moral_term \<Rightarrow> bool" (infix "\<models>\<^sub>m" 50) where
  "\<Gamma> \<models>\<^sub>m t \<equiv> \<forall>c. moral_sem c t"

text \<open>
  3. Formally prove the semantic failure witness with explicit quantifier instantiation.
\<close>
lemma semantic_failure_witness:
  "\<not> ({} \<models>\<^sub>m T_Investigate)"
  unfolding moral_models_def moral_sem_def investigate_purpose_def should_known_def
proof
  assume asm: "\<forall>c. (case T_Investigate of T_Known \<Rightarrow> c = Known_Should | T_Investigate \<Rightarrow> c = No_Known_Should)"
  have inst: "case T_Investigate of T_Known \<Rightarrow> Known_Should = Known_Should | T_Investigate \<Rightarrow> Known_Should = No_Known_Should"
    using asm [rule_format, of Known_Should] .
  thus False
    by simp
qed

text \<open>
  4. Define soundness for this custom object logic.
\<close>
definition soundness :: bool where
  "soundness \<longleftrightarrow> (\<forall>\<Gamma> t. (\<Gamma> \<turnstile>\<^sub>m t) \<longrightarrow> (\<Gamma> \models\<^sub>m t))"

text \<open>
  5. Prove the exact negation of soundness using ASCII notation (~ soundness).
\<close>
theorem not_soundness: "~ soundness"
unfolding soundness_def
proof
  assume sound_prop: "\<forall>\<Gamma> t. (\<Gamma> \<turnstile>\<^sub>m t) \<longrightarrow> (\<Gamma> \models\<^sub>m t)"
  have deriv: "{} \<turnstile>\<^sub>m T_Investigate" by (rule zero_assumption_ought)
  have sem: "{} \<models>\<^sub>m T_Investigate" using sound_prop [rule_format, OF deriv] .
  have not_sem: "\<not> ({} \<models>\<^sub>m T_Investigate)" by (rule semantic_failure_witness)
  show False using sem not_sem by contradiction
qed
thm_deps not_soundness
end
