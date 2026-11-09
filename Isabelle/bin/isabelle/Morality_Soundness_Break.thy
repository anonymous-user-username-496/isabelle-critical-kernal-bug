theory Morality_Soundness_Break
  imports Morality_Argument_Audit
begin

text \<open>
  1. Define object-level terms mapped to your zero-assumption derivation using pure ASCII.
\<close>
datatype moral_term = 
    T_Known
  | T_Investigate

inductive moral_vdash :: "moral_term set => moral_term => bool" (infix "|-" 50) where
  zero_assumption_ought: "{} |- T_Investigate"

text \<open>
  2. Define semantics over the closed knowledge_case datatype from your audit file.
\<close>
definition moral_sem :: "knowledge_case => moral_term => bool" where
  "moral_sem c t = (case t of 
     T_Known => should_known c 
   | T_Investigate => investigate_purpose c)"

definition moral_models :: "moral_term set => moral_term => bool" (infix "|=" 50) where
  "Gamma |= t == ALL c. moral_sem c t"

text \<open>
  3. Formally prove the semantic failure witness using pure ASCII syntax.
\<close>
lemma semantic_failure_witness:
  "~ ({} |= T_Investigate)"
  unfolding moral_models_def moral_sem_def investigate_purpose_def should_known_def
proof
  assume asm: "ALL c. (case T_Investigate of T_Known => c = Known_Should | T_Investigate => c = No_Known_Should)"
  have inst: "case T_Investigate of T_Known => Known_Should = Known_Should | T_Investigate => Known_Should = No_Known_Should"
    using asm [rule_format, of Known_Should] .
  thus False
    by simp
qed

text \<open>
  4. Define soundness explicitly for this object logic in ASCII.
\<close>
definition soundness :: bool where
  "soundness <-> (ALL Gamma t. (Gamma |- t) --> (Gamma |= t))"

text \<open>
  5. Prove the exact negation of soundness with zero unicode parsing risks.
\<close>
theorem not_soundness: "~ soundness"
unfolding soundness_def
proof
  assume sound_prop: "ALL Gamma t. (Gamma |- t) --> (Gamma |= t)"
  have deriv: "{} |- T_Investigate" by (rule zero_assumption_ought)
  have sem: "{} |= T_Investigate" using sound_prop [rule_format, of deriv] .
  have not_sem: "~ ({} |= T_Investigate)" by (rule semantic_failure_witness)
  show False using sem not_sem by contradiction
qed
thm_deps not_soundness
end
