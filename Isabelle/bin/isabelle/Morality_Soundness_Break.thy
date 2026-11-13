theory Morality_Soundness_Break
  imports Morality_Argument_Audit
begin

(* Standard-form definitions of Is and Ought bridging agency to normative status *)
definition standard_is :: "e \<Rightarrow> bool" where
  "standard_is x \<equiv> \<lfloor>PPA x\<rfloor>\<^sup>D"

definition standard_ought :: "e \<Rightarrow> bool" where
  "standard_ought x \<equiv> \<lfloor>RightTo x FWB\<rfloor>\<^sup>D"

(* Deriving the normative Ought from the descriptive Is using the audit framework *)
theorem is_to_ought_derivation:
  fixes x :: e
  assumes agent_premise: "standard_is x"
  shows "standard_ought x"
proof -
  have ppa_modal: "\<lfloor>PPA x\<rfloor>\<^sup>D"
    using agent_premise unfolding standard_is_def .

  have gewirth_implication: "\<lfloor>PPA x \<^bold>\<rightarrow> RightTo x FWB\<rfloor>\<^sup>D"
    using Gewirth_moral_should .

  have normative_modal: "\<lfloor>RightTo x FWB\<rfloor>\<^sup>D"
    using gewirth_implication ppa_modal by blast

  thus ?thesis
    unfolding standard_ought_def .
qed

(* Moral should instantiation via standard form *)
theorem moral_should_derivation:
  fixes x :: e
  assumes agent_premise: "standard_is x"
  shows "moral_should x"
proof -
  have norm: "standard_ought x"
    using is_to_ought_derivation [OF agent_premise] .

  thus ?thesis
    unfolding moral_should_def standard_ought_def .
qed

(* Integrating the case audit structure (Known_Should vs No_Known_Should) *)
theorem audit_case_integration:
  fixes x :: e and c :: knowledge_case
  assumes agent_premise: "standard_is x"
  shows "c = Known_Should \<or> c = No_Known_Should"
proof -
  have case_ex: "c = Known_Should \<or> c = No_Known_Should"
    using cases_exhaustive .

  have normative_derived: "moral_should x"
    using moral_should_derivation [OF agent_premise] .

  thus ?thesis
    using case_ex by blast
qed

thm_deps not_soundness

end
