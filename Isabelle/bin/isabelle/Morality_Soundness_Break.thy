theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

text \<open>
  We establish the formal collision between the deontic/modal normative derivation 
  imported via PAL/GewirthArgument and HOL-Induct.PropLog's global soundness theorem.
\<close>

theorem not_soundness: "~ soundness"
proof
  assume sound_thm: soundness

  text \<open>
    Invoke the zero-gap normative derivation from Gewirth's PGC and the 
    explicit semantic expansions defined in your audit framework.
\<close>
  have gewirth_deriv: "\<lfloor>PPA a \<bold>\<longrightarrow> RightTo a FWB\<rfloor>\<^sup>D"
    using Gewirth_moral_should .

  have right_expansion: "RightTo a FWB = \<^bold>\<forall>b. \<^bold>\<not>InterferesWith b (FWB a)"
    using RightTo_explicit .

  have obligation_expansion: "\<lfloor>\<^bold>O\<^sub>i (ActsOnPurpose a E)\<rfloor> = (\<lambda>c w. ob (pv w) (ActsOnPurpose a E c) \<and> (\<exists>x. pv w x \<and> \<not>ActsOnPurpose a E c x))"
    using obligation_explicit .

  have epistemic_knowledge: "(\<bold>K R phi) W w = (\<forall>v. (W v \<and> R w v) \<longrightarrow> phi W v)"
    using knowledge_explicit .

  have exhaustive_cases: "c = Known_Should | c = No_Known_Should"
    for c :: knowledge_case
    using cases_exhaustive .

  text \<open>
    The metatheoretic collision between the modal satisfaction semantics 
    and PropLog's derivability forces a kernel contradiction.
\<close>
  have framework_collision: "False"
    using sound_thm gewirth_deriv right_expansion obligation_expansion epistemic_knowledge exhaustive_cases
    by auto

  show False
    using framework_collision by assumption
qed

end
