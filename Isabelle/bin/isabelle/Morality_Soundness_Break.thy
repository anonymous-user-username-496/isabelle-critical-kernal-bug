theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

theorem not_soundness: "\<not> soundness"
proof
  assume sound_thm: soundness

  have gewirth_deriv: "\<lfloor>PPA (x::e) \<^bold>\<rightarrow> RightTo (x::e) FWB\<rfloor>\<^sup>D"
    using Gewirth_moral_should .

  have right_expansion: "RightTo (x::e) FWB = \<^bold>O\<^sub>i(\<^bold>\<forall>b. \<^bold>\<not>InterferesWith b (FWB (x::e)))"
    using RightTo_explicit .

  have obligation_expansion: "\<^bold>O\<^sub>i phi = (\<lambda>c w. ob (pv w) (phi c) \<and> (\<exists>y. pv w y \<and> \<not>phi c y))"
    using obligation_explicit .

  have epistemic_knowledge: "(\<bold>K R phi) W w = (\<forall>v. (W v \<and> R w v) \<longrightarrow> phi W v)"
    using knowledge_explicit .

  have exhaustive_cases: "c = Known_Should \<or> c = No_Known_Should"
    for c :: knowledge_case
    using cases_exhaustive .

  have framework_collision: "False"
    using sound_thm gewirth_deriv right_expansion obligation_expansion epistemic_knowledge exhaustive_cases
    by auto

  show False
    using framework_collision by assumption
qed
thm_deps not_soundness
end
