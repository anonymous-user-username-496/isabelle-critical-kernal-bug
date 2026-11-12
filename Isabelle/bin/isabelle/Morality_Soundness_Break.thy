theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

theorem not_soundness: "~ soundness"
proof
  assume sound_thm: soundness

  have gewirth_deriv: "\<lfloor>PPA (x::e) \<^bold>\<rightarrow> RightTo (x::e) FWB\<rfloor>\<^sup>D"
    using Gewirth_moral_should .

  have right_expansion: "RightTo (x::e) FWB = \<^bold>O\<^sub>i(ALL b. ~InterferesWith b (FWB (x::e)))"
    using RightTo_explicit .

  have obligation_expansion: "\<^bold>O\<^sub>i phi = (\<lambda>c w. ob (pv w) (phi c) & (EX y. pv w y & ~phi c y))"
    using obligation_explicit .

  have epistemic_knowledge: "(\<bold>K R phi) W w = (ALL v. (W v & R w v) --> phi W v)"
    using knowledge_explicit .

  have exhaustive_cases: "c = Known_Should | c = No_Known_Should"
    for c :: knowledge_case
    using cases_exhaustive .

  have framework_collision: "False"
    using sound_thm gewirth_deriv right_expansion obligation_expansion epistemic_knowledge exhaustive_cases
    by auto

  show False
    using framework_collision by assumption
qed

end
