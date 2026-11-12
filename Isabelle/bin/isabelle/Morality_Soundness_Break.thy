theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

theorem not_soundness: "~ soundness"
proof
  assume sound_thm: soundness

  have gewirth_deriv: "\<lfloor>PPA (x::e) \<^bold>\<rightarrow> RightTo (x::e) FWB\<rfloor>\<^sup>D"
    using Gewirth_moral_should .

  -- {* Alias the lemmas directly without re-parsing string literals containing \<^bold>K *}
  note obligation_expansion = obligation_explicit
  note epistemic_knowledge = knowledge_explicit

  have exhaustive_cases: "c = Known_Should | c = No_Known_Should"
    for c :: knowledge_case
    using cases_exhaustive .

  have framework_collision: "False"
  proof (cases "Known_Should :: knowledge_case")
    case Known_Should
    have c_case: "Known_Should = Known_Should | Known_Should = No_Known_Should"
      using exhaustive_cases .
    thus ?thesis
      using sound_thm gewirth_deriv obligation_expansion epistemic_knowledge c_case
      by auto
  next
    case No_Known_Should
    have c_case: "No_Known_Should = Known_Should | No_Known_Should = No_Known_Should"
      using exhaustive_cases .
    thus ?thesis
      using sound_thm gewirth_deriv obligation_expansion epistemic_knowledge c_case
      by auto
  qed

  show False
    using framework_collision by assumption
qed

thm_deps not_soundness

end
