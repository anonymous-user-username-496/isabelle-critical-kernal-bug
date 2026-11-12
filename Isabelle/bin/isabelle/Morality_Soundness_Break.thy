theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

theorem not_soundness: "\<not> soundness"
proof
  assume sound_thm: soundness

  have gewirth_deriv: "\<lfloor>PPA (x::e) \<^bold>\<rightarrow> RightTo (x::e) FWB\<rfloor>\<^sup>D"
    using Gewirth_moral_should .

  note obligation_expansion = obligation_explicit
  note epistemic_knowledge = knowledge_explicit

  have framework_collision: "False"
    using sound_thm gewirth_deriv obligation_expansion epistemic_knowledge
    by metis

  show False
    using framework_collision by assumption
qed

thm_deps not_soundness

end
