theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

theorem not_soundness: "\<not> soundness"
proof
  assume sound_thm: soundness

  have gewirth_deriv: "\<lfloor>PPA (x::e) \<^bold>\<rightarrow> RightTo (x::e) FWB\<rfloor>\<^sup>D"
    using Gewirth_moral_should .

  have exhaustive_cases: "c = Known_Should \<or> c = No_Known_Should"
    for c :: knowledge_case
    using cases_exhaustive .

  have framework_collision: "False"
  proof (cases "Known_Should :: knowledge_case")
    case Known_Should
    have c_case: "Known_Should = Known_Should \<or> Known_Should = No_Known_Should"
      using exhaustive_cases .
    (* Use sound_thm directly without manual token parsing of internal symbols *)
    have s_use: "soundness" using sound_thm .
    thus ?thesis
      using gewirth_deriv c_case s_use
      by blast
  next
    case No_Known_Should
    have c_case: "No_Known_Should = Known_Should \<or> No_Known_Should = No_Known_Should"
      using exhaustive_cases .
    have s_use: "soundness" using sound_thm .
    thus ?thesis
      using gewirth_deriv c_case s_use
      by blast
  qed

  show False
    using framework_collision by assumption
qed

thm_deps not_soundness

end
