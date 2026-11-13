theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

theorem is_to_ought_derivation:
  fixes x :: e
  assumes agent_premise: "\<lfloor>PPA x\<rfloor>\<^sup>D"
  shows "\<lfloor>RightTo x FWB\<rfloor>\<^sup>D"
proof -
  have gewirth_implication: "\<lfloor>PPA x \<^bold>\<rightarrow> RightTo x FWB\<rfloor>\<^sup>D"
    using Gewirth_moral_should .

  show ?thesis
    using gewirth_implication agent_premise
    by blast
qed

theorem moral_should_derivation:
  fixes x :: e
  assumes agent_premise: "\<lfloor>PPA x\<rfloor>\<^sup>D"
  shows "moral_should x"
proof -
  have norm: "\<lfloor>RightTo x FWB\<rfloor>\<^sup>D"
    using is_to_ought_derivation [OF agent_premise] .

  thus ?thesis
    unfolding moral_should_def .
qed

theorem not_soundness: "\<not> soundness"
proof (rule notI)
  assume sound_hyp: soundness

  have gewirth_deriv: "\<lfloor>PPA (x::e) \<^bold>\<rightarrow> RightTo (x::e) FWB\<rfloor>\<^sup>D"
    using Gewirth_moral_should .

  have exhaustive_cases: "c = Known_Should \<or> c = No_Known_Should"
    for c :: knowledge_case
    using cases_exhaustive .

  have case_known_should: "False"
  proof -
    have c_eval: "(Known_Should :: knowledge_case) = Known_Should \<or> (Known_Should :: knowledge_case) = No_Known_Should"
      using exhaustive_cases [of Known_Should] .

    have h1: "Known_Should = Known_Should" by simp
    have s_ref: "soundness" using sound_hyp .

    show ?thesis
      using s_ref gewirth_deriv c_eval h1
      by blast
  qed

  have case_no_known_should: "False"
  proof -
    have c_eval: "(No_Known_Should :: knowledge_case) = Known_Should \<or> (No_Known_Should :: knowledge_case) = No_Known_Should"
      using exhaustive_cases [of No_Known_Should] .

    have h1: "No_Known_Should = No_Known_Should" by simp
    have s_ref: "soundness" using sound_hyp .

    show ?thesis
      using s_ref gewirth_deriv c_eval h1
      by blast
  qed

  show False
    using exhaustive_cases [of Known_Should] case_known_should case_no_known_should
    by blast
qed

thm_deps not_soundness

end
