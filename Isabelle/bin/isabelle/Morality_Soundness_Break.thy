theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

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

    have modal_grounding: "\<lfloor>PPA x \<^bold>\<rightarrow> RightTo x FWB\<rfloor>\<^sup>D"
      using gewirth_deriv .

    have collision_1: "False"
    proof -
      have step_a: "(Known_Should :: knowledge_case) = Known_Should" by simp
      have step_b: "soundness" using sound_hyp .
      have step_c: "(\<exists>c. c = Known_Should) \<and> soundness" 
        using step_a step_b by blast
      thus ?thesis
        using modal_grounding obligation_explicit knowledge_explicit should_known_def c_eval
        by blast
    qed

    show ?thesis using collision_1 .
  qed

  have case_no_known_should: "False"
  proof -
    have c_eval: "(No_Known_Should :: knowledge_case) = Known_Should \<or> (No_Known_Should :: knowledge_case) = No_Known_Should"
      using exhaustive_cases [of No_Known_Should] .

    have modal_grounding: "\<lfloor>PPA x \<^bold>\<rightarrow> RightTo x FWB\<rfloor>\<^sup>D"
      using gewirth_deriv .

    have collision_2: "False"
    proof -
      have step_a: "(No_Known_Should :: knowledge_case) = No_Known_Should" by simp
      have step_b: "soundness" using sound_hyp .
      have step_c: "(\<exists>c. c = No_Known_Should) \<and> soundness"
        using step_a step_b by blast
      thus ?thesis
        using modal_grounding obligation_explicit knowledge_explicit investigate_purpose_def c_eval
        by blast
    qed

    show ?thesis using collision_2 .
  qed

  show False
    using exhaustive_cases [of Known_Should] case_known_should case_no_known_should
    by blast
qed

thm_deps not_soundness

end
