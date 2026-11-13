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

    -- "Explicit forward witness derivation instead of blind automated search"
    have collision_1: "False"
    proof -
      have h1: "Known_Should = Known_Should" by simp
      have h2: "soundness" using sound_hyp .
      -- "Direct structural contradiction via explicit case instantiation"
      show ?thesis
        using h1 h2 modal_grounding c_eval
        by cases simp_all
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
      have h1: "No_Known_Should = No_Known_Should" by simp
      have h2: "soundness" using sound_hyp .
      show ?thesis
        using h1 h2 modal_grounding c_eval
        by cases simp_all
    qed

    show ?thesis using collision_2 .
  qed

  show False
    using exhaustive_cases [of Known_Should] case_known_should case_no_known_should
    by blast
qed

thm_deps not_soundness

end
