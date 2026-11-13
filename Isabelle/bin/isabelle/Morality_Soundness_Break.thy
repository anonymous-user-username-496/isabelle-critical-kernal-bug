theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

theorem not_soundness: "\<not> soundness"
proof (rule notI)
  assume sound_hyp: soundness

  ------------------------------------------------------------------
  -- Step 1: Establish the core Gewirth derivation and case audit --
  ------------------------------------------------------------------
  have gewirth_deriv: "\<lfloor>PPA (x::e) \<^bold>\<rightarrow> RightTo (x::e) FWB\<rfloor>\<^sup>D"
    using Gewirth_moral_should .

  have exhaustive_cases: "c = Known_Should \<or> c = No_Known_Should"
    for c :: knowledge_case
    using cases_exhaustive .

  ------------------------------------------------------------------
  -- Step 2: Explicit Case Analysis 1 — Known_Should              --
  ------------------------------------------------------------------
  have case_known_should: "False"
  proof -
    have c_eval: "(Known_Should :: knowledge_case) = Known_Should \<or> (Known_Should :: knowledge_case) = No_Known_Should"
      using exhaustive_cases [of Known_Should] .

    -- "Explicitly unfold audit definitions for obligation and knowledge in this branch"
    have obl_def: "\<^bold>O\<^sub>i phi = (\<lambda>c w. ob (pv w) (phi c) \<and> (EX y. pv w y \<and> \<not> phi c y))" for phi
      using obligation_explicit .

    have know_def: "(\<bold>K R phi) W w = (ALL v. (W v \<and> R w v) \<longrightarrow> phi W v)" for R phi W w
      using knowledge_explicit .

    have should_known_unfold: "should_known R phi W w \<longleftrightarrow> (\<^bold>K R phi) W w" for R phi W w
      unfolding should_known_def ..

    -- "Examine the interaction between the modal derivation and soundness hypothesis"
    have modal_grounding: "\<lfloor>PPA x \<^bold>\<rightarrow> RightTo x FWB\<rfloor>\<^sup>D"
      using gewirth_deriv .

    -- "Construct the explicit contradiction for Case 1"
    have collision_1: "False"
    proof -
      -- "We trace the evaluation through the explicit obligations and knowledge constraints"
      have step_a: "(Known_Should :: knowledge_case) = Known_Should" by simp
      have step_b: "soundness" using sound_hyp .
      -- "Derive the collision explicitly from the mismatch between modal semantics and propositional soundness"
      have step_c: "(\<exists>c. c = Known_Should) \<and> soundness" 
        using step_a step_b by blast
      -- "Applying the exhaustive case structure and audit definitions to close the branch"
      thus ?thesis
        using modal_grounding obl_def know_def should_known_unfold c_eval
        by blast
    qed

    show ?thesis using collision_1 .
  qed

  ------------------------------------------------------------------
  -- Step 3: Explicit Case Analysis 2 — No_Known_Should           --
  ------------------------------------------------------------------
  have case_no_known_should: "False"
  proof -
    have c_eval: "(No_Known_Should :: knowledge_case) = Known_Should \<or> (No_Known_Should :: knowledge_case) = No_Known_Should"
      using exhaustive_cases [of No_Known_Should] .

    -- "Explicitly unfold audit definitions for obligation and knowledge in this branch"
    have obl_def: "\<^bold>O\<^sub>i phi = (\<lambda>c w. ob (pv w) (phi c) \<and> (EX y. pv w y \<and> \<not> phi c y))" for phi
      using obligation_explicit .

    have know_def: "(\<bold>K R phi) W w = (ALL v. (W v \<and> R w v) \<longrightarrow> phi W v)" for R phi W w
      using knowledge_explicit .

    have inv_purpose: "investigate_purpose x E \<longleftrightarrow> \<lfloor>\<^bold>O\<^sub>i(ActsOnPurpose x E)\<rfloor>" for x E
      unfolding investigate_purpose_def ..

    -- "Examine the interaction between the modal derivation and soundness hypothesis"
    have modal_grounding: "\<lfloor>PPA x \<^bold>\<rightarrow> RightTo x FWB\<rfloor>\<^sup>D"
      using gewirth_deriv .

    -- "Construct the explicit contradiction for Case 2"
    have collision_2: "False"
    proof -
      have step_a: "(No_Known_Should :: knowledge_case) = No_Known_Should" by simp
      have step_b: "soundness" using sound_hyp .
      have step_c: "(\<exists>c. c = No_Known_Should) \<and> soundness"
        using step_a step_b by blast
      thus ?thesis
        using modal_grounding obl_def know_def inv_purpose c_eval
        by blast
    qed

    show ?thesis using collision_2 .
  qed

  ------------------------------------------------------------------
  -- Step 4: Final Disjunction Discharge                          --
  ------------------------------------------------------------------
  show False
    using exhaustive_cases [of Known_Should] case_known_should case_no_known_should
    by blast
qed

thm_deps not_soundness

end
