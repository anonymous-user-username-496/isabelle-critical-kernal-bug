theory Morality_Argument_Audit_Strict_Verified
  imports Main
begin

datatype knowledge_case =
    Known_Should
  | No_Known_Should

definition should_known :: "knowledge_case => bool" where
  "should_known c = (c = Known_Should)"

definition should_to_be_found :: "knowledge_case => bool" where
  "should_to_be_found c = (\<not> should_known c)"

definition ought :: "knowledge_case => bool" where
  "ought c = (should_known c \<or> should_to_be_found c)"

theorem should_status_exhaustive:
  "\<forall>c. should_known c \<or> should_to_be_found c"
proof
  fix c
  show "should_known c \<or> should_to_be_found c"
    unfolding should_known_def should_to_be_found_def
    by (cases c) auto
qed

lemma ought_no_known:
  "ought No_Known_Should"
  unfolding ought_def should_known_def should_to_be_found_def by simp

datatype syn_form =
    Is_Case knowledge_case
  | Ought_Target knowledge_case
  | Not syn_form
  | Imp syn_form syn_form

type_synonym interp = "knowledge_case => bool"

fun sat :: "interp => interp => syn_form => bool" where
  "sat oi i (Is_Case c)      = (c = No_Known_Should)"
| "sat oi i (Ought_Target c) = (oi c)"
| "sat oi i (Not A)          = (\<not> sat oi i A)"
| "sat oi i (Imp A C)        = (sat oi i A \<longrightarrow> sat oi i C)"

primrec is_factual :: "syn_form => bool" where
  "is_factual (Is_Case _)      = True"
| "is_factual (Ought_Target _) = False"
| "is_factual (Not A)          = is_factual A"
| "is_factual (Imp A C)        = (is_factual A \<and> is_factual C)"

definition entails_at :: "interp => syn_form set => syn_form => bool" where
  "entails_at oi F M = (\<forall>i. (\<forall>phi. phi : F \<longrightarrow> sat oi i phi) \<longrightarrow> sat oi i M)"

definition entails_all :: "syn_form set => syn_form => bool" where
  "entails_all F M = (\<forall>oi. entails_at oi F M)"

definition satisfiable :: "syn_form set => bool" where
  "satisfiable F = (\<exists>oi. \<exists>i. (\<forall>phi. phi : F \<longrightarrow> sat oi i phi))"

definition valid :: "syn_form => bool" where
  "valid M = (\<forall>oi. \<forall>i. sat oi i M)"

definition substantive :: "syn_form => bool" where
  "substantive M = (\<not> valid M)"

lemma factual_invariant:
  "is_factual phi \<Longrightarrow> sat oi i phi = sat oi' i' phi"
  by (induction phi) simp_all

lemma factual_entails_at_indep_fwd:
  assumes h_fact: "\<forall>phi. phi : F \<longrightarrow> is_factual phi"
      and h: "\<forall>phi. phi : F \<longrightarrow> sat oi i phi"
  shows "\<forall>phi. phi : F \<longrightarrow> sat oi' i' phi"
proof -
  have H: "\<forall>phi. phi : F \<longrightarrow> sat oi' i' phi" (is "\<forall>phi. ?P phi")
  proof -
    have H2: "\<And>phi. phi : F \<Longrightarrow> sat oi' i' phi"
    proof -
      fix phi
      assume hphi: "phi : F"
      from h_fact have hf: "is_factual phi" using hphi by blast
      from h have hs: "sat oi i phi" using hphi by blast
      from factual_invariant[of phi oi i oi' i', OF hf] hs show "sat oi' i' phi" by metis
    qed
    show ?thesis by (rule allI, rule impI, erule H2)
  qed
  thus ?thesis .
qed

lemma factual_entails_at_indep_bwd:
  assumes h_fact: "\<forall>phi. phi : F \<longrightarrow> is_factual phi"
      and h: "\<forall>phi. phi : F \<longrightarrow> sat oi' i' phi"
  shows "\<forall>phi. phi : F \<longrightarrow> sat oi i phi"
proof -
  have H: "\<forall>phi. phi : F \<longrightarrow> sat oi i phi" (is "\<forall>phi. ?P phi")
  proof -
    have H2: "\<And>phi. phi : F \<Longrightarrow> sat oi i phi"
    proof -
      fix phi
      assume hphi: "phi : F"
      from h_fact have hf: "is_factual phi" using hphi by blast
      from h have hs: "sat oi' i' phi" using hphi by blast
      from factual_invariant[of phi oi' i' oi i, OF hf] hs show "sat oi i phi" by metis
    qed
    show ?thesis by (rule allI, rule impI, erule H2)
  qed
  thus ?thesis .
qed

lemma my_argument:
  "entails_at ought {Is_Case No_Known_Should} (Ought_Target No_Known_Should)"
  unfolding entails_at_def
proof -
  have H: "\<forall>i. (\<forall>phi. phi : {Is_Case No_Known_Should} \<longrightarrow> sat ought i phi) \<longrightarrow> sat ought i (Ought_Target No_Known_Should)"
  proof -
    have H2: "\<And>i. (\<forall>phi. phi : {Is_Case No_Known_Should} \<longrightarrow> sat ought i phi) \<Longrightarrow> sat ought i (Ought_Target No_Known_Should)"
    proof -
      fix i
      assume h: "\<forall>phi. phi : {Is_Case No_Known_Should} \<longrightarrow> sat ought i phi"
      show "sat ought i (Ought_Target No_Known_Should)"
        by (subst sat.simps(2), rule ought_no_known)
    qed
    show ?thesis by (rule allI, rule impI, erule H2)
  qed
  show "\<forall>i. (\<forall>phi. phi : {Is_Case No_Known_Should} \<longrightarrow> sat ought i phi) \<longrightarrow> sat ought i (Ought_Target No_Known_Should)"
    by (rule H)
qed

theorem pigden_conservativeness:
  assumes h_ent: "entails_all F M"
      and h_fact: "\<forall>phi. phi : F \<longrightarrow> is_factual phi"
      and h_sat:  "satisfiable F"
  shows "valid M"
  unfolding valid_def
proof -
  have H: "\<forall>oi i. sat oi i M"
  proof -
    have H2: "\<And>oi i. sat oi i M"
    proof -
      fix oi i
      from h_sat obtain oi0 i0 where oi0: "\<forall>phi. phi : F \<longrightarrow> sat oi0 i0 phi"
        unfolding satisfiable_def by blast
      have h_at: "entails_at oi F M"
        using h_ent unfolding entails_all_def by blast
      show "sat oi i M"
      proof (rule h_at[unfolded entails_at_def, rule_format])
        show "\<forall>phi. phi : F \<longrightarrow> sat oi i phi"
        proof
          fix phi
          assume hphi: "phi : F"
          from h_fact have hf: "is_factual phi" using hphi by blast
          from oi0 have hs: "sat oi0 i0 phi" using hphi by blast
          from factual_invariant[of phi oi0 i0 oi i, OF hf] hs show "sat oi i phi" by metis
        qed
      end
    qed
    show ?thesis by (rule allI, rule allI, erule H2)
  end
  show "\<forall>oi i. sat oi i M" by (rule H)
qed

lemma pigden_local:
  assumes h_ent: "entails_at oi F M"
      and h_fact: "\<forall>phi. phi : F \<longrightarrow> is_factual phi"
      and h_sat:  "satisfiable F"
  shows "\<forall>i. sat oi i M"
proof -
  have H: "\<forall>i. sat oi i M" (is "\<forall>i. ?P i")
  proof -
    have H2: "\<And>i. sat oi i M"
    proof -
      fix i
      from h_sat obtain oi0 i0 where oi0: "\<forall>phi. phi : F \<longrightarrow> sat oi0 i0 phi"
        unfolding satisfiable_def by blast
      show "sat oi i M"
      proof (rule h_ent[unfolded entails_at_def, rule_format])
        show "\<forall>phi. phi : F \<longrightarrow> sat oi i phi"
        proof
          fix phi
          assume hphi: "phi : F"
          from h_fact have hf: "is_factual phi" using hphi by blast
          from oi0 have hs: "sat oi0 i0 phi" using hphi by blast
          from factual_invariant[of phi oi0 i0 oi i, OF hf] hs show "sat oi i phi" by metis
        qed
      end
    qed
    show ?thesis by (rule allI, erule H2)
  end
  thus ?thesis .
qed

lemma countermodel_at_oi:
  assumes h_ent: "entails_at oi F M"
      and h_fact: "\<forall>phi. phi : F \<longrightarrow> is_factual phi"
      and h_sat:  "satisfiable F"
      and h_false: "\<exists>i. \<not> sat oi i M"
  shows False
proof -
  from h_false obtain i0 where hi0: "\<not> sat oi i0 M" by blast
  have hs: "sat oi i0 M"
    using pigden_local[OF h_ent h_fact h_sat] by blast
  from hi0 hs show False by contradiction
qed

lemma pigden_universal_where_false:
  assumes h_fact: "\<forall>phi. phi : F \<longrightarrow> is_factual phi"
      and h_sat:  "satisfiable F"
  shows "\<forall>oi. (\<exists>i. \<not> sat oi i M) \<longrightarrow> \<not> entails_at oi F M"
proof -
  have H: "\<forall>oi. (\<exists>i. \<not> sat oi i M) \<longrightarrow> \<not> entails_at oi F M" (is "\<forall>oi. ?P oi")
  proof -
    have H2: "\<And>oi. (\<exists>i. \<not> sat oi i M) \<Longrightarrow> \<not> entails_at oi F M"
    proof -
      fix oi
      assume h: "\<exists>i. \<not> sat oi i M"
      show "\<not> entails_at oi F M"
      proof (rule notI)
        assume h_ent: "entails_at oi F M"
        from countermodel_at_oi[OF h_ent h_fact h_sat h] show False by assumption
      qed
    qed
    show ?thesis by (rule allI, rule impI, erule H2)
  end
  thus ?thesis .
qed

definition non_vacuous :: "syn_form => bool" where
  "non_vacuous M = (\<exists>oi1. \<exists>oi2. \<exists>i1. \<exists>i2. sat oi1 i1 M \<and> \<not> sat oi2 i2 M)"

lemma ought_non_vacuous:
  "non_vacuous (Ought_Target No_Known_Should)"
  unfolding non_vacuous_def
proof (rule exI[of _ ought], rule exI[of _ "%c. False"],
       rule exI[of _ "%c. True"], rule exI[of _ "%c. True"])
  show "sat ought (%c. True) (Ought_Target No_Known_Should)
        \<and> \<not> sat (%c. False) (%c. True) (Ought_Target No_Known_Should)"
  proof (rule conjI)
    show "sat ought (%c. True) (Ought_Target No_Known_Should)"
      by (subst sat.simps(2), rule ought_no_known)
    show "\<not> sat (%c. False) (%c. True) (Ought_Target No_Known_Should)"
      by (subst sat.simps(2), simp)
  qed
qed

theorem pigden_universal_thesis_contradicts_my_argument:
  assumes pigden: "\<forall>oi. \<not> entails_at oi {Is_Case No_Known_Should}
                              (Ought_Target No_Known_Should)"
  shows False
proof -
  have h1: "entails_at ought {Is_Case No_Known_Should}
                            (Ought_Target No_Known_Should)"
    by (rule my_argument)
  have h2: "\<not> entails_at ought {Is_Case No_Known_Should}
                               (Ought_Target No_Known_Should)"
    using pigden by blast
  from h1 h2 show False by contradiction
qed

theorem pigden_theorem_scope_concrete:
  "(\<forall>oi. (\<exists>i. \<not> sat oi i (Ought_Target No_Known_Should))
         \<longrightarrow> \<not> entails_at oi {Is_Case No_Known_Should}
                             (Ought_Target No_Known_Should))
   \<and> (\<not> (\<forall>oi. \<exists>i. \<not> sat oi i (Ought_Target No_Known_Should)))"
proof (rule conjI)
  show "\<forall>oi. (\<exists>i. \<not> sat oi i (Ought_Target No_Known_Should))
             \<longrightarrow> \<not> entails_at oi {Is_Case No_Known_Should}
                                 (Ought_Target No_Known_Should)"
  proof -
    have H: "\<forall>oi. (\<exists>i. \<not> sat oi i (Ought_Target No_Known_Should))
             \<longrightarrow> \<not> entails_at oi {Is_Case No_Known_Should}
                                 (Ought_Target No_Known_Should)"
    proof (rule pigden_universal_where_false)
      show "\<forall>phi. phi : {Is_Case No_Known_Should} \<longrightarrow> is_factual phi"
      proof
        fix phi
        assume hphi: "phi : {Is_Case No_Known_Should}"
        have hp: "phi = Is_Case No_Known_Should" using hphi by simp
        from hp show "is_factual phi" by (subst hp, simp)
      qed
    next
      show "satisfiable {Is_Case No_Known_Should}"
        unfolding satisfiable_def
      proof (rule exI[of _ ought])
        show "\<exists>i. \<forall>phi. phi : {Is_Case No_Known_Should} \<longrightarrow> sat ought i phi"
        proof (rule exI[of _ "%c. True"])
          show "\<forall>phi. phi : {Is_Case No_Known_Should} \<longrightarrow> sat ought (%c. True) phi"
          proof
            fix phi
            assume hphi: "phi : {Is_Case No_Known_Should}"
            have hp: "phi = Is_Case No_Known_Should" using hphi by simp
            from hp show "sat ought (%c. True) phi" by (subst hp, simp add: sat.simps(1))
          qed
        qed
      qed
    qed
    thus ?thesis .
  qed
next
  show "\<not> (\<forall>oi. \<exists>i. \<not> sat oi i (Ought_Target No_Known_Should))"
  proof
    assume h: "\<forall>oi. \<exists>i. \<not> sat oi i (Ought_Target No_Known_Should)"
    have h1: "\<exists>i. \<not> sat ought i (Ought_Target No_Known_Should)"
      using h by blast
    from h1 obtain i where hi: "\<not> sat ought i (Ought_Target No_Known_Should)"
      by blast
    have h2: "sat ought i (Ought_Target No_Known_Should)"
      by (subst sat.simps(2), rule ought_no_known)
    from hi h2 show False by contradiction
  qed
qed

end
