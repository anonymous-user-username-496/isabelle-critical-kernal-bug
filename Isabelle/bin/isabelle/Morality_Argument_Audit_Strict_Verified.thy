theory Morality_Argument_Audit_Strict_Verified
  imports Main
begin

datatype knowledge_case =
    Known_Should
  | No_Known_Should

definition should_known :: "knowledge_case => bool" where
  "should_known c = (c = Known_Should)"

definition should_to_be_found :: "knowledge_case => bool" where
  "should_to_be_found c = (~ should_known c)"

definition ought :: "knowledge_case => bool" where
  "ought c = (should_known c | should_to_be_found c)"

theorem should_status_exhaustive:
  "!c. should_known c | should_to_be_found c"
proof
  fix c
  show "should_known c | should_to_be_found c"
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
| "sat oi i (Not A)          = (~ sat oi i A)"
| "sat oi i (Imp A C)        = (sat oi i A --> sat oi i C)"

primrec is_factual :: "syn_form => bool" where
  "is_factual (Is_Case _)      = True"
| "is_factual (Ought_Target _) = False"
| "is_factual (Not A)          = is_factual A"
| "is_factual (Imp A C)        = (is_factual A & is_factual C)"

definition entails_at :: "interp => syn_form set => syn_form => bool" where
  "entails_at oi F M = (!i. (!phi. phi : F --> sat oi i phi) --> sat oi i M)"

definition entails_all :: "syn_form set => syn_form => bool" where
  "entails_all F M = (!oi. entails_at oi F M)"

definition satisfiable :: "syn_form set => bool" where
  "satisfiable F = (?oi. ?i. (!phi. phi : F --> sat oi i phi))"

definition valid :: "syn_form => bool" where
  "valid M = (!oi. !i. sat oi i M)"

definition substantive :: "syn_form => bool" where
  "substantive M = (~ valid M)"

lemma factual_invariant:
  "is_factual phi ==> sat oi i phi = sat oi' i' phi"
  by (induction phi) simp_all

lemma factual_entails_at_indep_fwd:
  assumes h_fact: "!phi. phi : F --> is_factual phi"
      and h: "!phi. phi : F --> sat oi i phi"
  shows "!phi. phi : F --> sat oi' i' phi"
proof
  fix phi
  assume hphi: "phi : F"
  with h_fact have "is_factual phi" by blast
  with factual_invariant[of phi oi i oi' i'] h hphi
  show "sat oi' i' phi" by simp
qed

lemma factual_entails_at_indep_bwd:
  assumes h_fact: "!phi. phi : F --> is_factual phi"
      and h: "!phi. phi : F --> sat oi' i' phi"
  shows "!phi. phi : F --> sat oi i phi"
proof
  fix phi
  assume hphi: "phi : F"
  with h_fact have "is_factual phi" by blast
  with factual_invariant[of phi oi' i' oi i] h hphi
  show "sat oi i phi" by simp
qed

lemma my_argument:
  "entails_at ought {Is_Case No_Known_Should} (Ought_Target No_Known_Should)"
  unfolding entails_at_def
proof (rule allI impI)
  fix i
  assume h: "!phi. phi : {Is_Case No_Known_Should} --> sat ought i phi"
  show "sat ought i (Ought_Target No_Known_Should)"
    by (simp add: ought_no_known)
qed

theorem pigden_conservativeness:
  assumes h_ent: "entails_all F M"
      and h_fact: "!phi. phi : F --> is_factual phi"
      and h_sat:  "satisfiable F"
  shows "valid M"
proof (rule allI)+
  fix oi i
  from h_sat obtain oi0 i0 where oi0: "!phi. phi : F --> sat oi0 i0 phi"
    unfolding satisfiable_def by blast
  from h_ent have h_at: "entails_at oi F M"
    unfolding entails_all_def by (rule allE)
  show "sat oi i M"
  proof (rule h_at[unfolded entails_at_def, rule_format])
    show "!phi. phi : F --> sat oi i phi"
    proof
      fix phi
      assume hphi: "phi : F"
      with h_fact have "is_factual phi" by blast
      with factual_invariant[of phi oi0 i0 oi i] oi0 hphi
      show "sat oi i phi" by simp
    qed
  qed
qed

lemma pigden_local:
  assumes h_ent: "entails_at oi F M"
      and h_fact: "!phi. phi : F --> is_factual phi"
      and h_sat:  "satisfiable F"
  shows "!i. sat oi i M"
proof
  fix i
  from h_sat obtain oi0 i0 where oi0: "!phi. phi : F --> sat oi0 i0 phi"
    unfolding satisfiable_def by blast
  show "sat oi i M"
  proof (rule h_ent[unfolded entails_at_def, rule_format])
    show "!phi. phi : F --> sat oi i phi"
    proof
      fix phi
      assume hphi: "phi : F"
      with h_fact have "is_factual phi" by blast
      with factual_invariant[of phi oi0 i0 oi i] oi0 hphi
      show "sat oi i phi" by simp
    qed
  qed
qed

lemma countermodel_at_oi:
  assumes h_ent: "entails_at oi F M"
      and h_fact: "!phi. phi : F --> is_factual phi"
      and h_sat:  "satisfiable F"
      and h_false: "?i. ~ sat oi i M"
  shows False
proof -
  from h_false obtain i where hi: "~ sat oi i M" by blast
  from pigden_local[OF h_ent h_fact h_sat] have "sat oi i M" by (rule allE)
  with hi show False by simp
qed

lemma pigden_universal_where_false:
  assumes h_fact: "!phi. phi : F --> is_factual phi"
      and h_sat:  "satisfiable F"
  shows "!oi. (?i. ~ sat oi i M) --> ~ entails_at oi F M"
proof (rule allI impI)
  fix oi
  assume h: "?i. ~ sat oi i M"
  show "~ entails_at oi F M"
  proof
    assume h_ent: "entails_at oi F M"
    from countermodel_at_oi[OF h_ent h_fact h_sat h] show False .
  qed
qed

definition non_vacuous :: "syn_form => bool" where
  "non_vacuous M = (?oi1. ?oi2. ?i1. ?i2. sat oi1 i1 M & ~ sat oi2 i2 M)"

lemma ought_non_vacuous:
  "non_vacuous (Ought_Target No_Known_Should)"
  unfolding non_vacuous_def
proof (rule exI[of _ ought], rule exI[of _ "%c. False"],
       rule exI[of _ "%c. True"], rule exI[of _ "%c. True"])
  show "sat ought (%c. True) (Ought_Target No_Known_Should)
        & ~ sat (%c. False) (%c. True) (Ought_Target No_Known_Should)"
  proof (rule conjI)
    show "sat ought (%c. True) (Ought_Target No_Known_Should)"
      by (simp add: ought_no_known)
    show "~ sat (%c. False) (%c. True) (Ought_Target No_Known_Should)"
      by simp
  qed
qed

theorem pigden_universal_thesis_contradicts_my_argument:
  assumes pigden: "!oi. ~ entails_at oi {Is_Case No_Known_Should}
                              (Ought_Target No_Known_Should)"
  shows False
proof -
  have h1: "entails_at ought {Is_Case No_Known_Should}
                            (Ought_Target No_Known_Should)"
    by (rule my_argument)
  have h2: "~ entails_at ought {Is_Case No_Known_Should}
                               (Ought_Target No_Known_Should)"
    using pigden by (rule allE)
  from h1 h2 show False by simp
qed

theorem pigden_theorem_scope_concrete:
  "(!oi. (?i. ~ sat oi i (Ought_Target No_Known_Should))
         --> ~ entails_at oi {Is_Case No_Known_Should}
                             (Ought_Target No_Known_Should))
   & (~ (!oi. ?i. ~ sat oi i (Ought_Target No_Known_Should)))"
proof (rule conjI)
  show "!oi. (?i. ~ sat oi i (Ought_Target No_Known_Should))
             --> ~ entails_at oi {Is_Case No_Known_Should}
                                 (Ought_Target No_Known_Should)"
  proof (rule pigden_universal_where_false)
    show "!phi. phi : {Is_Case No_Known_Should} --> is_factual phi"
    proof
      fix phi
      assume hphi: "phi : {Is_Case No_Known_Should}"
      show "is_factual phi"
        using hphi by simp
    qed
  next
    show "satisfiable {Is_Case No_Known_Should}"
      unfolding satisfiable_def
    proof (rule exI[of _ ought], rule exI[of _ "%c. True"])
      show "!phi. phi : {Is_Case No_Known_Should} --> sat ought (%c. True) phi"
      proof
        fix phi
        assume hphi: "phi : {Is_Case No_Known_Should}"
        show "sat ought (%c. True) phi"
          using hphi by simp
      qed
    qed
  qed
next
  show "~ (!oi. ?i. ~ sat oi i (Ought_Target No_Known_Should))"
  proof
    assume h: "!oi. ?i. ~ sat oi i (Ought_Target No_Known_Should)"
    have h1: "?i. ~ sat ought i (Ought_Target No_Known_Should)"
      using h by (rule allE)
    from h1 obtain i where hi: "~ sat ought i (Ought_Target No_Known_Should)"
      by blast
    have h2: "sat ought i (Ought_Target No_Known_Should)"
      by (simp add: ought_no_known)
    from hi h2 show False by simp
  qed
qed

end
