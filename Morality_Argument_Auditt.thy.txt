theory Morality_Argument_Audit
  imports Main
begin

text \<open>
  A should is "known" when we know what we should do.
  The two cases are whether a should is known or not.
\<close>

datatype knowledge_case =
    Known_Should
  | No_Known_Should

definition should_known :: "knowledge_case \<Rightarrow> bool" where
  "should_known c \<longleftrightarrow> c = Known_Should"

definition investigate_purpose :: "knowledge_case \<Rightarrow> bool" where
  "investigate_purpose c \<longleftrightarrow> c = No_Known_Should"

text \<open>
  A should remains to be found when its status is not known.
\<close>

definition should_to_be_found :: "knowledge_case \<Rightarrow> bool" where
  "should_to_be_found c \<longleftrightarrow> \<not> should_known c"

lemma cases_exhaustive:
  "c = Known_Should \<or> c = No_Known_Should"
  by (cases c) simp_all

lemma no_known_should_means_investigate:
  assumes "\<not> should_known c"
  shows "investigate_purpose c"
  using assms
  unfolding should_known_def investigate_purpose_def
  by (cases c) simp_all

lemma investigate_when_should_unknown:
  assumes "c = No_Known_Should"
  shows "investigate_purpose c"
  using assms
  unfolding investigate_purpose_def
  by simp

lemma should_to_be_found_iff_investigate:
  "should_to_be_found c \<longleftrightarrow> investigate_purpose c"
  unfolding should_to_be_found_def
    should_known_def investigate_purpose_def
  by (cases c) simp_all


theorem should_status_exhaustive:
  "\<forall>c. should_known c \<or> should_to_be_found c"
proof
  fix c
  show "should_known c \<or> should_to_be_found c"
  proof (cases c)
    case Known_Should
    then show ?thesis
      unfolding should_known_def
      by simp
  next
    case No_Known_Should
    then show ?thesis
      unfolding should_known_def should_to_be_found_def
      by simp
  qed
qed
end
