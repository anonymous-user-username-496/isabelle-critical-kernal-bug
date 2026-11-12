theory Morality_Argument_Audit
  imports PAL GewirthArgument
begin

datatype knowledge_case =
    Known_Should
  | No_Known_Should

definition should_known ::
  "\<alpha> \<Rightarrow> \<tau> \<Rightarrow> \<sigma> \<Rightarrow> i \<Rightarrow> bool"
where
  "should_known R phi W w \<longleftrightarrow>
     (\<^bold>K R phi) W w"

definition moral_should ::
  "e \<Rightarrow> bool"
where
  "moral_should a \<longleftrightarrow>
     \<lfloor>RightTo a FWB\<rfloor>\<^sup>D"

definition investigate_purpose ::
  "e \<Rightarrow> m \<Rightarrow> bool"
where
  "investigate_purpose a E \<longleftrightarrow>
     \<lfloor>\<^bold>O\<^sub>i(ActsOnPurpose a E)\<rfloor>"

definition should_to_be_found ::
  "e \<Rightarrow> m \<Rightarrow> bool"
where
  "should_to_be_found a E \<longleftrightarrow>
     investigate_purpose a E"

lemma Gewirth_moral_should:
  "\<lfloor>PPA a \<^bold>\<rightarrow> RightTo a FWB\<rfloor>\<^sup>D"
  using PGC_strong by blast

lemma RightTo_explicit:
  "RightTo a FWB =
   \<^bold>O\<^sub>i(\<^bold>\<forall>b. \<^bold>\<not>InterferesWith b (FWB a))"
  unfolding RightTo_def
  by simp

lemma obligation_explicit:
  "\<^bold>O\<^sub>i phi =
   (\<lambda>c w.
      ob (pv w) (phi c) \<and>
      (\<exists>x. pv w x \<and> \<not>phi c x))"
  by (rule ext, rule ext, simp)

lemma knowledge_explicit:
  "(\<^bold>K R phi) W w =
   (\<forall>v. (W v \<and> R w v) \<longrightarrow> phi W v)"
  by simp

lemma cases_exhaustive:
  "c = Known_Should \<or> c = No_Known_Should"
  by (cases c) simp_all

end
