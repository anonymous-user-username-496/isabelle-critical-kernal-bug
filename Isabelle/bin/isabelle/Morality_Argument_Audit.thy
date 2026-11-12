theory Morality_Argument_Audit
  imports "PAL.PAL" "GewirthPGCProof.GewirthArgument"
begin

datatype knowledge_case =
    Known_Should
  | No_Known_Should

definition should_known ::
  "\<alpha> => \<tau> => \<sigma> => i => bool"
where
  "should_known R phi W w <->
     (\<^bold>K R phi) W w"

definition moral_should ::
  "e => bool"
where
  "moral_should (x::e) <->
     \<lfloor>RightTo x FWB\<rfloor>\<^sup>D"

definition investigate_purpose ::
  "e => m => bool"
where
  "investigate_purpose (x::e) (E::m) <->
     \<lfloor>\<^bold>O\<^sub>i(ActsOnPurpose x E)\<rfloor>"

definition should_to_be_found ::
  "e => m => bool"
where
  "should_to_be_found (x::e) (E::m) <->
     investigate_purpose x E"

lemma Gewirth_moral_should:
  "\<lfloor>PPA (x::e) \<^bold>\<rightarrow> RightTo x FWB\<rfloor>\<^sup>D"
  using PGC_strong by blast

lemma obligation_explicit:
  "\<^bold>O\<^sub>i phi =
   (%c w.
      ob (pv w) (phi c) &
      (EX y. pv w y & ~phi c y))"
  by (rule ext, rule ext, simp)

lemma knowledge_explicit:
  "(\<bold>K R phi) W w =
   (ALL v. (W v & R w v) --> phi W v)"
  by simp

lemma cases_exhaustive:
  "c = Known_Should | c = No_Known_Should"
  for c :: knowledge_case
  by (cases c) simp_all

end
